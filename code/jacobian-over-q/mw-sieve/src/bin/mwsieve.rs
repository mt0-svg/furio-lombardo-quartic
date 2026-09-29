//! Mordell-Weil sieve for C with the subgroup Gamma = <B1, B2, B3> of J(Q).
//!
//! Usage: mwsieve [--pmax B] [--ells 2,3,5,7] [--levels 2,2,3,2,5,...] [--greedy STEPS --cap C]
//!                [--pmin A] [--cache file] [--merge file] [--no-skip] [--out file]
//! (--pmin only restricts step A, to split it into several jobs. The per-prime directory
//! <cache>.d used to resume step A belongs to the --ells list and --no-skip setting that created it.)
//!
//! Step A (per sieving prime p, parallel; cached): for each ℓ in --ells dividing #J(F_p), a basis
//! of the ℓ-Sylow subgroup and the discrete logs of cof_ℓ·B_j (j = 1..3) and of cof_ℓ·[P - P0]
//! for every P in C(F_p), where cof_ℓ = #J/ℓ^{v_ℓ}. This gives the homomorphism
//! J(F_p) -> ⊕_{ℓ,i} Z/ℓ^{e_i} whose reduction mod ℓ^{min(a_ℓ, e_i)} is J(F_p) -> J(F_p)/N J(F_p)
//! (restricted to the ℓ dividing N), for N = ∏ ℓ^{a_ℓ}.
//!
//! Step B: N runs through the products of the prefixes of --levels. A coset a ∈ (Z/N)^3 survives
//! if for every sieving prime p the image of a1 B1 + a2 B2 + a3 B3 in J(F_p)/N J(F_p) lies in the
//! image of C(F_p) under P -> [P - P0]. Survivors mod N are lifted to N·ℓ (ℓ^3 lifts each) and
//! tested again. If [J(Q) : Gamma] is prime to N, the class of [P - P0] mod N J(Q) of any
//! P ∈ C(Q) is a survivor.

use base::abgroup::{ipow, AbGroup, Sylow};
use base::ff::Gf;
use base::ffpoly::SplitMix64;
use furio_lombardo_quartic_mw_sieve::mw;
use rayon::prelude::*;
use std::collections::{BTreeMap, HashSet};
use std::io::{BufRead, Write};
use std::time::Instant;

#[derive(Clone, Debug)]
struct LData {
    ell: u64,
    exps: Vec<u32>,
    gens: Vec<Vec<u128>>, // 3 vectors
    pts: Vec<Vec<u128>>,  // one vector per point
}

#[derive(Clone, Debug)]
struct PData {
    p: u64,
    nj: u128,
    npts: usize,
    known: Vec<usize>, // indices of P0, P1, P2, P3
    ls: Vec<LData>,
}

fn gamma_gens(j: &base::jac_quartic::Quartic<base::ff::Fp>) -> Option<Vec<base::jac_quartic::Elt<u64>>> {
    let c = mw::classes(j);
    let g3 = c.gen3?;
    let qb = c.qb?;
    let b2 = j.sub(&j.sub(&g3, &c.d2), &j.mul_u128(&c.d3, 3));
    let b3 = j.add(&j.sub(&qb, &c.d1), &c.d3);
    Some(vec![c.d1.clone(), b2, b3])
}

fn step_a(p: u64, nj: u128, ells: &[u64], min_smooth: u128) -> Option<PData> {
    let ls_todo: Vec<(u64, u32)> = ells
        .iter()
        .filter(|&&l| nj % l as u128 == 0)
        .map(|&l| {
            let mut v = 0;
            let mut t = nj;
            while t % l as u128 == 0 {
                t /= l as u128;
                v += 1;
            }
            (l, v)
        })
        .collect();
    if ls_todo.is_empty() {
        return None;
    }
    // no information when J(F_p)/N J(F_p) is not larger than C(F_p), whatever N
    let smooth_all: u128 = ls_todo.iter().map(|&(l, v)| ipow(l, v)).product();
    if smooth_all <= min_smooth {
        return None;
    }
    let j = mw::setup(p);
    let gens = gamma_gens(&j)?;
    let pts = j.all_points();
    let known: Vec<usize> = [[0i64, 0, 1], mw::P1, mw::P2, mw::P3]
        .iter()
        .map(|&q| {
            let r = mw::reduce_pt(p, q);
            pts.iter().position(|&x| x == r).expect("known point")
        })
        .collect();
    let e2 = Gf::<2>::standard(p);
    let e3 = Gf::<3>::standard(p);
    let mut rng = SplitMix64(0x5151 ^ p);
    let smooth: u128 = ls_todo.iter().map(|&(l, v)| ipow(l, v)).product();
    let mprime = nj / smooth;
    let mut sylows = Vec::new();
    for &(ell, v) in &ls_todo {
        let cof = nj / ipow(ell, v);
        let s = Sylow::build(
            &j,
            ell,
            v,
            || {
                let r = j.random_elt(&mut rng, &e2, &e3);
                j.mul(&r, cof)
            },
            40000, // table of H[ℓ] up to ℓ^k <= 40000 (167^2 at p = 1669, where J(F_p)[167] has rank 3)
            500,
        )
        .expect("Sylow basis");
        let g: Vec<Vec<u128>> = gens.iter().map(|b| s.dlog(&j, &j.mul(b, cof)).expect("dlog gen")).collect();
        sylows.push((s, g, smooth / ipow(ell, v)));
    }
    let mut ptcoords: Vec<Vec<Vec<u128>>> = vec![Vec::with_capacity(pts.len()); ls_todo.len()];
    for &pt in &pts {
        let y = j.mul(&j.point_class(pt), mprime);
        for (k, (s, _, other)) in sylows.iter().enumerate() {
            let z = j.mul(&y, *other);
            ptcoords[k].push(s.dlog(&j, &z).expect("dlog point"));
        }
    }
    let ls = sylows
        .into_iter()
        .zip(ptcoords)
        .map(|((s, g, _), pc)| LData { ell: s.ell, exps: s.exps.clone(), gens: g, pts: pc })
        .collect();
    Some(PData { p, nj, npts: pts.len(), known, ls })
}

fn write_cache(path: &str, data: &[PData]) {
    let mut w = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
    for d in data {
        write_block(&mut w, d);
    }
}

fn write_block(w: &mut dyn Write, d: &PData) {
    {
        let kn: Vec<String> = d.known.iter().map(|x| x.to_string()).collect();
        writeln!(w, "P {} {} {} {}", d.p, d.nj, d.npts, kn.join(",")).unwrap();
        for l in &d.ls {
            let ex: Vec<String> = l.exps.iter().map(|x| x.to_string()).collect();
            writeln!(w, "L {} {}", l.ell, ex.join(",")).unwrap();
            for g in &l.gens {
                let s: Vec<String> = g.iter().map(|x| x.to_string()).collect();
                writeln!(w, "G {}", s.join(",")).unwrap();
            }
            for x in &l.pts {
                let s: Vec<String> = x.iter().map(|x| x.to_string()).collect();
                writeln!(w, "X {}", s.join(",")).unwrap();
            }
        }
    }
}

fn read_cache(path: &str) -> Option<Vec<PData>> {
    let f = std::fs::File::open(path).ok()?;
    let mut out: Vec<PData> = Vec::new();
    let parse = |s: &str| -> Vec<u128> {
        if s.is_empty() {
            vec![]
        } else {
            s.split(',').map(|x| x.parse().unwrap()).collect()
        }
    };
    for line in std::io::BufReader::new(f).lines() {
        let line = line.unwrap();
        let w: Vec<&str> = line.split(' ').collect();
        match w[0] {
            "P" => out.push(PData {
                p: w[1].parse().unwrap(),
                nj: w[2].parse().unwrap(),
                npts: w[3].parse().unwrap(),
                known: w[4].split(',').map(|x| x.parse().unwrap()).collect(),
                ls: vec![],
            }),
            "L" => out.last_mut().unwrap().ls.push(LData {
                ell: w[1].parse().unwrap(),
                exps: w[2].split(',').map(|x| x.parse().unwrap()).collect(),
                gens: vec![],
                pts: vec![],
            }),
            "G" => out.last_mut().unwrap().ls.last_mut().unwrap().gens.push(parse(w.get(1).copied().unwrap_or(""))),
            "X" => out.last_mut().unwrap().ls.last_mut().unwrap().pts.push(parse(w.get(1).copied().unwrap_or(""))),
            _ => panic!("bad cache line"),
        }
    }
    Some(out)
}

/// Sieve data of one prime at one level: moduli, reduced generator images, image set of C(F_p).
struct Level {
    p: u64,
    moduli: Vec<u128>,
    gens: Vec<Vec<u128>>, // [j][i]
    image: HashSet<u128>,
    frac: f64,
    known_codes: Vec<u128>,
}

fn level_data(d: &PData, nexp: &BTreeMap<u64, u32>) -> Option<Level> {
    let mut moduli = Vec::new();
    let mut gens = vec![Vec::new(); 3];
    let mut cols: Vec<(usize, usize)> = Vec::new(); // (index in ls, i)
    for (k, l) in d.ls.iter().enumerate() {
        let a = *nexp.get(&l.ell).unwrap_or(&0);
        if a == 0 {
            continue;
        }
        for (i, &e) in l.exps.iter().enumerate() {
            let m = ipow(l.ell, e.min(a));
            moduli.push(m);
            for jx in 0..3 {
                gens[jx].push(l.gens[jx][i] % m);
            }
            cols.push((k, i));
        }
    }
    if moduli.is_empty() {
        return None;
    }
    let size: u128 = moduli.iter().product();
    let code_pt = |idx: usize| -> u128 {
        let mut c = 0u128;
        let mut r = 1u128;
        for (t, &(k, i)) in cols.iter().enumerate() {
            let v = d.ls[k].pts[idx][i] % moduli[t];
            c += v * r;
            r *= moduli[t];
        }
        c
    };
    let image: HashSet<u128> = (0..d.npts).map(code_pt).collect();
    let known_codes = d.known.iter().map(|&i| code_pt(i)).collect();
    let frac = image.len() as f64 / size as f64;
    Some(Level { p: d.p, moduli, gens, image, frac, known_codes })
}

fn code_of(lv: &Level, a: &[u128; 3]) -> u128 {
    let mut c = 0u128;
    let mut r = 1u128;
    for (t, &m) in lv.moduli.iter().enumerate() {
        let v = (a[0] % m * lv.gens[0][t] + a[1] % m * lv.gens[1][t] + a[2] % m * lv.gens[2][t]) % m;
        c += v * r;
        r *= m;
    }
    c
}

/// Lift the survivors mod n to n·ell and keep those passing every informative prime at the
/// exponents `nexp` (which must already include the new factor ell).
fn lift_filter(data: &[PData], surv: &[[u128; 3]], n: u128, ell: u64, nexp: &BTreeMap<u64, u32>) -> (Vec<[u128; 3]>, Vec<Level>, usize, f64) {
    let nn = n * ell as u128;
    let all_lvs: Vec<Level> = data.par_iter().filter_map(|d| level_data(d, nexp)).collect();
    let mut idx: Vec<usize> = (0..all_lvs.len()).filter(|&i| all_lvs[i].frac < 1.0).collect();
    idx.sort_by(|&a, &b| all_lvs[a].frac.partial_cmp(&all_lvs[b].frac).unwrap());
    let lvs: Vec<&Level> = idx.iter().map(|&i| &all_lvs[i]).collect();
    let lifts: Vec<[u128; 3]> = surv
        .iter()
        .flat_map(|s| {
            let s = *s;
            (0..ell as u128).flat_map(move |t0| {
                (0..ell as u128).flat_map(move |t1| {
                    (0..ell as u128).map(move |t2| [(s[0] + n * t0) % nn, (s[1] + n * t1) % nn, (s[2] + n * t2) % nn])
                })
            })
        })
        .collect();
    let mut out: Vec<[u128; 3]> = lifts
        .into_par_iter()
        .filter(|a| lvs.iter().all(|lv| lv.image.contains(&code_of(lv, a))))
        .collect();
    out.sort();
    let logexp: f64 = lvs.iter().map(|l| l.frac.ln()).sum::<f64>() + 3.0 * (nn as f64).ln();
    let ninf = lvs.len();
    (out, all_lvs, ninf, logexp)
}

fn report(w: &mut dyn Write, n: u128, nexp: &BTreeMap<u64, u32>, nlifts: usize, surv: &[[u128; 3]], ninf: usize, logexp: f64, all_lvs: &[Level]) {
    writeln!(
        w,
        "N = {} ({:?}): {} lifts, {} survivors, {} informative primes, expected fake survivors exp({:.1})",
        n, nexp, nlifts, surv.len(), ninf, logexp
    )
    .unwrap();
    if surv.len() <= 12 {
        writeln!(w, "  survivors: {:?}", surv).unwrap();
    }
    // cosets of the known points: survivors whose image equals that of [P_i - P0] at every prime
    if surv.len() <= 2000 {
        let mut desc = Vec::new();
        for i in 0..4 {
            let m: Vec<&[u128; 3]> = surv
                .iter()
                .filter(|a| all_lvs.iter().all(|lv| code_of(lv, a) == lv.known_codes[i]))
                .collect();
            desc.push(format!("P{} -> {:?}", i, m));
        }
        writeln!(w, "  known points: {}", desc.join("; ")).unwrap();
    }
    w.flush().unwrap();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str| args.iter().position(|a| a == k).map(|i| args[i + 1].clone());
    let lpath = get("--lpoly").unwrap_or("code/jacobian-over-q/lpoly/lpoly_C.txt".into());
    let jpath = get("--jorder").unwrap_or("code/jacobian-over-q/mw-sieve/jorder_C.txt".into());
    let pmax: u64 = get("--pmax").map(|s| s.parse().unwrap()).unwrap_or(2000);
    let pmin: u64 = get("--pmin").map(|s| s.parse().unwrap()).unwrap_or(0);
    let ells: Vec<u64> = get("--ells")
        .unwrap_or("2,3,5,7".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    let levels: Vec<u64> = get("--levels")
        .unwrap_or("2,2,3,2,5,7".into())
        .split(',')
        .map(|s| s.parse().unwrap())
        .collect();
    // greedy mode: --greedy STEPS; at each step every ell of --ells whose exponent in N is below
    // the largest exponent of ell in the #J(F_p) is tried, and the one leaving the fewest
    // survivors is kept (ties: the larger ell). Stops when the best candidate leaves more than
    // --cap survivors or N would exceed 2^120.
    let greedy: Option<usize> = get("--greedy").map(|s| s.parse().unwrap());
    let cap: usize = get("--cap").map(|s| s.parse().unwrap()).unwrap_or(4);
    // --first-fit: in greedy mode, try the ells in increasing order and keep the first one that leaves
    // at most --cap survivors (much cheaper than trying all of them at every step)
    let first_fit = args.iter().any(|a| a == "--first-fit");
    let cache = get("--cache");
    // --no-skip: keep every prime in step A (by default a prime is skipped when the product of the
    // ell-parts of #J(F_p) over --ells is at most 2p)
    let no_skip = args.iter().any(|a| a == "--no-skip");
    let out = get("--out");
    let mut w: Box<dyn Write> = match &out {
        Some(f) => Box::new(std::fs::File::create(f).unwrap()),
        None => Box::new(std::io::stdout()),
    };
    let t0 = Instant::now();
    let data: Vec<PData> = match cache.as_ref().and_then(|c| read_cache(c)) {
        Some(d) => d,
        None => {
            let orders = mw::load_orders(&lpath, &jpath);
            let ps: Vec<(u64, u128)> = orders.iter().filter(|(&p, _)| p >= pmin && p <= pmax).map(|(&p, &n)| (p, n)).collect();
            // with --cache, each prime is also written at once to <cache>.d/<p> (atomic rename), and
            // primes already there are not recomputed: a run killed by a time limit can be resumed
            let dir = cache.as_ref().map(|c| format!("{}.d", c));
            if let Some(dd) = &dir {
                std::fs::create_dir_all(dd).unwrap();
            }
            let mut ps = ps;
            ps.sort_by(|a, b| b.0.cmp(&a.0));
            let mut d: Vec<PData> = ps
                .par_iter()
                .filter_map(|&(p, nj)| {
                    if let Some(dd) = &dir {
                        if let Some(mut v) = read_cache(&format!("{}/{}", dd, p)) {
                            return v.pop();
                        }
                        if std::path::Path::new(&format!("{}/{}.none", dd, p)).exists() {
                            return None;
                        }
                    }
                    let t = Instant::now();
                    let r = step_a(p, nj, &ells, if no_skip { 0 } else { 2 * p as u128 });
                    eprintln!("step A p = {} ({:.1}s){}", p, t.elapsed().as_secs_f64(), if r.is_some() { "" } else { " none" });
                    if let Some(dd) = &dir {
                        match &r {
                            Some(x) => {
                                let tmp = format!("{}/{}.tmp", dd, p);
                                let mut f = std::fs::File::create(&tmp).unwrap();
                                write_block(&mut f, x);
                                f.sync_all().unwrap();
                                std::fs::rename(&tmp, format!("{}/{}", dd, p)).unwrap();
                            }
                            None => {
                                std::fs::File::create(format!("{}/{}.none", dd, p)).unwrap();
                            }
                        }
                    }
                    r
                })
                .collect();
            d.sort_by_key(|x| x.p);
            if let Some(c) = &cache {
                write_cache(c, &d);
            }
            d
        }
    };
    let mut data: Vec<PData> = data.into_iter().filter(|d| d.p <= pmax).collect();
    // --merge FILE: step A data for further ells (a cache written with the same point enumeration),
    // appended prime by prime; the point counts and the positions of the known points must agree.
    if let Some(mf) = get("--merge") {
        let extra = read_cache(&mf).expect("merge file");
        for e in extra.into_iter().filter(|e| e.p <= pmax) {
            match data.iter_mut().find(|d| d.p == e.p) {
                Some(d) => {
                    assert!(d.nj == e.nj && d.npts == e.npts && d.known == e.known, "merge: p = {} does not match", e.p);
                    for l in e.ls {
                        assert!(d.ls.iter().all(|x| x.ell != l.ell), "merge: ell = {} twice at p = {}", l.ell, e.p);
                        d.ls.push(l);
                    }
                }
                None => data.push(e),
            }
        }
        data.sort_by_key(|x| x.p);
    }
    writeln!(w, "# Mordell-Weil sieve, Gamma = <B1, B2, B3>, {} sieving primes p <= {} (step A {:.1}s)", data.len(), pmax, t0.elapsed().as_secs_f64()).unwrap();
    let ps: Vec<String> = data.iter().map(|d| d.p.to_string()).collect();
    writeln!(w, "# sieving primes: {}", ps.join(" ")).unwrap();
    let mut nexp: BTreeMap<u64, u32> = BTreeMap::new();
    let mut n: u128 = 1;
    let mut surv: Vec<[u128; 3]> = vec![[0, 0, 0]];
    // fixed levels (alone, or replayed before the greedy steps when --levels is given with --greedy)
    if greedy.is_none() || get("--levels").is_some() {
        {
            for &ell in &levels {
                assert!(ells.contains(&ell), "level prime not in --ells");
                *nexp.entry(ell).or_insert(0) += 1;
                let nlifts = surv.len() * (ell as usize).pow(3);
                let (s, all_lvs, ninf, logexp) = lift_filter(&data, &surv, n, ell, &nexp);
                surv = s;
                n *= ell as u128;
                report(&mut *w, n, &nexp, nlifts, &surv, ninf, logexp, &all_lvs);
            }
        }
    }
    if let Some(steps) = greedy {
        {
            // largest useful exponent of each ell
            let mut maxe: BTreeMap<u64, u32> = BTreeMap::new();
            for d in &data {
                for l in &d.ls {
                    let e = *l.exps.iter().max().unwrap_or(&0);
                    let m = maxe.entry(l.ell).or_insert(0);
                    *m = (*m).max(e);
                }
            }
            writeln!(w, "# largest exponents: {:?}", maxe).unwrap();
            for step in 0..steps {
                let mut best: Option<(usize, u64, Vec<[u128; 3]>, Vec<Level>, usize, f64)> = None;
                let mut tried = Vec::new();
                let mut order: Vec<u64> = ells.clone();
                if first_fit {
                    order.sort();
                }
                for &ell in &order {
                    if first_fit && best.as_ref().map_or(false, |b| b.0 <= cap) {
                        break;
                    }
                    let cur = *nexp.get(&ell).unwrap_or(&0);
                    if cur >= *maxe.get(&ell).unwrap_or(&0) {
                        continue;
                    }
                    if (n as f64) * (ell as f64) > 2f64.powi(120) {
                        continue;
                    }
                    let nlifts = surv.len() * (ell as usize).pow(3);
                    if nlifts > 400_000_000 {
                        continue;
                    }
                    let mut ne = nexp.clone();
                    *ne.entry(ell).or_insert(0) += 1;
                    let (s, lv, ninf, le) = lift_filter(&data, &surv, n, ell, &ne);
                    tried.push(format!("{}:{}", ell, s.len()));
                    let better = match &best {
                        None => true,
                        Some((bs, bl, ..)) => s.len() < *bs || (s.len() == *bs && ell > *bl),
                    };
                    if better {
                        best = Some((s.len(), ell, s, lv, ninf, le));
                    }
                }
                writeln!(w, "# step {}: candidates (ell:survivors) {}", step, tried.join(" ")).unwrap();
                let Some((ns, ell, s, lv, ninf, le)) = best else {
                    writeln!(w, "# no candidate left").unwrap();
                    break;
                };
                if ns > cap {
                    writeln!(w, "# best candidate ell = {} leaves {} > cap = {} survivors; stop", ell, ns, cap).unwrap();
                    break;
                }
                let nlifts = surv.len() * (ell as usize).pow(3);
                *nexp.entry(ell).or_insert(0) += 1;
                surv = s;
                n *= ell as u128;
                report(&mut *w, n, &nexp, nlifts, &surv, ninf, le, &lv);
            }
        }
    }
    writeln!(w, "# final N = {} = {:?}, {} survivors", n, nexp, surv.len()).unwrap();
    writeln!(w, "# total {:.1}s", t0.elapsed().as_secs_f64()).unwrap();
}
