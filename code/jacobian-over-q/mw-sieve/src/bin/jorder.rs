//! #J(F_p) from N1, N2 and the Jacobian arithmetic (baby steps / giant steps on c3).
//!
//! Usage: jorder --lpoly code/jacobian-over-q/lpoly/lpoly_C.txt [--pmin A] [--pmax B] [--out file]
//!
//! L(T) = 1 + c1 T + c2 T^2 + c3 T^3 + p c2 T^4 + p^2 c1 T^5 + p^3 T^6, with c1, c2 known from
//! N1, N2 (data file) and |c3| <= 20 p^{3/2} (Weil). #J(F_p) = L(1) = A + c3 with
//! A = 1 + c1 + c2 + p c2 + p^2 c1 + p^3. For random x in J(F_p), all c3 in the Weil interval
//! with (A + c3) x = 0 are found by baby steps / giant steps; the candidate sets are
//! intersected over random elements until one candidate is left. Since the true value is in
//! every candidate set, a single survivor is #J(F_p) (proof, given the arithmetic).
//! For primes with known full L-polynomial the result is compared with the data.

use base::abgroup::AbGroup;
use base::ff::Gf;
use base::ffpoly::SplitMix64;
use furio_lombardo_quartic_mw_sieve::mw;
use rayon::prelude::*;
use std::collections::{BTreeSet, HashMap};
use std::io::Write;

fn isqrt(n: u128) -> u128 {
    let mut x = (n as f64).sqrt() as u128;
    while x * x > n {
        x -= 1;
    }
    while (x + 1) * (x + 1) <= n {
        x += 1;
    }
    x
}

/// Range of c3 allowed by the real Weil polynomial (float computation, widened by a margin;
/// falls back to the Weil bound 20 p^{3/2}).
fn c3_range(p: u64, c1: i128, c2: i128) -> (i128, i128) {
    let pf = p as f64;
    let b = 2.0 * pf.sqrt();
    let s1 = -c1 as f64;
    let s2 = (c2 - 3 * p as i128) as f64;
    let g = |x: f64| x * x * x - s1 * x * x + s2 * x;
    let weil = 20 * isqrt((p as u128).pow(3)) as i128 + 20;
    let d = s1 * s1 - 3.0 * s2;
    if d < 0.0 {
        panic!("p = {}: no real Weil polynomial", p);
    }
    let xm = (s1 - d.sqrt()) / 3.0;
    let xp = (s1 + d.sqrt()) / 3.0;
    let s3lo = g(xp).max(g(-b));
    let s3hi = g(xm).min(g(b));
    let margin = 1e-7 * (b * b * b + s1.abs() * b * b + s2.abs() * b) + 2.0;
    let (s3lo, s3hi) = (s3lo - margin, s3hi + margin);
    let pc = 2 * p as i128 * c1;
    let lo = (pc - s3hi.ceil() as i128).max(-weil);
    let hi = (pc - s3lo.floor() as i128).min(weil);
    (lo, hi)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str| args.iter().position(|a| a == k).map(|i| args[i + 1].clone());
    let lpath = get("--lpoly").unwrap_or("code/jacobian-over-q/lpoly/lpoly_C.txt".into());
    let pmin: u64 = get("--pmin").map(|s| s.parse().unwrap()).unwrap_or(3);
    let pmax: u64 = get("--pmax").map(|s| s.parse().unwrap()).unwrap_or(2000);
    let out = get("--out");
    let text = std::fs::read_to_string(&lpath).unwrap();
    // p -> (N1, c1, c2, known #J)
    let mut rows: Vec<(u64, u64, i128, i128, Option<u128>)> = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        let w: Vec<&str> = line.split_whitespace().collect();
        let p: u64 = w[0].parse().unwrap();
        if p < pmin || p > pmax {
            continue;
        }
        let nj = if w[7] == "-" { None } else { Some(w[7].parse().unwrap()) };
        rows.push((p, w[1].parse().unwrap(), w[4].parse().unwrap(), w[5].parse().unwrap(), nj));
    }
    let mut res: Vec<(u64, String)> = rows
        .par_iter()
        .map(|&(p, n1, c1, c2, known)| {
            let j = mw::setup(p);
            assert_eq!(j.all_points().len() as u64, n1);
            let e2 = Gf::<2>::standard(p);
            let e3 = Gf::<3>::standard(p);
            let mut rng = SplitMix64(0x1234 ^ p);
            let pp = p as i128;
            let a = 1 + c1 + c2 + pp * c2 + pp * pp * c1 + pp * pp * pp;
            let (c3lo, c3hi) = c3_range(p, c1, c2);
            let lo = a + c3lo; // candidate orders M in [lo, lo + w]
            let w = (c3hi - c3lo) as u128;
            let m = isqrt(w) + 1;
            let mut cands: Option<BTreeSet<u128>> = None;
            let mut used = 0;
            let mut checks = 0;
            let mut stale = 0;
            while cands.as_ref().map_or(true, |c| c.len() > 1) || checks < 3 {
                if stale >= 8 || used >= 60 {
                    break;
                }
                let x = j.random_elt(&mut rng, &e2, &e3);
                used += 1;
                if let Some(c) = &cands {
                    if c.len() == 1 {
                        // extra checks of the single candidate
                        let mm = *c.iter().next().unwrap();
                        assert!(j.is_zero(&j.mul(&x, mm)), "p = {}: candidate fails", p);
                        checks += 1;
                        continue;
                    }
                }
                // s x = y with y = -lo x, s in [0, w]
                let mut table: HashMap<base::jac_quartic::Elt<u64>, u128> = HashMap::new();
                let mut cur = j.zero();
                let mut small_order = None;
                for i in 0..m {
                    if let Some(&i0) = table.get(&cur) {
                        small_order = Some(i - i0);
                        break;
                    }
                    table.insert(cur.clone(), i);
                    cur = j.add(&cur, &x);
                }
                let found: BTreeSet<u128> = if let Some(ord) = small_order {
                    // ord = order of x: candidates are the multiples of ord in the interval
                    let first = (lo as u128).div_ceil(ord) * ord;
                    (0..)
                        .map(|t| first + t * ord)
                        .take_while(|&mm| mm <= lo as u128 + w)
                        .collect()
                } else {
                    let step = j.neg(&cur); // -m x
                    let mut y = j.neg(&j.mul(&x, lo as u128));
                    let mut found = BTreeSet::new();
                    let mut jj = 0u128;
                    while jj * m <= w {
                        if let Some(&i) = table.get(&y) {
                            let s = jj * m + i;
                            if s <= w {
                                found.insert(lo as u128 + s);
                            }
                        }
                        y = j.add(&y, &step);
                        jj += 1;
                    }
                    found
                };
                let before = cands.as_ref().map(|c| c.len());
                cands = Some(match cands {
                    None => found,
                    Some(c) => c.intersection(&found).copied().collect(),
                });
                assert!(!cands.as_ref().unwrap().is_empty(), "p = {}: no candidate", p);
                if before == cands.as_ref().map(|c| c.len()) {
                    stale += 1;
                } else {
                    stale = 0;
                }
            }
            let cands = cands.unwrap();
            if cands.len() > 1 {
                if let Some(k) = known {
                    assert!(cands.contains(&k), "p = {}: true order not among the candidates", p);
                }
                let list: Vec<String> = cands.iter().map(|c| c.to_string()).collect();
                return (p, format!("# p = {} ambiguous, {} candidates: {}", p, cands.len(), list.join(" ")));
            }
            let nj = *cands.iter().next().unwrap();
            let c3 = nj as i128 - a;
            if let Some(k) = known {
                assert_eq!(k, nj, "p = {}: BSGS order differs from the L-polynomial", p);
            }
            (p, format!("{} {} {} {} {} {}", p, n1, c1, c2, c3, nj))
        })
        .collect();
    res.sort();
    let mut wr: Box<dyn Write> = match &out {
        Some(f) => Box::new(std::fs::File::create(f).unwrap()),
        None => Box::new(std::io::stdout()),
    };
    writeln!(wr, "# #J(F_p) by baby steps / giant steps on c3 (code/jacobian-over-q/mw-sieve/src/bin/jorder.rs)").unwrap();
    writeln!(wr, "# p N1 c1 c2 c3 #J(F_p)").unwrap();
    for (_, l) in &res {
        writeln!(wr, "{}", l).unwrap();
    }
}
