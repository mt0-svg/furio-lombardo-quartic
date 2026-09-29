//! L-polynomials of a smooth plane quartic (or cubic) over F_p for p <= B.
//!
//! Usage:
//!   lpoly (--poly "<F>" | --file <path>) --bound B [--full-bound B3] [--verify-bound B4]
//!         [--out <txt>] [--gp <gp file>]
//!
//! F is a homogeneous polynomial in x, y, z with integer coefficients, written as a sum
//! of monomials: `x^4 + 3x^3y - 3*x^2*y*z` (`*` optional; unicode superscripts and
//! minus accepted). With --file, the file holds that expression (lines starting with
//! `#` are ignored, the others are concatenated).
//!
//! For each prime p <= B the reduction mod p is tested for smoothness (exact test,
//! `base::plane_curve::smoothness_mod_p`). For good p: N_1 and N_2; for p <= B3 also
//! N_3 and the full L-polynomial (genus 3). For p <= B4 the counts N_4 (and N_5 when
//! p^5 < 2^40) are computed over F_{p^4}, F_{p^5} and compared with the prediction of L.

use base::ff::{Fp, Gf};
use base::plane_curve::{count_points, smoothness_mod_p, HomPoly, Smoothness};
use base::zeta;
use rayon::prelude::*;
use std::io::Write;
use std::time::Instant;

struct Row {
    p: u64,
    bad: Option<String>,
    counts: Vec<u64>,
    lpoly: Option<Vec<i128>>,
    verify: Option<String>,
    secs: f64,
}

fn primes_upto(n: u64) -> Vec<u64> {
    (2..=n)
        .filter(|&k| (2..).take_while(|d| d * d <= k).all(|d| k % d != 0))
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut poly_src: Option<String> = None;
    let mut bound: u64 = 100;
    let mut full_bound: Option<u64> = None;
    let mut verify_bound: u64 = 0;
    let mut out_path: Option<String> = None;
    let mut gp_path: Option<String> = None;
    let mut i = 1;
    while i < args.len() {
        let v = args.get(i + 1).cloned();
        match args[i].as_str() {
            "--poly" => poly_src = v,
            "--file" => {
                let txt = std::fs::read_to_string(v.expect("--file needs a path")).expect("read");
                poly_src = Some(
                    txt.lines()
                        .filter(|l| !l.trim_start().starts_with('#'))
                        .collect::<Vec<_>>()
                        .join(" "),
                );
            }
            "--bound" => bound = v.expect("value").parse().expect("integer"),
            "--full-bound" => full_bound = Some(v.expect("value").parse().expect("integer")),
            "--verify-bound" => verify_bound = v.expect("value").parse().expect("integer"),
            "--out" => out_path = v,
            "--gp" => gp_path = v,
            other => panic!("unknown argument {other}"),
        }
        i += 2;
    }
    let c = HomPoly::parse(&poly_src.expect("--poly or --file required")).expect("parse");
    let d = c.degree;
    assert!(
        d == 3 || d == 4,
        "only plane cubics and quartics (genus 1 or 3)"
    );
    let genus = ((d - 1) * (d - 2) / 2) as usize;
    let full_bound = full_bound.unwrap_or(bound.min(100));
    let t0 = Instant::now();

    let primes = primes_upto(bound);
    let mut rows: Vec<Row> = primes
        .par_iter()
        .map(|&p| {
            let t = Instant::now();
            let mut row = Row {
                p,
                bad: None,
                counts: vec![],
                lpoly: None,
                verify: None,
                secs: 0.0,
            };
            match smoothness_mod_p(&c, p) {
                Smoothness::Smooth => {}
                Smoothness::Singular(s) => {
                    row.bad = Some(format!("singular ({s})"));
                    return row;
                }
                Smoothness::Unknown(s) => {
                    row.bad = Some(format!("smoothness undetermined ({s})"));
                    return row;
                }
            }
            row.counts.push(count_points(&Fp::new(p), &c));
            if genus >= 2 || p <= full_bound {
                row.counts.push(count_points(&Gf::<2>::standard(p), &c));
            }
            if genus >= 3 && p <= full_bound {
                row.counts.push(count_points(&Gf::<3>::standard(p), &c));
            }
            if row.counts.len() >= genus {
                let l =
                    zeta::lpoly_from_counts(p, &row.counts[..genus]).expect("Newton identities");
                assert!(
                    zeta::weil_coefficient_bounds(p, &l),
                    "Weil bound violated at p = {p}"
                );
                // counts beyond the genus must agree with L
                let pred = zeta::counts_from_lpoly(p, &l, 5);
                for (k, &n) in row.counts.iter().enumerate().skip(genus) {
                    assert_eq!(
                        pred[k],
                        n as i128,
                        "N_{} disagrees with L at p = {p}",
                        k + 1
                    );
                }
                if p <= verify_bound {
                    let mut msg = String::new();
                    let n4 = count_points(&Gf::<4>::standard(p), &c);
                    msg.push_str(&format!("N4={n4} (pred {})", pred[3]));
                    assert_eq!(pred[3], n4 as i128, "N_4 disagrees with L at p = {p}");
                    if (p as u128).pow(5) < (1u128 << 40) {
                        let n5 = count_points(&Gf::<5>::standard(p), &c);
                        msg.push_str(&format!(" N5={n5} (pred {})", pred[4]));
                        assert_eq!(pred[4], n5 as i128, "N_5 disagrees with L at p = {p}");
                    }
                    row.verify = Some(msg);
                }
                row.lpoly = Some(l);
            }
            row.secs = t.elapsed().as_secs_f64();
            eprintln!("p = {p}: {:?} in {:.2}s", row.counts, row.secs);
            row
        })
        .collect();
    rows.sort_by_key(|r| r.p);

    let mut txt = String::new();
    txt.push_str(&format!("# F = {}\n", c.to_string_ascii()));
    txt.push_str(&format!(
        "# genus {genus}; N_k = #C(F_(p^k)); L(T) = 1 + c1 T + c2 T^2 + c3 T^3 + p c2 T^4 + p^2 c1 T^5 + p^3 T^6; #J(F_p) = L(1)\n"
    ));
    txt.push_str(&format!(
        "# bound {bound}, full L for p <= {full_bound}, N4/N5 check for p <= {verify_bound}\n"
    ));
    txt.push_str("# p  N1  N2  N3  c1  c2  c3  #J(F_p)\n");
    let mut gp =
        String::from("\\\\ [p, [N_1, ..., N_k], [c_0, ..., c_2g] or [] if k < g]\n{\nLPOLY = [\n");
    let mut first = true;
    for r in &rows {
        if let Some(b) = &r.bad {
            txt.push_str(&format!("# p = {}: bad reduction, {}\n", r.p, b));
            continue;
        }
        let n: Vec<String> = (0..3)
            .map(|k| r.counts.get(k).map(|v| v.to_string()).unwrap_or("-".into()))
            .collect();
        let (cs, jac) = match &r.lpoly {
            Some(l) => (
                (1..=genus)
                    .map(|j| l[j].to_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                zeta::eval(l, 1).to_string(),
            ),
            None => {
                // c1, c2 from N1, N2 (Newton), c3 unknown
                let q = r.p as i128;
                let s1 = q + 1 - r.counts[0] as i128;
                let s2 = q * q + 1 - r.counts[1] as i128;
                let c1 = -s1;
                let c2 = (s1 * s1 - s2) / 2;
                (format!("{c1} {c2} -"), "-".into())
            }
        };
        txt.push_str(&format!("{} {} {} {}\n", r.p, n.join(" "), cs, jac));
        if let Some(v) = &r.verify {
            txt.push_str(&format!("#   check p = {}: {}\n", r.p, v));
        }
        let lstr = match &r.lpoly {
            Some(l) => format!(
                "[{}]",
                l.iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            None => "[]".into(),
        };
        let cstr = r
            .counts
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(",");
        gp.push_str(&format!(
            "{}[{}, [{}], {}]\n",
            if first { " " } else { "," },
            r.p,
            cstr,
            lstr
        ));
        first = false;
    }
    gp.push_str("];\n}\n");
    let total = t0.elapsed().as_secs_f64();
    txt.push_str(&format!("# total time {:.1}s\n", total));
    match &out_path {
        Some(path) => std::fs::write(path, &txt).expect("write"),
        None => std::io::stdout().write_all(txt.as_bytes()).unwrap(),
    }
    if let Some(path) = &gp_path {
        std::fs::write(path, &gp).expect("write gp");
    }
    eprintln!("total {:.1}s", total);
}
