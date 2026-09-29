pub use base;

/// Jacobian of C mod p: the curve, the L-polynomial data and the explicit rational divisors.
pub mod mw {
    use base::ff::Fp;
    use base::jac_quartic::{Elt, Quartic};
    use base::plane_curve::HomPoly;
    use std::collections::BTreeMap;

    pub const CURVE: &str = "x^4 + 3x^3y - 3x^2yz - 3x^2z^2 + 6xy^3 - 6xy^2z + 3xyz^2 - 2xz^3 + 4y^4 + 2y^3z - 5yz^3";

    pub fn curve() -> HomPoly {
        HomPoly::parse(CURVE).unwrap()
    }

    /// Conics generating the ideal of the degree 3 divisor R of Furio-Lombardo (their `gen3`
    /// is [R - 3P0]); coordinates of C, integral primitive scalings.
    pub const R_IDEAL: [&str; 3] = [
        "242x^2 + 19xy - 625yz + 410y^2",
        "242xz + 47xy - 145yz + 250y^2",
        "13463xy + 30250z^2 - 18725yz + 4346y^2",
    ];
    /// The two degree 2 places on the line z = 0.
    pub const QA_IDEAL: [&str; 2] = ["z", "x^2 + 4xy + 2y^2"];
    pub const QB_IDEAL: [&str; 2] = ["z", "x^2 - xy + 2y^2"];

    pub const P1: [i64; 3] = [1, 1, 1];
    pub const P2: [i64; 3] = [2, 0, 1];
    pub const P3: [i64; 3] = [-1, 0, 1];

    /// Rows of code/jacobian-over-q/lpoly/lpoly_C.txt with the full L-polynomial: p -> (N1, #J(F_p)).
    pub fn load_lpoly(path: &str) -> BTreeMap<u64, (u64, u128)> {
        let text = std::fs::read_to_string(path).expect("lpoly data");
        let mut m = BTreeMap::new();
        for line in text.lines() {
            if line.starts_with('#') || line.trim().is_empty() {
                continue;
            }
            let w: Vec<&str> = line.split_whitespace().collect();
            if w.len() < 8 || w[7] == "-" {
                continue;
            }
            m.insert(w[0].parse().unwrap(), (w[1].parse().unwrap(), w[7].parse().unwrap()));
        }
        m
    }

    /// #J(F_p) for all primes where it is known: full L-polynomials (lpoly_C.txt) and the
    /// baby step / giant step orders (jorder_C.txt, ambiguous primes are commented out there).
    pub fn load_orders(lpoly: &str, jorder: &str) -> BTreeMap<u64, u128> {
        let mut m: BTreeMap<u64, u128> = load_lpoly(lpoly).into_iter().map(|(p, (_, nj))| (p, nj)).collect();
        if let Ok(text) = std::fs::read_to_string(jorder) {
            for line in text.lines() {
                if line.starts_with('#') || line.trim().is_empty() {
                    continue;
                }
                let w: Vec<&str> = line.split_whitespace().collect();
                let p: u64 = w[0].parse().unwrap();
                let nj: u128 = w[5].parse().unwrap();
                if let Some(&old) = m.get(&p) {
                    assert_eq!(old, nj);
                }
                m.insert(p, nj);
            }
        }
        m
    }

    pub fn reduce_pt(p: u64, pt: [i64; 3]) -> [u64; 3] {
        let f = |a: i64| a.rem_euclid(p as i64) as u64;
        [f(pt[0]), f(pt[1]), f(pt[2])]
    }

    pub fn ideal_mod_p(j: &Quartic<Fp>, gens: &[&str]) -> Vec<Vec<([u32; 3], u64)>> {
        gens.iter()
            .map(|s| HomPoly::parse(s).unwrap().reduce_mod(j.f.p))
            .collect()
    }

    /// Class [E - eP0] of the effective divisor E cut out by the ideal, or None if the
    /// generators mod p do not give the reduction (dimension test).
    pub fn ideal_class(j: &Quartic<Fp>, gens: &[&str], e: usize) -> Option<Elt<u64>> {
        let g = ideal_mod_p(j, gens);
        let w3 = j.w3_from_ideal(&g, e)?;
        Some(j.class_from_w3(w3, e))
    }

    /// Reductions of the explicit classes.
    pub struct Classes {
        pub d1: Elt<u64>,
        pub d2: Elt<u64>,
        pub d3: Elt<u64>,
        /// [R - 3P0]
        pub gen3: Option<Elt<u64>>,
        /// [Qa - 2P0], [Qb - 2P0]
        pub qa: Option<Elt<u64>>,
        pub qb: Option<Elt<u64>>,
    }

    pub fn classes(j: &Quartic<Fp>) -> Classes {
        let p = j.f.p;
        Classes {
            d1: j.point_class(reduce_pt(p, P1)),
            d2: j.point_class(reduce_pt(p, P2)),
            d3: j.point_class(reduce_pt(p, P3)),
            gen3: ideal_class(j, &R_IDEAL, 3),
            qa: ideal_class(j, &QA_IDEAL, 2),
            qb: ideal_class(j, &QB_IDEAL, 2),
        }
    }

    pub fn setup(p: u64) -> Quartic<Fp> {
        Quartic::new(Fp::new(p), &curve())
    }

    pub fn factor(mut n: u128) -> Vec<(u64, u32)> {
        let mut v = Vec::new();
        let mut d = 2u128;
        while d * d <= n {
            if n % d == 0 {
                let mut e = 0;
                while n % d == 0 {
                    n /= d;
                    e += 1;
                }
                v.push((d as u64, e));
            }
            d += 1;
        }
        if n > 1 {
            v.push((n as u64, 1));
        }
        v
    }
}
