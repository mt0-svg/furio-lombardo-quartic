//! Plane projective curves F(x, y, z) = 0, F homogeneous with integer coefficients.
//!
//! - [`HomPoly`]: parsing (`"x^4 + 3x^3y - 2*x*z^3"`, `*` optional, unicode
//!   superscripts and minus sign accepted), partial derivatives, evaluation.
//! - [`count_points`]: number of points of the curve in P^2(F_q), for any finite
//!   field implementing [`Field`] (projection to x, root counting in y; over
//!   F_{p^k} only one x per Frobenius orbit is treated). Parallel with rayon.
//! - [`smoothness_mod_p`]: exact test that the reduction mod p is a smooth curve
//!   of the same degree (resultants over F_p[x], then gcd checks over the residue
//!   fields of the candidate x-coordinates).

use crate::ff::{Field, Fp, Gf};
use crate::ffpoly;
use rayon::prelude::*;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HomPoly {
    pub degree: u32,
    /// Exponents [a, b, c] of x^a y^b z^c with nonzero integer coefficient.
    pub terms: BTreeMap<[u32; 3], i128>,
}

impl HomPoly {
    pub fn from_terms(terms: &[([u32; 3], i128)]) -> Result<Self, String> {
        let mut map: BTreeMap<[u32; 3], i128> = BTreeMap::new();
        for &(e, c) in terms {
            *map.entry(e).or_insert(0) += c;
        }
        map.retain(|_, c| *c != 0);
        let mut degree = None;
        for e in map.keys() {
            let d = e[0] + e[1] + e[2];
            match degree {
                None => degree = Some(d),
                Some(d0) if d0 != d => {
                    return Err(format!("not homogeneous: degrees {} and {}", d0, d))
                }
                _ => {}
            }
        }
        Ok(HomPoly {
            degree: degree.ok_or("zero polynomial")?,
            terms: map,
        })
    }

    /// Parses a sum of monomials in x, y, z with integer coefficients.
    pub fn parse(s: &str) -> Result<Self, String> {
        let sup = |c: char| "⁰¹²³⁴⁵⁶⁷⁸⁹".chars().position(|d| d == c);
        let chars: Vec<char> = s
            .chars()
            .filter(|c| !c.is_whitespace())
            .map(|c| match c {
                '\u{2212}' | '\u{2013}' => '-',
                '·' | '×' => '*',
                _ => c,
            })
            .collect();
        let mut terms: Vec<([u32; 3], i128)> = Vec::new();
        let mut i = 0;
        if chars.is_empty() {
            return Err("empty input".into());
        }
        while i < chars.len() {
            let mut sign: i128 = 1;
            while i < chars.len() && (chars[i] == '+' || chars[i] == '-') {
                if chars[i] == '-' {
                    sign = -sign;
                }
                i += 1;
            }
            let mut coef: i128 = sign;
            let mut e = [0u32; 3];
            let mut nfactors = 0;
            loop {
                if i < chars.len() && chars[i] == '*' && nfactors > 0 {
                    i += 1;
                }
                if i >= chars.len() {
                    break;
                }
                let c = chars[i];
                if c.is_ascii_digit() {
                    let st = i;
                    while i < chars.len() && chars[i].is_ascii_digit() {
                        i += 1;
                    }
                    let n: i128 = chars[st..i]
                        .iter()
                        .collect::<String>()
                        .parse()
                        .map_err(|e| format!("{e}"))?;
                    coef = coef.checked_mul(n).ok_or("coefficient overflow")?;
                    nfactors += 1;
                } else if c == 'x' || c == 'y' || c == 'z' {
                    let v = (c as u8 - b'x') as usize;
                    i += 1;
                    let mut pw = 1u32;
                    if i < chars.len() && chars[i] == '^' {
                        i += 1;
                        let st = i;
                        while i < chars.len() && chars[i].is_ascii_digit() {
                            i += 1;
                        }
                        if st == i {
                            return Err(format!("missing exponent at position {}", i));
                        }
                        pw = chars[st..i]
                            .iter()
                            .collect::<String>()
                            .parse()
                            .map_err(|e| format!("{e}"))?;
                    } else if i < chars.len() && sup(chars[i]).is_some() {
                        let mut v2 = 0u32;
                        while i < chars.len() {
                            match sup(chars[i]) {
                                Some(d) => {
                                    v2 = v2 * 10 + d as u32;
                                    i += 1;
                                }
                                None => break,
                            }
                        }
                        pw = v2;
                    }
                    e[v] += pw;
                    nfactors += 1;
                } else if c == '+' || c == '-' {
                    break;
                } else {
                    return Err(format!("unexpected character '{}' at position {}", c, i));
                }
            }
            if nfactors == 0 {
                return Err(format!("empty term before position {}", i));
            }
            terms.push((e, coef));
        }
        Self::from_terms(&terms)
    }

    pub fn coeff(&self, e: [u32; 3]) -> i128 {
        *self.terms.get(&e).unwrap_or(&0)
    }

    /// Partial derivative with respect to variable v (0 = x, 1 = y, 2 = z).
    /// Returns `None` if it is the zero polynomial.
    pub fn partial(&self, v: usize) -> Option<HomPoly> {
        let t: Vec<([u32; 3], i128)> = self
            .terms
            .iter()
            .filter(|(e, _)| e[v] > 0)
            .map(|(e, &c)| {
                let mut e2 = *e;
                e2[v] -= 1;
                (e2, c * e[v] as i128)
            })
            .collect();
        HomPoly::from_terms(&t).ok()
    }

    /// Exact evaluation, `None` on i128 overflow.
    pub fn eval_i128(&self, pt: [i128; 3]) -> Option<i128> {
        let mut acc: i128 = 0;
        for (e, &c) in &self.terms {
            let mut t = c;
            for v in 0..3 {
                t = t.checked_mul(pt[v].checked_pow(e[v])?)?;
            }
            acc = acc.checked_add(t)?;
        }
        Some(acc)
    }

    /// Reduction mod p: (exponents, residue) with nonzero residue.
    pub fn reduce_mod(&self, p: u64) -> Vec<([u32; 3], u64)> {
        self.terms
            .iter()
            .map(|(e, &c)| (*e, c.rem_euclid(p as i128) as u64))
            .filter(|&(_, r)| r != 0)
            .collect()
    }

    pub fn to_string_ascii(&self) -> String {
        let mut s = String::new();
        for (e, &c) in self.terms.iter().rev() {
            if s.is_empty() {
                if c < 0 {
                    s.push('-');
                }
            } else {
                s.push_str(if c < 0 { " - " } else { " + " });
            }
            let a = c.unsigned_abs();
            let mono: Vec<String> = ["x", "y", "z"]
                .iter()
                .zip(e.iter())
                .filter(|(_, &k)| k > 0)
                .map(|(v, &k)| {
                    if k == 1 {
                        v.to_string()
                    } else {
                        format!("{}^{}", v, k)
                    }
                })
                .collect();
            if a != 1 || mono.is_empty() {
                s.push_str(&a.to_string());
                if !mono.is_empty() {
                    s.push('*');
                }
            }
            s.push_str(&mono.join("*"));
        }
        s
    }
}

/// Number of points of {F = 0} in P^2(F_q).
pub fn count_points<F: Field>(f: &F, c: &HomPoly) -> u64 {
    let p = f.characteristic();
    let d = c.degree as usize;
    let red = c.reduce_mod(p);
    let q = f.order();
    assert!(q < (1u128 << 63), "field too large for enumeration");
    let q = q as u64;
    if red.is_empty() {
        return q * q + q + 1;
    }
    // affine chart z = 1: coefficient of y^j is sum_i a[j][i] x^i
    let mut a = vec![vec![0u64; d + 1]; d + 1];
    for &(e, r) in &red {
        a[e[1] as usize][e[0] as usize] = r;
    }
    let k = f.degree();
    assert!(d <= 32);
    let fiber = |i: u64| -> u64 {
        let x = f.from_index(i);
        let mut weight = 1u64;
        if k > 1 {
            let mut s = f.frob(x);
            while s != x {
                if f.index(s) < i {
                    return 0;
                }
                s = f.frob(s);
                weight += 1;
            }
        }
        let mut pw = [f.one(); 33];
        for t in 1..=d {
            pw[t] = f.mul(pw[t - 1], x);
        }
        let mut g = [f.zero(); 33];
        for j in 0..=d {
            let mut acc = f.zero();
            for (t, &r) in a[j].iter().enumerate() {
                if r != 0 {
                    acc = f.add(acc, f.mul_fp(pw[t], r));
                }
            }
            g[j] = acc;
        }
        let n = ffpoly::count_roots_small(f, &g[..=d])
            .map(|n| n as u64)
            .unwrap_or(q);
        weight * n
    };
    const CHUNK: u64 = 1024;
    let nchunks = q.div_ceil(CHUNK) as usize;
    let affine: u64 = (0..nchunks)
        .into_par_iter()
        .map(|ci| {
            let lo = ci as u64 * CHUNK;
            (lo..(lo + CHUNK).min(q)).map(fiber).sum::<u64>()
        })
        .sum();
    // line z = 0: [x:1:0] and [1:0:0]
    let mut h = vec![f.zero(); d + 1];
    let mut lead = 0u64;
    for &(e, r) in &red {
        if e[2] == 0 {
            h[e[0] as usize] = f.from_fp(r);
            if e[0] as usize == d {
                lead = r;
            }
        }
    }
    let at_inf = match ffpoly::count_distinct_roots(f, &h) {
        None => q + 1,
        Some(n) => n as u64 + if lead == 0 { 1 } else { 0 },
    };
    affine + at_inf
}

/// Naive count by evaluating F at every point of P^2(F_q) (for tests).
pub fn count_points_naive<F: Field>(f: &F, c: &HomPoly) -> u64 {
    let p = f.characteristic();
    let red = c.reduce_mod(p);
    let q = f.order() as u64;
    let eval = |pt: [F::E; 3]| {
        let mut acc = f.zero();
        for &(e, r) in &red {
            let mut t = f.from_fp(r);
            for v in 0..3 {
                t = f.mul(t, f.pow(pt[v], e[v] as u128));
            }
            acc = f.add(acc, t);
        }
        f.is_zero(acc)
    };
    let mut n = 0u64;
    for i in 0..q {
        for j in 0..q {
            if eval([f.from_index(i), f.from_index(j), f.one()]) {
                n += 1;
            }
        }
        if eval([f.from_index(i), f.one(), f.zero()]) {
            n += 1;
        }
    }
    if eval([f.one(), f.zero(), f.zero()]) {
        n += 1;
    }
    n
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Smoothness {
    /// The reduction mod p has the same degree and no singular point over the algebraic closure.
    Smooth,
    /// Singular, or the degree drops mod p. The string says where.
    Singular(String),
    /// The elimination degenerated (every resultant vanished identically).
    Unknown(String),
}

type PolyFp = Vec<u64>;

fn det_poly(f: &Fp, mut m: Vec<Vec<PolyFp>>) -> PolyFp {
    // Bareiss fraction-free elimination over F_p[x], row pivoting.
    let n = m.len();
    if n == 0 {
        return vec![1];
    }
    let mut prev: PolyFp = vec![1];
    let mut neg = false;
    for k in 0..n {
        match (k..n).find(|&i| !m[i][k].is_empty()) {
            None => return vec![],
            Some(i) => {
                if i != k {
                    m.swap(i, k);
                    neg = !neg;
                }
            }
        }
        for i in k + 1..n {
            for j in k + 1..n {
                let t = ffpoly::sub(
                    f,
                    &ffpoly::mul(f, &m[i][j], &m[k][k]),
                    &ffpoly::mul(f, &m[i][k], &m[k][j]),
                );
                m[i][j] = ffpoly::div_exact(f, &t, &prev);
            }
            m[i][k] = vec![];
        }
        prev = m[k][k].clone();
    }
    let d = m[n - 1][n - 1].clone();
    if neg {
        d.iter().map(|&c| f.neg(c)).collect()
    } else {
        d
    }
}

/// Res_y(A, B) for A, B in F_p[x][y] given as coefficient lists in y (entries in F_p[x],
/// last entry nonzero). Formal degrees are the actual y-degrees.
fn resultant_y(f: &Fp, a: &[PolyFp], b: &[PolyFp]) -> PolyFp {
    let m = a.len() - 1;
    let n = b.len() - 1;
    let size = m + n;
    let mut mat = vec![vec![Vec::<u64>::new(); size]; size];
    for r in 0..n {
        for i in 0..=m {
            mat[r][r + i] = a[m - i].clone();
        }
    }
    for r in 0..m {
        for j in 0..=n {
            mat[n + r][r + j] = b[n - j].clone();
        }
    }
    det_poly(f, mat)
}

/// The y-coefficients (in F_p[x]) of G(x, y, 1), trimmed; empty if G = 0 mod p.
fn affine_coeffs(f: &Fp, g: &[([u32; 3], u64)]) -> Vec<PolyFp> {
    let dy = g.iter().map(|(e, _)| e[1] as usize).max().unwrap_or(0);
    let dx = g.iter().map(|(e, _)| e[0] as usize).max().unwrap_or(0);
    let mut c = vec![vec![0u64; dx + 1]; dy + 1];
    for &(e, r) in g {
        c[e[1] as usize][e[0] as usize] = f.add(c[e[1] as usize][e[0] as usize], r);
    }
    for v in c.iter_mut() {
        ffpoly::trim(f, v);
    }
    while let Some(last) = c.last() {
        if last.is_empty() {
            c.pop();
        } else {
            break;
        }
    }
    c
}

fn singular_over_residue_field<const K: usize>(
    p: u64,
    modulus: &[u64],
    polys: &[Vec<PolyFp>],
) -> bool {
    let mut m = [0u64; K];
    m.copy_from_slice(&modulus[..K]);
    let fld = Gf::<K>::with_modulus(p, m);
    let x0 = fld.gen();
    let mut g: Vec<[u64; K]> = Vec::new();
    for bp in polys {
        let spec: Vec<[u64; K]> = bp
            .iter()
            .map(|cx| {
                let mut acc = fld.zero();
                for &c in cx.iter().rev() {
                    acc = fld.add(fld.mul(acc, x0), fld.from_fp(c));
                }
                acc
            })
            .collect();
        g = ffpoly::gcd(&fld, &g, &spec);
    }
    // g = 0: every polynomial vanishes on the whole line x = x0
    g.is_empty() || g.len() > 1
}

macro_rules! dispatch_residue_field {
    ($e:expr, $p:expr, $m:expr, $polys:expr; $($k:literal)*) => {
        match $e {
            $( $k => Some(singular_over_residue_field::<$k>($p, $m, $polys)), )*
            _ => None,
        }
    };
}

/// Exact smoothness test of the reduction of c mod p.
pub fn smoothness_mod_p(c: &HomPoly, p: u64) -> Smoothness {
    let f = Fp::new(p);
    let red = c.reduce_mod(p);
    if red.is_empty() {
        return Smoothness::Singular("F = 0 mod p".into());
    }
    // F and its partials mod p (F is kept so that p | deg F is handled)
    let mut gens: Vec<Vec<([u32; 3], u64)>> = vec![red.clone()];
    for v in 0..3 {
        if let Some(d) = c.partial(v) {
            let r = d.reduce_mod(p);
            if !r.is_empty() {
                gens.push(r);
            }
        }
    }
    let eval_fp = |g: &[([u32; 3], u64)], pt: [u64; 3]| {
        let mut acc = 0u64;
        for &(e, r) in g {
            let mut t = r;
            for v in 0..3 {
                t = f.mul(t, f.pow(pt[v], e[v] as u128));
            }
            acc = f.add(acc, t);
        }
        acc
    };
    if gens.iter().all(|g| eval_fp(g, [1, 0, 0]) == 0) {
        return Smoothness::Singular("[1:0:0]".into());
    }
    // points [x:1:0]
    let mut g_inf: PolyFp = Vec::new();
    for g in &gens {
        let d = g.iter().map(|(e, _)| e[0] + e[1] + e[2]).max().unwrap() as usize;
        let mut u = vec![0u64; d + 1];
        for &(e, r) in g {
            if e[2] == 0 {
                u[e[0] as usize] = f.add(u[e[0] as usize], r);
            }
        }
        g_inf = ffpoly::gcd(&f, &g_inf, &u);
    }
    if g_inf.is_empty() || g_inf.len() > 1 {
        return Smoothness::Singular("on the line z = 0".into());
    }
    // affine chart z = 1
    let polys: Vec<Vec<PolyFp>> = gens
        .iter()
        .map(|g| affine_coeffs(&f, g))
        .filter(|b| !b.is_empty())
        .collect();
    let mut cand: Option<PolyFp> = None;
    for i in 0..polys.len() {
        for j in i + 1..polys.len() {
            let r = if polys[i].len() == 1 && polys[j].len() == 1 {
                ffpoly::gcd(&f, &polys[i][0], &polys[j][0])
            } else {
                resultant_y(&f, &polys[i], &polys[j])
            };
            if !r.is_empty() {
                cand = Some(match cand {
                    None => ffpoly::monic(&f, &r),
                    Some(c0) => ffpoly::gcd(&f, &c0, &r),
                });
            }
        }
    }
    let cand = match cand {
        None => return Smoothness::Unknown("all resultants vanish".into()),
        Some(c0) => c0,
    };
    if cand.len() <= 1 {
        return Smoothness::Smooth;
    }
    for g in ffpoly::irreducible_factors(&f, &cand) {
        let e = g.len() - 1;
        let sing = dispatch_residue_field!(e, p, &g, &polys;
            1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16);
        match sing {
            None => return Smoothness::Unknown(format!("candidate factor of degree {} > 16", e)),
            Some(true) => {
                return Smoothness::Singular(format!(
                    "affine point with x-coordinate of degree {}",
                    e
                ))
            }
            Some(false) => {}
        }
    }
    Smoothness::Smooth
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::Gf;

    fn klein() -> HomPoly {
        HomPoly::parse("x^3y + y^3z + z^3x").unwrap()
    }

    #[test]
    fn parse_forms() {
        let a = HomPoly::parse("x⁴ + 3x³y − 3x²yz − 2*x*z^3").unwrap();
        assert_eq!(a.degree, 4);
        assert_eq!(a.coeff([2, 1, 1]), -3);
        assert_eq!(a.coeff([1, 0, 3]), -2);
        assert!(HomPoly::parse("x^2 + y").is_err());
        let b = HomPoly::parse(&a.to_string_ascii()).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn klein_counts() {
        let c = klein();
        assert_eq!(count_points(&Fp::new(2), &c), 3);
        assert_eq!(count_points(&Gf::<2>::standard(2), &c), 5);
        assert_eq!(count_points(&Gf::<3>::standard(2), &c), 24);
        // p = 3, 5 are inert in Q(sqrt(-7)): N_1 = p + 1
        assert_eq!(count_points(&Fp::new(3), &c), 4);
        assert_eq!(count_points(&Fp::new(5), &c), 6);
    }

    #[test]
    fn fast_matches_naive() {
        let curves = [
            klein(),
            HomPoly::parse("x^4 + 3x^3y - 3x^2yz - 3x^2z^2 + 6xy^3 - 6xy^2z + 3xyz^2 - 2xz^3 + 4y^4 + 2y^3z - 5yz^3").unwrap(),
            HomPoly::parse("x^3 + y^3 + z^3").unwrap(),
            HomPoly::parse("y^2z - x^3 - x z^2").unwrap(),
            HomPoly::parse("x^2y^2 + z^4 + x^4 - 3xyz^2").unwrap(),
        ];
        for c in &curves {
            for &p in &[2u64, 3, 5, 7, 11, 13] {
                assert_eq!(
                    count_points(&Fp::new(p), c),
                    count_points_naive(&Fp::new(p), c),
                    "p={p}"
                );
            }
            for &p in &[2u64, 3, 5] {
                let f = Gf::<2>::standard(p);
                assert_eq!(count_points(&f, c), count_points_naive(&f, c), "p^2, p={p}");
            }
            for &p in &[2u64, 3] {
                let f = Gf::<3>::standard(p);
                assert_eq!(count_points(&f, c), count_points_naive(&f, c), "p^3, p={p}");
            }
        }
    }

    #[test]
    fn smoothness() {
        let k = klein();
        // Klein quartic: bad reduction only at 7
        for &p in &[2u64, 3, 5, 11, 13, 29] {
            assert_eq!(smoothness_mod_p(&k, p), Smoothness::Smooth, "p={p}");
        }
        assert!(matches!(smoothness_mod_p(&k, 7), Smoothness::Singular(_)));
        // Fermat cubic: singular only mod 3
        let fc = HomPoly::parse("x^3 + y^3 + z^3").unwrap();
        assert!(matches!(smoothness_mod_p(&fc, 3), Smoothness::Singular(_)));
        assert_eq!(smoothness_mod_p(&fc, 2), Smoothness::Smooth);
        assert_eq!(smoothness_mod_p(&fc, 5), Smoothness::Smooth);
        // nodal cubic y^2 z = x^3 + x^2 z: singular at [0:0:1] for every p
        let nc = HomPoly::parse("y^2z - x^3 - x^2z").unwrap();
        for &p in &[2u64, 3, 5, 7] {
            assert!(matches!(smoothness_mod_p(&nc, p), Smoothness::Singular(_)));
        }
        // singular points defined only over F_{p^2} when p = 3 mod 4: the conic pair
        // (x^2 + y^2 - z^2)(x^2 + y^2 - 2z^2): the two conics meet at [1 : ±i : 0]
        let cc = HomPoly::parse("x^4 + 2x^2y^2 + y^4 - 3x^2z^2 - 3y^2z^2 + 2z^4").unwrap();
        for &p in &[3u64, 7, 11] {
            assert!(
                matches!(smoothness_mod_p(&cc, p), Smoothness::Singular(_)),
                "p={p}"
            );
        }
        // same pair with y and z swapped: singular points [x:0:1], x^2 = -1, an affine
        // point with a quadratic residue field when p = 3 mod 4
        let cc2 = HomPoly::parse("x^4 - 3x^2y^2 + 2x^2z^2 + 2y^4 - 3y^2z^2 + z^4").unwrap();
        for &p in &[3u64, 5, 7, 11, 13] {
            assert!(
                matches!(smoothness_mod_p(&cc2, p), Smoothness::Singular(_)),
                "p={p}"
            );
        }
        // elliptic curve y^2 = x^3 - x, discriminant 64: smooth for p odd
        let e = HomPoly::parse("y^2z - x^3 + x z^2").unwrap();
        for &p in &[3u64, 5, 7, 11] {
            assert_eq!(smoothness_mod_p(&e, p), Smoothness::Smooth, "p={p}");
        }
        assert!(matches!(smoothness_mod_p(&e, 2), Smoothness::Singular(_)));
    }
}
