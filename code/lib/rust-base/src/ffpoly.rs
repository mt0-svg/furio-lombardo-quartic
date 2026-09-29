//! Univariate polynomials over a finite field (any [`Field`]).
//!
//! A polynomial is a `Vec<F::E>` of coefficients, lowest degree first, with no
//! trailing zero; the zero polynomial is the empty vector. Functions that take
//! slices accept untrimmed input unless stated otherwise.
//!
//! Contents: arithmetic, gcd, modular powers, X^q mod m (via the p-power
//! Frobenius, semilinear over F_q), Rabin irreducibility test, distinct-degree
//! and equal-degree (Cantor-Zassenhaus) factorisation, roots, root counting.

use crate::ff::Field;

/// Deterministic generator (SplitMix64), for reproducible randomised algorithms.
#[derive(Clone, Debug)]
pub struct SplitMix64(pub u64);

impl SplitMix64 {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

pub fn trim<F: Field>(f: &F, a: &mut Vec<F::E>) {
    while let Some(&c) = a.last() {
        if f.is_zero(c) {
            a.pop();
        } else {
            break;
        }
    }
}

pub fn trimmed<F: Field>(f: &F, a: &[F::E]) -> Vec<F::E> {
    let mut v = a.to_vec();
    trim(f, &mut v);
    v
}

/// Degree, `None` for the zero polynomial.
pub fn deg<F: Field>(f: &F, a: &[F::E]) -> Option<usize> {
    (0..a.len()).rev().find(|&i| !f.is_zero(a[i]))
}

pub fn add<F: Field>(f: &F, a: &[F::E], b: &[F::E]) -> Vec<F::E> {
    let n = a.len().max(b.len());
    let mut r = Vec::with_capacity(n);
    for i in 0..n {
        let x = if i < a.len() { a[i] } else { f.zero() };
        let y = if i < b.len() { b[i] } else { f.zero() };
        r.push(f.add(x, y));
    }
    trim(f, &mut r);
    r
}

pub fn sub<F: Field>(f: &F, a: &[F::E], b: &[F::E]) -> Vec<F::E> {
    let n = a.len().max(b.len());
    let mut r = Vec::with_capacity(n);
    for i in 0..n {
        let x = if i < a.len() { a[i] } else { f.zero() };
        let y = if i < b.len() { b[i] } else { f.zero() };
        r.push(f.sub(x, y));
    }
    trim(f, &mut r);
    r
}

pub fn scale<F: Field>(f: &F, a: &[F::E], s: F::E) -> Vec<F::E> {
    let mut r: Vec<F::E> = a.iter().map(|&c| f.mul(c, s)).collect();
    trim(f, &mut r);
    r
}

pub fn mul<F: Field>(f: &F, a: &[F::E], b: &[F::E]) -> Vec<F::E> {
    let a = trimmed(f, a);
    let b = trimmed(f, b);
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut r = vec![f.zero(); a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        if f.is_zero(x) {
            continue;
        }
        for (j, &y) in b.iter().enumerate() {
            r[i + j] = f.add(r[i + j], f.mul(x, y));
        }
    }
    trim(f, &mut r);
    r
}

/// Euclidean division a = q b + r, deg r < deg b. Panics if b = 0.
pub fn divrem<F: Field>(f: &F, a: &[F::E], b: &[F::E]) -> (Vec<F::E>, Vec<F::E>) {
    let b = trimmed(f, b);
    assert!(!b.is_empty(), "division by the zero polynomial");
    let mut r = trimmed(f, a);
    let db = b.len() - 1;
    if r.len() < b.len() {
        return (Vec::new(), r);
    }
    let inv_lc = f.inv(b[db]);
    let mut q = vec![f.zero(); r.len() - db];
    for i in (db..r.len()).rev() {
        let c = r[i];
        if f.is_zero(c) {
            continue;
        }
        let t = f.mul(c, inv_lc);
        q[i - db] = t;
        for j in 0..=db {
            r[i - db + j] = f.sub(r[i - db + j], f.mul(t, b[j]));
        }
    }
    trim(f, &mut q);
    trim(f, &mut r);
    (q, r)
}

pub fn rem<F: Field>(f: &F, a: &[F::E], b: &[F::E]) -> Vec<F::E> {
    divrem(f, a, b).1
}

/// Exact quotient a / b, panics if b does not divide a.
pub fn div_exact<F: Field>(f: &F, a: &[F::E], b: &[F::E]) -> Vec<F::E> {
    let (q, r) = divrem(f, a, b);
    assert!(r.is_empty(), "div_exact: nonzero remainder");
    q
}

pub fn monic<F: Field>(f: &F, a: &[F::E]) -> Vec<F::E> {
    let a = trimmed(f, a);
    match a.last() {
        None => a,
        Some(&lc) => {
            let i = f.inv(lc);
            a.iter().map(|&c| f.mul(c, i)).collect()
        }
    }
}

/// Monic gcd (zero if both inputs are zero).
pub fn gcd<F: Field>(f: &F, a: &[F::E], b: &[F::E]) -> Vec<F::E> {
    let mut x = trimmed(f, a);
    let mut y = trimmed(f, b);
    while !y.is_empty() {
        let r = rem(f, &x, &y);
        x = y;
        y = r;
    }
    monic(f, &x)
}

pub fn derivative<F: Field>(f: &F, a: &[F::E]) -> Vec<F::E> {
    let mut r: Vec<F::E> = (1..a.len())
        .map(|i| f.mul(a[i], f.from_i64((i as u64 % f.characteristic()) as i64)))
        .collect();
    trim(f, &mut r);
    r
}

pub fn eval<F: Field>(f: &F, a: &[F::E], x: F::E) -> F::E {
    let mut acc = f.zero();
    for &c in a.iter().rev() {
        acc = f.add(f.mul(acc, x), c);
    }
    acc
}

pub fn mulmod<F: Field>(f: &F, a: &[F::E], b: &[F::E], m: &[F::E]) -> Vec<F::E> {
    rem(f, &mul(f, a, b), m)
}

pub fn powmod<F: Field>(f: &F, a: &[F::E], mut e: u128, m: &[F::E]) -> Vec<F::E> {
    let mut acc = rem(f, &[f.one()], m);
    let mut b = rem(f, a, m);
    while e > 0 {
        if e & 1 == 1 {
            acc = mulmod(f, &acc, &b, m);
        }
        e >>= 1;
        if e > 0 {
            b = mulmod(f, &b, &b, m);
        }
    }
    acc
}

/// X^e mod m by left-to-right binary powering (multiplication by X is a shift).
pub fn x_pow_mod<F: Field>(f: &F, e: u128, m: &[F::E]) -> Vec<F::E> {
    let m = trimmed(f, m);
    assert!(!m.is_empty());
    if e == 0 {
        return rem(f, &[f.one()], &m);
    }
    let mut acc = rem(f, &[f.zero(), f.one()], &m);
    let top = 127 - e.leading_zeros();
    for bit in (0..top).rev() {
        acc = mulmod(f, &acc, &acc, &m);
        if (e >> bit) & 1 == 1 {
            let mut s = vec![f.zero()];
            s.extend_from_slice(&acc);
            acc = rem(f, &s, &m);
        }
    }
    acc
}

/// X^q mod m, q = |F|: X^p mod m, then k-1 applications of the p-power map
/// g = sum c_i X^i -> sum frob(c_i) (X^p)^i, which is g^p mod m.
pub fn x_pow_q_mod<F: Field>(f: &F, m: &[F::E]) -> Vec<F::E> {
    let m = trimmed(f, m);
    let n = m.len() - 1;
    let y1 = x_pow_mod(f, f.characteristic() as u128, &m);
    let k = f.degree();
    if k == 1 || n == 0 {
        return y1;
    }
    let mut pows: Vec<Vec<F::E>> = Vec::with_capacity(n);
    pows.push(rem(f, &[f.one()], &m));
    for i in 1..n {
        let nxt = mulmod(f, &pows[i - 1], &y1, &m);
        pows.push(nxt);
    }
    let mut y = y1.clone();
    for _ in 1..k {
        let mut acc = vec![f.zero(); n];
        for (i, &c) in y.iter().enumerate() {
            if f.is_zero(c) {
                continue;
            }
            let s = f.frob(c);
            for (j, &t) in pows[i].iter().enumerate() {
                acc[j] = f.add(acc[j], f.mul(s, t));
            }
        }
        trim(f, &mut acc);
        y = acc;
    }
    y
}

/// Matrix of the q-power map on F_q[X]/(m): row i is X^{q i} mod m.
pub fn frobenius_matrix<F: Field>(f: &F, m: &[F::E]) -> Vec<Vec<F::E>> {
    let m = trimmed(f, m);
    let n = m.len() - 1;
    let xq = x_pow_q_mod(f, &m);
    let mut rows = Vec::with_capacity(n);
    rows.push(rem(f, &[f.one()], &m));
    for i in 1..n {
        let nxt = mulmod(f, &rows[i - 1], &xq, &m);
        rows.push(nxt);
    }
    rows
}

/// g^q mod m from the matrix of `frobenius_matrix` (g reduced mod m).
pub fn apply_frobenius<F: Field>(f: &F, mat: &[Vec<F::E>], g: &[F::E]) -> Vec<F::E> {
    let n = mat.len();
    let mut acc = vec![f.zero(); n];
    for (i, &c) in g.iter().enumerate() {
        if f.is_zero(c) {
            continue;
        }
        for (j, &t) in mat[i].iter().enumerate() {
            acc[j] = f.add(acc[j], f.mul(c, t));
        }
    }
    trim(f, &mut acc);
    acc
}

fn prime_divisors(mut n: usize) -> Vec<usize> {
    let mut r = Vec::new();
    let mut d = 2;
    while d * d <= n {
        if n % d == 0 {
            r.push(d);
            while n % d == 0 {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        r.push(n);
    }
    r
}

/// Rabin's test: m of degree n is irreducible iff X^{q^n} = X mod m and
/// gcd(X^{q^{n/r}} - X, m) = 1 for every prime r | n.
pub fn is_irreducible<F: Field>(f: &F, m: &[F::E]) -> bool {
    let m = monic(f, m);
    let n = match deg(f, &m) {
        None | Some(0) => return false,
        Some(1) => return true,
        Some(n) => n,
    };
    let mat = frobenius_matrix(f, &m);
    let x = vec![f.zero(), f.one()];
    let mut pw = vec![x.clone()]; // pw[i] = X^{q^i} mod m
    for i in 1..=n {
        let nxt = apply_frobenius(f, &mat, &pw[i - 1]);
        pw.push(nxt);
    }
    if sub(f, &pw[n], &x).len() != 0 {
        return false;
    }
    for r in prime_divisors(n) {
        let g = gcd(f, &m, &sub(f, &pw[n / r], &x));
        if g.len() != 1 {
            return false;
        }
    }
    true
}

/// Number of distinct roots in F_q, `None` for the zero polynomial.
pub fn count_distinct_roots<F: Field>(f: &F, a: &[F::E]) -> Option<usize> {
    let a = monic(f, a);
    match deg(f, &a) {
        None => None,
        Some(0) => Some(0),
        Some(1) => Some(1),
        Some(_) => {
            let xq = x_pow_q_mod(f, &a);
            let h = sub(f, &xq, &[f.zero(), f.one()]);
            Some(gcd(f, &a, &h).len() - 1)
        }
    }
}

/// For a nonzero polynomial a (not necessarily squarefree), returns the pairs (d, P_d)
/// where P_d is the product of the distinct monic irreducible factors of a of degree d
/// (only nontrivial P_d are listed).
pub fn distinct_degree_parts<F: Field>(f: &F, a: &[F::E]) -> Vec<(usize, Vec<F::E>)> {
    let g = monic(f, a);
    let n = deg(f, &g).expect("zero polynomial");
    let mut out: Vec<(usize, Vec<F::E>)> = Vec::new();
    if n == 0 {
        return out;
    }
    let mat = frobenius_matrix(f, &g);
    let x = rem(f, &[f.zero(), f.one()], &g);
    let mut h = x.clone();
    let mut remaining = g.clone();
    for d in 1..=n {
        if deg(f, &remaining) == Some(0) {
            break;
        }
        h = apply_frobenius(f, &mat, &h); // X^{q^d} mod g
        let gd = gcd(f, &g, &sub(f, &h, &x));
        let mut part = gd;
        for (e, pe) in &out {
            if d % e == 0 {
                part = div_exact(f, &part, pe);
            }
        }
        if part.len() > 1 {
            loop {
                let c = gcd(f, &remaining, &part);
                if c.len() <= 1 {
                    break;
                }
                remaining = div_exact(f, &remaining, &c);
            }
            out.push((d, part));
        }
    }
    out
}

fn random_poly<F: Field>(f: &F, n: usize, rng: &mut SplitMix64) -> Vec<F::E> {
    let q = f.order();
    assert!(q <= u64::MAX as u128, "random elements need q < 2^64");
    let mut v: Vec<F::E> = (0..n)
        .map(|_| f.from_index(rng.next_u64() % q as u64))
        .collect();
    trim(f, &mut v);
    v
}

/// Splits a monic squarefree product of irreducibles of degree d into its factors
/// (Cantor-Zassenhaus; trace map in characteristic 2).
pub fn equal_degree_split<F: Field>(
    f: &F,
    a: &[F::E],
    d: usize,
    rng: &mut SplitMix64,
) -> Vec<Vec<F::E>> {
    let a = monic(f, a);
    let n = deg(f, &a).expect("zero polynomial");
    assert!(d >= 1 && n % d == 0);
    if n == d {
        return vec![a];
    }
    if n == 0 {
        return vec![];
    }
    let mat = frobenius_matrix(f, &a);
    let p = f.characteristic();
    let q = f.order();
    loop {
        let r = random_poly(f, n, rng);
        if r.len() <= 1 {
            continue;
        }
        let b = if p == 2 {
            // absolute trace: sum_{i < k d} r^{2^i}
            let steps = f.degree() * d;
            let mut t = r.clone();
            let mut acc = r.clone();
            for _ in 1..steps {
                t = mulmod(f, &t, &t, &a);
                acc = add(f, &acc, &t);
            }
            acc
        } else {
            // (prod_{i<d} r^{q^i})^{(q-1)/2} = r^{(q^d - 1)/2}
            let mut t = rem(f, &r, &a);
            let mut nrm = t.clone();
            for _ in 1..d {
                t = apply_frobenius(f, &mat, &t);
                nrm = mulmod(f, &nrm, &t, &a);
            }
            let e = powmod(f, &nrm, (q - 1) / 2, &a);
            sub(f, &e, &[f.one()])
        };
        let g = gcd(f, &a, &b);
        let dg = g.len().saturating_sub(1);
        if dg > 0 && dg < n {
            let h = div_exact(f, &a, &g);
            let mut out = equal_degree_split(f, &g, d, rng);
            out.extend(equal_degree_split(f, &h, d, rng));
            return out;
        }
    }
}

/// Distinct monic irreducible factors of a nonzero polynomial (multiplicities dropped).
pub fn irreducible_factors<F: Field>(f: &F, a: &[F::E]) -> Vec<Vec<F::E>> {
    let mut rng = SplitMix64(0x5EED_1234_ABCD_0001);
    let mut out = Vec::new();
    for (d, part) in distinct_degree_parts(f, a) {
        out.extend(equal_degree_split(f, &part, d, &mut rng));
    }
    out
}

/// Distinct roots in F_q of a nonzero polynomial.
pub fn roots<F: Field>(f: &F, a: &[F::E]) -> Vec<F::E> {
    let a = monic(f, a);
    if deg(f, &a).expect("zero polynomial") == 0 {
        return vec![];
    }
    let xq = x_pow_q_mod(f, &a);
    let lin = gcd(f, &a, &sub(f, &xq, &[f.zero(), f.one()]));
    if lin.len() <= 1 {
        return vec![];
    }
    let mut rng = SplitMix64(0x5EED_0000_0000_0002);
    equal_degree_split(f, &lin, 1, &mut rng)
        .into_iter()
        .map(|l| f.neg(l[0]))
        .collect()
}

/// Fast distinct-root count for small degree (<= 24), stack buffers only.
/// `None` for the zero polynomial. Same result as `count_distinct_roots`.
pub fn count_roots_small<F: Field>(f: &F, coeffs: &[F::E]) -> Option<usize> {
    const M: usize = 24;
    let n = deg(f, coeffs)?;
    if n == 0 {
        return Some(0);
    }
    if n == 1 {
        return Some(1);
    }
    if n > M {
        return count_distinct_roots(f, coeffs);
    }
    // monic modulus m of degree n
    let il = f.inv(coeffs[n]);
    let mut m = [f.zero(); M + 1];
    for i in 0..n {
        m[i] = f.mul(coeffs[i], il);
    }
    m[n] = f.one();

    // reduce buf[0..len] mod m in place, result in buf[0..n]
    let reduce = |buf: &mut [F::E], len: usize| {
        for j in (n..len).rev() {
            let c = buf[j];
            if f.is_zero(c) {
                continue;
            }
            for i in 0..n {
                buf[j - n + i] = f.sub(buf[j - n + i], f.mul(c, m[i]));
            }
            buf[j] = f.zero();
        }
    };
    let mulm = |a: &[F::E], b: &[F::E], out: &mut [F::E]| {
        let mut buf = [f.zero(); 2 * M];
        for i in 0..n {
            if f.is_zero(a[i]) {
                continue;
            }
            for j in 0..n {
                buf[i + j] = f.add(buf[i + j], f.mul(a[i], b[j]));
            }
        }
        reduce(&mut buf, 2 * n - 1);
        out[..n].copy_from_slice(&buf[..n]);
    };

    // y1 = X^p mod m
    let p = f.characteristic();
    let mut y1 = [f.zero(); M];
    y1[1] = f.one(); // n >= 2 so X is reduced
    let top = 63 - p.leading_zeros();
    for bit in (0..top).rev() {
        let cur = y1;
        mulm(&cur, &cur, &mut y1);
        if (p >> bit) & 1 == 1 {
            let mut buf = [f.zero(); 2 * M];
            buf[1..n + 1].copy_from_slice(&y1[..n]);
            reduce(&mut buf, n + 1);
            y1[..n].copy_from_slice(&buf[..n]);
        }
    }
    let k = f.degree();
    let mut y = y1;
    if k > 1 {
        let mut pows = [[f.zero(); M]; M];
        pows[0][0] = f.one();
        for i in 1..n {
            let prev = pows[i - 1];
            mulm(&prev, &y1, &mut pows[i]);
        }
        for _ in 1..k {
            let mut acc = [f.zero(); M];
            for i in 0..n {
                if f.is_zero(y[i]) {
                    continue;
                }
                let s = f.frob(y[i]);
                for j in 0..n {
                    acc[j] = f.add(acc[j], f.mul(s, pows[i][j]));
                }
            }
            y = acc;
        }
    }
    // h = X^q - X mod m
    y[1] = f.sub(y[1], f.one());
    // gcd(m, h) on stack
    let mut a = m;
    let mut da = n;
    let mut b = [f.zero(); M + 1];
    b[..n].copy_from_slice(&y[..n]);
    let mut db = match (0..n).rev().find(|&i| !f.is_zero(b[i])) {
        None => return Some(n), // m divides X^q - X
        Some(d) => d,
    };
    loop {
        // a <- a mod b
        let ib = f.inv(b[db]);
        let mut i = da as isize;
        while i >= db as isize {
            let iu = i as usize;
            let c = a[iu];
            if !f.is_zero(c) {
                let t = f.mul(c, ib);
                for j in 0..=db {
                    a[iu - db + j] = f.sub(a[iu - db + j], f.mul(t, b[j]));
                }
            }
            i -= 1;
        }
        let new_da = if db == 0 {
            None
        } else {
            (0..db).rev().find(|&i| !f.is_zero(a[i]))
        };
        match new_da {
            None => return Some(db),
            Some(d) => {
                std::mem::swap(&mut a, &mut b);
                da = db;
                db = d;
                for c in b.iter_mut().skip(db + 1) {
                    *c = f.zero();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::{Fp, Gf};

    #[test]
    fn irreducibility_counts() {
        // number of monic irreducibles of degree n over F_p: (1/n) sum_{d|n} mu(d) p^{n/d}
        let f = Fp::new(3);
        let mut count = [0usize; 5];
        for n in 1..=4usize {
            let total = 3u64.pow(n as u32);
            for idx in 0..total {
                let mut m: Vec<u64> = (0..n).map(|i| (idx / 3u64.pow(i as u32)) % 3).collect();
                m.push(1);
                if is_irreducible(&f, &m) {
                    count[n] += 1;
                }
            }
        }
        assert_eq!(&count[1..], &[3, 3, 8, 18]);
        let f2 = Fp::new(2);
        let mut c5 = 0;
        for idx in 0..32u64 {
            let mut m: Vec<u64> = (0..5).map(|i| (idx >> i) & 1).collect();
            m.push(1);
            if is_irreducible(&f2, &m) {
                c5 += 1;
            }
        }
        assert_eq!(c5, 6);
    }

    #[test]
    fn roots_and_factors() {
        let f = Fp::new(101);
        // (x-3)(x-5)^2(x^2+1) over F_101: 10^2 = -1, four distinct roots
        let mut a = vec![1u64];
        for r in [3u64, 5, 5] {
            a = mul(&f, &a, &[f.neg(r), 1]);
        }
        a = mul(&f, &a, &[1, 0, 1]);
        let mut rs = roots(&f, &a);
        rs.sort();
        assert_eq!(rs.len(), 4);
        assert!(rs.contains(&3) && rs.contains(&5));
        assert_eq!(count_distinct_roots(&f, &a), Some(4));
        assert_eq!(count_roots_small(&f, &a), Some(4));
        // x^2 + 1 over F_7 is irreducible; factors of (x^2+1)^2 (x+1)
        let f7 = Fp::new(7);
        let b = mul(&f7, &mul(&f7, &[1, 0, 1], &[1, 0, 1]), &[1, 1]);
        let fac = irreducible_factors(&f7, &b);
        assert_eq!(fac.len(), 2);
        assert_eq!(count_roots_small(&f7, &b), Some(1));
    }

    #[test]
    fn small_counter_matches_generic() {
        fn run<F: Field>(f: &F, seed: u64) {
            let mut rng = SplitMix64(seed);
            let q = f.order() as u64;
            for _ in 0..400 {
                let n = 2 + (rng.next_u64() % 7) as usize;
                let mut a: Vec<F::E> = (0..=n).map(|_| f.from_index(rng.next_u64() % q)).collect();
                // sometimes force repeated roots
                if rng.next_u64() % 3 == 0 {
                    let r = f.from_index(rng.next_u64() % q);
                    let lin = vec![f.neg(r), f.one()];
                    a = mul(f, &mul(f, &a, &lin), &lin);
                }
                if deg(f, &a).is_none() {
                    assert_eq!(count_roots_small(f, &a), None);
                    continue;
                }
                let brute = (0..q)
                    .filter(|&i| f.is_zero(eval(f, &a, f.from_index(i))))
                    .count();
                assert_eq!(count_roots_small(f, &a), Some(brute));
                assert_eq!(count_distinct_roots(f, &a), Some(brute));
                assert_eq!(roots(f, &a).len(), brute);
            }
        }
        run(&Fp::new(2), 1);
        run(&Fp::new(3), 2);
        run(&Fp::new(31), 3);
        run(&Gf::<2>::standard(2), 4);
        run(&Gf::<3>::standard(2), 5);
        run(&Gf::<2>::standard(7), 6);
        run(&Gf::<3>::standard(5), 7);
        run(&Gf::<4>::standard(3), 8);
    }

    #[test]
    fn edf_extension() {
        // factor x^8 - x over F_4... = product of all (x - a), a in F_4, times irreducible quadratics
        let f = Gf::<2>::standard(2);
        let mut a = vec![f.zero(); 17];
        a[16] = f.one();
        a[1] = f.one(); // x^16 + x = x^16 - x in char 2
        let fac = irreducible_factors(&f, &a);
        // x^16 - x over F_4 = product of irreducibles of degree 1 and 2: 4 + 6
        assert_eq!(fac.len(), 10);
    }
}
