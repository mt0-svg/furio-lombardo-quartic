//! Finite fields: the prime field F_p (p < 2^31) and extensions
//! F_{p^K} = F_p[t]/(m(t)) with K a compile-time constant.
//!
//! Elements of F_p are `u64` in [0, p). Elements of `Gf<K>` are `[u64; K]`,
//! the coefficients of a polynomial of degree < K in t. Products of two reduced
//! values are < 2^62, and up to four of them can be summed in a `u64` before
//! reduction (4 (p-1)^2 < 2^64 for p < 2^31).
//!
//! The trait [`Field`] is what the polynomial and curve code is generic over.

use std::fmt::Debug;

pub trait Field: Sync + Send {
    type E: Copy + PartialEq + Eq + Send + Sync + Debug;

    fn characteristic(&self) -> u64;
    /// Degree over the prime field.
    fn degree(&self) -> usize;
    /// Field order q = p^k, as u128 (panics on overflow).
    fn order(&self) -> u128 {
        (self.characteristic() as u128)
            .checked_pow(self.degree() as u32)
            .expect("field order overflows u128")
    }
    fn zero(&self) -> Self::E;
    fn one(&self) -> Self::E;
    /// Image of an integer.
    fn from_i64(&self, n: i64) -> Self::E;
    /// Image of an element of F_p given as a reduced residue.
    fn from_fp(&self, a: u64) -> Self::E;
    fn is_zero(&self, a: Self::E) -> bool;
    fn add(&self, a: Self::E, b: Self::E) -> Self::E;
    fn sub(&self, a: Self::E, b: Self::E) -> Self::E;
    fn neg(&self, a: Self::E) -> Self::E;
    fn mul(&self, a: Self::E, b: Self::E) -> Self::E;
    /// Product with an element of F_p (reduced residue).
    fn mul_fp(&self, a: Self::E, s: u64) -> Self::E;
    /// Inverse. Panics on zero.
    fn inv(&self, a: Self::E) -> Self::E;
    /// Frobenius a -> a^p.
    fn frob(&self, a: Self::E) -> Self::E;
    /// Bijection [0, q) -> F_q (base-p digits are the coordinates). Needs q < 2^64.
    fn from_index(&self, i: u64) -> Self::E;
    /// Inverse of `from_index`.
    fn index(&self, a: Self::E) -> u64;

    fn pow(&self, a: Self::E, mut e: u128) -> Self::E {
        let mut acc = self.one();
        let mut b = a;
        while e > 0 {
            if e & 1 == 1 {
                acc = self.mul(acc, b);
            }
            b = self.mul(b, b);
            e >>= 1;
        }
        acc
    }
}

/// Prime field F_p, p < 2^31, Barrett reduction.
#[derive(Clone, Copy, Debug)]
pub struct Fp {
    pub p: u64,
    barrett: u64, // floor(2^64 / p)
}

impl Fp {
    pub fn new(p: u64) -> Self {
        assert!((2..(1u64 << 31)).contains(&p), "Fp needs 2 <= p < 2^31");
        let barrett = ((1u128 << 64) / p as u128) as u64;
        Fp { p, barrett }
    }

    /// Reduces any x < 2^64 to [0, p).
    #[inline(always)]
    pub fn reduce(&self, x: u64) -> u64 {
        // q in {floor(x/p) - 1, floor(x/p)}, so 0 <= r < 2p.
        let q = ((x as u128 * self.barrett as u128) >> 64) as u64;
        let r = x - q * self.p;
        if r >= self.p {
            r - self.p
        } else {
            r
        }
    }

    #[inline(always)]
    pub fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.p {
            s - self.p
        } else {
            s
        }
    }
    #[inline(always)]
    pub fn sub(&self, a: u64, b: u64) -> u64 {
        if a >= b {
            a - b
        } else {
            a + self.p - b
        }
    }
    #[inline(always)]
    pub fn neg(&self, a: u64) -> u64 {
        if a == 0 {
            0
        } else {
            self.p - a
        }
    }
    #[inline(always)]
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        self.reduce(a * b)
    }
    pub fn inv(&self, a: u64) -> u64 {
        assert!(a % self.p != 0, "inverse of 0 in F_{}", self.p);
        let (mut r0, mut r1) = (self.p as i64, (a % self.p) as i64);
        let (mut s0, mut s1) = (0i64, 1i64);
        while r1 != 0 {
            let q = r0 / r1;
            (r0, r1) = (r1, r0 - q * r1);
            (s0, s1) = (s1, s0 - q * s1);
        }
        debug_assert_eq!(r0, 1);
        s0.rem_euclid(self.p as i64) as u64
    }
    pub fn from_i64(&self, n: i64) -> u64 {
        n.rem_euclid(self.p as i64) as u64
    }
    pub fn from_i128(&self, n: i128) -> u64 {
        n.rem_euclid(self.p as i128) as u64
    }
    pub fn pow(&self, a: u64, mut e: u128) -> u64 {
        let mut acc = 1 % self.p;
        let mut b = a % self.p;
        while e > 0 {
            if e & 1 == 1 {
                acc = self.mul(acc, b);
            }
            b = self.mul(b, b);
            e >>= 1;
        }
        acc
    }
    /// Legendre symbol for odd p: 1, -1 or 0.
    pub fn legendre(&self, a: u64) -> i32 {
        let a = a % self.p;
        if a == 0 {
            return 0;
        }
        if self.pow(a, ((self.p - 1) / 2) as u128) == 1 {
            1
        } else {
            -1
        }
    }
}

impl Field for Fp {
    type E = u64;
    fn characteristic(&self) -> u64 {
        self.p
    }
    fn degree(&self) -> usize {
        1
    }
    fn zero(&self) -> u64 {
        0
    }
    fn one(&self) -> u64 {
        1
    }
    fn from_i64(&self, n: i64) -> u64 {
        Fp::from_i64(self, n)
    }
    fn from_fp(&self, a: u64) -> u64 {
        a
    }
    fn is_zero(&self, a: u64) -> bool {
        a == 0
    }
    fn add(&self, a: u64, b: u64) -> u64 {
        Fp::add(self, a, b)
    }
    fn sub(&self, a: u64, b: u64) -> u64 {
        Fp::sub(self, a, b)
    }
    fn neg(&self, a: u64) -> u64 {
        Fp::neg(self, a)
    }
    fn mul(&self, a: u64, b: u64) -> u64 {
        Fp::mul(self, a, b)
    }
    fn mul_fp(&self, a: u64, s: u64) -> u64 {
        Fp::mul(self, a, s)
    }
    fn inv(&self, a: u64) -> u64 {
        Fp::inv(self, a)
    }
    fn frob(&self, a: u64) -> u64 {
        a
    }
    fn from_index(&self, i: u64) -> u64 {
        debug_assert!(i < self.p);
        i
    }
    fn index(&self, a: u64) -> u64 {
        a
    }
    fn pow(&self, a: u64, e: u128) -> u64 {
        Fp::pow(self, a, e)
    }
}

/// F_{p^K} = F_p[t]/(m), m monic irreducible of degree K.
#[derive(Clone, Debug)]
pub struct Gf<const K: usize> {
    pub fp: Fp,
    /// Coefficients m_0..m_{K-1} of m (m_K = 1 implied).
    pub modulus: [u64; K],
    /// Nonzero (i, -m_i mod p): t^K = sum (-m_i) t^i.
    sparse: Vec<(usize, u64)>,
    /// frob[i] = t^{i p} mod m, so that sigma(a) = sum_i a_i frob[i].
    frob: Vec<[u64; K]>,
    /// The class of t.
    gen: [u64; K],
}

impl<const K: usize> Gf<K> {
    /// Field with the given monic modulus m (coefficients m_0..m_{K-1}, leading 1 implied).
    /// Irreducibility is checked.
    pub fn with_modulus(p: u64, modulus: [u64; K]) -> Self {
        assert!(K >= 1);
        let fp = Fp::new(p);
        let mut full: Vec<u64> = modulus.iter().map(|&c| c % p).collect();
        full.push(1);
        assert!(
            crate::ffpoly::is_irreducible(&fp, &full),
            "modulus {:?} is not irreducible over F_{}",
            full,
            p
        );
        Self::build(fp, full)
    }

    /// Field with a deterministic sparse modulus: t (K = 1), else the first irreducible
    /// t^K + a t + b in lexicographic (a, b), else the first irreducible monic polynomial
    /// in lexicographic order of (m_{K-1}, ..., m_0).
    pub fn standard(p: u64) -> Self {
        let fp = Fp::new(p);
        if K == 1 {
            return Self::build(fp, vec![0, 1]);
        }
        for a in 0..p {
            for b in 1..p {
                let mut m = vec![0u64; K + 1];
                m[0] = b;
                m[1] = (m[1] + a) % p;
                m[K] = 1;
                if crate::ffpoly::is_irreducible(&fp, &m) {
                    return Self::build(fp, m);
                }
            }
        }
        let total = (p as u128).pow(K as u32);
        for idx in 0..total {
            let mut m = vec![0u64; K + 1];
            let mut r = idx;
            for c in m.iter_mut().take(K) {
                *c = (r % p as u128) as u64;
                r /= p as u128;
            }
            m[K] = 1;
            if crate::ffpoly::is_irreducible(&fp, &m) {
                return Self::build(fp, m);
            }
        }
        unreachable!("no irreducible polynomial of degree {} over F_{}", K, p)
    }

    fn build(fp: Fp, full: Vec<u64>) -> Self {
        let p = fp.p;
        let mut modulus = [0u64; K];
        modulus.copy_from_slice(&full[..K]);
        let sparse: Vec<(usize, u64)> = (0..K)
            .filter(|&i| modulus[i] != 0)
            .map(|i| (i, fp.neg(modulus[i])))
            .collect();
        let mut gen = [0u64; K];
        if K == 1 {
            gen[0] = fp.neg(modulus[0]); // t = -m_0 mod (t + m_0)
        } else {
            gen[1] = 1;
        }
        let mut f = Gf {
            fp,
            modulus,
            sparse,
            frob: Vec::new(),
            gen,
        };
        // frob[i] = (t^p)^i
        let tp = f.pow_nofrob(gen, p as u128);
        let mut acc = f.one_elem();
        let mut frob = Vec::with_capacity(K);
        for _ in 0..K {
            frob.push(acc);
            acc = f.mul_elem(acc, tp);
        }
        f.frob = frob;
        f
    }

    fn one_elem(&self) -> [u64; K] {
        let mut o = [0u64; K];
        o[0] = 1 % self.fp.p;
        o
    }

    fn pow_nofrob(&self, a: [u64; K], mut e: u128) -> [u64; K] {
        let mut acc = self.one_elem();
        let mut b = a;
        while e > 0 {
            if e & 1 == 1 {
                acc = self.mul_elem(acc, b);
            }
            b = self.mul_elem(b, b);
            e >>= 1;
        }
        acc
    }

    #[inline(always)]
    fn mul_elem(&self, a: [u64; K], b: [u64; K]) -> [u64; K] {
        let fp = &self.fp;
        if K == 1 {
            let mut r = [0u64; K];
            r[0] = fp.mul(a[0], b[0]);
            return r;
        }
        // convolution, length 2K-1 (fixed buffer, K <= 32)
        let mut c = [0u64; 64];
        if K <= 4 {
            for i in 0..K {
                for j in 0..K {
                    c[i + j] += a[i] * b[j];
                }
            }
            for x in c.iter_mut().take(2 * K - 1) {
                *x = fp.reduce(*x);
            }
        } else {
            for i in 0..K {
                for j in 0..K {
                    c[i + j] += fp.reduce(a[i] * b[j]);
                }
            }
            for x in c.iter_mut().take(2 * K - 1) {
                *x = fp.reduce(*x);
            }
        }
        for j in (K..2 * K - 1).rev() {
            let cj = c[j];
            if cj == 0 {
                continue;
            }
            for &(i, nm) in &self.sparse {
                let t = j - K + i;
                c[t] = fp.reduce(c[t] + cj * nm);
            }
        }
        let mut r = [0u64; K];
        r.copy_from_slice(&c[..K]);
        r
    }

    /// The class of t in F_p[t]/(m).
    pub fn gen(&self) -> [u64; K] {
        self.gen
    }

    /// Norm to F_p.
    pub fn norm(&self, a: [u64; K]) -> u64 {
        let mut prod = a;
        let mut s = a;
        for _ in 1..K {
            s = self.frob(s);
            prod = self.mul_elem(prod, s);
        }
        prod[0]
    }
}

impl<const K: usize> Field for Gf<K> {
    type E = [u64; K];
    fn characteristic(&self) -> u64 {
        self.fp.p
    }
    fn degree(&self) -> usize {
        K
    }
    fn zero(&self) -> [u64; K] {
        [0u64; K]
    }
    fn one(&self) -> [u64; K] {
        self.one_elem()
    }
    fn from_i64(&self, n: i64) -> [u64; K] {
        let mut r = [0u64; K];
        r[0] = self.fp.from_i64(n);
        r
    }
    fn from_fp(&self, a: u64) -> [u64; K] {
        let mut r = [0u64; K];
        r[0] = a;
        r
    }
    #[inline(always)]
    fn is_zero(&self, a: [u64; K]) -> bool {
        a.iter().all(|&c| c == 0)
    }
    #[inline(always)]
    fn add(&self, a: [u64; K], b: [u64; K]) -> [u64; K] {
        let mut r = [0u64; K];
        for i in 0..K {
            r[i] = self.fp.add(a[i], b[i]);
        }
        r
    }
    #[inline(always)]
    fn sub(&self, a: [u64; K], b: [u64; K]) -> [u64; K] {
        let mut r = [0u64; K];
        for i in 0..K {
            r[i] = self.fp.sub(a[i], b[i]);
        }
        r
    }
    #[inline(always)]
    fn neg(&self, a: [u64; K]) -> [u64; K] {
        let mut r = [0u64; K];
        for i in 0..K {
            r[i] = self.fp.neg(a[i]);
        }
        r
    }
    #[inline(always)]
    fn mul(&self, a: [u64; K], b: [u64; K]) -> [u64; K] {
        self.mul_elem(a, b)
    }
    #[inline(always)]
    fn mul_fp(&self, a: [u64; K], s: u64) -> [u64; K] {
        let mut r = [0u64; K];
        for i in 0..K {
            r[i] = self.fp.mul(a[i], s);
        }
        r
    }
    fn inv(&self, a: [u64; K]) -> [u64; K] {
        assert!(!self.is_zero(a), "inverse of 0 in F_q");
        // a^{-1} = sigma(a) ... sigma^{K-1}(a) / N(a)
        let mut b = self.one_elem();
        let mut s = a;
        for _ in 1..K {
            s = self.frob(s);
            b = self.mul_elem(b, s);
        }
        let n = self.mul_elem(a, b);
        debug_assert!(n[1..].iter().all(|&c| c == 0));
        self.mul_fp(b, self.fp.inv(n[0]))
    }
    #[inline(always)]
    fn frob(&self, a: [u64; K]) -> [u64; K] {
        if K == 1 {
            return a;
        }
        let mut acc = [0u64; K];
        for i in 0..K {
            if a[i] == 0 {
                continue;
            }
            let row = &self.frob[i];
            for j in 0..K {
                acc[j] += self.fp.reduce(a[i] * row[j]);
            }
        }
        for x in acc.iter_mut() {
            *x = self.fp.reduce(*x);
        }
        acc
    }
    fn from_index(&self, mut i: u64) -> [u64; K] {
        let mut r = [0u64; K];
        for c in r.iter_mut() {
            *c = i % self.fp.p;
            i /= self.fp.p;
        }
        r
    }
    fn index(&self, a: [u64; K]) -> u64 {
        let mut i = 0u64;
        for &c in a.iter().rev() {
            i = i * self.fp.p + c;
        }
        i
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn barrett_matches_rem() {
        for &p in &[2u64, 3, 7, 65_537, 2_147_483_647] {
            let f = Fp::new(p);
            let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
            for _ in 0..10_000 {
                x = x
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                assert_eq!(f.reduce(x), x % p);
            }
            assert_eq!(f.reduce(u64::MAX), u64::MAX % p);
        }
    }

    #[test]
    fn fp_inverse() {
        let f = Fp::new(1_000_003);
        for a in 1..2000u64 {
            assert_eq!(f.mul(a, f.inv(a)), 1);
        }
    }

    fn check_field<const K: usize>(p: u64) {
        let f = Gf::<K>::standard(p);
        let q = f.order() as u64;
        // multiplicative group has order q - 1, Frobenius is a^p, inverses are correct
        for i in 1..q.min(3000) {
            let a = f.from_index(i);
            assert_eq!(f.index(a), i);
            assert_eq!(f.pow(a, (q - 1) as u128), f.one());
            assert_eq!(f.frob(a), f.pow(a, p as u128));
            assert_eq!(f.mul(a, f.inv(a)), f.one());
        }
        // distributivity on a sample
        for i in 0..200u64 {
            let a = f.from_index((i * 7919) % q);
            let b = f.from_index((i * 104_729 + 3) % q);
            let c = f.from_index((i * 1_299_709 + 11) % q);
            assert_eq!(f.mul(a, f.add(b, c)), f.add(f.mul(a, b), f.mul(a, c)));
        }
    }

    #[test]
    fn extension_fields() {
        check_field::<1>(13);
        check_field::<2>(2);
        check_field::<2>(101);
        check_field::<3>(2);
        check_field::<3>(97);
        check_field::<4>(3);
        check_field::<5>(5);
        check_field::<7>(3);
    }

    #[test]
    fn given_modulus() {
        // F_8 = F_2[t]/(t^3 + t + 1): t^7 = 1, t^3 = t + 1
        let f = Gf::<3>::with_modulus(2, [1, 1, 0]);
        let t = f.gen();
        assert_eq!(f.mul(f.mul(t, t), t), [1, 1, 0]);
        assert_eq!(f.pow(t, 7), f.one());
    }
}
