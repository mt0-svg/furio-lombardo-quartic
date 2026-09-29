//! Arithmetic in the Jacobian of a smooth plane quartic C : F(x, y, z) = 0 over a
//! finite field F_q, with [0:0:1] a point of C (the base point P).
//!
//! Method (Khuri-Makdisi style linear algebra on Riemann-Roch spaces).
//!
//! S_n = H^0(C, O(n)) = forms of degree n modulo F (plane curves are projectively
//! normal), dim S_n = 1, 3, 6, 10, 14 for n = 0..4. A section is stored through a
//! ring homomorphism rho into F_q^L: its Taylor coefficients at P in a local
//! parameter t (k of them) followed by its values at npts fixed points of
//! C(F_q) other than P. With npts + k >= 29 = 4*7 + 1, rho is injective on S_n for
//! n <= 7 (a nonzero section of O(n) has 4n zeros), and every product used below
//! has degree <= 7, so membership tests in the image are exact.
//!
//! Class x in Pic^0 is stored canonically: let r = min{r : h^0(x + rP) >= 1}, D_x the
//! unique effective divisor in |x + rP| (so P is not in supp D_x), and
//! E_x = D_x + (3 - r)P. The element is the subspace W_x = H^0(O(3)(-E_x)) of S_3
//! (dimension 7) in reduced row echelon form in F_q^L, Taylor coordinates first.
//! Equal classes give identical matrices, so elements can be hashed.
//!
//! Facts used (C of genus 3):
//! - a line bundle of degree >= 2g = 6 is base point free and non special, so for an
//!   effective divisor A with 4n - deg A >= 6 the common zeros (with multiplicity) of
//!   H^0(O(n)(-A)) are exactly A;
//! - (Mumford) H^0(L1) x H^0(L2) -> H^0(L1 L2) is onto if deg L1 >= 2g + 1 and
//!   deg L2 >= 2g;
//! - (colon) if U has common zeros exactly B and h != 0, then
//!   {g in S_a : g U within h V} = {g : div g >= div h - B + (conditions of V)}.
//!
//! Every dimension predicted by Riemann-Roch is asserted at run time.

use crate::ff::{Field, Fp, Gf};
use crate::ffpoly;
use crate::plane_curve::HomPoly;
use std::hash::Hash;

/// Canonical representative of a class of Pic^0(C)(F_q): RREF basis of W_x.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Elt<E> {
    pub rows: Vec<Vec<E>>,
}

/// A subspace in reduced row echelon form.
#[derive(Clone, Debug)]
pub struct Space<E> {
    pub rows: Vec<Vec<E>>,
    pub piv: Vec<usize>,
}

impl<E> Space<E> {
    pub fn dim(&self) -> usize {
        self.rows.len()
    }
}

pub struct Quartic<F: Field> {
    pub f: F,
    /// Terms of F reduced into the field.
    pub terms: Vec<([u32; 3], F::E)>,
    /// Number of Taylor coefficients at P.
    pub k: usize,
    pub npts: usize,
    pub len: usize,
    /// The evaluation points (projective coordinates, fixed representatives).
    pub pts: Vec<[F::E; 3]>,
    /// true: t = y and x = ser(t); false: t = x and y = ser(t). z = 1 near P.
    t_is_y: bool,
    ser: Vec<F::E>,
    pub s1: Vec<Vec<F::E>>,
    pub s3: Vec<Vec<F::E>>,
    pub s4: Vec<Vec<F::E>>,
    cubes: Vec<Vec<F::E>>,
    /// Basis of H^0(O(3)(-6P)) and an element of order exactly 6 at P.
    w6p: Vec<Vec<F::E>>,
    h6: Vec<F::E>,
    zero: Elt<F::E>,
}

/// Monomials x^a y^b z^c of degree n, in a fixed order.
pub fn monomials(n: u32) -> Vec<[u32; 3]> {
    let mut v = Vec::new();
    for a in (0..=n).rev() {
        for b in (0..=n - a).rev() {
            v.push([a, b, n - a - b]);
        }
    }
    v
}

impl<F: Field> Quartic<F>
where
    F::E: Hash,
{
    /// Sets up the arithmetic. `curve` must be a quartic, smooth mod p, through [0:0:1].
    /// Total number of coordinates: `total` (at least 29).
    pub fn new(f: F, curve: &HomPoly) -> Self {
        Self::with_total(f, curve, 29, 21)
    }

    pub fn with_total(f: F, curve: &HomPoly, total: usize, max_pts: usize) -> Self {
        assert_eq!(curve.degree, 4, "not a quartic");
        assert!(total >= 29);
        let p = f.characteristic();
        let terms: Vec<([u32; 3], F::E)> = curve
            .reduce_mod(p)
            .into_iter()
            .map(|(e, r)| (e, f.from_fp(r)))
            .collect();
        let q = Quartic::<F> {
            f,
            terms,
            k: 0,
            npts: 0,
            len: 0,
            pts: vec![],
            t_is_y: true,
            ser: vec![],
            s1: vec![],
            s3: vec![],
            s4: vec![],
            cubes: vec![],
            w6p: vec![],
            h6: vec![],
            zero: Elt { rows: vec![] },
        };
        q.finish(total, max_pts)
    }

    fn finish(mut self, total: usize, max_pts: usize) -> Self {
        let f = &self.f;
        let o = [f.zero(), f.zero(), f.one()];
        assert!(f.is_zero(self.eval_form_terms(&self.terms, o)), "[0:0:1] not on C");
        // linear part a x + b y of F(x, y, 1)
        let a = self.coeff_of([1, 0, 3]);
        let b = self.coeff_of([0, 1, 3]);
        self.t_is_y = !f.is_zero(a);
        assert!(self.t_is_y || !f.is_zero(b), "[0:0:1] singular");
        // points of C(F_q) other than [0:0:1]
        let q = f.order();
        let mut pts: Vec<[F::E; 3]> = Vec::new();
        let qq = if max_pts == 0 { 0 } else { q.min(1 << 40) as u64 };
        'outer: for i in 0..qq {
            let x = f.from_index(i);
            for j in 0..qq {
                let y = f.from_index(j);
                let pt = [x, y, f.one()];
                if (i != 0 || j != 0) && f.is_zero(self.eval_form_terms(&self.terms, pt)) {
                    pts.push(pt);
                    if pts.len() >= max_pts {
                        break 'outer;
                    }
                }
            }
        }
        if pts.len() < max_pts {
            // line z = 0
            let cand: Vec<[F::E; 3]> = std::iter::once([f.one(), f.zero(), f.zero()])
                .chain((0..qq).map(|i| [f.from_index(i), f.one(), f.zero()]))
                .collect();
            for pt in cand {
                if f.is_zero(self.eval_form_terms(&self.terms, pt)) {
                    pts.push(pt);
                    if pts.len() >= max_pts {
                        break;
                    }
                }
            }
        }
        self.npts = pts.len();
        self.pts = pts;
        self.k = total - self.npts;
        self.len = total;
        assert!(self.k >= 8);
        self.ser = self.local_series(self.k);
        self.s1 = monomials(1).iter().map(|&m| self.rho_mono(m)).collect();
        self.s3 = monomials(3).iter().map(|&m| self.rho_mono(m)).collect();
        let s4all: Vec<Vec<F::E>> = monomials(4).iter().map(|&m| self.rho_mono(m)).collect();
        let s4 = self.rref(s4all);
        assert_eq!(s4.dim(), 14, "dim S_4");
        self.s4 = s4.rows;
        assert_eq!(self.rref(self.s3.clone()).dim(), 10, "dim S_3");
        self.cubes = vec![
            self.rho_mono([3, 0, 0]),
            self.rho_mono([0, 3, 0]),
            self.rho_mono([0, 0, 3]),
        ];
        let s3r = self.rref(self.s3.clone());
        let w6p = self.order_filter(&s3r, 6);
        assert_eq!(w6p.len(), 4, "h^0(O(3)(-6P))");
        let w6ps = self.rref(w6p);
        assert_eq!(w6ps.piv[0], 6, "O(3)(-6P) not base point free at P");
        self.h6 = w6ps.rows[0].clone();
        self.w6p = w6ps.rows;
        let z = self.order_filter(&s3r, 3);
        assert_eq!(z.len(), 7);
        self.zero = Elt { rows: self.rref(z).rows };
        self
    }

    fn coeff_of(&self, e: [u32; 3]) -> F::E {
        self.terms
            .iter()
            .find(|(t, _)| *t == e)
            .map(|(_, c)| *c)
            .unwrap_or(self.f.zero())
    }

    pub fn eval_form_terms(&self, terms: &[([u32; 3], F::E)], pt: [F::E; 3]) -> F::E {
        let f = &self.f;
        let mut acc = f.zero();
        for &(e, c) in terms {
            let mut m = c;
            for v in 0..3 {
                m = f.mul(m, f.pow(pt[v], e[v] as u128));
            }
            acc = f.add(acc, m);
        }
        acc
    }

    fn ser_mul(&self, a: &[F::E], b: &[F::E], k: usize) -> Vec<F::E> {
        let f = &self.f;
        let mut c = vec![f.zero(); k];
        for i in 0..k {
            if f.is_zero(a[i]) {
                continue;
            }
            for j in 0..k - i {
                c[i + j] = f.add(c[i + j], f.mul(a[i], b[j]));
            }
        }
        c
    }

    fn ser_pow(&self, a: &[F::E], e: u32, k: usize) -> Vec<F::E> {
        let f = &self.f;
        let mut r = vec![f.zero(); k];
        r[0] = f.one();
        for _ in 0..e {
            r = self.ser_mul(&r, a, k);
        }
        r
    }

    /// Series of the dependent coordinate in the local parameter, mod t^k.
    fn local_series(&self, k: usize) -> Vec<F::E> {
        let f = &self.f;
        let mut tser = vec![f.zero(); k];
        tser[1] = f.one();
        let lin = if self.t_is_y {
            self.coeff_of([1, 0, 3])
        } else {
            self.coeff_of([0, 1, 3])
        };
        let linv = f.inv(lin);
        let mut s = vec![f.zero(); k];
        for _ in 0..k + 1 {
            // value of F(x, y, 1) on the current approximation
            let (xs, ys) = if self.t_is_y { (&s, &tser) } else { (&tser, &s) };
            let mut val = vec![f.zero(); k];
            for &(e, c) in &self.terms {
                let m = self.ser_mul(&self.ser_pow(xs, e[0], k), &self.ser_pow(ys, e[1], k), k);
                for i in 0..k {
                    val[i] = f.add(val[i], f.mul(c, m[i]));
                }
            }
            for i in 0..k {
                s[i] = f.sub(s[i], f.mul(val[i], linv));
            }
        }
        // check
        let (xs, ys) = if self.t_is_y { (&s, &tser) } else { (&tser, &s) };
        let mut val = vec![f.zero(); k];
        for &(e, c) in &self.terms {
            let m = self.ser_mul(&self.ser_pow(xs, e[0], k), &self.ser_pow(ys, e[1], k), k);
            for i in 0..k {
                val[i] = f.add(val[i], f.mul(c, m[i]));
            }
        }
        assert!(val.iter().all(|&v| f.is_zero(v)), "local expansion failed");
        s
    }

    /// rho of a monomial.
    pub fn rho_mono(&self, e: [u32; 3]) -> Vec<F::E> {
        let f = &self.f;
        let k = self.k;
        let mut tser = vec![f.zero(); k];
        tser[1] = f.one();
        let (xs, ys) = if self.t_is_y { (&self.ser, &tser) } else { (&tser, &self.ser) };
        let mut v = self.ser_mul(&self.ser_pow(xs, e[0], k), &self.ser_pow(ys, e[1], k), k);
        for pt in &self.pts {
            let mut m = f.one();
            for i in 0..3 {
                m = f.mul(m, f.pow(pt[i], e[i] as u128));
            }
            v.push(m);
        }
        v
    }

    /// rho of a form given by terms.
    pub fn rho_form(&self, terms: &[([u32; 3], F::E)]) -> Vec<F::E> {
        let f = &self.f;
        let mut v = vec![f.zero(); self.len];
        for &(e, c) in terms {
            let m = self.rho_mono(e);
            for i in 0..self.len {
                v[i] = f.add(v[i], f.mul(c, m[i]));
            }
        }
        v
    }

    #[inline]
    pub fn sec_mul(&self, a: &[F::E], b: &[F::E]) -> Vec<F::E> {
        let f = &self.f;
        let k = self.k;
        let mut c = vec![f.zero(); self.len];
        for i in 0..k {
            let ai = a[i];
            if f.is_zero(ai) {
                continue;
            }
            for j in 0..k - i {
                c[i + j] = f.add(c[i + j], f.mul(ai, b[j]));
            }
        }
        for i in k..self.len {
            c[i] = f.mul(a[i], b[i]);
        }
        c
    }

    /// Reduced row echelon form of the span of `rows`.
    pub fn rref(&self, mut rows: Vec<Vec<F::E>>) -> Space<F::E> {
        let f = &self.f;
        let ncols = if rows.is_empty() { 0 } else { rows[0].len() };
        let mut piv = Vec::new();
        let mut rank = 0;
        for col in 0..ncols {
            if rank == rows.len() {
                break;
            }
            let Some(r) = (rank..rows.len()).find(|&r| !f.is_zero(rows[r][col])) else {
                continue;
            };
            rows.swap(rank, r);
            let inv = f.inv(rows[rank][col]);
            for x in rows[rank].iter_mut().skip(col) {
                *x = f.mul(*x, inv);
            }
            let pr = rows[rank].clone();
            for (i, row) in rows.iter_mut().enumerate() {
                if i == rank {
                    continue;
                }
                let c = row[col];
                if f.is_zero(c) {
                    continue;
                }
                for j in col..ncols {
                    row[j] = f.sub(row[j], f.mul(c, pr[j]));
                }
            }
            piv.push(col);
            rank += 1;
        }
        rows.truncate(rank);
        Space { rows, piv }
    }

    /// v minus its projection: coordinates at the pivots become 0.
    #[inline]
    pub fn reduce_vec(&self, s: &Space<F::E>, v: &mut [F::E]) {
        let f = &self.f;
        for (row, &p) in s.rows.iter().zip(&s.piv) {
            let c = v[p];
            if f.is_zero(c) {
                continue;
            }
            for j in p..v.len() {
                v[j] = f.sub(v[j], f.mul(c, row[j]));
            }
        }
    }

    pub fn contains(&self, s: &Space<F::E>, v: &[F::E]) -> bool {
        let mut w = v.to_vec();
        self.reduce_vec(s, &mut w);
        w.iter().all(|&c| self.f.is_zero(c))
    }

    /// Basis of {g in span(cand) : g u in T for every u in us}; `cand` independent.
    pub fn colon(&self, cand: &[Vec<F::E>], us: &[Vec<F::E>], t: &Space<F::E>) -> Vec<Vec<F::E>> {
        let f = &self.f;
        let n = cand.len();
        let mut is_piv = vec![false; self.len];
        for &p in &t.piv {
            is_piv[p] = true;
        }
        let nonpiv: Vec<usize> = (0..self.len).filter(|&c| !is_piv[c]).collect();
        let w = us.len() * nonpiv.len();
        let mut m: Vec<Vec<F::E>> = Vec::with_capacity(n);
        for (i, b) in cand.iter().enumerate() {
            let mut row = Vec::with_capacity(w + n);
            for u in us {
                let mut pr = self.sec_mul(b, u);
                self.reduce_vec(t, &mut pr);
                for &c in &nonpiv {
                    row.push(pr[c]);
                }
            }
            for j in 0..n {
                row.push(if i == j { f.one() } else { f.zero() });
            }
            m.push(row);
        }
        let mut rank = 0;
        for col in 0..w {
            if rank == n {
                break;
            }
            let Some(r) = (rank..n).find(|&r| !f.is_zero(m[r][col])) else {
                continue;
            };
            m.swap(rank, r);
            let inv = f.inv(m[rank][col]);
            let pr: Vec<F::E> = m[rank].iter().map(|&x| f.mul(x, inv)).collect();
            for row in m.iter_mut().skip(rank + 1) {
                let c = row[col];
                if f.is_zero(c) {
                    continue;
                }
                for j in col..w + n {
                    row[j] = f.sub(row[j], f.mul(c, pr[j]));
                }
            }
            m[rank] = pr;
            rank += 1;
        }
        m[rank..]
            .iter()
            .map(|row| {
                let mut v = vec![f.zero(); self.len];
                for (j, b) in cand.iter().enumerate() {
                    let c = row[w + j];
                    if f.is_zero(c) {
                        continue;
                    }
                    for i in 0..self.len {
                        v[i] = f.add(v[i], f.mul(c, b[i]));
                    }
                }
                v
            })
            .collect()
    }

    /// Order at P of a section (k if all Taylor coefficients vanish).
    pub fn order(&self, v: &[F::E]) -> usize {
        (0..self.k).find(|&i| !self.f.is_zero(v[i])).unwrap_or(self.k)
    }

    /// Elements of order >= j (the space must be in RREF).
    pub fn order_filter(&self, s: &Space<F::E>, j: usize) -> Vec<Vec<F::E>> {
        s.rows
            .iter()
            .zip(&s.piv)
            .filter(|(_, &p)| p >= j)
            .map(|(r, _)| r.clone())
            .collect()
    }

    fn products(&self, a: &[Vec<F::E>], b: &[Vec<F::E>]) -> Vec<Vec<F::E>> {
        let mut v = Vec::with_capacity(a.len() * b.len());
        for x in a {
            for y in b {
                v.push(self.sec_mul(x, y));
            }
        }
        v
    }

    fn times(&self, h: &[F::E], b: &[Vec<F::E>]) -> Space<F::E> {
        self.rref(b.iter().map(|y| self.sec_mul(h, y)).collect())
    }

    pub fn zero(&self) -> Elt<F::E> {
        self.zero.clone()
    }

    pub fn is_zero(&self, x: &Elt<F::E>) -> bool {
        *x == self.zero
    }

    /// Class of E - eP, from W3 = H^0(O(3)(-E)) (any basis), E effective of degree e <= 6.
    pub fn class_from_w3(&self, w3: Vec<Vec<F::E>>, e: usize) -> Elt<F::E> {
        assert!(e <= 6);
        let w3s = self.rref(w3);
        assert_eq!(w3s.dim(), 10 - e, "h^0(O(3)(-E))");
        if e < 3 {
            // E + (3 - e)P: order at P at least v_P(E) + 3 - e, v_P(E) = min order
            let vmin = w3s.piv[0];
            assert!(vmin < self.k);
            let w = self.order_filter(&w3s, vmin + 3 - e);
            return self.reduce_w3(&self.rref(w), 3);
        }
        self.reduce_w3(&w3s, e)
    }

    /// Core reduction: W3 = H^0(O(3)(-E)) in RREF, deg E = e in [3, 6]; returns the class of E - eP.
    fn reduce_w3(&self, w3: &Space<F::E>, e: usize) -> Elt<F::E> {
        assert!((3..=6).contains(&e));
        assert_eq!(w3.dim(), 10 - e);
        // h of minimal order, so that P is not in supp A, div h = E + A
        assert!(w3.piv[0] < self.k);
        let h = &w3.rows[0];
        let hs3 = self.times(h, &self.s3);
        assert_eq!(hs3.dim(), 10);
        // Z = H^0(O(3)(-A)) ~ H^0(E) through g -> g/h
        let z = self.colon(&self.s3, &w3.rows, &hs3);
        let zs = self.rref(z);
        // element of maximal order: j* = max{j : h^0(E - jP) > 0}
        let ntay = zs.piv.iter().filter(|&&p| p < self.k).count();
        assert_eq!(ntay, zs.dim(), "element of H^0(E) of order >= k");
        let g = zs.rows[ntay - 1].clone();
        let jstar = zs.piv[ntay - 1];
        assert!(jstar + 3 >= e && jstar <= e, "j* out of range");
        // U = H^0(O(4)(-A - (e-3)P)); then W = {w : w U within g S_4}; E_x = div g - A - (e-3)P
        let hs4 = self.times(h, &self.s4);
        assert_eq!(hs4.dim(), 14);
        let u0 = self.colon(&self.s4, &w3.rows, &hs4);
        assert_eq!(u0.len(), e + 2, "h^0(O(4)(-A))");
        let u = self.order_filter(&self.rref(u0), e - 3);
        assert_eq!(u.len(), 5, "h^0(O(4)(-A-(e-3)P))");
        let gs4 = self.times(&g, &self.s4);
        assert_eq!(gs4.dim(), 14);
        let w = self.colon(&self.s3, &u, &gs4);
        assert_eq!(w.len(), 7, "h^0(O(3)(-E_x))");
        Elt { rows: self.rref(w).rows }
    }

    pub fn add(&self, x: &Elt<F::E>, y: &Elt<F::E>) -> Elt<F::E> {
        let w6 = self.rref(self.products(&x.rows, &y.rows));
        assert_eq!(w6.dim(), 16, "h^0(O(6)(-E_x-E_y))");
        let w3 = self.colon(&self.s3, &self.cubes, &w6);
        assert_eq!(w3.len(), 4, "h^0(O(3)(-E_x-E_y))");
        self.reduce_w3(&self.rref(w3), 6)
    }

    pub fn neg(&self, x: &Elt<F::E>) -> Elt<F::E> {
        // div h6 = 6P + B, P not in B; H^0(6P - E_x) ~ H^0(O(3)(-B-E_x)) through g -> g/h6
        let t = self.times(&self.h6, &x.rows);
        assert_eq!(t.dim(), 7);
        let z = self.colon(&self.s3, &self.w6p, &t);
        assert!(!z.is_empty());
        let zs = self.rref(z);
        let ntay = zs.piv.iter().filter(|&&p| p < self.k).count();
        assert_eq!(ntay, zs.dim());
        let g = zs.rows[ntay - 1].clone();
        // U = H^0(O(4)(-B-E_x)) = {s : s W(6P) within h6 W_x^(4)}
        let x4 = self.rref(self.products(&x.rows, &self.s1));
        assert_eq!(x4.dim(), 11, "h^0(O(4)(-E_x))");
        let t4 = self.times(&self.h6, &x4.rows);
        assert_eq!(t4.dim(), 11);
        let u = self.colon(&self.s4, &self.w6p, &t4);
        assert_eq!(u.len(), 5, "h^0(O(4)(-B-E_x))");
        let gs4 = self.times(&g, &self.s4);
        assert_eq!(gs4.dim(), 14);
        let w = self.colon(&self.s3, &u, &gs4);
        assert_eq!(w.len(), 7);
        Elt { rows: self.rref(w).rows }
    }

    pub fn sub(&self, x: &Elt<F::E>, y: &Elt<F::E>) -> Elt<F::E> {
        self.add(x, &self.neg(y))
    }

    pub fn mul_u128(&self, x: &Elt<F::E>, n: u128) -> Elt<F::E> {
        let mut acc = self.zero();
        if n == 0 {
            return acc;
        }
        let top = 127 - n.leading_zeros();
        for i in (0..=top).rev() {
            acc = self.add(&acc, &acc);
            if (n >> i) & 1 == 1 {
                acc = self.add(&acc, x);
            }
        }
        acc
    }

    pub fn mul_i128(&self, x: &Elt<F::E>, n: i128) -> Elt<F::E> {
        let r = self.mul_u128(x, n.unsigned_abs());
        if n < 0 {
            self.neg(&r)
        } else {
            r
        }
    }

    /// W3 of an effective divisor cut out by homogeneous forms of degree <= 3 (the degree 3
    /// part of the ideal they generate); returns None if its dimension is not 10 - e.
    pub fn w3_from_ideal(&self, gens: &[Vec<([u32; 3], F::E)>], e: usize) -> Option<Vec<Vec<F::E>>> {
        let f = &self.f;
        let mut v = Vec::new();
        for g in gens {
            let d = g.iter().map(|(t, _)| t[0] + t[1] + t[2]).max().unwrap();
            assert!(d <= 3);
            for m in monomials(3 - d) {
                let terms: Vec<([u32; 3], F::E)> = g
                    .iter()
                    .map(|&(t, c)| ([t[0] + m[0], t[1] + m[1], t[2] + m[2]], c))
                    .collect();
                v.push(self.rho_form(&terms));
            }
        }
        let s = self.rref(v);
        let _ = f;
        if s.dim() == 10 - e {
            Some(s.rows)
        } else {
            None
        }
    }

    /// W3 of a point of C(F_q) other than P.
    pub fn w3_point(&self, pt: [F::E; 3]) -> Vec<Vec<F::E>> {
        let f = &self.f;
        let mons = monomials(3);
        let vals: Vec<F::E> = mons
            .iter()
            .map(|&m| {
                let mut r = f.one();
                for i in 0..3 {
                    r = f.mul(r, f.pow(pt[i], m[i] as u128));
                }
                r
            })
            .collect();
        let piv = vals.iter().position(|&v| !f.is_zero(v)).expect("zero point");
        let inv = f.inv(vals[piv]);
        let mut out = Vec::new();
        for j in 0..mons.len() {
            if j == piv {
                continue;
            }
            // m_j - (v_j / v_piv) m_piv
            let c = f.neg(f.mul(vals[j], inv));
            let mut v = self.s3[j].clone();
            for i in 0..self.len {
                v[i] = f.add(v[i], f.mul(c, self.s3[piv][i]));
            }
            out.push(v);
        }
        out
    }

    pub fn is_on_curve(&self, pt: [F::E; 3]) -> bool {
        self.f.is_zero(self.eval_form_terms(&self.terms, pt))
    }

    pub fn is_base_point(&self, pt: [F::E; 3]) -> bool {
        let f = &self.f;
        f.is_zero(pt[0]) && f.is_zero(pt[1]) && !f.is_zero(pt[2])
    }

    /// Class [Q - P] of a point Q of C(F_q).
    pub fn point_class(&self, pt: [F::E; 3]) -> Elt<F::E> {
        assert!(self.is_on_curve(pt));
        if self.is_base_point(pt) {
            return self.zero();
        }
        self.class_from_w3(self.w3_point(pt), 1)
    }
}

impl Quartic<Fp> {
    /// All points of C(F_p), P first.
    pub fn all_points(&self) -> Vec<[u64; 3]> {
        let p = self.f.p;
        let mut v = vec![[0, 0, 1]];
        for x in 0..p {
            for y in 0..p {
                if (x, y) != (0, 0) && self.is_on_curve([x, y, 1]) {
                    v.push([x, y, 1]);
                }
            }
        }
        if self.is_on_curve([1, 0, 0]) {
            v.push([1, 0, 0]);
        }
        for x in 0..p {
            if self.is_on_curve([x, 1, 0]) {
                v.push([x, 1, 0]);
            }
        }
        v
    }

    /// W3 of the place of a point of C(F_{p^K}) of exact degree K (conditions w(pt) = 0).
    pub fn w3_place<const K: usize>(&self, ext: &Gf<K>, pt: [[u64; K]; 3]) -> Vec<Vec<u64>> {
        let f = &self.f;
        let mons = monomials(3);
        // rows of the K x 10 system over F_p
        let vals: Vec<[u64; K]> = mons
            .iter()
            .map(|&m| {
                let mut r = ext.one();
                for i in 0..3 {
                    r = ext.mul(r, ext.pow(pt[i], m[i] as u128));
                }
                r
            })
            .collect();
        // kernel of the K x 10 matrix (columns: monomials)
        let mut rows: Vec<Vec<u64>> = (0..10)
            .map(|j| {
                let mut r: Vec<u64> = vals[j].to_vec();
                for i in 0..10 {
                    r.push(if i == j { 1 } else { 0 });
                }
                r
            })
            .collect();
        let mut rank = 0;
        for col in 0..K {
            let Some(r) = (rank..10).find(|&r| rows[r][col] != 0) else {
                continue;
            };
            rows.swap(rank, r);
            let inv = f.inv(rows[rank][col]);
            let pr: Vec<u64> = rows[rank].iter().map(|&x| f.mul(x, inv)).collect();
            for row in rows.iter_mut().skip(rank + 1) {
                let c = row[col];
                if c == 0 {
                    continue;
                }
                for j in col..K + 10 {
                    row[j] = f.sub(row[j], f.mul(c, pr[j]));
                }
            }
            rows[rank] = pr;
            rank += 1;
        }
        rows[rank..]
            .iter()
            .map(|row| {
                let mut v = vec![0u64; self.len];
                for j in 0..10 {
                    let c = row[K + j];
                    if c == 0 {
                        continue;
                    }
                    for i in 0..self.len {
                        v[i] = f.add(v[i], f.mul(c, self.s3[j][i]));
                    }
                }
                v
            })
            .collect()
    }

    /// A random point of C(F_{p^K}) not defined over a proper subfield (affine chart z = 1).
    pub fn random_point_ext<const K: usize>(&self, ext: &Gf<K>, rng: &mut ffpoly::SplitMix64) -> [[u64; K]; 3] {
        let p = self.f.p;
        loop {
            let mut x = [0u64; K];
            for c in x.iter_mut() {
                *c = rng.next_u64() % p;
            }
            // is x in a proper subfield? then skip (the point might still be of degree K, but
            // restricting to x generating F_{p^K} is simpler and still random enough)
            let mut s = ext.frob(x);
            let mut deg = 1;
            while s != x {
                s = ext.frob(s);
                deg += 1;
            }
            if deg != K {
                continue;
            }
            // polynomial in y: F(x, y, 1)
            let mut poly = vec![ext.zero(); 5];
            for &(e, c) in &self.terms {
                if e[2] + e[0] + e[1] != 4 {
                    continue;
                }
                let m = ext.mul(ext.from_fp(c), ext.pow(x, e[0] as u128));
                poly[e[1] as usize] = ext.add(poly[e[1] as usize], m);
            }
            let roots = ffpoly::roots(ext, &poly);
            if roots.is_empty() {
                continue;
            }
            let y = roots[(rng.next_u64() % roots.len() as u64) as usize];
            return [x, y, ext.one()];
        }
    }

    /// Class [place - K P] of a random place of degree K (K <= 6).
    pub fn random_place_class<const K: usize>(&self, ext: &Gf<K>, rng: &mut ffpoly::SplitMix64) -> Elt<u64> {
        let pt = self.random_point_ext(ext, rng);
        let w3 = self.w3_place(ext, pt);
        self.class_from_w3(w3, K)
    }

    /// A random element of J(F_p): sum of the classes of a random place of degree 3 and a
    /// random place of degree 2 (spread over the whole group).
    pub fn random_elt(&self, rng: &mut ffpoly::SplitMix64, e2: &Gf<2>, e3: &Gf<3>) -> Elt<u64> {
        let a = self.random_place_class(e3, rng);
        let b = self.random_place_class(e2, rng);
        self.add(&a, &b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn klein() -> HomPoly {
        // x^3 y + y^3 z + z^3 x passes through [0:0:1]? F(0,0,1) = 0 yes
        HomPoly::parse("x^3*y + y^3*z + z^3*x").unwrap()
    }

    #[test]
    fn group_law_klein_mod_29() {
        let f = Fp::new(29);
        let c = klein();
        let j = Quartic::new(f, &c);
        let pts = j.all_points();
        let e2 = Gf::<2>::standard(29);
        let e3 = Gf::<3>::standard(29);
        let mut rng = ffpoly::SplitMix64(7);
        let x = j.random_elt(&mut rng, &e2, &e3);
        let y = j.random_elt(&mut rng, &e2, &e3);
        let z = j.point_class(pts[3]);
        assert_eq!(j.add(&x, &y), j.add(&y, &x));
        assert_eq!(j.add(&j.add(&x, &y), &z), j.add(&x, &j.add(&y, &z)));
        assert!(j.is_zero(&j.add(&x, &j.neg(&x))));
        assert_eq!(j.add(&x, &j.zero()), x);
        // #J(F_29) of the Klein quartic: 29 = 1 mod 7, L = L_E^3 with E = 49a1
        // a_29(49a1) = 0? compute N1 via points: L(1) from zeta is checked in the binary tests
        let n1 = pts.len() as i64;
        let a = 29 + 1 - n1; // trace = 3 a_E
        assert_eq!(a % 3, 0);
        let ae = a / 3;
        let ord = (1 + 29 - ae) * (1 + 29 - ae) * (1 + 29 - ae);
        assert!(j.is_zero(&j.mul_u128(&x, ord as u128)));
        assert!(j.is_zero(&j.mul_u128(&z, ord as u128)));
    }
}

impl<F: Field> crate::abgroup::AbGroup for Quartic<F>
where
    F::E: Hash,
{
    type El = Elt<F::E>;
    fn zero(&self) -> Elt<F::E> {
        self.zero.clone()
    }
    fn add(&self, a: &Elt<F::E>, b: &Elt<F::E>) -> Elt<F::E> {
        Quartic::add(self, a, b)
    }
    fn neg(&self, a: &Elt<F::E>) -> Elt<F::E> {
        Quartic::neg(self, a)
    }
    fn mul(&self, a: &Elt<F::E>, n: u128) -> Elt<F::E> {
        self.mul_u128(a, n)
    }
}
