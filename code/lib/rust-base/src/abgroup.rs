//! Finite abelian groups given by a black box with canonical (hashable) elements:
//! basis of an ℓ-Sylow subgroup and discrete logarithms in it.
//!
//! [`Sylow::build`] needs the order ℓ^v of the Sylow subgroup and a source of random
//! elements of it. It keeps an independent family b_1..b_k (orders ℓ^{e_i}, e_1 >= e_2 >= ...)
//! generating H, adds random elements y (smallest m with ℓ^m y in H, relation found by
//! discrete log) and recomputes a basis from the relation matrix by a Smith normal form
//! over Z/ℓ^M (local ring, pivots of minimal valuation). It stops when |H| = ℓ^v.
//!
//! [`Sylow::dlog`] is Pohlig-Hellman digit by digit: at step s = 1..E (E = e_1) the element
//! ℓ^{E-s}(y - known part) lies in H[ℓ] and gives one more digit of every coordinate x_i
//! with e_i >= E - s + 1, by lookup in a table of H[ℓ] (split in two halves, baby steps /
//! giant steps, when ℓ^k is large). The answer is always verified by recomputing
//! sum x_i b_i, so a returned value is a proof of membership.

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

pub trait AbGroup {
    type El: Clone + Eq + Hash + Debug;
    fn zero(&self) -> Self::El;
    fn add(&self, a: &Self::El, b: &Self::El) -> Self::El;
    fn neg(&self, a: &Self::El) -> Self::El;
    fn is_zero(&self, a: &Self::El) -> bool {
        *a == self.zero()
    }
    fn mul(&self, a: &Self::El, n: u128) -> Self::El {
        let mut acc = self.zero();
        if n == 0 {
            return acc;
        }
        let top = 127 - n.leading_zeros();
        for i in (0..=top).rev() {
            acc = self.add(&acc, &acc);
            if (n >> i) & 1 == 1 {
                acc = self.add(&acc, a);
            }
        }
        acc
    }
    /// sum c_i g_i
    fn combo(&self, gens: &[Self::El], coeffs: &[u128]) -> Self::El {
        let mut acc = self.zero();
        for (g, &c) in gens.iter().zip(coeffs) {
            if c != 0 {
                acc = self.add(&acc, &self.mul(g, c));
            }
        }
        acc
    }
}

pub fn ipow(b: u64, e: u32) -> u128 {
    (b as u128).pow(e)
}

fn val(ell: u64, mut x: u128, cap: u32) -> u32 {
    if x == 0 {
        return cap;
    }
    let mut v = 0;
    while x % ell as u128 == 0 {
        x /= ell as u128;
        v += 1;
    }
    v.min(cap)
}

fn inv_mod(a: u128, m: u128) -> u128 {
    // extended Euclid on i128 (m < 2^62)
    let (mut r0, mut r1) = (m as i128, (a % m) as i128);
    let (mut s0, mut s1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
    }
    assert_eq!(r0, 1, "not invertible");
    s0.rem_euclid(m as i128) as u128
}

/// Smith form over Z/ℓ^M of a square relation matrix (rows = relations among generators).
/// Returns (exponents a_j, matrix Vinv) such that the new generators x'_j = sum_i Vinv[j][i] x_i
/// have orders ℓ^{a_j} and generate the same group.
fn local_snf(ell: u64, mm: u32, mut a: Vec<Vec<u128>>) -> (Vec<u32>, Vec<Vec<u128>>) {
    let n = a.len();
    let modu = ipow(ell, mm);
    assert!(modu < (1u128 << 62));
    let mut vinv: Vec<Vec<u128>> = (0..n)
        .map(|i| (0..n).map(|j| if i == j { 1 } else { 0 }).collect())
        .collect();
    let mut exps = vec![0u32; n];
    for t in 0..n {
        // pivot of minimal valuation in a[t.., t..]
        let mut best = (mm + 1, t, t);
        for i in t..n {
            for j in t..n {
                let v = val(ell, a[i][j] % modu, mm);
                if v < best.0 {
                    best = (v, i, j);
                }
            }
        }
        let (v, pi, pj) = best;
        assert!(v < mm, "relation matrix not of full rank mod ℓ^M");
        a.swap(t, pi);
        for row in a.iter_mut() {
            row.swap(t, pj);
        }
        vinv.swap(t, pj);
        let pv = ipow(ell, v);
        let unit = (a[t][t] / pv) % modu;
        let uinv = inv_mod(unit, modu);
        for j in 0..n {
            a[t][j] = a[t][j] * uinv % modu;
        }
        // now a[t][t] = ℓ^v (mod ℓ^M)
        for i in 0..n {
            if i == t {
                continue;
            }
            let w = (a[i][t] / pv) % modu;
            if w == 0 {
                continue;
            }
            for j in 0..n {
                a[i][j] = (a[i][j] + modu - w * a[t][j] % modu) % modu;
            }
        }
        for j in 0..n {
            if j == t {
                continue;
            }
            let w = (a[t][j] / pv) % modu;
            if w == 0 {
                continue;
            }
            // col_j -= w col_t ; Vinv: row_t += w row_j
            for i in 0..n {
                a[i][j] = (a[i][j] + modu - w * a[i][t] % modu) % modu;
            }
            for i in 0..n {
                vinv[t][i] = (vinv[t][i] + w * vinv[j][i]) % modu;
            }
        }
        exps[t] = v;
    }
    (exps, vinv)
}

pub struct Sylow<El> {
    pub ell: u64,
    /// Basis, e_1 >= e_2 >= ... >= 1.
    pub gens: Vec<El>,
    pub exps: Vec<u32>,
    /// pw[i][j] = ℓ^j gens[i], j < e_i.
    pw: Vec<Vec<El>>,
    /// Table of the first `ka` generators' contribution to H[ℓ].
    tab: HashMap<El, Vec<u32>>,
    ka: usize,
    /// All elements sum_{i >= ka} d_i ℓ^{e_i - 1} b_i, with their digits.
    giant: Vec<(El, Vec<u32>)>,
}

impl<El: Clone + Eq + Hash + Debug> Sylow<El> {
    pub fn log_order(&self) -> u32 {
        self.exps.iter().sum()
    }

    fn empty(ell: u64) -> Self {
        Sylow {
            ell,
            gens: vec![],
            exps: vec![],
            pw: vec![],
            tab: HashMap::new(),
            ka: 0,
            giant: vec![],
        }
    }

    fn set_basis<G: AbGroup<El = El>>(&mut self, g: &G, gens: Vec<El>, exps: Vec<u32>, table_limit: u128) {
        let mut idx: Vec<usize> = (0..gens.len()).collect();
        idx.sort_by(|&a, &b| exps[b].cmp(&exps[a]));
        self.gens = idx.iter().map(|&i| gens[i].clone()).collect();
        self.exps = idx.iter().map(|&i| exps[i]).collect();
        let ell = self.ell as u128;
        self.pw = self
            .gens
            .iter()
            .zip(&self.exps)
            .map(|(b, &e)| {
                let mut v = vec![b.clone()];
                for _ in 1..e {
                    let last = v.last().unwrap().clone();
                    v.push(g.mul(&last, ell));
                }
                v
            })
            .collect();
        let k = self.gens.len();
        let tors: Vec<El> = (0..k).map(|i| self.pw[i][self.exps[i] as usize - 1].clone()).collect();
        // split
        let mut ka = k;
        while ka > 0 && ipow(self.ell, ka as u32) > table_limit {
            ka -= 1;
        }
        self.ka = ka;
        let enumerate = |ids: &[usize]| -> Vec<(El, Vec<u32>)> {
            let mut out = vec![(g.zero(), vec![0u32; ids.len()])];
            for (pos, &i) in ids.iter().enumerate() {
                let mut next = Vec::with_capacity(out.len() * self.ell as usize);
                for (e, d) in &out {
                    let mut cur = e.clone();
                    for c in 0..self.ell as u32 {
                        let mut dd = d.clone();
                        dd[pos] = c;
                        next.push((cur.clone(), dd));
                        cur = g.add(&cur, &tors[i]);
                    }
                }
                out = next;
            }
            out
        };
        let a_ids: Vec<usize> = (0..ka).collect();
        let b_ids: Vec<usize> = (ka..k).collect();
        self.tab = enumerate(&a_ids).into_iter().collect();
        assert_eq!(self.tab.len() as u128, ipow(self.ell, ka as u32), "H[ℓ] table not injective");
        self.giant = enumerate(&b_ids)
            .into_iter()
            .map(|(e, d)| (g.neg(&e), d))
            .collect();
    }

    /// Digits d with z = sum d_i ℓ^{e_i-1} b_i, if z is in H[ℓ].
    fn lookup<G: AbGroup<El = El>>(&self, g: &G, z: &El) -> Option<Vec<u32>> {
        for (ng, db) in &self.giant {
            let w = if db.iter().all(|&c| c == 0) { z.clone() } else { g.add(z, ng) };
            if let Some(da) = self.tab.get(&w) {
                let mut d = da.clone();
                d.extend_from_slice(db);
                return Some(d);
            }
        }
        None
    }

    /// Coordinates of y in the basis (x_i mod ℓ^{e_i}), or None if y is not in H.
    pub fn dlog<G: AbGroup<El = El>>(&self, g: &G, y: &El) -> Option<Vec<u128>> {
        let k = self.gens.len();
        if k == 0 {
            return if g.is_zero(y) { Some(vec![]) } else { None };
        }
        let ell = self.ell as u128;
        let emax = self.exps[0];
        // ly[j] = ℓ^j y
        let mut ly = vec![y.clone()];
        for _ in 1..emax {
            let last = ly.last().unwrap().clone();
            ly.push(g.mul(&last, ell));
        }
        let mut x = vec![0u128; k];
        for s in 1..=emax {
            let lev = (emax - s) as usize; // multiply by ℓ^lev
            let mut z = ly[lev].clone();
            for i in 0..k {
                let e = self.exps[i];
                if e + s <= emax {
                    continue; // e_i < E - s + 1
                }
                let u = e + s - emax - 1; // digits known: x_i mod ℓ^u
                if u == 0 || x[i] == 0 {
                    continue;
                }
                // subtract ℓ^lev x_i b_i, with ℓ^lev b_i = pw[i][lev] (lev < e_i here)
                let t = g.mul(&self.pw[i][lev], x[i]);
                z = g.add(&z, &g.neg(&t));
            }
            let d = self.lookup(g, &z)?;
            for i in 0..k {
                let e = self.exps[i];
                if e + s <= emax {
                    if d[i] != 0 {
                        return None;
                    }
                    continue;
                }
                let u = e + s - emax - 1;
                x[i] += d[i] as u128 * ipow(self.ell, u);
            }
        }
        // verify
        if g.combo(&self.gens, &x) == *y {
            Some(x)
        } else {
            None
        }
    }

    /// Basis of the ℓ-Sylow subgroup of order ℓ^v. `rand` returns random elements of the
    /// Sylow subgroup (for instance cofactor times random elements of the group).
    pub fn build<G: AbGroup<El = El>>(
        g: &G,
        ell: u64,
        v: u32,
        mut rand: impl FnMut() -> El,
        table_limit: u128,
        max_tries: usize,
    ) -> Option<Self> {
        let mut s = Sylow::empty(ell);
        let mm = v + 2;
        let mut tries = 0;
        while s.log_order() < v {
            tries += 1;
            if tries > max_tries {
                return None;
            }
            let y = rand();
            // smallest m with ℓ^m y in H
            let mut cur = y.clone();
            let mut m = 0u32;
            let rel = loop {
                if let Some(c) = s.dlog(g, &cur) {
                    break c;
                }
                cur = g.mul(&cur, ell as u128);
                m += 1;
                assert!(m <= v, "element of order > ℓ^v: wrong group order?");
            };
            if m == 0 {
                continue;
            }
            // relations: ℓ^{e_i} b_i = 0, ℓ^m y - sum c_i b_i = 0
            let k = s.gens.len();
            let modu = ipow(ell, mm);
            let mut a = vec![vec![0u128; k + 1]; k + 1];
            for i in 0..k {
                a[i][i] = ipow(ell, s.exps[i]);
            }
            for i in 0..k {
                a[k][i] = (modu - rel[i] % modu) % modu;
            }
            a[k][k] = ipow(ell, m);
            let (exps, vinv) = local_snf(ell, mm, a);
            let mut oldgens = s.gens.clone();
            oldgens.push(y.clone());
            let mut ng = Vec::new();
            let mut ne = Vec::new();
            for j in 0..=k {
                if exps[j] == 0 {
                    continue;
                }
                let el = g.combo(&oldgens, &vinv[j]);
                // check exact order ℓ^{exps[j]}
                let t = g.mul(&el, ipow(ell, exps[j] - 1));
                assert!(!g.is_zero(&t) && g.is_zero(&g.mul(&t, ell as u128)), "SNF order check failed");
                ng.push(el);
                ne.push(exps[j]);
            }
            assert_eq!(ne.iter().sum::<u32>(), s.log_order() + m, "SNF: group order mismatch");
            s.set_basis(g, ng, ne, table_limit);
        }
        Some(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Z/n1 x Z/n2 x ... as a test group.
    struct Prod(Vec<u128>);
    impl AbGroup for Prod {
        type El = Vec<u128>;
        fn zero(&self) -> Vec<u128> {
            vec![0; self.0.len()]
        }
        fn add(&self, a: &Vec<u128>, b: &Vec<u128>) -> Vec<u128> {
            a.iter().zip(b).zip(&self.0).map(|((x, y), n)| (x + y) % n).collect()
        }
        fn neg(&self, a: &Vec<u128>) -> Vec<u128> {
            a.iter().zip(&self.0).map(|(x, n)| (n - x) % n).collect()
        }
    }

    #[test]
    fn sylow_structure() {
        // Z/8 x Z/4 x Z/2 x Z/27 x Z/9 x Z/5 : 2-part 2^6, 3-part 3^5
        let g = Prod(vec![8, 4, 2, 27, 9, 5]);
        let mut rng = crate::ffpoly::SplitMix64(3);
        let order: u128 = 8 * 4 * 2 * 27 * 9 * 5;
        for (ell, v, want) in [(2u64, 6u32, vec![3u32, 2, 1]), (3, 5, vec![3, 2]), (5, 1, vec![1])] {
            let cof = order / ipow(ell, v);
            let s = Sylow::build(
                &g,
                ell,
                v,
                || {
                    let r: Vec<u128> = g.0.iter().map(|n| rng.next_u64() as u128 % n).collect();
                    g.mul(&r, cof)
                },
                4,
                1000,
            )
            .unwrap();
            assert_eq!(s.exps, want);
            // dlog of random Sylow elements
            for _ in 0..20 {
                let r: Vec<u128> = g.0.iter().map(|n| rng.next_u64() as u128 % n).collect();
                let y = g.mul(&r, cof);
                let x = s.dlog(&g, &y).unwrap();
                assert_eq!(g.combo(&s.gens, &x), y);
            }
            // element outside the Sylow subgroup is rejected
            if ell == 2 {
                assert!(s.dlog(&g, &vec![0, 0, 0, 1, 0, 0]).is_none());
            }
        }
    }
}
