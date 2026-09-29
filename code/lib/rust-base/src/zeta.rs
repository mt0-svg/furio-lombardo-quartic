//! L-polynomials of curves over finite fields from point counts.
//!
//! For a curve of genus g over F_q, Z(T) = L(T) / ((1 - T)(1 - qT)) with
//! L(T) = prod_{i=1}^{2g} (1 - a_i T) = sum_j c_j T^j, and
//! N_k = q^k + 1 - s_k where s_k = sum_i a_i^k.

/// Coefficients c_0..c_{2g} of L from N_1..N_g (g = counts.len()).
/// Newton's identities j c_j = -sum_{k=1}^{j} s_k c_{j-k} give c_1..c_g, the
/// functional equation c_{2g-j} = q^{g-j} c_j gives the rest.
pub fn lpoly_from_counts(q: u64, counts: &[u64]) -> Result<Vec<i128>, String> {
    let g = counts.len();
    let q = q as i128;
    let s: Vec<i128> = (1..=g)
        .map(|k| q.pow(k as u32) + 1 - counts[k - 1] as i128)
        .collect();
    let mut c = vec![0i128; 2 * g + 1];
    c[0] = 1;
    for j in 1..=g {
        let mut acc: i128 = 0;
        for k in 1..=j {
            acc += s[k - 1] * c[j - k];
        }
        if acc % j as i128 != 0 {
            return Err(format!(
                "Newton identity not integral at j = {}: {} / {}",
                j, -acc, j
            ));
        }
        c[j] = -acc / j as i128;
    }
    for j in 0..g {
        c[2 * g - j] = q.pow((g - j) as u32) * c[j];
    }
    Ok(c)
}

/// Power sums s_1..s_n of the reciprocal roots of L (c = c_0..c_{2g}).
pub fn power_sums(l: &[i128], n: usize) -> Vec<i128> {
    let mut s = Vec::with_capacity(n);
    for k in 1..=n {
        let ck = if k < l.len() { l[k] } else { 0 };
        let mut acc = -(k as i128) * ck;
        for i in 1..k {
            let c = if k - i < l.len() { l[k - i] } else { 0 };
            acc -= s[i - 1] * c;
        }
        s.push(acc);
    }
    s
}

/// N_1..N_n predicted by L.
pub fn counts_from_lpoly(q: u64, l: &[i128], n: usize) -> Vec<i128> {
    power_sums(l, n)
        .iter()
        .enumerate()
        .map(|(k, &sk)| (q as i128).pow(k as u32 + 1) + 1 - sk)
        .collect()
}

/// Value of L at an integer point, e.g. L(1) = #Jac(F_q).
pub fn eval(l: &[i128], t: i128) -> i128 {
    l.iter().rev().fold(0i128, |acc, &c| acc * t + c)
}

/// Necessary condition from the Riemann hypothesis: c_j^2 <= binom(2g, j)^2 q^j.
pub fn weil_coefficient_bounds(q: u64, l: &[i128]) -> bool {
    let n = l.len() - 1;
    let mut binom: i128 = 1;
    for (j, &c) in l.iter().enumerate() {
        let lhs = (c as f64).powi(2);
        let rhs = (binom as f64).powi(2) * (q as f64).powi(j as i32);
        if lhs > rhs * (1.0 + 1e-12) {
            return false;
        }
        binom = binom * (n - j) as i128 / (j as i128 + 1);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn klein_over_f2() {
        // N = 3, 5, 24 over F_2, F_4, F_8: L = 1 + 5T^3 + 8T^6
        let l = lpoly_from_counts(2, &[3, 5, 24]).unwrap();
        assert_eq!(l, vec![1, 0, 0, 5, 0, 0, 8]);
        assert_eq!(eval(&l, 1), 14);
        assert_eq!(counts_from_lpoly(2, &l, 3), vec![3, 5, 24]);
        assert!(weil_coefficient_bounds(2, &l));
    }

    #[test]
    fn elliptic_roundtrip() {
        // y^2 = x^3 - x over F_5: a_5 = -2... any (q, a) with |a| <= 2 sqrt q works
        let l = vec![1i128, 2, 5];
        let n = counts_from_lpoly(5, &l, 4);
        let back = lpoly_from_counts(5, &[n[0] as u64]).unwrap();
        assert_eq!(back, l);
    }
}
