import FurioLombardo.M2.ZimmertDefs

/-!
# Zimmert's `S₂` for `K21` at `γ = 1/2`, `α = 1/12` (lane M2)

For the signature `(r₁, r₂) = (3, 9)` of `K21` and Zimmert's parameters `γ = 1/2`, `α = 1/12`:

* `zimmertS2_half`: the closed form
  `21 γ_E - 3π/2 + 60 log 2 + 12 log π - 204/5 + log (207/143)` (about 22.30460);
* `zimmertS2_half_ge`: it is at least `log √(2^22 7^27) - log 120000` (about 22.19916).

The closed form uses `ψ(3/4) = π/2 - 3 log 2 - γ_E` (reflection at `1/4` and duplication at `1/4`)
and `ψ(3/2) = 2 - 2 log 2 - γ_E`. The numerical bound uses the lower bound
`γ_E ≥ H_16 - log 16 - 1/32`, from the monotonicity of `H_n - log n - 1/(2n)` (trapezoid rule for
`1/x`), and truncated logarithm series.
-/

namespace FurioLombardo.M2

open Real

/-! ### The real logarithmic derivative of `Γ` and `Complex.digamma` -/

lemma logDerivGamma_eq_re_digamma {x : ℝ} (hx : 0 < x) :
    logDerivGamma x = (Complex.digamma (x : ℂ)).re := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h'
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hd : HasDerivAt Complex.Gamma (deriv Complex.Gamma x) x :=
    (Complex.differentiableAt_Gamma _ hne).hasDerivAt
  have hr : HasDerivAt (fun y : ℝ => (Complex.Gamma y).re) (deriv Complex.Gamma x).re x :=
    hd.real_of_complex
  have hfun : (fun y : ℝ => (Complex.Gamma y).re) = Real.Gamma := by
    funext y
    rw [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [hfun] at hr
  unfold logDerivGamma
  rw [hr.deriv, Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]

lemma complex_log_two : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_log (by norm_num)]
  norm_num

lemma digamma_three_halves :
    Complex.digamma (3 / 2) = 2 - 2 * ((Real.log 2 : ℝ) : ℂ) - (eulerMascheroniConstant : ℂ) := by
  have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    norm_num at h'
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have h := Complex.digamma_apply_add_one (1 / 2) hs
  rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num, Complex.digamma_one_half, complex_log_two] at h
  rw [h]
  ring

lemma cot_pi_quarter : Complex.cot ((π : ℂ) * (1 / 4)) = 1 := by
  rw [show (π : ℂ) * (1 / 4) = ((π / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cot,
    Real.cot_eq_cos_div_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have : (√2 / 2 : ℝ) ≠ 0 := by positivity
  rw [div_self this, Complex.ofReal_one]

lemma digamma_three_quarters :
    Complex.digamma (3 / 4) = (π : ℂ) / 2 - 3 * ((Real.log 2 : ℝ) : ℂ)
      - (eulerMascheroniConstant : ℂ) := by
  have hz : ∀ n : ℤ, (1 / 4 : ℂ) ≠ n := by
    intro n h
    have h' := congrArg Complex.re h
    norm_num at h'
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hm : ∀ m : ℕ, 2 * (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    norm_num at h'
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have e1 := Complex.digamma_one_sub hz
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by norm_num, cot_pi_quarter, mul_one] at e1
  have e2 := Complex.digamma_two_mul hm
  rw [show 2 * (1 / 4 : ℂ) = 1 / 2 by norm_num, show (1 / 4 : ℂ) + 1 / 2 = 3 / 4 by norm_num,
    Complex.digamma_one_half, complex_log_two] at e2
  linear_combination (1 / 2 : ℂ) * e1 - e2

lemma logDerivGamma_three_halves :
    logDerivGamma (3 / 2) = 2 - 2 * Real.log 2 - eulerMascheroniConstant := by
  rw [logDerivGamma_eq_re_digamma (by norm_num)]
  rw [show (((3 / 2 : ℝ)) : ℂ) = 3 / 2 by push_cast; ring, digamma_three_halves]
  simp [Complex.log_re]

lemma logDerivGamma_three_quarters :
    logDerivGamma (3 / 4) = π / 2 - 3 * Real.log 2 - eulerMascheroniConstant := by
  rw [logDerivGamma_eq_re_digamma (by norm_num)]
  rw [show (((3 / 4 : ℝ)) : ℂ) = 3 / 4 by push_cast; ring, digamma_three_quarters]
  simp [Complex.log_re]

lemma Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  ring

lemma log_Gamma_three_halves : Real.log (Real.Gamma (3 / 2)) = Real.log π / 2 - Real.log 2 := by
  rw [Gamma_three_halves, Real.log_div (by positivity) (by norm_num), Real.log_sqrt pi_pos.le]

/-- Closed form of Zimmert's `S₂` for the signature `(3, 9)` at `γ = 1/2`, `α = 1/12`. -/
theorem zimmertS2_half :
    zimmertS2 3 9 (1 / 2) (1 / 12) = 21 * Real.eulerMascheroniConstant - 3 * π / 2
      + 60 * Real.log 2 + 12 * Real.log π - 204 / 5 + Real.log (207 / 143) := by
  unfold zimmertS2
  rw [show ((1 : ℝ) + 1 / 2) / 2 = 3 / 4 by norm_num, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, logDerivGamma_three_quarters,
    logDerivGamma_three_halves, Real.Gamma_one, log_Gamma_three_halves,
    show (1 + (1 / 12 : ℝ)⁻¹) * ((1 + (1 / 2 : ℝ)⁻¹) ^ 2)⁻¹ * (1 + (2 * (1 / 2) - 1 / 12)⁻¹)⁻¹
      = (207 / 143 : ℝ)⁻¹ by norm_num, Real.log_inv, Real.log_one]
  push_cast
  ring

/-! ### Truncated logarithm series -/

lemma log_one_sub_le_series {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    Real.log (1 - x)
      ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).2
  linarith

lemma series_le_log_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x)
      ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg h0]; exact h1) n
  rw [abs_of_nonneg h0] at h
  have := (abs_le.mp h).1
  linarith

/-! ### A lower bound for the Euler-Mascheroni constant -/

/-- Trapezoid rule for `1/x` on `[n, n + 1]`, from the series of `log (1 + 1/n)`. -/
lemma log_succ_sub_log_le {n : ℝ} (hn : 0 < n) :
    Real.log (n + 1) - Real.log n ≤ (1 / n + 1 / (n + 1)) / 2 := by
  set y : ℝ := 1 / (2 * n + 1) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hS := Real.hasSum_log_one_add_inv hn
  have hG : HasSum (fun k : ℕ => 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 * y)
  have hle : Real.log (1 + n⁻¹) ≤ 2 * y * (1 - y ^ 2)⁻¹ := by
    refine hasSum_le (fun k => ?_) hS hG
    have hk : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      linarith
    have hp : 0 ≤ y ^ (2 * k + 1) := pow_nonneg hy0 _
    calc 2 * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * n + 1)) ^ (2 * k + 1)
        = 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1) := by rw [hy]
      _ ≤ 2 * 1 * y ^ (2 * k + 1) := by gcongr
      _ = 2 * y * (y ^ 2) ^ k := by rw [← pow_mul, pow_succ]; ring
  have hlog : Real.log (1 + n⁻¹) = Real.log (n + 1) - Real.log n := by
    rw [← Real.log_div (by linarith) hn.ne', show 1 + n⁻¹ = (n + 1) / n by field_simp]
  have h2n : (2 * n + 1) ≠ 0 := by positivity
  have h1y : 1 - y ^ 2 = 4 * n * (n + 1) / (2 * n + 1) ^ 2 := by
    rw [hy]
    field_simp
    ring
  have heq : 2 * y * (1 - y ^ 2)⁻¹ = (1 / n + 1 / (n + 1)) / 2 := by
    rw [h1y, hy]
    field_simp
    ring
  linarith

/-- `H_n - log n - 1/(2n)`, increasing for `n ≥ 1` with limit `γ_E`. -/
noncomputable def emLower (n : ℕ) : ℝ := harmonic n - Real.log n - 1 / (2 * n)

lemma emLower_le_succ {n : ℕ} (hn : 1 ≤ n) : emLower n ≤ emLower (n + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := log_succ_sub_log_le hn'
  unfold emLower
  rw [harmonic_succ]
  push_cast
  have e1 : (1 : ℝ) / (2 * n) = (1 / n) / 2 := by ring
  have e2 : (1 : ℝ) / (2 * (n + 1)) = (1 / (n + 1)) / 2 := by
    field_simp
  rw [inv_eq_one_div, e1, e2]
  linarith

lemma emLower_mono {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : emLower n ≤ emLower m := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact ih.trans (emLower_le_succ (hn.trans hm))

lemma tendsto_emLower :
    Filter.Tendsto emLower Filter.atTop (nhds eulerMascheroniConstant) := by
  have h1 := Real.tendsto_harmonic_sub_log
  have h2 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * n)) Filter.atTop (nhds 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  exact h3

lemma emLower_le_eulerMascheroniConstant {n : ℕ} (hn : 1 ≤ n) :
    emLower n ≤ eulerMascheroniConstant :=
  ge_of_tendsto tendsto_emLower
    (Filter.eventually_atTop.2 ⟨n, fun _ hm => emLower_mono hn hm⟩)

lemma harmonic_sixteen : harmonic 16 = 2436559 / 720720 := by
  simp [harmonic, Finset.sum_range_succ]
  norm_num

lemma eulerMascheroniConstant_ge :
    2436559 / 720720 - 4 * Real.log 2 - 1 / 32 ≤ eulerMascheroniConstant := by
  have h := emLower_le_eulerMascheroniConstant (n := 16) (by norm_num)
  have hH : ((harmonic 16 : ℚ) : ℝ) = 2436559 / 720720 := by
    rw [harmonic_sixteen]
    push_cast
    ring
  have hl : Real.log ((16 : ℕ) : ℝ) = 4 * Real.log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  unfold emLower at h
  rw [hH, hl] at h
  have e : (1 : ℝ) / (2 * ((16 : ℕ) : ℝ)) = 1 / 32 := by norm_num
  rw [e] at h
  exact h

/-! ### Logarithm bounds -/

lemma log_seven_le : Real.log 7 ≤ 3 * Real.log 2 - 13353 / 100000 := by
  have h := log_one_sub_le_series (x := 1 / 8) (by norm_num) (by norm_num) 6
  have hs : -(∑ i ∈ Finset.range 6, (1 / 8 : ℝ) ^ (i + 1) / (i + 1))
      + (1 / 8 : ℝ) ^ (6 + 1) / (1 - 1 / 8) ≤ -13353 / 100000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h7 : Real.log 7 = 3 * Real.log 2 + Real.log (1 - 1 / 8) := by
    rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith

lemma log_pi_ge : 2 * Real.log 2 - 24172 / 100000 ≤ Real.log π := by
  have h := series_le_log_one_sub (x := 2147 / 10000) (by norm_num) (by norm_num) 6
  have hs : -24172 / 100000 ≤ -(∑ i ∈ Finset.range 6, (2147 / 10000 : ℝ) ^ (i + 1) / (i + 1))
      - (2147 / 10000 : ℝ) ^ (6 + 1) / (1 - 2147 / 10000) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hq : Real.log (1 - 2147 / 10000) ≤ Real.log (π / 4) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_d6])
  have hπ : Real.log π = 2 * Real.log 2 + Real.log (π / 4) := by
    rw [Real.log_div pi_ne_zero (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith

lemma log_ratio_ge : 3698 / 10000 ≤ Real.log (207 / 143) := by
  have h := log_one_sub_le_series (x := 64 / 207) (by norm_num) (by norm_num) 8
  have hs : -(∑ i ∈ Finset.range 8, (64 / 207 : ℝ) ^ (i + 1) / (i + 1))
      + (64 / 207 : ℝ) ^ (8 + 1) / (1 - 64 / 207) ≤ -3698 / 10000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have he : Real.log (207 / 143) = -Real.log (1 - 64 / 207) := by
    rw [show (1 : ℝ) - 64 / 207 = (207 / 143)⁻¹ by norm_num, Real.log_inv, neg_neg]
  linarith

lemma log_sqrt_disc :
    Real.log (Real.sqrt (2 ^ 22 * 7 ^ 27)) = 11 * Real.log 2 + 27 / 2 * Real.log 7 := by
  rw [Real.log_sqrt (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  push_cast
  ring

lemma log_120000 : Real.log 120000 = 6 * Real.log 2 + Real.log 3 + 4 * Real.log 5 := by
  rw [show (120000 : ℝ) = 2 ^ 6 * 3 * 5 ^ 4 by norm_num,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Zimmert's `S₂` for the signature `(3, 9)` at `γ = 1/2`, `α = 1/12` is at least
`log √(2^22 7^27) - log 120000`. -/
theorem zimmertS2_half_ge :
    Real.log (Real.sqrt (2 ^ 22 * 7 ^ 27)) - Real.log 120000 ≤ zimmertS2 3 9 (1 / 2) (1 / 12) := by
  rw [zimmertS2_half, log_sqrt_disc, log_120000]
  have h7 := log_seven_le
  have hπ := log_pi_ge
  have hr := log_ratio_ge
  have hγ := eulerMascheroniConstant_ge
  have h2l := Real.log_two_gt_d9
  have h2u := Real.log_two_lt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_gt_d9
  have hpi := Real.pi_lt_d6
  linarith

end FurioLombardo.M2
