import Mathlib
import FurioLombardo.M2.ZimmertNum
import FurioLombardo.M2.Zimmert.Satz1

/-!
# Zimmert's Satz 1 at `γ = 1/2`: the limit `β → 1/2` (lane M2)

`ZData.satz1_half`: if `m ≤ μ_j` for every `j` (and `ιg` is nonempty), then
`(a-b) log Γ(3/2) + log(9α(2-α)/((1-α)(1+α))) - a ψ(3/4) - b ψ(5/4) - 2/(1/2-α) ≤ log(A/m)`.

`satz1_beta` gives `Dfun β ≤ 0` for `α < β < 1/2`, `Dfun (1/2) = 0`, and the left derivative of
`Dfun` at `1/2` is then `≥ 0`; it is the difference of the two sides above.
-/

namespace FurioLombardo.M2.Zimmert

open scoped Topology Filter

theorem Tz_half (a b : ℕ) : Tz a b (1 / 2) = 1 := by
  unfold Tz
  have hpos34 : Real.Gamma (3/4 : ℝ) > 0 := Real.Gamma_pos_of_pos (by norm_num)
  have hpos54 : Real.Gamma (5/4 : ℝ) > 0 := Real.Gamma_pos_of_pos (by norm_num)
  have h34ne : Real.Gamma (3/4 : ℝ) ^ a ≠ 0 := pow_ne_zero _ (by linarith)
  have h54ne : Real.Gamma (5/4 : ℝ) ^ b ≠ 0 := pow_ne_zero _ (by linarith)
  have hdenom : Real.Gamma (3/4 : ℝ) ^ a * Real.Gamma (5/4 : ℝ) ^ b ≠ 0 := mul_ne_zero h34ne h54ne
  field_simp [hdenom]
  norm_num

theorem hasDerivAt_log_Tz (a b : ℕ) :
    HasDerivAt (fun β : ℝ => Real.log (Tz a b β))
      (a * logDerivGamma (3 / 4) + b * logDerivGamma (5 / 4)) (1 / 2) := by
  -- The four Gamma arguments at β = 1/2 are positive
  have hpos34 : 0 < (3/4 : ℝ) := by norm_num
  have hpos54 : 0 < (5/4 : ℝ) := by norm_num
  -- These arguments are not nonpositive integers
  have hne34 : ∀ m : ℕ, (3/4 : ℝ) ≠ -(m : ℝ) := by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hne54 : ∀ m : ℕ, (5/4 : ℝ) ≠ -(m : ℝ) := by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  -- Near 1/2, all Gamma arguments are positive
  have hpos_eventually : ∀ᶠ (β : ℝ) in 𝓝 (1/2 : ℝ),
    0 < (1 + β) / 2 ∧ 0 < 1 + β / 2 ∧ 0 < 1 - β / 2 ∧ 0 < (3 - β) / 2 := by
    have h1 : ContinuousAt (fun (β : ℝ) => (1 + β) / 2) (1/2) :=
      ((continuousAt_const.add continuousAt_id).div_const 2)
    have h2 : ContinuousAt (fun (β : ℝ) => 1 + β / 2) (1/2) :=
      (continuousAt_const.add ((continuousAt_id).div_const 2))
    have h3 : ContinuousAt (fun (β : ℝ) => 1 - β / 2) (1/2) :=
      (continuousAt_const.sub ((continuousAt_id).div_const 2))
    have h4 : ContinuousAt (fun (β : ℝ) => (3 - β) / 2) (1/2) :=
      ((continuousAt_const (x := (1/2 : ℝ)) (y := (3 : ℝ))).sub continuousAt_id).div_const 2
    have hp1 : 0 < ((1 + (1/2 : ℝ)) / 2) := by norm_num
    have hp2 : 0 < (1 + (1/2 : ℝ) / 2) := by norm_num
    have hp3 : 0 < (1 - (1/2 : ℝ) / 2) := by norm_num
    have hp4 : 0 < ((3 - (1/2 : ℝ)) / 2) := by norm_num
    have hpos1 : ∀ᶠ β in 𝓝 (1/2 : ℝ), 0 < (1 + β) / 2 :=
      h1.eventually (lt_mem_nhds hp1)
    have hpos2 : ∀ᶠ β in 𝓝 (1/2 : ℝ), 0 < 1 + β / 2 :=
      h2.eventually (lt_mem_nhds hp2)
    have hpos3 : ∀ᶠ β in 𝓝 (1/2 : ℝ), 0 < 1 - β / 2 :=
      h3.eventually (lt_mem_nhds hp3)
    have hpos4 : ∀ᶠ β in 𝓝 (1/2 : ℝ), 0 < (3 - β) / 2 :=
      h4.eventually (lt_mem_nhds hp4)
    filter_upwards [hpos1, hpos2, hpos3, hpos4] with β h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- Express Real.log (Tz a b β) as a sum of logs near 1/2
  have h_eq : ∀ᶠ (β : ℝ) in 𝓝 (1/2 : ℝ),
    Real.log (Tz a b β) = (a : ℝ) * Real.log (Real.Gamma ((1 + β) / 2)) + (b : ℝ) * Real.log (Real.Gamma (1 + β / 2)) -
    (a : ℝ) * Real.log (Real.Gamma (1 - β / 2)) - (b : ℝ) * Real.log (Real.Gamma ((3 - β) / 2)) := by
    filter_upwards [hpos_eventually] with β ⟨h1, h2, h3, h4⟩
    unfold Tz
    have hG1 : Real.Gamma ((1 + β) / 2) ≠ 0 := (Real.Gamma_pos_of_pos h1).ne'
    have hG2 : Real.Gamma (1 + β / 2) ≠ 0 := (Real.Gamma_pos_of_pos h2).ne'
    have hG3 : Real.Gamma (1 - β / 2) ≠ 0 := (Real.Gamma_pos_of_pos h3).ne'
    have hG4 : Real.Gamma ((3 - β) / 2) ≠ 0 := (Real.Gamma_pos_of_pos h4).ne'
    calc
      Real.log (Real.Gamma ((1 + β) / 2) ^ a * Real.Gamma (1 + β / 2) ^ b /
        (Real.Gamma (1 - β / 2) ^ a * Real.Gamma ((3 - β) / 2) ^ b))
      = Real.log (Real.Gamma ((1 + β) / 2) ^ a * Real.Gamma (1 + β / 2) ^ b) -
        Real.log (Real.Gamma (1 - β / 2) ^ a * Real.Gamma ((3 - β) / 2) ^ b) := by
        rw [Real.log_div (mul_ne_zero (pow_ne_zero a hG1) (pow_ne_zero b hG2))
          (mul_ne_zero (pow_ne_zero a hG3) (pow_ne_zero b hG4))]
      _ = (Real.log (Real.Gamma ((1 + β) / 2) ^ a) + Real.log (Real.Gamma (1 + β / 2) ^ b)) -
        (Real.log (Real.Gamma (1 - β / 2) ^ a) + Real.log (Real.Gamma ((3 - β) / 2) ^ b)) := by
        rw [Real.log_mul (pow_ne_zero a hG1) (pow_ne_zero b hG2),
          Real.log_mul (pow_ne_zero a hG3) (pow_ne_zero b hG4)]
      _ = ((a : ℝ) * Real.log (Real.Gamma ((1 + β) / 2)) + (b : ℝ) * Real.log (Real.Gamma (1 + β / 2))) -
        ((a : ℝ) * Real.log (Real.Gamma (1 - β / 2)) + (b : ℝ) * Real.log (Real.Gamma ((3 - β) / 2))) := by
        simp [Real.log_pow]
      _ = (a : ℝ) * Real.log (Real.Gamma ((1 + β) / 2)) + (b : ℝ) * Real.log (Real.Gamma (1 + β / 2)) -
        (a : ℝ) * Real.log (Real.Gamma (1 - β / 2)) - (b : ℝ) * Real.log (Real.Gamma ((3 - β) / 2)) := by ring
  -- Now compute the derivative of the expanded expression
  have h_deriv : HasDerivAt (fun (β : ℝ) =>
    (a : ℝ) * Real.log (Real.Gamma ((1 + β) / 2)) + (b : ℝ) * Real.log (Real.Gamma (1 + β / 2)) -
    (a : ℝ) * Real.log (Real.Gamma (1 - β / 2)) - (b : ℝ) * Real.log (Real.Gamma ((3 - β) / 2)))
    ((a : ℝ) * logDerivGamma (3 / 4) + (b : ℝ) * logDerivGamma (5 / 4)) (1/2) := by
    -- Inner functions and their derivatives at 1/2
    have hg1 : HasDerivAt (fun (β : ℝ) => (1 + β) / 2) (1/2) (1/2) := by
      have h : HasDerivAt (fun (β : ℝ) => 1 + β) 1 (1/2) :=
        (hasDerivAt_id (1/2)).const_add (1 : ℝ)
      simpa [div_eq_mul_inv] using h.mul_const (1/2 : ℝ)
    have hg2 : HasDerivAt (fun (β : ℝ) => 1 + β / 2) (1/2) (1/2) := by
      have h : HasDerivAt (fun (β : ℝ) => β / 2) (1/2) (1/2) := by
        have := (hasDerivAt_id (1/2)).mul_const (2⁻¹ : ℝ)
        simpa [div_eq_mul_inv] using this
      simpa using h.const_add (1 : ℝ)
    have hg3 : HasDerivAt (fun (β : ℝ) => 1 - β / 2) (-(1/2)) (1/2) := by
      have hβ : HasDerivAt (fun (β : ℝ) => β / 2) (1/2) (1/2) := by
        have := (hasDerivAt_id (1/2)).mul_const (2⁻¹ : ℝ)
        simpa [div_eq_mul_inv] using this
      exact hβ.const_sub 1
    have hg4 : HasDerivAt (fun (β : ℝ) => (3 - β) / 2) (-(1/2)) (1/2) := by
      have h_sub : HasDerivAt (fun (β : ℝ) => (3 - β)) (-1) (1/2) :=
        (hasDerivAt_id' (1/2)).const_sub 3
      simpa [div_eq_mul_inv] using h_sub.mul_const (2⁻¹ : ℝ)
    -- Gamma derivative at the relevant points
    have hGam34 : HasDerivAt Real.Gamma (deriv Real.Gamma (3/4)) (3/4) :=
      (Real.differentiableAt_Gamma hne34).hasDerivAt
    have hGam54 : HasDerivAt Real.Gamma (deriv Real.Gamma (5/4)) (5/4) :=
      (Real.differentiableAt_Gamma hne54).hasDerivAt
    -- Gamma is positive at these points, hence nonzero
    have hGpos34 : Real.Gamma (3/4) ≠ 0 := (Real.Gamma_pos_of_pos hpos34).ne'
    have hGpos54 : Real.Gamma (5/4) ≠ 0 := (Real.Gamma_pos_of_pos hpos54).ne'
    -- Derivative of log ∘ Gamma at the relevant points
    have hlogGam34 : HasDerivAt (fun (x : ℝ) => Real.log (Real.Gamma x))
      (logDerivGamma (3/4)) (3/4) := by
      have := hGam34.log hGpos34
      simpa [logDerivGamma] using this
    have hlogGam54 : HasDerivAt (fun (x : ℝ) => Real.log (Real.Gamma x))
      (logDerivGamma (5/4)) (5/4) := by
      have := hGam54.log hGpos54
      simpa [logDerivGamma] using this
    -- Chain rule for each term
    have h1 : HasDerivAt (fun (β : ℝ) => Real.log (Real.Gamma ((1 + β) / 2)))
      (logDerivGamma (3/4) * (1/2)) (1/2) := by
      have hlog34_at_g1 : HasDerivAt (fun (x : ℝ) => Real.log (Real.Gamma x))
        (logDerivGamma (3/4)) ((1 + (1/2 : ℝ)) / 2) := by
        rw [show ((1 + (1/2 : ℝ)) / 2) = (3/4 : ℝ) by ring]
        exact hlogGam34
      apply HasDerivAt.comp (1/2) hlog34_at_g1 hg1
    have h2 : HasDerivAt (fun (β : ℝ) => Real.log (Real.Gamma (1 + β / 2)))
      (logDerivGamma (5/4) * (1/2)) (1/2) := by
      have hlog54_at_g2 : HasDerivAt (fun (x : ℝ) => Real.log (Real.Gamma x))
        (logDerivGamma (5/4)) (1 + (1/2 : ℝ) / 2) := by
        rw [show (1 + (1/2 : ℝ) / 2) = (5/4 : ℝ) by ring]
        exact hlogGam54
      apply HasDerivAt.comp (1/2) hlog54_at_g2 hg2
    have h3 : HasDerivAt (fun (β : ℝ) => Real.log (Real.Gamma (1 - β / 2)))
      (logDerivGamma (3/4) * (-(1/2))) (1/2) := by
      have hlog34_at_g3 : HasDerivAt (fun (x : ℝ) => Real.log (Real.Gamma x))
        (logDerivGamma (3/4)) (1 - (1/2 : ℝ) / 2) := by
        rw [show (1 - (1/2 : ℝ) / 2) = (3/4 : ℝ) by ring]
        exact hlogGam34
      apply HasDerivAt.comp (1/2) hlog34_at_g3 hg3
    have h4 : HasDerivAt (fun (β : ℝ) => Real.log (Real.Gamma ((3 - β) / 2)))
      (logDerivGamma (5/4) * (-(1/2))) (1/2) := by
      have hlog54_at_g4 : HasDerivAt (fun (x : ℝ) => Real.log (Real.Gamma x))
        (logDerivGamma (5/4)) ((3 - (1/2 : ℝ)) / 2) := by
        rw [show ((3 - (1/2 : ℝ)) / 2) = (5/4 : ℝ) by ring]
        exact hlogGam54
      apply HasDerivAt.comp (1/2) hlog54_at_g4 hg4
    -- Multiply by a, b and combine with addition/subtraction
    have ha1 : HasDerivAt (fun (β : ℝ) => (a : ℝ) * Real.log (Real.Gamma ((1 + β) / 2)))
      ((a : ℝ) * (logDerivGamma (3/4) * (1/2))) (1/2) :=
      HasDerivAt.const_mul (a : ℝ) h1
    have hb1 : HasDerivAt (fun (β : ℝ) => (b : ℝ) * Real.log (Real.Gamma (1 + β / 2)))
      ((b : ℝ) * (logDerivGamma (5/4) * (1/2))) (1/2) :=
      HasDerivAt.const_mul (b : ℝ) h2
    have ha2 : HasDerivAt (fun (β : ℝ) => (a : ℝ) * Real.log (Real.Gamma (1 - β / 2)))
      ((a : ℝ) * (logDerivGamma (3/4) * (-(1/2)))) (1/2) :=
      HasDerivAt.const_mul (a : ℝ) h3
    have hb2 : HasDerivAt (fun (β : ℝ) => (b : ℝ) * Real.log (Real.Gamma ((3 - β) / 2)))
      ((b : ℝ) * (logDerivGamma (5/4) * (-(1/2)))) (1/2) :=
      HasDerivAt.const_mul (b : ℝ) h4
    -- Combine: ha1 + hb1 - ha2 - hb2
    have hsum12 : HasDerivAt (fun (β : ℝ) =>
      (a : ℝ) * Real.log (Real.Gamma ((1 + β) / 2)) + (b : ℝ) * Real.log (Real.Gamma (1 + β / 2)))
      ((a : ℝ) * (logDerivGamma (3/4) * (1/2)) + (b : ℝ) * (logDerivGamma (5/4) * (1/2))) (1/2) :=
      HasDerivAt.add ha1 hb1
    have hsum2 : HasDerivAt (fun (β : ℝ) =>
      (a : ℝ) * Real.log (Real.Gamma (1 - β / 2)) + (b : ℝ) * Real.log (Real.Gamma ((3 - β) / 2)))
      ((a : ℝ) * (logDerivGamma (3/4) * (-(1/2))) + (b : ℝ) * (logDerivGamma (5/4) * (-(1/2)))) (1/2) :=
      HasDerivAt.add ha2 hb2
    have htotal : HasDerivAt (fun (β : ℝ) =>
      ((a : ℝ) * Real.log (Real.Gamma ((1 + β) / 2)) + (b : ℝ) * Real.log (Real.Gamma (1 + β / 2))) -
      ((a : ℝ) * Real.log (Real.Gamma (1 - β / 2)) + (b : ℝ) * Real.log (Real.Gamma ((3 - β) / 2))))
      (((a : ℝ) * (logDerivGamma (3/4) * (1/2)) + (b : ℝ) * (logDerivGamma (5/4) * (1/2))) -
       ((a : ℝ) * (logDerivGamma (3/4) * (-(1/2))) + (b : ℝ) * (logDerivGamma (5/4) * (-(1/2))))) (1/2) :=
      HasDerivAt.sub hsum12 hsum2
    -- Now simplify the derivative expression to the target
    have h' := htotal.congr_deriv (show _ = (a : ℝ) * logDerivGamma (3 / 4) + (b : ℝ) * logDerivGamma (5 / 4) by ring)
    convert h' using 1
    funext β
    ring
  -- Transfer using congr_of_eventuallyEq
  exact h_deriv.congr_of_eventuallyEq h_eq

theorem nonneg_of_le_zero_left {f : ℝ → ℝ} {c d α : ℝ} (hα : α < c)
    (hf : HasDerivWithinAt f d (Set.Iio c) c) (hc : f c = 0)
    (hle : ∀ β, α < β → β < c → f β ≤ 0) : 0 ≤ d := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.mp hf
  rw [Set.sdiff_singleton_eq_self (by simp : c ∉ Set.Iio c)] at ht
  have hev : ∀ᶠ β in 𝓝[<] c, 0 ≤ slope f c β := by
    filter_upwards [Ioo_mem_nhdsLT hα] with β hβ
    rw [slope_def_field, hc, sub_zero]
    exact div_nonneg_of_nonpos (hle β hβ.1 hβ.2) (by linarith [hβ.2])
  exact ge_of_tendsto ht hev

/-- The duplication formula `ψ(3/4) + ψ(5/4) = 2 ψ(3/2) - 2 log 2`. -/
theorem logDerivGamma_dup :
    logDerivGamma (3 / 4) + logDerivGamma (5 / 4) = 2 * logDerivGamma (3 / 2) - 2 * Real.log 2 := by
  rw [logDerivGamma_eq_re_digamma (by norm_num), logDerivGamma_eq_re_digamma (by norm_num),
    logDerivGamma_eq_re_digamma (by norm_num)]
  have hm : ∀ m : ℕ, 2 * (3 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    norm_num at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have e := Complex.digamma_two_mul hm
  have hlog2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  rw [show 2 * (3 / 4 : ℂ) = 3 / 2 by norm_num, show (3 / 4 : ℂ) + 1 / 2 = 5 / 4 by norm_num,
    hlog2] at e
  have e' := congrArg Complex.re e
  simp only [Complex.add_re, Complex.ofReal_re] at e'
  rw [show (((3 / 4 : ℝ)) : ℂ) = 3 / 4 by push_cast; ring,
    show (((5 / 4 : ℝ)) : ℂ) = 5 / 4 by push_cast; ring,
    show (((3 / 2 : ℝ)) : ℂ) = 3 / 2 by push_cast; ring]
  have hre : ((1 / 2 : ℂ) * (Complex.digamma (3 / 4) + Complex.digamma (5 / 4))).re
      = (1 / 2) * ((Complex.digamma (3 / 4)).re + (Complex.digamma (5 / 4)).re) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      Complex.add_re]
  rw [hre] at e'
  linarith

/-- Conversion of the limit bound to Zimmert's `S₂` at `γ = 1/2` (with `a = r₁ + r₂`, `b = r₂`,
`A = √d π^{-n/2}`, `n = r₁ + 2 r₂`). -/
theorem satz2_of_bound (r₁ r₂ : ℕ) {α dd m : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2) (hd : 0 < dd)
    (hm : 0 < m)
    (h : (((r₁ + r₂ : ℕ) : ℝ) - (r₂ : ℝ)) * Real.log (Real.Gamma (3 / 2))
        + Real.log (9 * α * (2 - α) / ((1 - α) * (1 + α)))
        - ((r₁ + r₂ : ℕ) : ℝ) * logDerivGamma (3 / 4) - (r₂ : ℝ) * logDerivGamma (5 / 4)
        - 2 / (1 / 2 - α)
      ≤ Real.log (Real.sqrt dd * Real.pi ^ (-((r₁ + 2 * r₂ : ℕ) : ℝ) / 2) / m)) :
    zimmertS2 r₁ r₂ (1 / 2) α ≤ Real.log (Real.sqrt dd / m) := by
  have h1a : 1 - α ≠ 0 := by linarith
  have h2a : 2 - α ≠ 0 := by linarith
  have hpa : 1 + α ≠ 0 := by linarith
  have ha0 : α ≠ 0 := hα.ne'
  have harg : (1 + α⁻¹) * ((1 + (1 / 2 : ℝ)⁻¹) ^ 2)⁻¹ * (1 + (2 * (1 / 2) - α)⁻¹)⁻¹
      = (9 * α * (2 - α) / ((1 - α) * (1 + α)))⁻¹ := by
    have e1 : (1 + (1 / 2 : ℝ)⁻¹) ^ 2 = 9 := by norm_num
    have e2 : (1 : ℝ) + (2 * (1 / 2) - α)⁻¹ = (2 - α) / (1 - α) := by
      rw [show (2 : ℝ) * (1 / 2) - α = 1 - α by ring]
      field_simp
      ring
    have e3 : (1 : ℝ) + α⁻¹ = (1 + α) / α := by
      field_simp; ring
    rw [e1, e2, e3, inv_div, inv_div]
    field_simp
  have hS : zimmertS2 r₁ r₂ (1 / 2) α
      = r₁ * (-logDerivGamma (3 / 4) + Real.log (Real.Gamma (3 / 2)) + Real.log Real.pi / 2)
        + r₂ * (-2 * logDerivGamma (3 / 2) + 2 * Real.log 2 + Real.log Real.pi)
        - 2 / (1 / 2 - α) + Real.log (9 * α * (2 - α) / ((1 - α) * (1 + α))) := by
    unfold zimmertS2
    rw [show ((1 : ℝ) + 1 / 2) / 2 = 3 / 4 by norm_num, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, Real.Gamma_one, Real.log_one, harg, Real.log_inv]
    ring
  have hlog : Real.log (Real.sqrt dd * Real.pi ^ (-((r₁ + 2 * r₂ : ℕ) : ℝ) / 2) / m)
      = Real.log (Real.sqrt dd / m) - (((r₁ + 2 * r₂ : ℕ) : ℝ) / 2) * Real.log Real.pi := by
    have hs : 0 < Real.sqrt dd / m := div_pos (Real.sqrt_pos.mpr hd) hm
    have hp : 0 < Real.pi ^ (-((r₁ + 2 * r₂ : ℕ) : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    rw [show Real.sqrt dd * Real.pi ^ (-((r₁ + 2 * r₂ : ℕ) : ℝ) / 2) / m
        = Real.sqrt dd / m * Real.pi ^ (-((r₁ + 2 * r₂ : ℕ) : ℝ) / 2) by ring,
      Real.log_mul hs.ne' hp.ne', Real.log_rpow Real.pi_pos]
    ring
  have hdup := logDerivGamma_dup
  have key : zimmertS2 r₁ r₂ (1 / 2) α
      = ((((r₁ + r₂ : ℕ) : ℝ) - (r₂ : ℝ)) * Real.log (Real.Gamma (3 / 2))
        + Real.log (9 * α * (2 - α) / ((1 - α) * (1 + α)))
        - ((r₁ + r₂ : ℕ) : ℝ) * logDerivGamma (3 / 4) - (r₂ : ℝ) * logDerivGamma (5 / 4)
        - 2 / (1 / 2 - α)) + (((r₁ + 2 * r₂ : ℕ) : ℝ) / 2) * Real.log Real.pi := by
    rw [hS]
    push_cast
    linear_combination (r₂ : ℝ) * hdup
  rw [key]
  linarith

/-- The function whose left derivative at `1/2` gives Satz 1 at `γ = 1/2`. -/
noncomputable def Dfun (a b : ℕ) (A α m β : ℝ) : ℝ :=
  (1 / 2 - β) * Real.log (xz a b A α β) + (2 * β - 1) * Real.log A + Real.log (β - α)
    - Real.log (1 - α - β) + Real.log (Tz a b β) + (1 / 2 - β) * Real.log m

theorem Dfun_half (a b : ℕ) (A α m : ℝ) : Dfun a b A α m (1 / 2) = 0 := by
  unfold Dfun
  rw [Tz_half, Real.log_one, show (1 : ℝ) - α - 1 / 2 = 1 / 2 - α by ring]
  ring

namespace ZData

variable {a b : ℕ} {ιf ιg : Type*} (D : ZData a b ιf ιg)

theorem Dfun_nonpos [Nonempty ιg] (ha : 1 ≤ a) {α m β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1 / 2) (hm : 0 < m) (hmμ : ∀ j, m ≤ D.μ j) : Dfun a b D.A α m β ≤ 0 := by
  have h1 := D.satz1_beta ha hα hαβ hβ
  have hβ0 : 0 < β := lt_trans hα hαβ
  have hx : 0 < xz a b D.A α β := xz_pos a b D.hA hα hβ0 (by linarith) (by linarith)
  set x := xz a b D.A α β with hxdef
  have hD32 : 0 < dserR D.μ (3 / 2) := dserR_pos D.μ D.hμ (D.hμs _ (by norm_num))
  have hge : m ^ (1 / 2 - β) * dserR D.μ (3 / 2) ≤ dserR D.μ (1 + β) :=
    dserR_ge D.μ hm hmμ hβ (D.hμs _ (by norm_num)) (D.hμs _ (by linarith))
  have hT : 0 < Tz a b β := Tz_pos a b hβ0.le (by linarith)
  have p1 : 0 < x ^ (-β) := Real.rpow_pos_of_pos hx _
  have p2 : 0 < D.A ^ (1 + 2 * β) := Real.rpow_pos_of_pos D.hA _
  have p3 : 0 < β - α := by linarith
  have p4 : 0 < m ^ (1 / 2 - β) := Real.rpow_pos_of_pos hm _
  have p5 : 0 < 1 - α - β := by linarith
  have p6 : 0 < x ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hx _
  have p7 : 0 < D.A ^ (2 : ℝ) := Real.rpow_pos_of_pos D.hA _
  have hcoef : 0 ≤ x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β / (1 - α - β) := by
    positivity
  have hL : x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β * m ^ (1 / 2 - β) / (1 - α - β)
      * dserR D.μ (3 / 2) ≤ x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * dserR D.μ (3 / 2) := by
    calc x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β * m ^ (1 / 2 - β) / (1 - α - β)
          * dserR D.μ (3 / 2)
        = x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β / (1 - α - β)
          * (m ^ (1 / 2 - β) * dserR D.μ (3 / 2)) := by ring
      _ ≤ x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β / (1 - α - β)
          * dserR D.μ (1 + β) := mul_le_mul_of_nonneg_left hge hcoef
      _ = x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β * dserR D.μ (1 + β)
          / (1 - α - β) := by ring
      _ ≤ _ := h1
  have hL2 := le_of_mul_le_mul_right hL hD32
  have hLpos : 0 < x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β * m ^ (1 / 2 - β)
      / (1 - α - β) := by positivity
  have hlog := Real.log_le_log hLpos hL2
  have q2 : 0 < x ^ (-β) * D.A ^ (1 + 2 * β) := mul_pos p1 p2
  have q3 : 0 < x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) := mul_pos q2 p3
  have q4 : 0 < x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β := mul_pos q3 hT
  have q5 : 0 < x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β * m ^ (1 / 2 - β) :=
    mul_pos q4 p4
  rw [Real.log_div q5.ne' p5.ne', Real.log_mul q4.ne' p4.ne', Real.log_mul q3.ne' hT.ne',
    Real.log_mul q2.ne' p3.ne', Real.log_mul p1.ne' p2.ne', Real.log_rpow hx, Real.log_rpow D.hA,
    Real.log_rpow hm, Real.log_mul p6.ne' p7.ne', Real.log_rpow hx, Real.log_rpow D.hA] at hlog
  unfold Dfun
  nlinarith [hlog]

/-- **Zimmert's Satz 1 at `γ = 1/2`, limit `β → 1/2`.** -/
theorem satz1_half [Nonempty ιg] (ha : 1 ≤ a) {α m : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2)
    (hm : 0 < m) (hmμ : ∀ j, m ≤ D.μ j) :
    ((a : ℝ) - (b : ℝ)) * Real.log (Real.Gamma (3 / 2))
        + Real.log (9 * α * (2 - α) / ((1 - α) * (1 + α)))
        - (a : ℝ) * logDerivGamma (3 / 4) - (b : ℝ) * logDerivGamma (5 / 4) - 2 / (1 / 2 - α)
      ≤ Real.log (D.A / m) := by
  have h1a : 0 < 1 - α := by linarith
  have hpa : 0 < 1 + α := by linarith
  have hden : (1 / 2 : ℝ) * (1 - 1 / 2) * (1 - α) * (1 + α) ≠ 0 := by positivity
  have hxd : DifferentiableAt ℝ (fun β => xz a b D.A α β) (1 / 2) := by
    unfold xz
    fun_prop (disch := exact hden)
  have hG : 0 < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hF : α * (1 + 1 / 2) * (2 - 1 / 2) * (2 - α) / ((1 / 2) * (1 - 1 / 2) * (1 - α) * (1 + α))
      = 9 * α * (2 - α) / ((1 - α) * (1 + α)) := by
    field_simp
    ring
  have hFpos : 0 < 9 * α * (2 - α) / ((1 - α) * (1 + α)) := by
    have : 0 < 2 - α := by linarith
    positivity
  have hx12 : xz a b D.A α (1 / 2) = D.A * (9 * α * (2 - α) / ((1 - α) * (1 + α)))
      * (Real.Gamma (3 / 2) ^ a / Real.Gamma (3 / 2) ^ b) := by
    unfold xz
    rw [mul_div_assoc, hF]
  have hGr : 0 < Real.Gamma (3 / 2) ^ a / Real.Gamma (3 / 2) ^ b := div_pos (pow_pos hG a) (pow_pos hG b)
  have hx12pos : 0 < xz a b D.A α (1 / 2) := by
    rw [hx12]
    exact mul_pos (mul_pos D.hA hFpos) hGr
  have hlogx : Real.log (xz a b D.A α (1 / 2)) = Real.log D.A
      + Real.log (9 * α * (2 - α) / ((1 - α) * (1 + α)))
      + ((a : ℝ) * Real.log (Real.Gamma (3 / 2)) - (b : ℝ) * Real.log (Real.Gamma (3 / 2))) := by
    rw [hx12, Real.log_mul (mul_pos D.hA hFpos).ne' hGr.ne',
      Real.log_mul D.hA.ne' hFpos.ne',
      Real.log_div (x := Real.Gamma (3 / 2) ^ a) (pow_pos hG a).ne' (pow_pos hG b).ne',
      Real.log_pow, Real.log_pow]
  -- derivative of `Dfun` at `1/2`
  have t1 := ((hasDerivAt_id' (1 / 2 : ℝ)).const_sub (1 / 2)).mul
    (hxd.hasDerivAt.log hx12pos.ne')
  have t2 := (((hasDerivAt_id' (1 / 2 : ℝ)).const_mul 2).sub_const 1).mul_const (Real.log D.A)
  have t3 := ((hasDerivAt_id' (1 / 2 : ℝ)).sub_const α).log (by linarith : (1 / 2 : ℝ) - α ≠ 0)
  have t4 := ((hasDerivAt_id' (1 / 2 : ℝ)).const_sub (1 - α)).log
    (by linarith : (1 - α) - (1 / 2 : ℝ) ≠ 0)
  have t5 := hasDerivAt_log_Tz a b
  have t6 := ((hasDerivAt_id' (1 / 2 : ℝ)).const_sub (1 / 2)).mul_const (Real.log m)
  have hD : HasDerivAt (Dfun a b D.A α m) _ (1 / 2) := ((((t1.add t2).add t3).sub t4).add t5).add t6
  have h0 := nonneg_of_le_zero_left hα2 hD.hasDerivWithinAt (Dfun_half a b D.A α m)
    (fun β h1 h2 => D.Dfun_nonpos ha hα h1 h2 hm hmμ)
  rw [hlogx] at h0
  rw [Real.log_div D.hA.ne' hm.ne']
  have e : (1 - α - 1 / 2 : ℝ) = 1 / 2 - α := by ring
  simp only [sub_self, zero_mul, add_zero, e] at h0
  have e2 : (2 : ℝ) / (1 / 2 - α) = 1 / (1 / 2 - α) + 1 / (1 / 2 - α) := by ring
  rw [e2]
  rw [neg_div] at h0
  linarith [h0]

end ZData

end FurioLombardo.M2.Zimmert
