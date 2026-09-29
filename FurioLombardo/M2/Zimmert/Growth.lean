import Mathlib
import FurioLombardo.M2.Zimmert.Defs
import FurioLombardo.Vendor.AINTLIB.CompletedZeta.GammaStrip

/-!
# Growth bounds for Zimmert's Satz 1 at `γ = 1/2` (lane M2)

* `norm_inv_Gamma_le`: `‖1/Γ(z)‖ ≤ √(12π)/π · (3/2 + |Im z|) · exp(π |Im z| / 2)` for
  `1/2 ≤ Re z ≤ 5/2` and `|Im z| ≥ 1`, from the lower bound `le_norm_Gamma_base_add_nat` of
  AINTLIB (no Stirling formula);
* `norm_iG1_le`: the resulting exponential bound for `iG1 a b s = 1/G₁(s)` on the strip
  `-1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2`;
* `norm_le_of_strip`: Phragmén-Lindelöf on a vertical strip of width `< π` for a function of
  at most exponential growth (wrapper of Mathlib `PhragmenLindelof.vertical_strip`).
-/

namespace FurioLombardo.M2.Zimmert

open Complex Filter Set

/-- `‖1/Γ(z)‖ ≤ √(12π)/π · (3/2 + |Im z|) · exp(π |Im z| / 2)` on `1/2 ≤ Re z ≤ 5/2`,
`|Im z| ≥ 1`. -/
theorem norm_inv_Gamma_le {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 5 / 2) (ht : 1 ≤ |z.im|) :
    ‖(Gamma z)⁻¹‖ ≤ Real.sqrt (12 * Real.pi) / Real.pi * (3 / 2 + |z.im|)
      * Real.exp (Real.pi * |z.im| / 2) := by
  obtain ⟨σ, n, hσ1, hσ2, hz⟩ : ∃ σ : ℝ, ∃ n : ℕ, 1 / 2 ≤ σ ∧ σ ≤ 3 / 2 ∧
      z = ((σ + n : ℝ) : ℂ) + (z.im : ℂ) * I := by
    rcases le_or_gt z.re (3 / 2) with h | h
    · refine ⟨z.re, 0, h1, h, ?_⟩
      simp [Complex.re_add_im]
    · refine ⟨z.re - 1, 1, by linarith, by linarith, ?_⟩
      simp [Complex.re_add_im]
  set t := z.im with ht_def
  have hL := FurioLombardo.Vendor.AINTLIB.DedekindResidue.le_norm_Gamma_base_add_nat hσ1 hσ2 ht n
  rw [← hz] at hL
  set N : ℝ := ‖((2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I‖ with hN
  have hN1 : |t| ≤ N := by
    have h0 := Complex.abs_im_le_norm (((2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)
    have him : (((2 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I).im = -t := by simp
    rw [him, abs_neg] at h0
    exact h0
  have hNpos : 0 < N := lt_of_lt_of_le (by linarith) hN1
  have hN2 : N ≤ 3 / 2 + |t| := by
    calc N ≤ ‖((2 - σ : ℝ) : ℂ)‖ + ‖((-t : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |2 - σ| + |t| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
      _ ≤ 3 / 2 + |t| := by
          have : |2 - σ| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith
  have hS : 0 < Real.sqrt (12 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hpos : 0 < Real.pi / (Real.sqrt (12 * Real.pi) * N) * Real.exp (-(Real.pi * |t|) / 2) := by
    positivity
  rw [norm_inv]
  calc ‖Gamma z‖⁻¹
      ≤ (Real.pi / (Real.sqrt (12 * Real.pi) * N) * Real.exp (-(Real.pi * |t|) / 2))⁻¹ :=
        inv_anti₀ hpos hL
    _ = Real.sqrt (12 * Real.pi) / Real.pi * N * Real.exp (Real.pi * |t| / 2) := by
        rw [neg_div, Real.exp_neg]
        field_simp
    _ ≤ Real.sqrt (12 * Real.pi) / Real.pi * (3 / 2 + |t|) * Real.exp (Real.pi * |t| / 2) := by
        gcongr

/-- The constant `c₀ = 3 √(12π) / (2π)` of `norm_iG1_le`. -/
noncomputable def cG : ℝ := 3 * Real.sqrt (12 * Real.pi) / (2 * Real.pi)

/-- The rate `k₀ = (2 + π)/4` of `norm_iG1_le`. -/
noncomputable def kG : ℝ := (2 + Real.pi) / 4

theorem cG_pos : 0 < cG := by
  unfold cG
  have : 0 < Real.sqrt (12 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- One Gamma factor: `‖1/Γ(z)‖ ≤ c₀ exp(k₀ |Im s|)` when `Im z = Im s / 2`. -/
theorem norm_inv_Gamma_le_half {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 5 / 2) (y : ℝ)
    (hy : z.im = y / 2) (ht : 2 ≤ |y|) :
    ‖(Gamma z)⁻¹‖ ≤ cG * Real.exp (kG * |y|) := by
  have hu : |z.im| = |y| / 2 := by rw [hy, abs_div, abs_two]
  have h := norm_inv_Gamma_le h1 h2 (by rw [hu]; linarith)
  rw [hu] at h
  refine le_trans h ?_
  set u := |y| / 2 with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hexp : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have hsplit : Real.exp (kG * |y|) = Real.exp u * Real.exp (Real.pi * u / 2) := by
    rw [← Real.exp_add]
    congr 1
    unfold kG
    rw [hu_def]
    ring
  rw [hsplit]
  have hS : 0 < Real.sqrt (12 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hE : 0 < Real.exp (Real.pi * u / 2) := Real.exp_pos _
  have hkey : 3 / 2 + u ≤ 3 / 2 * Real.exp u := by nlinarith
  calc Real.sqrt (12 * Real.pi) / Real.pi * (3 / 2 + u) * Real.exp (Real.pi * u / 2)
      ≤ Real.sqrt (12 * Real.pi) / Real.pi * (3 / 2 * Real.exp u) * Real.exp (Real.pi * u / 2) := by
        gcongr
    _ = cG * (Real.exp u * Real.exp (Real.pi * u / 2)) := by
        unfold cG
        field_simp

/-- `‖1/G₁(s)‖ ≤ (c₀ exp(k₀ |Im s|))^(a+b)` on `-1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2`. -/
theorem norm_iG1_le (a b : ℕ) {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖iG1 a b s‖ ≤ (cG * Real.exp (kG * |s.im|)) ^ (a + b) := by
  have hA : ‖(Gamma (s / 2 + 1))⁻¹‖ ≤ cG * Real.exp (kG * |s.im|) := by
    refine norm_inv_Gamma_le_half ?_ ?_ s.im ?_ ht
    · simp; linarith
    · simp; linarith
    · simp
  have hB : ‖(Gamma ((s + 3) / 2))⁻¹‖ ≤ cG * Real.exp (kG * |s.im|) := by
    refine norm_inv_Gamma_le_half ?_ ?_ s.im ?_ ht
    · simp; linarith
    · simp; linarith
    · simp
  unfold iG1
  rw [norm_mul, norm_pow, norm_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA a)
    (pow_le_pow_left₀ (norm_nonneg _) hB b) (pow_nonneg (norm_nonneg _) _)
    (pow_nonneg (le_trans (norm_nonneg _) hA) _)

/-- Phragmén-Lindelöf on a closed vertical strip of width `< π`: a function holomorphic near
the strip, of at most exponential growth `K exp(k |Im s|)` for `|Im s| ≥ T₁` inside, and bounded
by `C` on both edges, is bounded by `C` on the strip. -/
theorem norm_le_of_strip {σL σR : ℝ} (hLR : σL < σR) (hw : σR - σL < Real.pi) {U : Set ℂ}
    (hstrip : ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR → s ∈ U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {K k T₁ : ℝ}
    (hgrowth : ∀ s : ℂ, σL < s.re → s.re < σR → T₁ ≤ |s.im| → ‖F s‖ ≤ K * Real.exp (k * |s.im|))
    {C : ℝ} (hCL : ∀ s : ℂ, s.re = σL → ‖F s‖ ≤ C) (hCR : ∀ s : ℂ, s.re = σR → ‖F s‖ ≤ C)
    {s : ℂ} (h1 : σL ≤ s.re) (h2 : s.re ≤ σR) : ‖F s‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip ?_ ?_ hCL hCR h1 h2
  · refine DifferentiableOn.diffContOnCl (hF.mono ?_)
    have hcl : closure (re ⁻¹' Ioo σL σR) ⊆ re ⁻¹' Icc σL σR :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
    intro z hz
    have := hcl hz
    exact hstrip z this.1 this.2
  · refine ⟨1, ?_, max k 0, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]
      linarith
    refine Asymptotics.IsBigO.of_bound (max K 0) ?_
    rw [Filter.eventually_inf_principal]
    have hev : ∀ᶠ z : ℂ in comap (_root_.abs ∘ im) atTop, T₁ ≤ (_root_.abs ∘ im) z :=
      tendsto_comap.eventually (eventually_ge_atTop T₁)
    filter_upwards [hev] with z hz hzS
    have hb := hgrowth z hzS.1 hzS.2 hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have ht0 : 0 ≤ |z.im| := abs_nonneg _
    have hexp : |z.im| ≤ Real.exp (1 * |z.im|) := by
      rw [one_mul]
      linarith [Real.add_one_le_exp |z.im|]
    calc ‖F z‖ ≤ K * Real.exp (k * |z.im|) := hb
      _ ≤ max K 0 * Real.exp (max k 0 * |z.im|) := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_left _ _
      _ ≤ max K 0 * Real.exp (max k 0 * Real.exp (1 * |z.im|)) := by
          gcongr

end FurioLombardo.M2.Zimmert
