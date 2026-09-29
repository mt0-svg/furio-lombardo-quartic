import Mathlib
import FurioLombardo.M2.Zimmert.Defs

/-!
# Elementary lemmas for Zimmert's Satz 1 at `γ = 1/2` (lane M2)

Algebraic identities and norm estimates for `Rz`, `rz`, `Gz`, `iG1`, `dser`, `xz`, `Tz`.
-/

namespace FurioLombardo.M2.Zimmert

open Complex

/-! ### Gamma factors -/

/-- `G(s)/G₁(s) = (2/s)^a (2/(s+1))^b` for `Re s > 0`. -/
theorem Gz_mul_iG1 (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Gz a b s * iG1 a b s = (2 / s) ^ a * (2 / (s + 1)) ^ b := by
  unfold Gz iG1
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre : (s + 1).re = s.re + 1 := by simp
    rw [h] at hre
    simp at hre
    linarith
  have hr1 : 0 < (s / 2).re := by simp; linarith
  have hr2 : 0 < ((s + 1) / 2).re := by simp; linarith
  have hG1 : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hr1
  have hG2 : Gamma ((s + 1) / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hr2
  have hA : Gamma (s / 2 + 1) = s / 2 * Gamma (s / 2) :=
    Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  have hB : Gamma ((s + 3) / 2) = (s + 1) / 2 * Gamma ((s + 1) / 2) := by
    rw [show (s + 3) / 2 = (s + 1) / 2 + 1 by ring]
    exact Gamma_add_one _ (div_ne_zero hs1 two_ne_zero)
  rw [hA, hB]
  have e1 : Gamma (s / 2) * (s / 2 * Gamma (s / 2))⁻¹ = 2 / s := by
    field_simp
  have e2 : Gamma ((s + 1) / 2) * ((s + 1) / 2 * Gamma ((s + 1) / 2))⁻¹ = 2 / (s + 1) := by
    field_simp
  rw [← e1, ← e2, mul_pow, mul_pow]
  ring

/-- `Gz` at a real point. -/
theorem Gz_ofReal (a b : ℕ) (x : ℝ) :
    Gz a b (x : ℂ) = ((Real.Gamma (x / 2) ^ a * Real.Gamma ((x + 1) / 2) ^ b : ℝ) : ℂ) := by
  unfold Gz
  have h1 : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : ((x : ℂ) + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp

/-- `iG1` at a real point. -/
theorem iG1_ofReal (a b : ℕ) (x : ℝ) :
    iG1 a b (x : ℂ) =
      (((Real.Gamma (x / 2 + 1))⁻¹ ^ a * (Real.Gamma ((x + 3) / 2))⁻¹ ^ b : ℝ) : ℂ) := by
  unfold iG1
  have h1 : (x : ℂ) / 2 + 1 = ((x / 2 + 1 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : ((x : ℂ) + 3) / 2 = (((x + 3) / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp

theorem differentiable_iG1 (a b : ℕ) : Differentiable ℂ (iG1 a b) := by
  unfold iG1
  have h := differentiable_one_div_Gamma
  have h1 : Differentiable ℂ fun s : ℂ => (Gamma (s / 2 + 1))⁻¹ :=
    h.comp ((differentiable_id.div_const 2).add_const 1)
  have h2 : Differentiable ℂ fun s : ℂ => (Gamma ((s + 3) / 2))⁻¹ :=
    h.comp ((differentiable_id.add_const 3).div_const 2)
  exact (h1.pow a).mul (h2.pow b)

/-! ### The rational function `Rz` -/

/-- `Rz = rz / (s + β)` (no hypothesis: division by zero is zero). -/
theorem Rz_eq_rz_div (α β : ℝ) (s : ℂ) : Rz α β s = rz α β s / (s + β) := by
  unfold Rz rz
  rw [div_div]
  ring_nf

/-- `|s+3| / |s(s-1)(s+β)| ≤ 2/t^2` on the strip for `|t| ≥ 5`. -/
theorem norm_div_cubic_le {β : ℝ} (hβ : 0 ≤ β) {s : ℂ} (hre1 : -1 / 2 ≤ s.re) (hre2 : s.re ≤ 2)
    (him : 5 ≤ |s.im|) :
    ‖s + 3‖ / ‖s * (s - 1) * (s + β)‖ ≤ 2 / s.im ^ 2 := by
  have h_re_bound : |s.re + 3| ≤ 5 := by
    have h_low : -5 ≤ s.re + 3 := by linarith
    have h_high : s.re + 3 ≤ 5 := by linarith
    exact abs_le.mpr ⟨h_low, h_high⟩
  have h_num : ‖s + 3‖ ≤ 2 * |s.im| := by
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re + 3| + |s.im| := by simp
      _ ≤ 5 + |s.im| := by linarith
      _ ≤ |s.im| + |s.im| := by linarith
      _ = 2 * |s.im| := by ring
  have h_den : |s.im| ^ 3 ≤ ‖s * (s - 1) * (s + β)‖ := by
    have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have h2 : |s.im| ≤ ‖s - 1‖ := by
      simpa using Complex.abs_im_le_norm (s - 1)
    have h3 : |s.im| ≤ ‖s + β‖ := by
      simpa using Complex.abs_im_le_norm (s + β)
    have h_nonneg_im : 0 ≤ |s.im| := abs_nonneg _
    have h_nonneg_norm_s : 0 ≤ ‖s‖ := norm_nonneg _
    have h_nonneg_norm_s1 : 0 ≤ ‖s - 1‖ := norm_nonneg _
    have h_nonneg_norm_sβ : 0 ≤ ‖s + β‖ := norm_nonneg _
    calc
      |s.im| ^ 3 = (|s.im| * |s.im|) * |s.im| := by ring
      _ ≤ (‖s‖ * ‖s - 1‖) * ‖s + β‖ := by
        apply mul_le_mul
        · apply mul_le_mul h1 h2 h_nonneg_im h_nonneg_norm_s
        · exact h3
        · exact h_nonneg_im
        · exact mul_nonneg h_nonneg_norm_s h_nonneg_norm_s1
      _ = ‖s * (s - 1) * (s + β)‖ := by
        rw [norm_mul, norm_mul]
  have h_main : ‖s + 3‖ * s.im ^ 2 ≤ 2 * ‖s * (s - 1) * (s + β)‖ := by
    calc
      ‖s + 3‖ * s.im ^ 2 ≤ (2 * |s.im|) * s.im ^ 2 := by
        nlinarith
      _ = 2 * (|s.im| ^ 3) := by
        have : s.im ^ 2 = |s.im| ^ 2 := by simpa using (sq_abs s.im).symm
        nlinarith
      _ ≤ 2 * ‖s * (s - 1) * (s + β)‖ := by
        nlinarith
  have h_im_sq_pos : 0 < s.im ^ 2 := by
    have h_ne_zero : s.im ≠ 0 := by
      intro h
      rw [h, abs_zero] at him
      linarith
    exact sq_pos_iff.mpr h_ne_zero
  have h_den_pos : 0 < ‖s * (s - 1) * (s + β)‖ := by
    have h_im_pos : 0 < |s.im| := by linarith
    have h_s_pos : 0 < ‖s‖ := by
      have h_abs := Complex.abs_im_le_norm s
      linarith
    have h_s1_pos : 0 < ‖s - 1‖ := by
      have h_abs := Complex.abs_im_le_norm (s - 1)
      have h_im_eq : (s - 1).im = s.im := by simp
      rw [h_im_eq] at h_abs
      linarith
    have h_sβ_pos : 0 < ‖s + β‖ := by
      have h_abs := Complex.abs_im_le_norm (s + β)
      have h_im_eq : (s + β).im = s.im := by simp
      rw [h_im_eq] at h_abs
      linarith
    have h_prod_pos : 0 < ‖s‖ * ‖s - 1‖ * ‖s + β‖ := by
      positivity
    have h_eq : ‖s * (s - 1) * (s + β)‖ = ‖s‖ * ‖s - 1‖ * ‖s + β‖ := by
      rw [norm_mul, norm_mul]
    rw [h_eq]
    exact h_prod_pos
  exact (div_le_div_iff₀ h_den_pos h_im_sq_pos).mpr h_main

/-! ### Dirichlet series -/

/-- `|D_μ(s)| ≤ D_μ(Re s)`. -/
theorem norm_dser_le {ι : Type*} (μ : ι → ℝ) (hμ : ∀ j, 1 ≤ μ j) (s : ℂ)
    (hs : Summable fun j => μ j ^ (-s.re)) :
    ‖dser μ s‖ ≤ dserR μ s.re := by
  have hpos : ∀ j, 0 < μ j := by
    intro j
    have := hμ j
    linarith
  have hnorm : ∀ j, ‖((μ j : ℝ) : ℂ) ^ (-s)‖ = μ j ^ (-s.re) := by
    intro j
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos j) (-s), Complex.neg_re]
  have hsum_norm : Summable fun j => ‖((μ j : ℝ) : ℂ) ^ (-s)‖ := by
    have : (fun j => ‖((μ j : ℝ) : ℂ) ^ (-s)‖) = fun j => μ j ^ (-s.re) := by
      funext j; rw [hnorm j]
    rw [this]
    exact hs
  calc
    ‖dser μ s‖ = ‖∑' j, ((μ j : ℝ) : ℂ) ^ (-s)‖ := rfl
    _ ≤ ∑' j, ‖((μ j : ℝ) : ℂ) ^ (-s)‖ := norm_tsum_le_tsum_norm hsum_norm
    _ = ∑' j, μ j ^ (-s.re) := by rw [tsum_congr hnorm]
    _ = dserR μ s.re := rfl

/-- `D_μ` at a real point. -/
theorem dser_ofReal {ι : Type*} (μ : ι → ℝ) (hμ : ∀ j, 1 ≤ μ j) (σ : ℝ) :
    dser μ (σ : ℂ) = ((dserR μ σ : ℝ) : ℂ) := by
  unfold dser dserR
  rw [Complex.ofReal_tsum]
  congr 1
  funext j
  rw [Complex.ofReal_cpow (by linarith [hμ j]), Complex.ofReal_neg]

theorem dserR_pos {ι : Type*} [Nonempty ι] (μ : ι → ℝ) (hμ : ∀ j, 1 ≤ μ j) {σ : ℝ}
    (hs : Summable fun j => μ j ^ (-σ)) : 0 < dserR μ σ := by
  have hpos : ∀ j, 0 < μ j ^ (-σ) := fun j => Real.rpow_pos_of_pos (by linarith [hμ j]) _
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  exact hs.tsum_pos (fun j => (hpos j).le) j₀ (hpos j₀)

theorem dserR_nonneg {ι : Type*} (μ : ι → ℝ) (hμ : ∀ j, 1 ≤ μ j) (σ : ℝ) : 0 ≤ dserR μ σ :=
  tsum_nonneg fun j => Real.rpow_nonneg (by linarith [hμ j]) _

theorem dserR_ge {ι : Type*} (μ : ι → ℝ) {m : ℝ} (hm : 0 < m) (hmμ : ∀ j, m ≤ μ j) {β : ℝ}
    (hβ : β < 1 / 2) (hs : Summable fun j => μ j ^ (-(3 / 2 : ℝ)))
    (hs' : Summable fun j => μ j ^ (-(1 + β))) :
    m ^ (1 / 2 - β) * dserR μ (3 / 2) ≤ dserR μ (1 + β) := by
  have hpos : ∀ j, 0 < μ j := fun j => lt_of_lt_of_le hm (hmμ j)
  have hterm : ∀ j, m ^ (1 / 2 - β) * μ j ^ (-(3 / 2 : ℝ)) ≤ μ j ^ (-(1 + β)) := by
    intro j
    calc m ^ (1 / 2 - β) * μ j ^ (-(3 / 2 : ℝ))
        ≤ μ j ^ (1 / 2 - β) * μ j ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm.le (hmμ j) (by linarith))
            (Real.rpow_nonneg (hpos j).le _)
      _ = μ j ^ (-(1 + β)) := by
          rw [← Real.rpow_add (hpos j)]
          ring_nf
  calc m ^ (1 / 2 - β) * dserR μ (3 / 2) = ∑' j, m ^ (1 / 2 - β) * μ j ^ (-(3 / 2 : ℝ)) := by
        unfold dserR
        rw [tsum_mul_left]
    _ ≤ ∑' j, μ j ^ (-(1 + β)) := Summable.tsum_le_tsum hterm (hs.mul_left _) hs'
    _ = dserR μ (1 + β) := rfl

/-! ### Real constants -/

theorem xz_pos (a b : ℕ) {A α β : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hα1 : α < 1) : 0 < xz a b A α β := by
  unfold xz
  have hG : 0 < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - α := by linarith
  have h3 : 0 < 2 - β := by linarith
  have h4 : 0 < 2 - α := by linarith
  positivity

/-- Zimmert's `x` kills the residues at `1` and `0`. -/
theorem xz_residue (a b : ℕ) {A α β : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (hα1 : α < 1) :
    xz a b A α β / A * ((Real.Gamma (3 / 2))⁻¹ ^ a * (Real.Gamma 2)⁻¹ ^ b)
        * ((1 + α) / ((2 - β) * (2 - α))) / (1 + β)
      = ((Real.Gamma 1)⁻¹ ^ a * (Real.Gamma (3 / 2))⁻¹ ^ b) * (α / ((1 - β) * (1 - α))) / β := by
  unfold xz
  have hα' : α ≠ 0 := by linarith
  have hβ' : β ≠ 0 := by linarith
  have h1a : 1 + α ≠ 0 := by linarith
  have h1b : 1 + β ≠ 0 := by linarith
  have h1ma : 1 - α ≠ 0 := by linarith
  have h1mb : 1 - β ≠ 0 := by linarith
  have h2ma : 2 - α ≠ 0 := by linarith
  have h2mb : 2 - β ≠ 0 := by linarith
  have hA' : A ≠ 0 := by linarith
  have hG3 : Real.Gamma (3/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : 0 < (3/2 : ℝ))).ne.symm
  have hG3a : Real.Gamma (3/2) ^ a ≠ 0 := pow_ne_zero a hG3
  have hG3b : Real.Gamma (3/2) ^ b ≠ 0 := pow_ne_zero b hG3
  field_simp [hα', hβ', h1a, h1b, h1ma, h1mb, h2ma, h2mb, hA']
  ring_nf
  simp [Real.Gamma_one, hG3a, hG3b]

theorem Tz_pos (a b : ℕ) {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) : 0 < Tz a b β := by
  unfold Tz
  have h1 : 0 < Real.Gamma ((1 + β) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (1 + β / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : 0 < Real.Gamma (1 - β / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h4 : 0 < Real.Gamma ((3 - β) / 2) := Real.Gamma_pos_of_pos (by linarith)
  positivity

/-- `x^σ ≤ x^σ₁ + x^σ₂` for `σ ∈ [σ₁, σ₂]`, `x > 0`. -/
theorem rpow_le_add_of_mem {x σ σ₁ σ₂ : ℝ} (hx : 0 < x) (h1 : σ₁ ≤ σ) (h2 : σ ≤ σ₂) :
    x ^ σ ≤ x ^ σ₁ + x ^ σ₂ := by
  rcases le_or_gt 1 x with hx1 | hx1
  · have := Real.rpow_le_rpow_of_exponent_le hx1 h2
    linarith [Real.rpow_nonneg hx.le σ₁]
  · have := Real.rpow_le_rpow_of_exponent_ge hx hx1.le h1
    linarith [Real.rpow_nonneg hx.le σ₂]

/-- `∫ 1/(c² + t²) dt = π/c`. -/
theorem zf_integral_one_div_sq_add_sq {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, 1 / (c ^ 2 + t ^ 2) = Real.pi / c := by
  have hc_ne : c ≠ 0 := by linarith
  -- pointwise equality of integrands
  have h_eq (t : ℝ) : 1 / (c ^ 2 + t ^ 2) = (c ^ 2)⁻¹ * ((1 + ((t / c) ^ 2))⁻¹) := by
    field_simp [hc_ne]
  have h_eq_ae : (fun t : ℝ => 1 / (c ^ 2 + t ^ 2)) =ᵐ[MeasureTheory.volume]
      (fun t : ℝ => (c ^ 2)⁻¹ * ((1 + ((t / c) ^ 2))⁻¹)) := by
    filter_upwards with t
    exact h_eq t
  calc
    ∫ t : ℝ, 1 / (c ^ 2 + t ^ 2) = ∫ t : ℝ, (c ^ 2)⁻¹ * ((1 + ((t / c) ^ 2))⁻¹) := by
      rw [MeasureTheory.integral_congr_ae h_eq_ae]
    _ = (c ^ 2)⁻¹ * ∫ t : ℝ, ((1 + ((t / c) ^ 2))⁻¹) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (c ^ 2)⁻¹ * ∫ t : ℝ, ((1 + (((1 / c) * t) ^ 2))⁻¹) := by
      refine congrArg (fun x => (c ^ 2)⁻¹ * x) (MeasureTheory.integral_congr_ae ?_)
      filter_upwards with t
      simp [div_eq_mul_inv, mul_comm]
    _ = (c ^ 2)⁻¹ * (Real.pi / |(1 : ℝ) / c|) := by
      rw [integral_univ_inv_one_add_mul_sq (1 / c)]
    _ = (c ^ 2)⁻¹ * (Real.pi / (c⁻¹)) := by
      rw [abs_of_pos (div_pos (by norm_num) hc), div_eq_inv_mul]
      ring
    _ = (c ^ 2)⁻¹ * (Real.pi * c) := by
      field_simp [hc_ne]
    _ = ((c ^ 2)⁻¹ * c) * Real.pi := by ring
    _ = c⁻¹ * Real.pi := by
      field_simp [hc_ne]
    _ = Real.pi / c := by ring

theorem zf_integrable_one_div_sq_add_sq {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun t : ℝ => 1 / (c ^ 2 + t ^ 2)) := by
  have hc_ne : c ≠ 0 := by linarith
  have h_eq : (fun t : ℝ => 1 / (c ^ 2 + t ^ 2)) =
      (fun t : ℝ => (c⁻¹)^2 * ((1 + (t / c) ^ 2)⁻¹)) := by
    ext t
    field_simp [hc_ne]
  rw [h_eq]
  exact ((integrable_inv_one_add_sq.comp_div hc_ne).const_mul ((c⁻¹)^2))

/-! ### Norm identities on the lines `Re s = 2` and `Re s = -1/2` -/

open ComplexConjugate

theorem norm_le_norm_of_re_im {z w : ℂ} (hre : |z.re| ≤ |w.re|) (him : z.im = w.im) :
    ‖z‖ ≤ ‖w‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply, him]
  have := mul_self_le_mul_self (abs_nonneg _) hre
  rw [abs_mul_abs_self, abs_mul_abs_self] at this
  linarith

theorem norm_div_le_one_of_re_im {z w : ℂ} (hw : 0 < |w.re|) (hre : |z.re| ≤ |w.re|)
    (him : z.im = w.im) : ‖z / w‖ ≤ 1 := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hw (Complex.abs_re_le_norm w)
  rw [norm_div, div_le_one hw0]
  exact norm_le_norm_of_re_im hre him

theorem norm_Gz_one_sub_mul_iG1 (a b : ℕ) {s : ℂ} (hs : s.re = -1 / 2) :
    ‖Gz a b (1 - s) * iG1 a b s‖ = 1 := by
  unfold Gz iG1
  have e1 : (1 - s) / 2 = conj (s / 2 + 1) := by
    rw [map_add, map_div₀, map_one, map_ofNat]
    apply Complex.ext <;> simp [hs] <;> ring
  have e2 : (1 - s + 1) / 2 = conj ((s + 3) / 2) := by
    rw [map_div₀, map_add, map_ofNat, map_ofNat]
    apply Complex.ext <;> simp [hs] <;> ring
  have h1 : Gamma (s / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have h2 : Gamma ((s + 3) / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have n1 : ‖Gamma (s / 2 + 1)‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  have n2 : ‖Gamma ((s + 3) / 2)‖ ≠ 0 := norm_ne_zero_iff.mpr h2
  rw [e1, e2, Complex.Gamma_conj, Complex.Gamma_conj]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_conj]
  rw [inv_pow, inv_pow, mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero _ n1),
    mul_inv_cancel₀ (pow_ne_zero _ n2), one_mul]

theorem Rz_mul_cubic {α β : ℝ} {s : ℂ} (hb : s + β ≠ 0) (h1 : s + 1 - β ≠ 0) (h2 : s + 1 - α ≠ 0)
    (h3 : s + 3 ≠ 0) :
    Rz α β s * (s * (s - 1) * (s + β) / (s + 3))
      = (s + α) / (s + 1 - α) * ((s - 1) / (s + 3)) * (s / (s + 1 - β)) := by
  unfold Rz
  field_simp

theorem norm_Rz_left {α β : ℝ} (hα : α < 1 / 2) (hβ : β < 1 / 2) {s : ℂ} (hs : s.re = -1 / 2) :
    ‖Rz α β s‖ = 1 / ((1 / 2 - β) ^ 2 + s.im ^ 2) := by
  have e1 : s + 1 - α = -conj (s + α) := by
    rw [map_add, Complex.conj_ofReal]
    apply Complex.ext <;> simp [hs] <;> ring
  have e2 : s + 1 - β = -conj (s + β) := by
    rw [map_add, Complex.conj_ofReal]
    apply Complex.ext <;> simp [hs] <;> ring
  have hα0 : ‖s + α‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h; have := congrArg Complex.re h; simp [hs] at this; linarith
  have hsq : ‖s + β‖ ^ 2 = (1 / 2 - β) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hs]
    ring
  unfold Rz
  rw [e1, e2, norm_div, norm_mul, norm_mul, norm_neg, norm_neg, Complex.norm_conj,
    Complex.norm_conj, ← hsq]
  field_simp

theorem norm_Rz_right_le {α β : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hβ : 0 ≤ β) (hβ1 : β ≤ 1 / 2)
    {s : ℂ} (hs : s.re = 2) :
    ‖Rz α β s‖ ≤ 1 / ((2 + β) ^ 2 + s.im ^ 2) := by
  have hsq : ‖s + β‖ ^ 2 = (2 + β) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hs]
    ring
  have hb0 : 0 < ‖s + β‖ := by
    have := Complex.abs_re_le_norm (s + β)
    simp [hs] at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  have hαn : ‖s + α‖ ≤ ‖s + 1 - α‖ :=
    norm_le_norm_of_re_im (by simp [hs]; rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith)
      (by simp)
  have hβn : ‖s + β‖ ≤ ‖s + 1 - β‖ :=
    norm_le_norm_of_re_im (by simp [hs]; rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith)
      (by simp)
  have ha0 : 0 < ‖s + 1 - α‖ := by
    have := Complex.abs_re_le_norm (s + 1 - α)
    simp [hs] at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  unfold Rz
  rw [norm_div, norm_mul, norm_mul, ← hsq,
    div_le_div_iff₀ (mul_pos (mul_pos hb0 (lt_of_lt_of_le hb0 hβn)) ha0) (pow_pos hb0 2)]
  calc ‖s + α‖ * ‖s + β‖ ^ 2 ≤ ‖s + 1 - α‖ * (‖s + β‖ * ‖s + 1 - β‖) := by
        rw [sq]
        gcongr
    _ = 1 * (‖s + β‖ * ‖s + 1 - β‖ * ‖s + 1 - α‖) := by ring

theorem norm_right_factor_le (a b : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hβ1 : β < 1) {s : ℂ} (hs : s.re = 2) :
    ‖Rz α β s * (2 / s) ^ a * (2 / (s + 1)) ^ b * (s * (s - 1) * (s + β) / (s + 3))‖ ≤ 1 := by
  have ne : ∀ c : ℝ, 0 < 2 + c → s + c ≠ 0 := by
    intro c hc h; have := congrArg Complex.re h; simp [hs] at this; linarith
  have hb := ne β (by linarith)
  have h1 : s + 1 - β ≠ 0 := by
    have := ne (1 - β) (by linarith); push_cast at this; rwa [add_sub_assoc]
  have h2 : s + 1 - α ≠ 0 := by
    have := ne (1 - α) (by linarith); push_cast at this; rwa [add_sub_assoc]
  have h3 : s + 3 ≠ 0 := by
    have := ne 3 (by norm_num); push_cast at this; exact this
  have hre : ∀ c : ℝ, (s + c).re = 2 + c := fun c => by simp [hs]
  rw [show Rz α β s * (2 / s) ^ a * (2 / (s + 1)) ^ b * (s * (s - 1) * (s + β) / (s + 3))
      = Rz α β s * (s * (s - 1) * (s + β) / (s + 3)) * (2 / s) ^ a * (2 / (s + 1)) ^ b by ring,
    Rz_mul_cubic hb h1 h2 h3]
  have ra : (s + α).re = 2 + α := by simp [hs]
  have ra1 : (s + 1 - α).re = 3 - α := by simp [hs]; ring
  have rb1 : (s + 1 - β).re = 3 - β := by simp [hs]; ring
  have r1 : (s - 1).re = 1 := by simp [hs]; norm_num
  have r3 : (s + 3).re = 5 := by simp [hs]; norm_num
  rw [show (s + α) / (s + 1 - α) * ((s - 1) / (s + 3)) = (s + α) / (s + 3) * ((s - 1) / (s + 1 - α))
    by ring]
  have f1 : ‖(s + α) / (s + 3)‖ ≤ 1 :=
    norm_div_le_one_of_re_im (by rw [r3]; norm_num)
      (by rw [ra, r3, abs_of_pos (by linarith : (0 : ℝ) < 2 + α)]; norm_num; linarith) (by simp)
  have f2 : ‖(s - 1) / (s + 1 - α)‖ ≤ 1 :=
    norm_div_le_one_of_re_im (by rw [ra1, abs_of_pos (by linarith)]; linarith)
      (by rw [r1, ra1, abs_of_pos (by linarith : (0 : ℝ) < 3 - α)]; norm_num; linarith) (by simp)
  have f3 : ‖s / (s + 1 - β)‖ ≤ 1 :=
    norm_div_le_one_of_re_im (by rw [rb1, abs_of_pos (by linarith)]; linarith)
      (by rw [hs, rb1, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith) (by simp)
  have hs2 : 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hs] at this; simpa using this
  have hs3 : 2 ≤ ‖s + 1‖ := by
    have := Complex.abs_re_le_norm (s + 1)
    simp [hs] at this; norm_num at this; linarith
  have f4 : ‖(2 / s) ^ a‖ ≤ 1 := by
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [norm_div, div_le_one (by linarith)]
    simpa using hs2
  have f5 : ‖(2 / (s + 1)) ^ b‖ ≤ 1 := by
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [norm_div, div_le_one (by linarith)]
    simpa using hs3
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  calc _ ≤ (1 : ℝ) * 1 * 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

theorem norm_left_factor_le {α β : ℝ} (hα : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1 / 2) {s : ℂ}
    (hs : s.re = -1 / 2) :
    ‖Rz α β s * (s * (s - 1) * (s + β) / (s + 3))‖ ≤ 3 / (1 - 2 * β) := by
  have ne : ∀ c : ℝ, c ≠ 1 / 2 → s + c ≠ 0 := by
    intro c hc h; have := congrArg Complex.re h; simp [hs] at this
    exact hc (by linarith)
  have hb := ne β (by linarith)
  have h1 : s + 1 - β ≠ 0 := by
    have := ne (1 - β) (by linarith); push_cast at this; rwa [add_sub_assoc]
  have h2 : s + 1 - α ≠ 0 := by
    have := ne (1 - α) (by linarith); push_cast at this; rwa [add_sub_assoc]
  have h3 : s + 3 ≠ 0 := by
    have := ne 3 (by norm_num); push_cast at this; exact this
  rw [Rz_mul_cubic hb h1 h2 h3]
  have ra : (s + α).re = α - 1 / 2 := by simp [hs]; ring
  have ra1 : (s + 1 - α).re = 1 / 2 - α := by simp [hs]; ring
  have r1 : (s - 1).re = -3 / 2 := by simp [hs]; norm_num
  have r3 : (s + 3).re = 5 / 2 := by simp [hs]; norm_num
  have f1 : ‖(s + α) / (s + 1 - α)‖ ≤ 1 :=
    norm_div_le_one_of_re_im (by rw [ra1, abs_of_pos (by linarith)]; linarith)
      (by rw [ra, ra1, abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith) (by simp)
  have f2 : ‖(s - 1) / (s + 3)‖ ≤ 1 :=
    norm_div_le_one_of_re_im (by rw [r3]; norm_num) (by rw [r1, r3]; norm_num) (by simp)
  have hb12 : 0 < 1 - 2 * β := by linarith
  have f3 : ‖s / (s + 1 - β)‖ ≤ 1 / (1 - 2 * β) := by
    have hd : 0 < ‖s + 1 - β‖ := by
      have := Complex.abs_re_le_norm (s + 1 - β)
      simp [hs] at this
      rw [abs_of_pos (by linarith)] at this
      linarith
    rw [norm_div, div_le_div_iff₀ hd hb12, one_mul]
    have hsq : (‖s‖ * (1 - 2 * β)) ^ 2 ≤ ‖s + 1 - β‖ ^ 2 := by
      rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp [hs]
      have : (1 - 2 * β) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg s.im]
    exact (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hb12.le) (norm_nonneg _)).mp hsq
  rw [norm_mul, norm_mul]
  calc _ ≤ (1 : ℝ) * 1 * (1 / (1 - 2 * β)) := by gcongr
    _ ≤ 3 / (1 - 2 * β) := by
        rw [one_mul, one_mul]
        gcongr
        norm_num

end FurioLombardo.M2.Zimmert
