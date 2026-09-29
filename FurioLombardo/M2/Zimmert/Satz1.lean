import Mathlib
import FurioLombardo.M2.Zimmert.Leaves
import FurioLombardo.M2.Zimmert.Growth
import FurioLombardo.M2.Zimmert.Contour
import FurioLombardo.M2.Zimmert.Positivity

/-!
# Zimmert's Satz 1 at `γ = 1/2`, fixed `β` (lane M2)

For `D : ZData a b ιf ιg` with `a ≥ 1` and `0 < α < β < 1/2`, with `x = xz a b A α β`:

`x^{-β} A^{1+2β} (β-α) T_β D_μ(1+β) / (1-α-β) ≤ x^{-1/2} A^2 D_μ(3/2)`   (`ZData.satz1_beta`).

Proof: `H = E R Λf` with `E(s) = x^s A^{-s}/G₁(s)`;
contour shift from `Re s = 2` to `Re s = -1/2` past the poles `1, 0, -β` (`contour_shift`),
the residues at `1` and `0` cancel by the choice of `x`, positivity of the right integral
(`re_integral_right_nonneg`), explicit bound of the left integral; growth through
Phragmén-Lindelöf applied to `F = H s(s-1)(s+β)/(s+3)` (`norm_le_of_strip`).
-/

namespace FurioLombardo.M2.Zimmert

open Complex MeasureTheory

/-- A function equal on a vertical line to a finite sum of `Φ_p(s)/(s-p)`, with `Φ_p`
holomorphic near the line and no `p` on the line, is continuous along the line. -/
theorem continuous_line_of_sum {U : Set ℂ} (P : Finset ℂ) (Φ : ℂ → ℂ → ℂ)
    (hΦ : ∀ p ∈ P, DifferentiableOn ℂ (Φ p) U) {H : ℂ → ℂ}
    (hH : ∀ s : ℂ, s ∉ P → H s = ∑ p ∈ P, Φ p s / (s - p)) {σ : ℝ}
    (hσU : ∀ t : ℝ, (σ : ℂ) + t * I ∈ U) (hσP : ∀ p ∈ P, p.re ≠ σ) :
    Continuous fun t : ℝ => H (σ + t * I) := by
  have hnot : ∀ t : ℝ, (σ : ℂ) + t * I ∉ P := by
    intro t ht
    exact hσP _ ht (by simp)
  have heq : (fun t : ℝ => H (σ + t * I)) =
      fun t : ℝ => ∑ p ∈ P, Φ p (σ + t * I) / ((σ : ℂ) + t * I - p) := by
    funext t
    exact hH _ (hnot t)
  rw [heq]
  have hline : Continuous fun t : ℝ => (σ : ℂ) + t * I := by fun_prop
  refine continuous_finsetSum _ fun p hp => ?_
  refine Continuous.div ((hΦ p hp).continuousOn.comp_continuous hline hσU)
    (hline.sub continuous_const) fun t h0 => ?_
  have := congrArg Complex.re h0
  simp at this
  exact hσP p hp (by linarith)

namespace ZData

variable {a b : ℕ} {ιf ιg : Type*} (D : ZData a b ιf ιg)

/-- The functional equation of the completed functions (no exceptional point, by the
conventions of division by zero). -/
theorem Λf_eq_Λg (s : ℂ) : D.Λf s = D.Λg (1 - s) := by
  unfold Λf Λg
  rw [← D.hfe s]
  have h1 : D.κ / (1 - s) = -(D.κ / (s - 1)) := by
    rw [show (1 : ℂ) - s = -(s - 1) by ring, div_neg]
  have h2 : D.κ / (1 - s - 1) = -(D.κ / s) := by
    rw [show (1 : ℂ) - s - 1 = -s by ring, div_neg]
  rw [h1, h2]
  ring

/-- `E(s) = x^s A^{-s} / G₁(s)`. -/
noncomputable def Ez (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s * (D.A : ℂ) ^ (-s) * iG1 a b s

/-- Zimmert's integrand `H(s) = E(s) R(s) Λf(s)`. -/
noncomputable def Hz (α β x : ℝ) (s : ℂ) : ℂ := D.Ez x s * Rz α β s * D.Λf s

/-- The auxiliary function `F(s) = H(s) s (s-1) (s+β) / (s+3)` of the growth argument,
written without the removable singularities. -/
noncomputable def Fz (α β x : ℝ) (s : ℂ) : ℂ :=
  D.Ez x s * rz α β s * (D.Lf s * s * (s - 1) + D.κ) / (s + 3)

theorem A_ne_zero : (D.A : ℂ) ≠ 0 := by
  exact_mod_cast D.hA.ne'

theorem differentiable_Ez {x : ℝ} (hx : 0 < x) : Differentiable ℂ (D.Ez x) := by
  intro s
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold Ez
  exact ((differentiableAt_id.const_cpow (Or.inl hx0)).mul
    (differentiableAt_id.neg.const_cpow (Or.inl D.A_ne_zero))).mul
    (differentiable_iG1 a b s)

/-- On `Re s > 1`, `H(s) = x^s Q(s) D_ν(s)`. -/
theorem Hz_right (α β x : ℝ) (s : ℂ) (hs : 1 < s.re) :
    D.Hz α β x s = (x : ℂ) ^ s * (Rz α β s * (2 / s) ^ a * (2 / (s + 1)) ^ b) * dser D.ν s := by
  have hΛ : D.Λf s = (D.A : ℂ) ^ s * Gz a b s * dser D.ν s := D.hdf s hs
  have hA : (D.A : ℂ) ^ (-s) * (D.A : ℂ) ^ s = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl D.A_ne_zero))]
  have hG := Gz_mul_iG1 a b (s := s) (by linarith)
  unfold Hz Ez
  rw [hΛ]
  linear_combination ((x : ℂ) ^ s * Rz α β s * dser D.ν s * iG1 a b s * Gz a b s) * hA
    + ((x : ℂ) ^ s * Rz α β s * dser D.ν s) * hG

/-- On `Re s < 0`, `H(s) = x^s A^{-s} A^{1-s} (G(1-s)/G₁(s)) R(s) D_μ(1-s)`. -/
theorem Hz_left (α β x : ℝ) (s : ℂ) (hs : s.re < 0) :
    D.Hz α β x s = (x : ℂ) ^ s * ((D.A : ℂ) ^ (-s) * (D.A : ℂ) ^ (1 - s))
      * (Gz a b (1 - s) * iG1 a b s) * Rz α β s * dser D.μ (1 - s) := by
  have hΛ : D.Λf s = (D.A : ℂ) ^ (1 - s) * Gz a b (1 - s) * dser D.μ (1 - s) := by
    rw [D.Λf_eq_Λg]
    exact D.hdg (1 - s) (by simp; linarith)
  unfold Hz Ez
  rw [hΛ]
  ring

theorem norm_cpow_A (s : ℂ) : ‖(D.A : ℂ) ^ s‖ = D.A ^ s.re :=
  norm_cpow_eq_rpow_re_of_pos D.hA s

/-- The left line bound `|H(-1/2+it)| ≤ x^{-1/2} A² D_μ(3/2) / ((1/2-β)² + t²)`. -/
theorem norm_Hz_left_le {α β x : ℝ} (hα : α < 1 / 2) (hβ : β < 1 / 2) (hx : 0 < x) (s : ℂ)
    (hs : s.re = -1 / 2) :
    ‖D.Hz α β x s‖ ≤
      x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * dserR D.μ (3 / 2) * (1 / ((1 / 2 - β) ^ 2 + s.im ^ 2)) := by
  rw [D.Hz_left α β x s (by linarith)]
  have h1 : ‖(x : ℂ) ^ s‖ = x ^ (-(1 / 2) : ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, hs]
    norm_num
  have h2 : ‖(D.A : ℂ) ^ (-s) * (D.A : ℂ) ^ (1 - s)‖ = D.A ^ (2 : ℝ) := by
    rw [norm_mul, D.norm_cpow_A, D.norm_cpow_A, ← Real.rpow_add D.hA]
    congr 1
    simp [hs]
    norm_num
  have h3 := norm_Gz_one_sub_mul_iG1 a b hs
  have h4 := norm_Rz_left hα hβ hs
  have hre : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
  have h5 : ‖dser D.μ (1 - s)‖ ≤ dserR D.μ (3 / 2) := by
    have := norm_dser_le D.μ D.hμ (1 - s) (by rw [hre]; exact D.hμs _ (by norm_num))
    rwa [hre] at this
  rw [norm_mul, norm_mul, norm_mul, norm_mul, h1, h2, h3, h4, mul_one]
  have hpos : 0 ≤ x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) := by
    have := Real.rpow_nonneg hx.le (-(1 / 2) : ℝ)
    have := Real.rpow_nonneg D.hA.le (2 : ℝ)
    positivity
  have hq : 0 ≤ 1 / ((1 / 2 - β) ^ 2 + s.im ^ 2) := by positivity
  calc x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * (1 / ((1 / 2 - β) ^ 2 + s.im ^ 2)) * ‖dser D.μ (1 - s)‖
      ≤ x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * (1 / ((1 / 2 - β) ^ 2 + s.im ^ 2)) * dserR D.μ (3 / 2) :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg hpos hq)
    _ = _ := by ring

/-- The right line bound `|H(2+it)| ≤ x² D_ν(2) / ((2+β)² + t²)`. -/
theorem norm_Hz_right_le {α β x : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1 / 2) (hx : 0 < x) (s : ℂ) (hs : s.re = 2) :
    ‖D.Hz α β x s‖ ≤ x ^ (2 : ℝ) * dserR D.ν 2 * (1 / ((2 + β) ^ 2 + s.im ^ 2)) := by
  rw [D.Hz_right α β x s (by rw [hs]; norm_num)]
  have h1 : ‖(x : ℂ) ^ s‖ = x ^ (2 : ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, hs]
  have hsn : 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hs] at this
    simpa using this
  have hs1n : 2 ≤ ‖s + 1‖ := by
    have := Complex.abs_re_le_norm (s + 1)
    simp [hs] at this
    norm_num at this
    linarith
  have h2 : ‖(2 / s) ^ a‖ ≤ 1 := by
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [norm_div, div_le_one (by linarith)]
    simpa using hsn
  have h3 : ‖(2 / (s + 1)) ^ b‖ ≤ 1 := by
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [norm_div, div_le_one (by linarith)]
    simpa using hs1n
  have h4 := norm_Rz_right_le hα hα1 hβ hβ1 hs
  have h5 : ‖dser D.ν s‖ ≤ dserR D.ν 2 := by
    have := norm_dser_le D.ν D.hν s (by rw [hs]; exact D.hνs _ (by norm_num))
    rwa [hs] at this
  have hq : 0 ≤ 1 / ((2 + β) ^ 2 + s.im ^ 2) := by positivity
  have hx2 : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hx.le _
  rw [norm_mul, norm_mul, norm_mul, norm_mul, h1]
  calc x ^ (2 : ℝ) * (‖Rz α β s‖ * ‖(2 / s) ^ a‖ * ‖(2 / (s + 1)) ^ b‖) * ‖dser D.ν s‖
      ≤ x ^ (2 : ℝ) * ((1 / ((2 + β) ^ 2 + s.im ^ 2)) * 1 * 1) * dserR D.ν 2 := by
        gcongr
    _ = _ := by ring

theorem differentiableOn_rz {α β : ℝ} (hαβ : α ≤ β) :
    DifferentiableOn ℂ (rz α β) {s : ℂ | β - 1 < s.re} := by
  intro s hs
  have hs' : β - 1 < s.re := hs
  have h1 : s + 1 - β ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : s + 1 - α ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hd : DifferentiableAt ℂ (fun s : ℂ => (s + α) / ((s + 1 - β) * (s + 1 - α))) s :=
    DifferentiableAt.div (by fun_prop) (by fun_prop) (mul_ne_zero h1 h2)
  exact hd.differentiableWithinAt

theorem differentiableOn_Fz {α β x : ℝ} (hαβ : α ≤ β) (hβ0 : 0 ≤ β) (hx : 0 < x) :
    DifferentiableOn ℂ (D.Fz α β x) {s : ℂ | β - 1 < s.re} := by
  intro s hs
  have hs' : β - 1 < s.re := hs
  have h3 : s + 3 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hE := (D.differentiable_Ez hx s).differentiableWithinAt (s := {s : ℂ | β - 1 < s.re})
  have hr := differentiableOn_rz hαβ s hs
  have hL := (D.hLf s).differentiableWithinAt (s := {s : ℂ | β - 1 < s.re})
  have hid := differentiableWithinAt_id (𝕜 := ℂ) (x := s) (s := {s : ℂ | β - 1 < s.re})
  exact ((hE.mul hr).mul (((hL.mul hid).mul (hid.sub_const 1)).add_const _)).div
    (hid.add_const 3) h3

/-- `F = H · s(s-1)(s+β)/(s+3)` away from the poles. -/
theorem Fz_eq (α β x : ℝ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hb : s + β ≠ 0) (h3 : s + 3 ≠ 0) :
    D.Fz α β x s = D.Hz α β x s * (s * (s - 1) * (s + β) / (s + 3)) := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold Fz Hz Λf
  rw [Rz_eq_rz_div]
  field_simp
  ring

theorem Hz_eq_Fz (α β x : ℝ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (hb : s + β ≠ 0) (h3 : s + 3 ≠ 0) :
    D.Hz α β x s = D.Fz α β x s * ((s + 3) / (s * (s - 1) * (s + β))) := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [D.Fz_eq α β x h0 h1 hb h3]
  field_simp

theorem ne_of_re_ne {s : ℂ} {c : ℝ} (h : s.re ≠ -c) : s + c ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this
  exact h (by linarith)

/-- `|F| ≤ x² D_ν(2)` on `Re s = 2`. -/
theorem norm_Fz_right_le {α β x : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1 / 2) (hx : 0 < x) (s : ℂ) (hs : s.re = 2) :
    ‖D.Fz α β x s‖ ≤ x ^ (2 : ℝ) * dserR D.ν 2 := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hb : s + β ≠ 0 := ne_of_re_ne (by rw [hs]; linarith)
  have h3 : s + 3 ≠ 0 := by
    have := ne_of_re_ne (s := s) (c := 3) (by rw [hs]; norm_num)
    simpa using this
  rw [D.Fz_eq α β x h0 h1 hb h3, D.Hz_right α β x s (by rw [hs]; norm_num)]
  have hW := norm_right_factor_le a b hα (by linarith) hβ (by linarith) hs (α := α) (β := β)
  have h1n : ‖(x : ℂ) ^ s‖ = x ^ (2 : ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, hs]
  have h5 : ‖dser D.ν s‖ ≤ dserR D.ν 2 := by
    have := norm_dser_le D.ν D.hν s (by rw [hs]; exact D.hνs _ (by norm_num))
    rwa [hs] at this
  have hx2 : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hx.le _
  calc ‖(x : ℂ) ^ s * (Rz α β s * (2 / s) ^ a * (2 / (s + 1)) ^ b) * dser D.ν s
        * (s * (s - 1) * (s + β) / (s + 3))‖
      = ‖(x : ℂ) ^ s‖ * ‖dser D.ν s‖
        * ‖Rz α β s * (2 / s) ^ a * (2 / (s + 1)) ^ b * (s * (s - 1) * (s + β) / (s + 3))‖ := by
        rw [← norm_mul, ← norm_mul]
        ring_nf
    _ ≤ x ^ (2 : ℝ) * dserR D.ν 2 * 1 := by
        rw [h1n]
        gcongr
        exact mul_nonneg hx2 (dserR_nonneg D.ν D.hν 2)
    _ = _ := mul_one _

/-- `|F| ≤ x^{-1/2} A² D_μ(3/2) · 3/(1-2β)` on `Re s = -1/2`. -/
theorem norm_Fz_left_le {α β x : ℝ} (hα : α < 1 / 2) (hβ : 0 < β) (hβ1 : β < 1 / 2)
    (hx : 0 < x) (s : ℂ) (hs : s.re = -1 / 2) :
    ‖D.Fz α β x s‖ ≤ x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * dserR D.μ (3 / 2) * (3 / (1 - 2 * β)) := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hb : s + β ≠ 0 := ne_of_re_ne (by rw [hs]; linarith)
  have h3 : s + 3 ≠ 0 := by
    have := ne_of_re_ne (s := s) (c := 3) (by rw [hs]; norm_num)
    simpa using this
  rw [D.Fz_eq α β x h0 h1 hb h3, D.Hz_left α β x s (by rw [hs]; norm_num)]
  have hW := norm_left_factor_le hα hβ hβ1 hs
  have h1n : ‖(x : ℂ) ^ s‖ = x ^ (-(1 / 2) : ℝ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx, hs]
    norm_num
  have h2n : ‖(D.A : ℂ) ^ (-s) * (D.A : ℂ) ^ (1 - s)‖ = D.A ^ (2 : ℝ) := by
    rw [norm_mul, D.norm_cpow_A, D.norm_cpow_A, ← Real.rpow_add D.hA]
    congr 1
    simp [hs]
    norm_num
  have h3n := norm_Gz_one_sub_mul_iG1 a b hs
  have hre : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
  have h5 : ‖dser D.μ (1 - s)‖ ≤ dserR D.μ (3 / 2) := by
    have := norm_dser_le D.μ D.hμ (1 - s) (by rw [hre]; exact D.hμs _ (by norm_num))
    rwa [hre] at this
  have hpos : 0 ≤ x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) := by
    have := Real.rpow_nonneg hx.le (-(1 / 2) : ℝ)
    have := Real.rpow_nonneg D.hA.le (2 : ℝ)
    positivity
  calc ‖(x : ℂ) ^ s * ((D.A : ℂ) ^ (-s) * (D.A : ℂ) ^ (1 - s)) * (Gz a b (1 - s) * iG1 a b s)
        * Rz α β s * dser D.μ (1 - s) * (s * (s - 1) * (s + β) / (s + 3))‖
      = ‖(x : ℂ) ^ s‖ * ‖(D.A : ℂ) ^ (-s) * (D.A : ℂ) ^ (1 - s)‖
        * ‖Gz a b (1 - s) * iG1 a b s‖ * ‖dser D.μ (1 - s)‖
        * ‖Rz α β s * (s * (s - 1) * (s + β) / (s + 3))‖ := by
        rw [← norm_mul, ← norm_mul, ← norm_mul, ← norm_mul]
        ring_nf
    _ ≤ x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * 1 * dserR D.μ (3 / 2) * (3 / (1 - 2 * β)) := by
        rw [h1n, h2n, h3n]
        gcongr
        exact mul_nonneg (mul_nonneg hpos zero_le_one) (dserR_nonneg D.μ D.hμ _)
    _ = _ := by ring

/-- `‖s + c‖ ≤ |Re s + c| + |Im s|`. -/
theorem norm_add_ofReal_le (s : ℂ) (c : ℝ) : ‖s + c‖ ≤ |s.re + c| + |s.im| := by
  have := Complex.norm_le_abs_re_add_abs_im (s + c)
  simpa using this

/-- `|Im s| ≤ ‖s + c‖`. -/
theorem abs_im_le_norm_add_ofReal (s : ℂ) (c : ℝ) : |s.im| ≤ ‖s + c‖ := by
  have := Complex.abs_im_le_norm (s + c)
  simpa using this

/-- `‖rz s‖ ≤ 4` on the strip for `|Im s| ≥ 1`. -/
theorem norm_rz_le {α β : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1 / 2) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 2) (ht : 1 ≤ |s.im|) : ‖rz α β s‖ ≤ 4 := by
  unfold rz
  have hn1 : ‖s + α‖ ≤ 5 / 2 + |s.im| := by
    refine le_trans (norm_add_ofReal_le s α) ?_
    have : |s.re + α| ≤ 5 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hd1 : |s.im| ≤ ‖s + 1 - β‖ := by
    have := abs_im_le_norm_add_ofReal s (1 - β)
    simpa [add_sub_assoc] using this
  have hd2 : |s.im| ≤ ‖s + 1 - α‖ := by
    have := abs_im_le_norm_add_ofReal s (1 - α)
    simpa [add_sub_assoc] using this
  have hpos : 0 < ‖s + 1 - β‖ * ‖s + 1 - α‖ := by
    have : 0 < |s.im| := by linarith
    exact mul_pos (lt_of_lt_of_le this hd1) (lt_of_lt_of_le this hd2)
  rw [norm_div, norm_mul, div_le_iff₀ hpos]
  have hsq : |s.im| * |s.im| ≤ ‖s + 1 - β‖ * ‖s + 1 - α‖ :=
    mul_le_mul hd1 hd2 (abs_nonneg _) (le_trans (abs_nonneg _) hd1)
  nlinarith

/-- `(2 + u)^2 ≤ 4 exp(2u)` for `u ≥ 0`. -/
theorem two_add_sq_le_exp {u : ℝ} (hu : 0 ≤ u) : (2 + u) ^ 2 ≤ 4 * Real.exp (2 * u) := by
  have h := Real.add_one_le_exp u
  have h2 : 2 + u ≤ 2 * Real.exp u := by linarith
  have h3 : Real.exp (2 * u) = Real.exp u ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  nlinarith

/-- The a priori growth of `F` in the open strip: `|F(s)| ≤ K exp(k |Im s|)` for `|Im s| ≥ 2`. -/
theorem norm_Fz_growth {α β x : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hx : 0 < x) :
    ∃ K k : ℝ, ∀ s : ℂ, -1 / 2 < s.re → s.re < 2 → 2 ≤ |s.im| →
      ‖D.Fz α β x s‖ ≤ K * Real.exp (k * |s.im|) := by
  obtain ⟨M, hM⟩ := D.hstrip (-1 / 2) 2
  set M' := max M 0 with hM'
  refine ⟨(x ^ (-(1 / 2) : ℝ) + x ^ (2 : ℝ)) * (D.A ^ (-2 : ℝ) + D.A ^ (1 / 2 : ℝ))
      * cG ^ (a + b) * 4 * ((M' + ‖D.κ‖) * 4), ((a + b : ℕ) : ℝ) * kG + 2, ?_⟩
  intro s h1 h2 ht
  set t := s.im with ht_def
  have hu : 0 ≤ |t| := abs_nonneg _
  -- the factor `E`
  have hE : ‖D.Ez x s‖ ≤ (x ^ (-(1 / 2) : ℝ) + x ^ (2 : ℝ)) * (D.A ^ (-2 : ℝ) + D.A ^ (1 / 2 : ℝ))
      * (cG ^ (a + b) * Real.exp (((a + b : ℕ) : ℝ) * kG * |t|)) := by
    unfold Ez
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, D.norm_cpow_A]
    have e1 : x ^ s.re ≤ x ^ (-(1 / 2) : ℝ) + x ^ (2 : ℝ) := rpow_le_add_of_mem hx (by linarith) h2.le
    have e2 : D.A ^ (-s).re ≤ D.A ^ (-2 : ℝ) + D.A ^ (1 / 2 : ℝ) := by
      rw [Complex.neg_re]
      exact rpow_le_add_of_mem D.hA (by linarith) (by linarith)
    have e3 : ‖iG1 a b s‖ ≤ cG ^ (a + b) * Real.exp (((a + b : ℕ) : ℝ) * kG * |t|) := by
      have := norm_iG1_le a b h1.le h2.le ht
      refine le_trans this (le_of_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul, ht_def]
      ring_nf
    have hX : 0 ≤ x ^ (-(1 / 2) : ℝ) + x ^ (2 : ℝ) :=
      add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)
    exact mul_le_mul (mul_le_mul e1 e2 (Real.rpow_nonneg D.hA.le _) hX) e3 (norm_nonneg _)
      (mul_nonneg hX (add_nonneg (Real.rpow_nonneg D.hA.le _) (Real.rpow_nonneg D.hA.le _)))
  -- the factor `r`
  have hr : ‖rz α β s‖ ≤ 4 := norm_rz_le hα hα1 h1.le h2.le (by linarith)
  -- the factor `Lf s s (s-1) + κ`
  have hL : ‖D.Lf s * s * (s - 1) + D.κ‖ ≤ (M' + ‖D.κ‖) * (4 * Real.exp (2 * |t|)) := by
    have hLs : ‖D.Lf s‖ ≤ M' := le_trans (hM s h1.le h2.le) (le_max_left _ _)
    have hs1 : ‖s‖ ≤ 2 + |t| := by
      have := Complex.norm_le_abs_re_add_abs_im s
      have : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hs2 : ‖s - 1‖ ≤ 2 + |t| := by
      have := norm_add_ofReal_le s (-1)
      have h' : |s.re + -1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have e : s + ((-1 : ℝ) : ℂ) = s - 1 := by push_cast; ring
      rw [e] at this
      linarith
    have hM0 : 0 ≤ M' := le_max_right _ _
    have hsq : 1 ≤ (2 + |t|) ^ 2 := by nlinarith
    have hexp := two_add_sq_le_exp hu
    calc ‖D.Lf s * s * (s - 1) + D.κ‖ ≤ ‖D.Lf s‖ * ‖s‖ * ‖s - 1‖ + ‖D.κ‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, norm_mul]
      _ ≤ M' * (2 + |t|) * (2 + |t|) + ‖D.κ‖ * (2 + |t|) ^ 2 := by
          gcongr
          nlinarith [norm_nonneg D.κ]
      _ = (M' + ‖D.κ‖) * (2 + |t|) ^ 2 := by ring
      _ ≤ (M' + ‖D.κ‖) * (4 * Real.exp (2 * |t|)) := by
          gcongr
  -- the factor `1/(s+3)`
  have h3 : 1 ≤ ‖s + 3‖ := by
    have := Complex.abs_re_le_norm (s + 3)
    have e : (s + 3).re = s.re + 3 := by simp
    rw [e, abs_of_pos (by linarith)] at this
    linarith
  have hFle : ‖D.Fz α β x s‖ ≤ ‖D.Ez x s‖ * ‖rz α β s‖ * ‖D.Lf s * s * (s - 1) + D.κ‖ := by
    unfold Fz
    rw [norm_div, norm_mul, norm_mul]
    exact div_le_self (by positivity) h3
  have hK1 : 0 ≤ (x ^ (-(1 / 2) : ℝ) + x ^ (2 : ℝ)) * (D.A ^ (-2 : ℝ) + D.A ^ (1 / 2 : ℝ))
      * (cG ^ (a + b) * Real.exp (((a + b : ℕ) : ℝ) * kG * |t|)) := le_trans (norm_nonneg _) hE
  have hexp : Real.exp ((((a + b : ℕ) : ℝ) * kG + 2) * |t|)
      = Real.exp (((a + b : ℕ) : ℝ) * kG * |t|) * Real.exp (2 * |t|) := by
    rw [← Real.exp_add]; ring_nf
  refine le_trans hFle (le_trans (mul_le_mul (mul_le_mul hE hr (norm_nonneg _) hK1) hL
    (norm_nonneg _) (mul_nonneg hK1 (by norm_num))) (le_of_eq ?_))
  rw [hexp]
  ring

/-- The constant `C` of the Phragmén-Lindelöf bound on `F`. -/
noncomputable def Cz (_α β x : ℝ) : ℝ :=
  x ^ (2 : ℝ) * dserR D.ν 2 + x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * dserR D.μ (3 / 2) * (3 / (1 - 2 * β))

theorem Cz_nonneg {α β x : ℝ} (hβ : β < 1 / 2) (hx : 0 < x) : 0 ≤ D.Cz α β x := by
  unfold Cz
  have := Real.rpow_nonneg hx.le (-(1 / 2) : ℝ)
  have := Real.rpow_nonneg hx.le (2 : ℝ)
  have := Real.rpow_nonneg D.hA.le (2 : ℝ)
  have := dserR_nonneg D.μ D.hμ (3 / 2)
  have := dserR_nonneg D.ν D.hν 2
  have : 0 < 1 - 2 * β := by linarith
  positivity

/-- Phragmén-Lindelöf: `|F| ≤ C` on the closed strip `-1/2 ≤ Re s ≤ 2`. -/
theorem norm_Fz_le_strip {α β x : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2) (hx : 0 < x)
    {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 2) : ‖D.Fz α β x s‖ ≤ D.Cz α β x := by
  obtain ⟨K, k, hK⟩ := D.norm_Fz_growth (β := β) hα.le (by linarith) hx
  have hβ0 : 0 < β := by linarith
  have hC1 : 0 ≤ x ^ (2 : ℝ) * dserR D.ν 2 :=
    mul_nonneg (Real.rpow_nonneg hx.le _) (dserR_nonneg _ D.hν _)
  have hC2 : 0 ≤ x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * dserR D.μ (3 / 2) * (3 / (1 - 2 * β)) := by
    have := Real.rpow_nonneg hx.le (-(1 / 2) : ℝ)
    have := Real.rpow_nonneg D.hA.le (2 : ℝ)
    have := dserR_nonneg D.μ D.hμ (3 / 2)
    have : 0 < 1 - 2 * β := by linarith
    positivity
  refine norm_le_of_strip (σL := -1 / 2) (σR := 2) (by norm_num)
    (by linarith [Real.pi_gt_three]) (U := {s : ℂ | β - 1 < s.re})
    (fun s h1 _ => by show β - 1 < s.re; linarith) (D.differentiableOn_Fz hαβ.le hβ0.le hx)
    (T₁ := 2) hK ?_ ?_ h1 h2
  · intro s hs
    exact le_trans (D.norm_Fz_left_le (by linarith) hβ0 hβ hx s hs) (le_add_of_nonneg_left hC1)
  · intro s hs
    exact le_trans (D.norm_Fz_right_le hα.le (by linarith) hβ0.le hβ.le hx s hs)
      (le_add_of_nonneg_right hC2)

theorem add_ofReal_ne_zero_of_im {s : ℂ} (h : s.im ≠ 0) (c : ℝ) : s + c ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp at this
  exact h this

/-- Decay of `H` on the strip: `|H(s)| ≤ C · 2/t²` for `|t| ≥ 5`. -/
theorem norm_Hz_decay {α β x : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2) (hx : 0 < x)
    {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 2) (ht : 5 ≤ |s.im|) :
    ‖D.Hz α β x s‖ ≤ D.Cz α β x * (2 / s.im ^ 2) := by
  have him : s.im ≠ 0 := by
    intro h; rw [h, abs_zero] at ht; linarith
  have h0 : s ≠ 0 := by intro h; rw [h] at him; simp at him
  have h1' : s ≠ 1 := by intro h; rw [h] at him; simp at him
  have hb : s + β ≠ 0 := add_ofReal_ne_zero_of_im him β
  have h3 : s + 3 ≠ 0 := by
    have := add_ofReal_ne_zero_of_im him 3
    simpa using this
  rw [D.Hz_eq_Fz α β x h0 h1' hb h3, norm_mul, norm_div]
  have hβ0 : 0 ≤ β := by linarith
  exact mul_le_mul (D.norm_Fz_le_strip hα hαβ hβ hx h1 h2) (norm_div_cubic_le hβ0 h1 h2 ht)
    (by positivity) (D.Cz_nonneg hβ hx)

/-! ### Partial fractions and residues -/

/-- The three polar parts of `H`: `H = Φ₁/(s-1) + Φ₀/s + Φ_β/(s+β)`. -/
noncomputable def Φz (α β x : ℝ) (p : ℂ) (s : ℂ) : ℂ :=
  if p = 1 then D.κ * (D.Ez x s * rz α β s) / (1 + β)
  else if p = 0 then -(D.κ * (D.Ez x s * rz α β s)) / β
  else D.Ez x s * rz α β s * D.Lf s + D.κ * (D.Ez x s * rz α β s) / β
    - D.κ * (D.Ez x s * rz α β s) / (1 + β)

/-- The poles `1, 0, -β`. -/
noncomputable def Pz (β : ℝ) : Finset ℂ := {1, 0, -(β : ℂ)}

theorem negβ_ne_one {β : ℝ} (hβ : 0 < β) : (-(β : ℂ)) ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp at this; linarith

theorem negβ_ne_zero {β : ℝ} (hβ : 0 < β) : (-(β : ℂ)) ≠ 0 :=
  neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hβ.ne')

theorem sum_Pz {β : ℝ} (hβ : 0 < β) (f : ℂ → ℂ) :
    ∑ p ∈ Pz β, f p = f 1 + f 0 + f (-(β : ℂ)) := by
  unfold Pz
  have h1 : (1 : ℂ) ∉ ({0, -(β : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨one_ne_zero, (negβ_ne_one hβ).symm⟩
  have h2 : (0 : ℂ) ∉ ({-(β : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    exact (negβ_ne_zero hβ).symm
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  ring

theorem Φz_one (α β x : ℝ) : D.Φz α β x 1 = fun s => D.κ * (D.Ez x s * rz α β s) / (1 + β) := by
  funext s; simp [Φz]

theorem Φz_zero (α β x : ℝ) : D.Φz α β x 0 = fun s => -(D.κ * (D.Ez x s * rz α β s)) / β := by
  funext s; simp [Φz]

theorem Φz_negβ {α β x : ℝ} (hβ : 0 < β) : D.Φz α β x (-(β : ℂ)) = fun s =>
    D.Ez x s * rz α β s * D.Lf s + D.κ * (D.Ez x s * rz α β s) / β
      - D.κ * (D.Ez x s * rz α β s) / (1 + β) := by
  funext s; simp [Φz, negβ_ne_one hβ, negβ_ne_zero hβ]

theorem Hz_partial {α β x : ℝ} (hβ : 0 < β) (s : ℂ) (hs : s ∉ Pz β) :
    D.Hz α β x s = ∑ p ∈ Pz β, D.Φz α β x p s / (s - p) := by
  have hs1 : s ≠ 1 := fun h => hs (by simp [Pz, h])
  have hs0 : s ≠ 0 := fun h => hs (by simp [Pz, h])
  have hsb : s + β ≠ 0 := fun h => hs (by
    have : s = -(β : ℂ) := by linear_combination h
    simp [Pz, this])
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hb0 : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hb1 : (1 : ℂ) + β ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [sum_Pz hβ, D.Φz_one, D.Φz_zero, D.Φz_negβ hβ]
  simp only [sub_zero, sub_neg_eq_add]
  unfold Hz Λf
  rw [Rz_eq_rz_div]
  field_simp
  ring

theorem differentiableOn_Φz {α β x : ℝ} (hαβ : α ≤ β) (hx : 0 < x) (p : ℂ) :
    DifferentiableOn ℂ (D.Φz α β x p) {s : ℂ | β - 1 < s.re} := by
  have hE : DifferentiableOn ℂ (D.Ez x) {s : ℂ | β - 1 < s.re} :=
    (D.differentiable_Ez hx).differentiableOn
  have hr := differentiableOn_rz hαβ
  have hL : DifferentiableOn ℂ D.Lf {s : ℂ | β - 1 < s.re} := D.hLf.differentiableOn
  have hEr := hE.mul hr
  unfold Φz
  split_ifs
  · exact (hEr.const_mul D.κ).div_const _
  · exact (hEr.const_mul D.κ).neg.div_const _
  · exact ((hEr.mul hL).add ((hEr.const_mul D.κ).div_const _)).sub ((hEr.const_mul D.κ).div_const _)

/-- The residues at `1` and `0` cancel for Zimmert's choice of `x`. -/
theorem res_one_zero {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (hα1 : α < 1) :
    D.Φz α β (xz a b D.A α β) 1 1 + D.Φz α β (xz a b D.A α β) 0 0 = 0 := by
  have key := xz_residue a b D.hA hα hβ hβ1 hα1
  set x := xz a b D.A α β with hxdef
  rw [D.Φz_one, D.Φz_zero]
  beta_reduce
  set g1 : ℝ := (Real.Gamma (3 / 2))⁻¹ ^ a * (Real.Gamma 2)⁻¹ ^ b with hg1
  set g0 : ℝ := (Real.Gamma 1)⁻¹ ^ a * (Real.Gamma (3 / 2))⁻¹ ^ b with hg0
  have hi1 : iG1 a b 1 = (g1 : ℂ) := by
    have := iG1_ofReal a b 1
    rw [Complex.ofReal_one] at this
    rw [this, hg1]
    norm_num
  have hi0 : iG1 a b 0 = (g0 : ℂ) := by
    have := iG1_ofReal a b 0
    rw [Complex.ofReal_zero] at this
    rw [this, hg0]
    norm_num
  have hE1 : D.Ez x 1 = (x : ℂ) / (D.A : ℂ) * (g1 : ℂ) := by
    unfold Ez
    rw [cpow_one, cpow_neg_one, hi1]
    ring
  have hE0 : D.Ez x 0 = (g0 : ℂ) := by
    unfold Ez
    rw [cpow_zero, neg_zero, cpow_zero, hi0]
    ring
  have hr1 : rz α β 1 = (1 + (α : ℂ)) / ((2 - (β : ℂ)) * (2 - (α : ℂ))) := by
    unfold rz
    ring
  have hr0 : rz α β 0 = (α : ℂ) / ((1 - (β : ℂ)) * (1 - (α : ℂ))) := by
    unfold rz
    ring
  have keyC : ((x / D.A * g1 * ((1 + α) / ((2 - β) * (2 - α))) / (1 + β) : ℝ) : ℂ)
      = ((g0 * (α / ((1 - β) * (1 - α))) / β : ℝ) : ℂ) := by
    rw [key]
  push_cast at keyC
  rw [hE1, hE0, hr1, hr0]
  linear_combination D.κ * keyC

/-- The value of the residue at `-β` (a real number). -/
noncomputable def Pbz (α β x : ℝ) : ℝ :=
  x ^ (-β) * D.A ^ (1 + 2 * β) * Tz a b β * ((α - β) / ((1 - 2 * β) * (1 - α - β)))
    * dserR D.μ (1 + β)

theorem res_negβ {α β x : ℝ} (hβ : 0 < β) (hx : 0 < x) :
    D.Φz α β x (-(β : ℂ)) (-(β : ℂ)) = ((D.Pbz α β x : ℝ) : ℂ) := by
  rw [D.Φz_negβ hβ]
  beta_reduce
  have hΛ : D.Lf (-(β : ℂ)) + D.κ / β - D.κ / (1 + β) = D.Λf (-(β : ℂ)) := by
    unfold Λf
    rw [div_neg, show -(β : ℂ) - 1 = -(1 + β) by ring, div_neg]
    ring
  have hΛg : D.Λf (-(β : ℂ)) = (D.A : ℂ) ^ ((1 + β : ℝ) : ℂ) * Gz a b ((1 + β : ℝ) : ℂ)
      * dser D.μ ((1 + β : ℝ) : ℂ) := by
    rw [D.Λf_eq_Λg, show (1 : ℂ) - -(β : ℂ) = ((1 + β : ℝ) : ℂ) by push_cast; ring]
    exact D.hdg _ (by simp; linarith)
  have hsplit : D.Ez x (-(β : ℂ)) * rz α β (-(β : ℂ)) * D.Lf (-(β : ℂ))
      + D.κ * (D.Ez x (-(β : ℂ)) * rz α β (-(β : ℂ))) / β
      - D.κ * (D.Ez x (-(β : ℂ)) * rz α β (-(β : ℂ))) / (1 + β)
      = D.Ez x (-(β : ℂ)) * rz α β (-(β : ℂ)) * (D.Lf (-(β : ℂ)) + D.κ / β - D.κ / (1 + β)) := by
    ring
  rw [hsplit, hΛ, hΛg]
  have h1 : (x : ℂ) ^ (-(β : ℂ)) = ((x ^ (-β) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx.le, Complex.ofReal_neg]
  have h2 : (D.A : ℂ) ^ (-(-(β : ℂ))) = ((D.A ^ β : ℝ) : ℂ) := by
    rw [neg_neg, Complex.ofReal_cpow D.hA.le]
  have h3 : iG1 a b (-(β : ℂ))
      = (((Real.Gamma (1 - β / 2))⁻¹ ^ a * (Real.Gamma ((3 - β) / 2))⁻¹ ^ b : ℝ) : ℂ) := by
    have := iG1_ofReal a b (-β)
    rw [Complex.ofReal_neg] at this
    rw [this, show -β / 2 + 1 = 1 - β / 2 by ring, show (-β + 3) / 2 = (3 - β) / 2 by ring]
  have h4 : rz α β (-(β : ℂ)) = (((α - β) / ((1 - 2 * β) * (1 - α - β)) : ℝ) : ℂ) := by
    unfold rz
    push_cast
    ring
  have h5 : (D.A : ℂ) ^ ((1 + β : ℝ) : ℂ) = ((D.A ^ (1 + β) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow D.hA.le _).symm
  have h6 := Gz_ofReal a b (1 + β)
  have h7 := dser_ofReal D.μ D.hμ (1 + β)
  unfold Ez
  rw [h1, h2, h3, h4, h5, h6, h7]
  have hreal : x ^ (-β) * D.A ^ β * ((Real.Gamma (1 - β / 2))⁻¹ ^ a * (Real.Gamma ((3 - β) / 2))⁻¹ ^ b)
      * ((α - β) / ((1 - 2 * β) * (1 - α - β)))
      * (D.A ^ (1 + β) * (Real.Gamma ((1 + β) / 2) ^ a * Real.Gamma ((1 + β + 1) / 2) ^ b)
        * dserR D.μ (1 + β)) = D.Pbz α β x := by
    have hA2 : D.A ^ (1 + 2 * β) = D.A ^ β * D.A ^ (1 + β) := by
      rw [← Real.rpow_add D.hA]; ring_nf
    unfold Pbz Tz
    rw [hA2, show (1 + β + 1) / 2 = 1 + β / 2 by ring]
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring
  rw [← hreal]
  push_cast
  ring

/-! ### Zimmert's Satz 1 at fixed `β` -/

/-- **Zimmert's Satz 1 at `γ = 1/2`, fixed `β`.** For `a ≥ 1`, `0 < α < β < 1/2` and
`x = xz a b A α β`:
`x^{-β} A^{1+2β} (β-α) T_β D_μ(1+β) / (1-α-β) ≤ x^{-1/2} A² D_μ(3/2)`. -/
theorem satz1_beta (ha : 1 ≤ a) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < 1 / 2) :
    xz a b D.A α β ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β * dserR D.μ (1 + β)
        / (1 - α - β)
      ≤ xz a b D.A α β ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * dserR D.μ (3 / 2) := by
  have hβ0 : 0 < β := lt_trans hα hαβ
  have hx : 0 < xz a b D.A α β := xz_pos a b D.hA hα hβ0 (by linarith) (by linarith)
  set x := xz a b D.A α β with hxdef
  set U : Set ℂ := {s : ℂ | β - 1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hstripU : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → s ∈ U := fun s h1 _ => by
    show β - 1 < s.re
    linarith
  have hΦ : ∀ p ∈ Pz β, DifferentiableOn ℂ (D.Φz α β x p) U :=
    fun p _ => D.differentiableOn_Φz hαβ.le hx p
  have hP : ∀ p ∈ Pz β, (-1 / 2 : ℝ) < p.re ∧ p.re < 2 ∧ p.im = 0 := by
    intro p hp
    simp only [Pz, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · norm_num
    · norm_num
    · simp; constructor <;> linarith
  have hH : ∀ s : ℂ, s ∉ Pz β → D.Hz α β x s = ∑ p ∈ Pz β, D.Φz α β x p s / (s - p) :=
    fun s hs => D.Hz_partial hβ0 s hs
  have hPre : ∀ σ : ℝ, (σ = 2 ∨ σ = -1 / 2) → ∀ p ∈ Pz β, p.re ≠ σ := by
    intro σ hσ p hp
    simp only [Pz, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> rcases hσ with rfl | rfl <;> simp <;> linarith
  have hlineU : ∀ σ : ℝ, (σ = 2 ∨ σ = -1 / 2) → ∀ t : ℝ, (σ : ℂ) + t * I ∈ U := by
    intro σ hσ t
    show β - 1 < ((σ : ℂ) + t * I).re
    simp
    rcases hσ with rfl | rfl <;> linarith
  have hcontR := continuous_line_of_sum (Pz β) (D.Φz α β x) hΦ hH (hlineU 2 (Or.inl rfl))
    (hPre 2 (Or.inl rfl))
  have hcontL := continuous_line_of_sum (Pz β) (D.Φz α β x) hΦ hH (hlineU (-1 / 2) (Or.inr rfl))
    (hPre (-1 / 2) (Or.inr rfl))
  -- the right line
  have hbR : ∀ t : ℝ, ‖D.Hz α β x (((2 : ℝ) : ℂ) + t * I)‖
      ≤ x ^ (2 : ℝ) * dserR D.ν 2 * (1 / ((2 + β) ^ 2 + t ^ 2)) := by
    intro t
    have := D.norm_Hz_right_le hα.le (by linarith) hβ0.le hβ.le hx (((2 : ℝ) : ℂ) + t * I)
      (by simp)
    simpa using this
  have hintR : Integrable fun t : ℝ => D.Hz α β x (((2 : ℝ) : ℂ) + t * I) :=
    Integrable.mono' ((zf_integrable_one_div_sq_add_sq (c := 2 + β) (by linarith)).const_mul _)
      hcontR.aestronglyMeasurable (Filter.Eventually.of_forall hbR)
  -- the left line
  set Cst := x ^ (-(1 / 2) : ℝ) * D.A ^ (2 : ℝ) * dserR D.μ (3 / 2) with hCst
  have hbL : ∀ t : ℝ, ‖D.Hz α β x (((-1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ Cst * (1 / ((1 / 2 - β) ^ 2 + t ^ 2)) := by
    intro t
    have := D.norm_Hz_left_le (α := α) (by linarith) hβ hx (((-1 / 2 : ℝ) : ℂ) + t * I) (by simp)
    rw [hCst]
    simpa using this
  have hintL : Integrable fun t : ℝ => D.Hz α β x (((-1 / 2 : ℝ) : ℂ) + t * I) :=
    Integrable.mono' ((zf_integrable_one_div_sq_add_sq (c := 1 / 2 - β) (by linarith)).const_mul _)
      hcontL.aestronglyMeasurable (Filter.Eventually.of_forall hbL)
  -- horizontal decay
  have hC0 := D.Cz_nonneg (α := α) hβ hx
  have hhor : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ y : ℝ, (-1 / 2 : ℝ) ≤ y → y ≤ 2 →
      ‖D.Hz α β x (y + T * I)‖ ≤ ε ∧ ‖D.Hz α β x (y + (-T) * I)‖ ≤ ε := by
    intro ε hε
    refine ⟨5 + 2 * D.Cz α β x / ε, fun T hT y hy1 hy2 => ?_⟩
    have hq : 0 ≤ 2 * D.Cz α β x / ε := by positivity
    have hT5 : 5 ≤ T := by linarith
    have hT2 : 2 * D.Cz α β x ≤ ε * T := by
      have : 2 * D.Cz α β x / ε ≤ T := by linarith
      rw [div_le_iff₀ hε] at this
      linarith
    have hfin : D.Cz α β x * (2 / T ^ 2) ≤ ε := by
      rw [show D.Cz α β x * (2 / T ^ 2) = 2 * D.Cz α β x / T ^ 2 by ring,
        div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ T - 1) (by positivity : (0 : ℝ) ≤ ε * T)]
    constructor
    · have h := D.norm_Hz_decay hα hαβ hβ hx (s := (y : ℂ) + T * I) (by simpa using hy1)
        (by simpa using hy2) (by simp; rw [abs_of_pos (by linarith)]; exact hT5)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im] at h
      refine le_trans h (le_of_eq_of_le ?_ hfin)
      ring_nf
    · have h := D.norm_Hz_decay hα hαβ hβ hx (s := (y : ℂ) + (-T : ℝ) * I) (by simpa using hy1)
        (by simpa using hy2) (by simp; rw [abs_of_pos (by linarith)]; exact hT5)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im] at h
      have e : ((-T : ℝ) : ℂ) = -(T : ℂ) := by push_cast; ring
      rw [e] at h
      refine le_trans (by simpa using h) (le_of_eq_of_le ?_ hfin)
      ring_nf
  -- the contour shift
  have hcs := contour_shift (σL := -1 / 2) (σR := 2) (by norm_num) hUo hstripU (Pz β)
    (D.Φz α β x) hΦ hP (D.Hz α β x) hH hintR hintL hhor
  rw [sum_Pz hβ0, D.res_one_zero hα hβ0 (by linarith) (by linarith), zero_add,
    D.res_negβ hβ0 hx] at hcs
  -- positivity of the right integral
  have hposR : 0 ≤ (∫ t : ℝ, D.Hz α β x (((2 : ℝ) : ℂ) + t * I)).re := by
    have heq : (fun t : ℝ => D.Hz α β x (((2 : ℝ) : ℂ) + t * I)) = fun t : ℝ =>
        (x : ℂ) ^ ((2 : ℂ) + t * I) *
          (Rz α β (2 + t * I) * (2 / (2 + t * I)) ^ a * (2 / (2 + t * I + 1)) ^ b) *
            dser D.ν (2 + t * I) := by
      funext t
      rw [D.Hz_right α β x _ (by simp)]
      simp only [Complex.ofReal_ofNat]
    rw [heq]
    exact re_integral_right_nonneg a b ha hα.le (by linarith) hβ0.le (by linarith) hx D.ν D.hν
      (D.hνs 2 (by norm_num))
  -- bound of the left integral
  have hnormL : ‖∫ t : ℝ, D.Hz α β x (((-1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ Cst * (Real.pi / (1 / 2 - β)) := by
    refine le_trans (norm_integral_le_of_norm_le
      ((zf_integrable_one_div_sq_add_sq (c := 1 / 2 - β) (by linarith)).const_mul _)
      (Filter.Eventually.of_forall hbL)) (le_of_eq ?_)
    rw [integral_const_mul, zf_integral_one_div_sq_add_sq (by linarith)]
  -- combine
  have hre := congrArg Complex.re hcs
  rw [Complex.sub_re] at hre
  have hre2 : (2 * (Real.pi : ℂ) * ((D.Pbz α β x : ℝ) : ℂ)).re = 2 * Real.pi * D.Pbz α β x := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * ((D.Pbz α β x : ℝ) : ℂ)
      = ((2 * Real.pi * D.Pbz α β x : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [hre2] at hre
  have hLre : (∫ t : ℝ, D.Hz α β x (((-1 / 2 : ℝ) : ℂ) + t * I)).re ≤ Cst * (Real.pi / (1 / 2 - β)) :=
    le_trans (Complex.re_le_norm _) hnormL
  have hmain : 0 ≤ Cst * (Real.pi / (1 / 2 - β)) + 2 * Real.pi * D.Pbz α β x := by linarith
  set Y := x ^ (-β) * D.A ^ (1 + 2 * β) * Tz a b β * dserR D.μ (1 + β) with hY
  have h12 : 0 < 1 - 2 * β := by linarith
  have h1ab : 0 < 1 - α - β := by linarith
  have hkey : Cst * (Real.pi / (1 / 2 - β)) + 2 * Real.pi * D.Pbz α β x
      = (2 * Real.pi / (1 - 2 * β)) * (Cst - Y * (β - α) / (1 - α - β)) := by
    unfold Pbz
    rw [hY]
    field_simp
    ring
  rw [hkey] at hmain
  have hpos : 0 < 2 * Real.pi / (1 - 2 * β) := by positivity
  have hfin := (mul_nonneg_iff_of_pos_left hpos).mp hmain
  have hgoal : x ^ (-β) * D.A ^ (1 + 2 * β) * (β - α) * Tz a b β * dserR D.μ (1 + β)
      / (1 - α - β) = Y * (β - α) / (1 - α - β) := by
    rw [hY]; ring
  rw [hgoal]
  linarith

end ZData

end FurioLombardo.M2.Zimmert
