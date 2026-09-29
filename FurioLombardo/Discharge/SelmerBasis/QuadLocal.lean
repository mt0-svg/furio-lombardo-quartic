import FurioLombardo.Discharge.SelmerBasis.QuadField
import FurioLombardo.Discharge.SelmerBasis.LocalLemmas

/-!
# Quadratic components as local fields

For a complete ultrametric field `K` with a norm uniformizer `π` (`NormUnif π`) and residue field
`𝔽₂`, the two shapes of quadratic components used at the places of the Selmer bound,
with the spectral norm of `QF`:

* **Eisenstein**, `QF K A B` with `‖A‖ = ‖π‖`, `‖B‖ < 1` (`Y² = A + B Y`): `‖x + y Y‖ =
  max ‖x‖ (‖y‖ ‖Y‖)` with `‖Y‖² = ‖π‖` (`qfE_norm`, `qfE_norm_Y`), `Y` is a norm uniformizer
  (`qfE_normUnif`), the residue field is still `𝔽₂` (`qfE_res`), `‖2‖ = ‖Y‖ ^ (2 e)` (`qfE_two`);
  `X² - B X - A` has no root in `K` (`no_root_eisen`).
* **Unramified**, `QF K (-1) 1` (`ω² = ω - 1`): `‖x + y ω‖ = max ‖x‖ ‖y‖` (`qfU_norm`), `π` stays a
  norm uniformizer (`qfU_normUnif`), the residue field is `𝔽₄ = 𝔽₂(ω̄)` (`qfU_res`, `qfU_omega`),
  `‖2‖` is unchanged (`qfU_two`).

These give the hypotheses of `compOK_F2`, `compOK_F4`, `sb_span_dyadic` at a quadratic component.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open QF

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

theorem qf_mk_re_im (A B : K) (z : QF K A B) : QF.mk K A B (z : QuadraticAlgebra K A B).re
    (z : QuadraticAlgebra K A B).im = z := rfl

theorem max_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : max a b ^ 2 = max (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ ha h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hb h 2)]

/-- The norm of `x + y Y` from the norm form. -/
theorem qf_norm_mk (A B : K) [Fact (∀ r : K, r ^ 2 ≠ A + B * r)] (x y : K) :
    ‖QF.mk K A B x y‖ ^ 2 = ‖x ^ 2 + B * x * y - A * y ^ 2‖ := by
  rw [QF.norm_sq, QF.qnorm]
  show ‖QuadraticAlgebra.norm ((⟨x, y⟩ : QuadraticAlgebra K A B))‖ = _
  rw [QuadraticAlgebra.norm_def]
  congr 1
  ring

/-! ## Eisenstein components -/

/-- **The Eisenstein norm form**: `‖x² + B x y - A y²‖ = max (‖x‖²) (‖π‖ ‖y‖²)`. The two terms have
norms of different parity in the exponent of `‖π‖`, and the cross term is smaller than both. -/
theorem qfE_norm_form {π A B : K} (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (x y : K) :
    ‖x ^ 2 + B * x * y - A * y ^ 2‖ = max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) := by
  have hp0 : 0 < ‖π‖ := norm_pos_iff.mpr hπ.ne_zero
  have hp1 : ‖π‖ < 1 := hπ.norm_lt_one
  have hAy : ‖A * y ^ 2‖ = ‖π‖ * ‖y‖ ^ 2 := by rw [norm_mul, norm_pow, hA]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : (0 : K) ^ 2 + B * 0 * y - A * y ^ 2 = -(A * y ^ 2) := by ring
    rw [h0, norm_neg, hAy, norm_zero, zero_pow two_ne_zero, max_eq_right (by positivity)]
  obtain ⟨m, hm⟩ := hπ.disc x hx
  obtain ⟨n, hn⟩ := hπ.disc y hy
  have ha : ‖x‖ ^ 2 = ‖π‖ ^ (2 * m) := by
    rw [hm, ← zpow_natCast, ← zpow_mul]
    ring_nf
  have hb : ‖π‖ * ‖y‖ ^ 2 = ‖π‖ ^ (2 * n + 1) := by
    rw [hn, ← zpow_natCast, ← zpow_mul, zpow_add_one₀ hp0.ne']
    ring_nf
  have hne : ‖x ^ 2‖ ≠ ‖-(A * y ^ 2)‖ := by
    rw [norm_neg, hAy, norm_pow, ha, hb]
    intro h
    have := (zpow_right_inj₀ hp0 hp1.ne).mp h
    omega
  have h1 : ‖x ^ 2 - A * y ^ 2‖ = max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, hAy,
      norm_pow]
  have hxy : ‖x‖ * ‖y‖ ≤ max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) := by
    have hxy' : ‖x‖ * ‖y‖ = ‖π‖ ^ (m + n) := by rw [hm, hn, zpow_add₀ hp0.ne']
    rw [hxy', ha, hb]
    rcases le_or_gt m n with h | h
    · exact le_max_of_le_left (zpow_le_zpow_right_of_le_one₀ hp0 hp1.le (by omega))
    · exact le_max_of_le_right (zpow_le_zpow_right_of_le_one₀ hp0 hp1.le (by omega))
  have hM : 0 < max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) :=
    lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hx) 2) (le_max_left _ _)
  have h2 : ‖B * x * y‖ < max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) := by
    rw [norm_mul, norm_mul, mul_assoc]
    calc ‖B‖ * (‖x‖ * ‖y‖) ≤ ‖B‖ * max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) := by gcongr
      _ < 1 * max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) := mul_lt_mul_of_pos_right hB hM
      _ = max (‖x‖ ^ 2) (‖π‖ * ‖y‖ ^ 2) := one_mul _
  have hd : x ^ 2 + B * x * y - A * y ^ 2 = (x ^ 2 - A * y ^ 2) + B * x * y := by ring
  rw [hd, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact (ne_of_lt h2).symm),
    h1]
  exact max_eq_left h2.le

/-- `X² - B X - A` has no root in `K`. -/
theorem no_root_eisen {π A B : K} (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) :
    ∀ r : K, r ^ 2 ≠ A + B * r := by
  intro r hr
  have h := qfE_norm_form hπ hA hB r (-1)
  have h0 : r ^ 2 + B * r * (-1) - A * (-1) ^ 2 = 0 := by rw [hr]; ring
  rw [h0, norm_zero] at h
  have hpos : 0 < ‖π‖ * ‖(-1 : K)‖ ^ 2 := by
    rw [norm_neg, norm_one, one_pow, mul_one]
    exact norm_pos_iff.mpr hπ.ne_zero
  exact absurd h (ne_of_lt (lt_of_lt_of_le hpos (le_max_right _ _)))

section Eisenstein

variable {π A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]

theorem qfE_norm_Y (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) :
    ‖QF.mk K A B 0 1‖ ^ 2 = ‖π‖ := by
  rw [qf_norm_mk, qfE_norm_form hπ hA hB]
  simp

theorem qfE_norm (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (x y : K) :
    ‖QF.mk K A B x y‖ = max ‖x‖ (‖y‖ * ‖QF.mk K A B 0 1‖) := by
  have h1 := qf_norm_mk A B x y
  rw [qfE_norm_form hπ hA hB, ← qfE_norm_Y hπ hA hB] at h1
  have h2 : max (‖x‖ ^ 2) (‖QF.mk K A B 0 1‖ ^ 2 * ‖y‖ ^ 2) =
      (max ‖x‖ (‖y‖ * ‖QF.mk K A B 0 1‖)) ^ 2 := by
    rw [max_sq_of_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    ring_nf
  rw [h2] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (le_max_of_le_left (norm_nonneg _))).1 h1

theorem qfE_Y_pos (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) :
    0 < ‖QF.mk K A B 0 1‖ := by
  have h := qfE_norm_Y hπ hA hB
  have hp0 : 0 < ‖π‖ := norm_pos_iff.mpr hπ.ne_zero
  rcases (norm_nonneg (QF.mk K A B 0 1)).lt_or_eq with h1 | h1
  · exact h1
  · rw [← h1] at h
    have h0 : (0 : ℝ) = ‖π‖ := by simpa using h
    linarith

theorem qfE_Y_lt_one (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) :
    ‖QF.mk K A B 0 1‖ < 1 := by
  by_contra h
  have h1 : 1 ≤ ‖QF.mk K A B 0 1‖ ^ 2 := one_le_pow₀ (not_lt.mp h)
  rw [qfE_norm_Y hπ hA hB] at h1
  exact absurd hπ.norm_lt_one (not_lt.mpr h1)

theorem qfE_pow_eq (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (n : ℤ) :
    ‖π‖ ^ n = ‖QF.mk K A B 0 1‖ ^ (2 * n) := by
  rw [← qfE_norm_Y hπ hA hB, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem qf_mk_zero_zero : QF.mk K A B 0 0 = 0 := rfl

theorem qf_mk_sub_one (x y : K) : QF.mk K A B x y - 1 = QF.mk K A B (x - 1) y := by
  show (⟨x, y⟩ : QuadraticAlgebra K A B) - 1 = ⟨x - 1, y⟩
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- `Y` is a norm uniformizer of the Eisenstein component. -/
theorem qfE_normUnif (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) :
    NormUnif (QF.mk K A B 0 1) := by
  have hY0 := qfE_Y_pos hπ hA hB
  refine ⟨norm_pos_iff.mp hY0, qfE_Y_lt_one hπ hA hB, ?_⟩
  intro z hz
  rw [← qf_mk_re_im A B z] at hz ⊢
  set x := (z : QuadraticAlgebra K A B).re
  set y := (z : QuadraticAlgebra K A B).im
  rw [qfE_norm hπ hA hB]
  rcases eq_or_ne y 0 with hy | hy
  · have hx : x ≠ 0 := by
      rintro hx
      apply hz
      rw [hx, hy]
      rfl
    obtain ⟨m, hm⟩ := hπ.disc x hx
    refine ⟨2 * m, ?_⟩
    rw [hy, norm_zero, zero_mul, max_eq_left (norm_nonneg _), hm, qfE_pow_eq hπ hA hB]
  obtain ⟨n, hn⟩ := hπ.disc y hy
  have hyY : ‖y‖ * ‖QF.mk K A B 0 1‖ = ‖QF.mk K A B 0 1‖ ^ (2 * n + 1) := by
    rw [hn, qfE_pow_eq hπ hA hB, zpow_add_one₀ hY0.ne']
  rcases eq_or_ne x 0 with hx | hx
  · refine ⟨2 * n + 1, ?_⟩
    rw [hx, norm_zero, max_eq_right (by positivity), hyY]
  obtain ⟨m, hm⟩ := hπ.disc x hx
  rw [hm, qfE_pow_eq hπ hA hB, hyY]
  rcases le_total (‖QF.mk K A B 0 1‖ ^ (2 * m)) (‖QF.mk K A B 0 1‖ ^ (2 * n + 1)) with h | h
  · exact ⟨2 * n + 1, max_eq_right h⟩
  · exact ⟨2 * m, max_eq_left h⟩

/-- The residue field of the Eisenstein component is `𝔽₂`. -/
theorem qfE_res (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1)
    (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) :
    ∀ z : QF K A B, ‖z‖ ≤ 1 → ‖z‖ < 1 ∨ ‖z - 1‖ < 1 := by
  intro z hz
  rw [← qf_mk_re_im A B z] at hz ⊢
  set x := (z : QuadraticAlgebra K A B).re
  set y := (z : QuadraticAlgebra K A B).im
  have hY0 := qfE_Y_pos hπ hA hB
  have hY1 := qfE_Y_lt_one hπ hA hB
  rw [qfE_norm hπ hA hB] at hz
  have hx1 : ‖x‖ ≤ 1 := le_trans (le_max_left _ _) hz
  have hyY1 : ‖y‖ * ‖QF.mk K A B 0 1‖ ≤ 1 := le_trans (le_max_right _ _) hz
  -- `‖y‖ ≤ 1`, so the `y` term is `< 1`
  have hy1 : ‖y‖ ≤ 1 := by
    by_contra hgt
    have hgt := not_le.mp hgt
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hgt
      linarith
    obtain ⟨n, hn⟩ := hπ.disc y hy0
    rw [hn, qfE_pow_eq hπ hA hB] at hgt hyY1
    have hn0 : 2 * n < 0 := by
      by_contra hn0
      have := zpow_le_one₀ hY0 hY1.le (not_lt.mp hn0)
      linarith
    have hle : 2 * n + 1 ≤ -1 := by omega
    rw [← zpow_add_one₀ hY0.ne'] at hyY1
    have h2 : ‖QF.mk K A B 0 1‖ ^ (-1 : ℤ) ≤ ‖QF.mk K A B 0 1‖ ^ (2 * n + 1) :=
      zpow_le_zpow_right_of_le_one₀ hY0 hY1.le hle
    rw [zpow_neg_one] at h2
    have h3 : 1 < ‖QF.mk K A B 0 1‖⁻¹ := one_lt_inv₀ hY0 |>.mpr hY1
    linarith
  have hyY : ‖y‖ * ‖QF.mk K A B 0 1‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left hY0.le hy1) hY1
  rcases hres x hx1 with h | h
  · left
    rw [qfE_norm hπ hA hB]
    exact max_lt h hyY
  · right
    rw [qf_mk_sub_one, qfE_norm hπ hA hB]
    exact max_lt h hyY
theorem qfE_two (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) {e : ℕ}
    (h2 : ‖(2 : K)‖ = ‖π‖ ^ e) : ‖(2 : QF K A B)‖ = ‖QF.mk K A B 0 1‖ ^ (2 * e) := by
  have h : (2 : QF K A B) = algebraMap K (QF K A B) 2 := (map_ofNat _ 2).symm
  rw [h, QF.norm_algebraMap, h2, pow_mul, qfE_norm_Y hπ hA hB]

end Eisenstein

/-! ## Unramified components -/

section UnramifiedForm

variable (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) {A B : K} (hA : ‖A + 1‖ < 1)
  (hB : ‖B - 1‖ < 1)
include hres hA hB

/-- **The unramified norm form**: `‖x² + B x y - A y²‖ = max ‖x‖ ‖y‖ ^ 2` when `A ≡ -1` and
`B ≡ 1`: a perturbation of `x² + x y + y²`, whose reduction has no root in `𝔽₂`. -/
theorem qfU_norm_form (x y : K) : ‖x ^ 2 + B * x * y - A * y ^ 2‖ = max ‖x‖ ‖y‖ ^ 2 := by
  have h0 := norm_sq_add_mul_add_sq hres x y
  have hd : x ^ 2 + B * x * y - A * y ^ 2 =
      (x ^ 2 + x * y + y ^ 2) + ((B - 1) * x * y - (A + 1) * y ^ 2) := by ring
  set M := max ‖x‖ ‖y‖
  rcases eq_or_ne M 0 with hm | hm
  · have hx : x = 0 := norm_eq_zero.mp (le_antisymm (hm ▸ le_max_left _ _) (norm_nonneg _))
    have hy : y = 0 := norm_eq_zero.mp (le_antisymm (hm ▸ le_max_right _ _) (norm_nonneg _))
    subst hx hy
    simp [M]
  have hM : 0 < M ^ 2 := by
    have : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
    positivity
  have hxy : ‖x‖ * ‖y‖ ≤ M ^ 2 := by
    rw [sq]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _)
      (le_max_of_le_left (norm_nonneg _))
  have hyy : ‖y‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
  have h1 : ‖(B - 1) * x * y‖ < M ^ 2 := by
    rw [norm_mul, norm_mul, mul_assoc]
    calc ‖B - 1‖ * (‖x‖ * ‖y‖) ≤ ‖B - 1‖ * M ^ 2 := by gcongr
      _ < 1 * M ^ 2 := mul_lt_mul_of_pos_right hB hM
      _ = M ^ 2 := one_mul _
  have h2 : ‖(A + 1) * y ^ 2‖ < M ^ 2 := by
    rw [norm_mul, norm_pow]
    calc ‖A + 1‖ * ‖y‖ ^ 2 ≤ ‖A + 1‖ * M ^ 2 := by gcongr
      _ < 1 * M ^ 2 := mul_lt_mul_of_pos_right hA hM
      _ = M ^ 2 := one_mul _
  have hs : ‖(B - 1) * x * y - (A + 1) * y ^ 2‖ < M ^ 2 := by
    rw [sub_eq_add_neg]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 (by rw [norm_neg]; exact h2))
  rw [hd, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h0]; exact (ne_of_lt hs).symm),
    h0, max_eq_left (le_of_lt (by rw [← h0] at hs ⊢; exact hs))]

/-- `X² - B X - A` has no root in `K`. -/
theorem no_root_unram' : ∀ r : K, r ^ 2 ≠ A + B * r := by
  intro r hr
  have h := qfU_norm_form hres hA hB r (-1)
  have h0 : r ^ 2 + B * r * (-1) - A * (-1) ^ 2 = 0 := by rw [hr]; ring
  rw [h0, norm_zero, norm_neg, norm_one] at h
  have : (0 : ℝ) < max ‖r‖ 1 ^ 2 := by
    have : (1 : ℝ) ≤ max ‖r‖ 1 := le_max_right _ _
    positivity
  exact absurd h (ne_of_lt this)

end UnramifiedForm

section Unramified

variable {A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]

theorem qfU_norm (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (hA : ‖A + 1‖ < 1)
    (hB : ‖B - 1‖ < 1) (x y : K) : ‖QF.mk K A B x y‖ = max ‖x‖ ‖y‖ := by
  have h1 := qf_norm_mk A B x y
  rw [qfU_norm_form hres hA hB] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (le_max_of_le_left (norm_nonneg _))).1 h1

/-- `π` stays a norm uniformizer in the unramified component. -/
theorem qfU_normUnif {π : K} (hπ : NormUnif π)
    (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (hA : ‖A + 1‖ < 1) (hB : ‖B - 1‖ < 1) :
    NormUnif (algebraMap K (QF K A B) π) := by
  refine ⟨?_, by rw [QF.norm_algebraMap]; exact hπ.norm_lt_one, ?_⟩
  · intro h
    have := congrArg norm h
    rw [QF.norm_algebraMap, norm_zero] at this
    exact hπ.ne_zero (norm_eq_zero.mp this)
  intro z hz
  rw [QF.norm_algebraMap]
  rw [← qf_mk_re_im A B z] at hz ⊢
  set x := (z : QuadraticAlgebra K A B).re
  set y := (z : QuadraticAlgebra K A B).im
  rw [qfU_norm hres hA hB]
  rcases eq_or_ne y 0 with hy | hy
  · have hx : x ≠ 0 := by
      rintro hx
      apply hz
      rw [hx, hy]
      rfl
    obtain ⟨m, hm⟩ := hπ.disc x hx
    exact ⟨m, by rw [hy, norm_zero, max_eq_left (norm_nonneg _), hm]⟩
  obtain ⟨n, hn⟩ := hπ.disc y hy
  rcases eq_or_ne x 0 with hx | hx
  · exact ⟨n, by rw [hx, norm_zero, max_eq_right (norm_nonneg _), hn]⟩
  obtain ⟨m, hm⟩ := hπ.disc x hx
  rw [hm, hn]
  rcases le_total (‖π‖ ^ m) (‖π‖ ^ n) with h | h
  · exact ⟨n, max_eq_right h⟩
  · exact ⟨m, max_eq_left h⟩

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem qf_mk_sub_nat (x y : K) (a b : ℕ) :
    QF.mk K A B x y - ((a : QF K A B) + (b : QF K A B) * QF.mk K A B 0 1) =
      QF.mk K A B (x - a) (y - b) := by
  show (⟨x, y⟩ : QuadraticAlgebra K A B) - ((a : QuadraticAlgebra K A B) +
    (b : QuadraticAlgebra K A B) * ⟨0, 1⟩) = ⟨x - a, y - b⟩
  ext <;> simp

/-- The residue field of the unramified component is `𝔽₂(Ȳ)`. -/
theorem qfU_res {π : K} (hπ : NormUnif π) (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1)
    (hA : ‖A + 1‖ < 1) (hB : ‖B - 1‖ < 1) :
    ∀ z : QF K A B, ‖z‖ ≤ 1 → ∃ a b : ZMod 2,
      ‖z - (((a.val : ℕ) : QF K A B) + ((b.val : ℕ) : QF K A B) * QF.mk K A B 0 1)‖ < 1 := by
  intro z hz
  rw [← qf_mk_re_im A B z] at hz ⊢
  set x := (z : QuadraticAlgebra K A B).re
  set y := (z : QuadraticAlgebra K A B).im
  rw [qfU_norm hres hA hB] at hz
  have hdig : ∀ t : K, ‖t‖ ≤ 1 → ∃ c : ZMod 2, ‖t - ((c.val : ℕ) : K)‖ < 1 := by
    intro t ht
    rcases hres t ht with h | h
    · exact ⟨0, by rw [show (0 : ZMod 2).val = 0 from rfl, Nat.cast_zero, sub_zero]; exact h⟩
    · exact ⟨1, by rw [show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one]; exact h⟩
  obtain ⟨a, ha⟩ := hdig x (le_trans (le_max_left _ _) hz)
  obtain ⟨b, hb⟩ := hdig y (le_trans (le_max_right _ _) hz)
  refine ⟨a, b, ?_⟩
  rw [qf_mk_sub_nat, qfU_norm hres hA hB]
  exact max_lt ha hb
theorem qfU_omega (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (hA : ‖A + 1‖ < 1)
    (hB : ‖B - 1‖ < 1) (h21 : ‖(2 : K)‖ < 1) :
    ‖QF.mk K A B 0 1‖ ≤ 1 ∧ ‖QF.mk K A B 0 1 ^ 2 + QF.mk K A B 0 1 + 1‖ < 1 := by
  have hY : ‖QF.mk K A B 0 1‖ = 1 := by rw [qfU_norm hres hA hB]; simp
  have hB1 : ‖B + 1‖ < 1 := by
    have hb : B + 1 = (B - 1) + 2 := by ring
    rw [hb]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hB h21)
  have he' : (QuadraticAlgebra.mk 0 1 : QuadraticAlgebra K A B) ^ 2 + QuadraticAlgebra.mk 0 1 + 1 =
      QuadraticAlgebra.mk (A + 1) (B + 1) := by
    ext <;> simp [sq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
  have he : QF.mk K A B 0 1 ^ 2 + QF.mk K A B 0 1 + 1 = QF.mk K A B (A + 1) (B + 1) := he'
  refine ⟨hY.le, ?_⟩
  rw [he, qfU_norm hres hA hB]
  exact max_lt hA hB1

theorem qfU_two {π : K} {e : ℕ} (h2 : ‖(2 : K)‖ = ‖π‖ ^ e) :
    ‖(2 : QF K A B)‖ = ‖algebraMap K (QF K A B) π‖ ^ e := by
  have h : (2 : QF K A B) = algebraMap K (QF K A B) 2 := (map_ofNat _ 2).symm
  rw [h, QF.norm_algebraMap, QF.norm_algebraMap, h2]

end Unramified

end FurioLombardo.Discharge.SelmerBasis
