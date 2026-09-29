import Mathlib
import FurioLombardo.Discharge.M3a.K1Res

/-!
# The two norm identities of the elementary proof of (K1) (lane K1, brick E3)

Notation: `f` of degree 6 with leading coefficient `f₆`,
`N_g(p) = Algebra.norm K (AdjoinRoot.mk g p)`.

* `lc_sq_mul_norm_eq_sq` (Step 3): `f₆² N_f(u) = N_u(v)²` for `u` monic quadratic with
  `u ∣ v² - f`;
* `norm_formula` (Step 6, Cassels and Flynn's Lemma 6.8.1 in the form (N')):
  `f₆ w η² N_f(M) = -N_u(M) N_f(L)` when `η M² - u L² = w f`, `deg L ≤ 2`, `deg M ≤ 3`, `η, w ≠ 0`.
  The resultants keep the formal degrees `2` for `L` and `3` for `M`, so no assumption on the true
  degrees is needed.
-/

open Polynomial

namespace FurioLombardo.Discharge.M3a.K1

variable {K : Type*} [Field K]

/-- **Step 3.** `f₆² N_f(u) = N_u(v)²` for `u` monic quadratic dividing `v² - f`, `deg f = 6`. -/
theorem lc_sq_mul_norm_eq_sq {f u v : K[X]} (hf : f.natDegree = 6) (hu : u.Monic)
    (h2 : u.natDegree = 2) (huv : u ∣ v ^ 2 - f) :
    f.leadingCoeff ^ 2 * Algebra.norm K (AdjoinRoot.mk f u) =
      Algebra.norm K (AdjoinRoot.mk u v) ^ 2 := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hswap := norm_mk_swap hf0 hu
  rw [h2, hf] at hswap
  rw [hswap, show AdjoinRoot.mk u f = AdjoinRoot.mk u (v ^ 2) from
    (AdjoinRoot.mk_eq_mk.mpr (by rw [← neg_sub, dvd_neg]; exact huv)), map_pow, map_pow]
  norm_num

/-- `N_g(0) = 0` for `g` of positive degree. -/
theorem norm_mk_zero {g : K[X]} (hg : 0 < g.natDegree) :
    Algebra.norm K (AdjoinRoot.mk g 0) = 0 := by
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have h := lc_pow_mul_norm_mk hg0 (p := 0) (n := 0) (by simp)
  rw [pow_zero, one_mul, resultant_zero_right_deg, coeff_zero, zero_pow hg.ne'] at h
  exact h

/-- **Step 6, the norm formula (N').** -/
theorem norm_formula {f u L M : K[X]} (hf : f.natDegree = 6) (hu : u.Monic)
    (h2 : u.natDegree = 2) (hL : L ≠ 0) (hL2 : L.natDegree ≤ 2) (hM3 : M.natDegree ≤ 3)
    {η w : K} (hη : η ≠ 0) (hw : w ≠ 0) (hW : C η * M ^ 2 - u * L ^ 2 = C w * f) :
    f.leadingCoeff * w * η ^ 2 * Algebra.norm K (AdjoinRoot.mk f M) =
      -(Algebra.norm K (AdjoinRoot.mk u M) * Algebra.norm K (AdjoinRoot.mk f L)) := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  by_cases hM : M = 0
  · subst hM
    rw [norm_mk_zero (by omega), norm_mk_zero (by omega)]
    ring
  have hNu : Algebra.norm K (AdjoinRoot.mk u M) = resultant u M 2 3 := by
    rw [norm_mk_eq_resultant_of_le hu hM3, h2]
  have hηM : C η * M ≠ 0 := mul_ne_zero (C_ne_zero.mpr hη) hM
  have hηM3 : (C η * M).natDegree ≤ 3 := (natDegree_C_mul_le η M).trans hM3
  have ha : w ^ 3 * (f.leadingCoeff ^ 3 * Algebra.norm K (AdjoinRoot.mk f M)) =
      -(Algebra.norm K (AdjoinRoot.mk u M)) * resultant L M 2 3 ^ 2 := by
    rw [lc_pow_mul_norm_mk hf0 hM3, hf, ← resultant_C_mul_left, ← hW]
    have e1 : C η * M ^ 2 - u * L ^ 2 = -(u * L ^ 2) + M * (C η * M) := by ring
    rw [e1, resultant_add_mul_left _ _ _ _ _ (by omega) hM3]
    have e2 : -(u * L ^ 2) = (C (-1) * u) * (L * L) := by rw [C_neg, C_1]; ring
    have hu1 : C (-1) * u ≠ 0 := mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))
      hu.ne_zero
    have hu2 : (C (-1) * u).natDegree ≤ 2 := (natDegree_C_mul_le _ u).trans h2.le
    have hLL : (L * L).natDegree ≤ 2 + 2 := natDegree_mul_le.trans (add_le_add hL2 hL2)
    rw [e2, show (6 : ℕ) = 2 + (2 + 2) from rfl,
      resultant_mul_left_of_le hu1 (mul_ne_zero hL hL) hu2 hLL hM3,
      resultant_mul_left_of_le hL hL hL2 hL2 hM3, resultant_C_mul_left, hNu]
    ring
  have hb : w ^ 2 * (f.leadingCoeff ^ 2 * Algebra.norm K (AdjoinRoot.mk f L)) =
      η ^ 2 * resultant L M 2 3 ^ 2 := by
    rw [lc_pow_mul_norm_mk hf0 hL2, hf, ← resultant_C_mul_left, ← hW]
    have e1 : C η * M ^ 2 - u * L ^ 2 = (C η * M) * M + L * (-(u * L)) := by ring
    have huL : (-(u * L)).natDegree ≤ 4 := by
      rw [natDegree_neg]
      exact natDegree_mul_le.trans (by omega)
    rw [e1, resultant_add_mul_left _ _ _ _ _ (by omega) hL2, show (6 : ℕ) = 3 + 3 from rfl,
      resultant_mul_left_of_le hηM hM hηM3 hM3 hL2, resultant_C_mul_left,
      resultant_comm M L 3 2]
    ring
  have hne : w ^ 2 * f.leadingCoeff ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hw) (pow_ne_zero 2 hlc)
  apply mul_left_cancel₀ hne
  linear_combination η ^ 2 * ha + Algebra.norm K (AdjoinRoot.mk u M) * hb

end FurioLombardo.Discharge.M3a.K1
