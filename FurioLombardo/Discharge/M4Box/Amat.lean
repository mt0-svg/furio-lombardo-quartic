import Mathlib
import FurioLombardo.Discharge.M4Log.Defs

/-!
# The linear part `Amat k` of lane M4's logarithm is integral (lane lean-m4box)

`Amat k = b⁻¹ [[a, 1 + a g1], [1, g1]]` with `a = k`, `b² = f_0`, `g1 = -f_1 / (2 f_0)`. From the
residue of `2b` modulo `2^3` (`bK_approx`: `‖b‖ = 1` for `k = 0`, `‖b‖ = 2` for `k = 1`) and the
residues of `4 f_1` modulo `2^16` (`approx_g`: `‖f_1‖ ≤ 1/2` for `k = 0`, `‖f_1‖ ≤ 4` for `k = 1`),
every entry has norm at most `1` (`norm_Amat_le_one`).
-/

open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv

namespace FurioLombardo.Discharge.M4Box

/-- `evZ` in the coordinates of `evQ`. -/
theorem evZ_eq_evQ (a : T3) :
    evZ a = evQ ![(a.1 : ℚ_[2]), (a.2.1 : ℚ_[2]), (a.2.2 : ℚ_[2])] := by
  simp [evZ, evQ, map_intCast]

/-- The 2-adic norm of an odd integer is `1`. -/
theorem norm_intCast_odd {u : ℤ} (hu : ¬ (2 : ℤ) ∣ u) : ‖(u : ℚ_[2])‖ = 1 :=
  le_antisymm (Padic.norm_int_le_one u)
    (not_lt.mp fun h => hu (by exact_mod_cast Padic.norm_intCast_lt_one_iff.mp h))

/-- Near a triple of larger norm, the norm is that of the triple. -/
theorem norm_eq_of_approx {x : Kv} {b : T3} {n : ℕ} (h : Approx x b n)
    (hlt : (2⁻¹ : ℝ) ^ n < ‖evZ b‖) : ‖x‖ = ‖evZ b‖ := by
  have hl : ‖x - evZ b‖ < ‖evZ b‖ := lt_of_le_of_lt h hlt
  have e := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hl)
  rwa [sub_add_cancel, max_eq_right hl.le] at e

theorem norm_evZ_bT0 : ‖evZ (6, 6, 8)‖ = 2⁻¹ := by
  have h6 : ‖((6 : ℤ) : ℚ_[2])‖ = 2⁻¹ := by
    have := norm_intCast_two_mul_odd 3 (by norm_num)
    norm_num at this ⊢
    exact this
  have h8 : ‖((8 : ℤ) : ℚ_[2])‖ = 2⁻¹ ^ 3 := by
    rw [show ((8 : ℤ) : ℚ_[2]) = 2 ^ 3 by norm_num, norm_pow, norm_two_padic]
  have hp := norm_pv_lt_one.le
  have hp0 := norm_pv_pos.le
  rw [evZ_eq_evQ, norm_evQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [h6, h8]
  refine max_eq_left (max_le ?_ ?_)
  · nlinarith
  · have : ‖pv‖ ^ 2 ≤ 1 := pow_le_one₀ hp0 hp
    nlinarith

theorem norm_evZ_bT1 : ‖evZ (11, 11, 15)‖ = 1 := by
  have h11 : ‖((11 : ℤ) : ℚ_[2])‖ = 1 := norm_intCast_odd (by norm_num)
  have h15 : ‖((15 : ℤ) : ℚ_[2])‖ = 1 := norm_intCast_odd (by norm_num)
  have hp := norm_pv_lt_one.le
  have hp0 := norm_pv_pos.le
  rw [evZ_eq_evQ, norm_evQ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [h11, h15, one_mul, one_mul]
  exact max_eq_left (max_le hp (pow_le_one₀ hp0 hp))

theorem norm_bK_zero : ‖bK 0‖ = 1 := by
  have h := norm_eq_of_approx (bK_approx 0) (by rw [show bT 0 = (6, 6, 8) from rfl, norm_evZ_bT0]; norm_num)
  rw [show bT 0 = (6, 6, 8) from rfl, norm_evZ_bT0, norm_mul, norm_two_Kv] at h
  linarith

theorem norm_bK_one : ‖bK 1‖ = 2 := by
  have h := norm_eq_of_approx (bK_approx 1) (by rw [show bT 1 = (11, 11, 15) from rfl, norm_evZ_bT1]; norm_num)
  rw [show bT 1 = (11, 11, 15) from rfl, norm_evZ_bT1, norm_mul, norm_two_Kv] at h
  linarith

/-- Kernel check: the residue of `4 f_1` for `k = 0` vanishes modulo `2^3`. -/
theorem modT_gT_zero_one : modT (gT 0 1) 3 = modT (0, 0, 0) 3 := by decide +kernel

theorem norm_f1_zero : ‖(fK 0).coeff 1‖ ≤ 2⁻¹ := by
  have h := ((approx_g 0 1).mono (by norm_num : 3 ≤ 16)).of_modT_eq modT_gT_zero_one
  have e0 : evZ (0, 0, 0) = 0 := by simp [evZ]
  unfold Approx at h
  rw [e0, sub_zero, norm_mul, show (4 : Kv) = 2 * 2 by norm_num, norm_mul, norm_two_Kv] at h
  linarith

theorem norm_f1_one : ‖(fK 1).coeff 1‖ ≤ 4 := by
  have h := (approx_g 1 1).norm_le_one
  rw [norm_mul, show (4 : Kv) = 2 * 2 by norm_num, norm_mul, norm_two_Kv] at h
  linarith

/-- `‖g1‖ = 2 ‖f_1‖ / ‖b‖²`. -/
theorem norm_g1K (k : Fin 2) : ‖g1K k‖ = 2 * ‖(fK k).coeff 1‖ / ‖bK k‖ ^ 2 := by
  have hb : ‖bK k‖ ≠ 0 := norm_ne_zero_iff.mpr (bK_ne k)
  rw [g1K, norm_div, norm_neg, norm_mul, norm_two_Kv, ← bK_sq, norm_pow]
  field_simp

/-- **`Amat k` is integral.** -/
theorem norm_Amat_le_one (k : Fin 2) (i j : Fin 2) : ‖Amat k i j‖ ≤ 1 := by
  have hg := norm_g1K k
  rw [Amat, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
  fin_cases k
  · have hb := norm_bK_zero
    have hf := norm_f1_zero
    have ha : aK 0 = 0 := by simp [aK]
    simp only [Fin.zero_eta] at hg ⊢
    rw [hb] at hg
    have hg1 : ‖g1K 0‖ ≤ 1 := by rw [hg]; linarith
    rw [hb, inv_one, one_mul]
    fin_cases i <;> fin_cases j <;> simp [ha, hg1]
  · have hb := norm_bK_one
    have hf := norm_f1_one
    have ha : aK 1 = 1 := by simp [aK]
    simp only [Fin.mk_one] at hg ⊢
    rw [hb] at hg
    have hg2 : ‖g1K 1‖ ≤ 2 := by rw [hg]; linarith
    have h1g : ‖1 + g1K 1‖ ≤ 2 := (IsUltrametricDist.norm_add_le_max (1 : Kv) (g1K 1)).trans
      (max_le (by rw [norm_one]; norm_num) hg2)
    rw [hb]
    fin_cases i <;> fin_cases j <;> simp [ha]
    all_goals linarith

end FurioLombardo.Discharge.M4Box
