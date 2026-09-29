import Mathlib
import FurioLombardo.Discharge.M4Cert.Kv
import FurioLombardo.Discharge.M4Cert.Hensel
import FurioLombardo.Discharge.M4Cert.Data
import FurioLombardo.M1.ZK

/-!
# The embedding `σ : K21 → K_v`

`θ⋆` is the root of `f` (the defining polynomial of K21, lane M1's `fZ`) in `Kv` given by Hensel's lemma
(`hensel_of_norm_lt`) from the integer triple `θ0` of `FurioLombardo.Discharge.M4Cert.Data`: the kernel
checks that `f(θ0)` has coordinates divisible by `2^40` (`fL_θ0`) and that the `π²` coordinate of
`f'(θ0)` is not divisible by `2^6` (`dfL_θ0`), so `‖f(θ0)‖ ≤ 2^-40 < 2^-14 ≤ ‖f'(θ0)‖²` and
`‖θ⋆ - θ0‖ ≤ 2^-33`. `σ` is `AdjoinRoot.lift` at `θ⋆`.
-/

namespace FurioLombardo.Discharge.M4Cert

open Polynomial FurioLombardo.M1

/-! ## Horner evaluation on integer triples -/

/-- Horner evaluation of an integer coefficient list (constant term first) at a triple, exactly. -/
def hornerZ (v : T3) : List ℤ → T3
  | [] => (0, 0, 0)
  | a :: l => (a, 0, 0) + mulZ v (hornerZ v l)

theorem evZ_const (a : ℤ) : evZ (a, 0, 0) = (a : Kv) := by
  simp [evZ]

theorem evZ_zero : evZ (0, 0, 0) = 0 := by
  simp [evZ]

/-- `hornerZ` computes `evalL`. -/
theorem evZ_hornerZ (v : T3) : ∀ L : List ℤ, evZ (hornerZ v L) = evalL (evZ v) L
  | [] => by simp [hornerZ, evZ_zero]
  | a :: l => by
    rw [hornerZ, evZ_add, evZ_mul, evZ_hornerZ v l, evZ_const, evalL_cons]

/-- Formal derivative of a coefficient list. -/
def dL : List ℤ → List ℤ
  | [] => []
  | _ :: l => addL l (0 :: dL l)

theorem evalL_zero_cons {R : Type*} [CommRing R] (t : R) (l : List ℤ) :
    evalL t (0 :: l) = t * evalL t l := by
  simp

/-- The derivative of `ofListL L`, evaluated, is the evaluation of `dL L`. -/
theorem eval₂_derivative_ofListL {R : Type*} [CommRing R] (t : R) :
    ∀ L : List ℤ, (derivative (ofListL L)).eval₂ (Int.castRingHom R) t = evalL t (dL L)
  | [] => by simp [ofListL, dL]
  | a :: l => by
    rw [ofListL, dL, evalL_addL, evalL_zero_cons, ← eval₂_derivative_ofListL t l,
      ← evalL_ofListL]
    simp [derivative_mul, eval₂_add, eval₂_mul]

/-! ## The certificate -/

/-- The coordinates of `f(θ0)` are divisible by `2^40`. -/
theorem fL_θ0 : (2 : ℤ) ^ 40 ∣ (hornerZ θ0 fL).1 ∧ (2 : ℤ) ^ 40 ∣ (hornerZ θ0 fL).2.1 ∧
    (2 : ℤ) ^ 40 ∣ (hornerZ θ0 fL).2.2 := by
  decide +kernel

/-- The `π²` coordinate of `f'(θ0)` is not divisible by `2^6`. -/
theorem dfL_θ0 : ¬ (2 : ℤ) ^ 6 ∣ (hornerZ θ0 (dL fL)).2.2 := by
  decide +kernel

/-- `f` over `Kv` (integer coefficients). -/
noncomputable def fK : Kv[X] := (ofListL fL).map (Int.castRingHom Kv)

theorem norm_intCast_le_one (n : ℤ) : ‖(n : Kv)‖ ≤ 1 := by
  have := norm_evZ_le_one (n, 0, 0)
  rwa [evZ_const] at this

theorem fK_coeff_le (i : ℕ) : ‖fK.coeff i‖ ≤ 1 := by
  rw [fK, coeff_map]
  exact norm_intCast_le_one _

theorem fK_eval (x : Kv) : fK.eval x = evalL x fL := by
  rw [fK, eval_map, evalL_ofListL]

theorem fK_derivative_eval (x : Kv) : fK.derivative.eval x = evalL x (dL fL) := by
  rw [fK, derivative_map, eval_map, eval₂_derivative_ofListL]

theorem norm_fK_θ0 : ‖fK.eval (evZ θ0)‖ ≤ (2⁻¹ : ℝ) ^ 40 := by
  rw [fK_eval, ← evZ_hornerZ]
  exact norm_evZ_le_of_dvd _ _ fL_θ0

theorem norm_pv_le_one : ‖pv‖ ≤ 1 := by
  have h := norm_evZ_le_one (0, 1, 0)
  simpa [evZ] using h

theorem half_le_norm_pv_sq : (2⁻¹ : ℝ) ≤ ‖pv‖ ^ 2 := half_lt_norm_pv_sq.le

/-- The `π²` term of a triple bounds its norm from below. -/
theorem norm_evZ_ge_third (a : T3) : ‖(a.2.2 : ℚ_[2])‖ * ‖pv‖ ^ 2 ≤ ‖evZ a‖ := by
  rw [evZ_eq_evQ, norm_evQ]
  simp only [qOfT3, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- A lower bound for `‖f'(θ0)‖`. -/
theorem norm_dfK_θ0 : (2⁻¹ : ℝ) ^ 7 ≤ ‖fK.derivative.eval (evZ θ0)‖ := by
  rw [fK_derivative_eval, ← evZ_hornerZ]
  set v := hornerZ θ0 (dL fL)
  have hv : (2⁻¹ : ℝ) ^ 6 < ‖(v.2.2 : ℚ_[2])‖ := by
    by_contra hle
    push Not at hle
    apply dfL_θ0
    exact (norm_intCast_le_two_pow_iff v.2.2 6).1 hle
  calc (2⁻¹ : ℝ) ^ 7 = (2⁻¹ : ℝ) ^ 6 * 2⁻¹ := by ring
    _ ≤ ‖(v.2.2 : ℚ_[2])‖ * ‖pv‖ ^ 2 := by
        exact mul_le_mul hv.le half_le_norm_pv_sq (by norm_num) (norm_nonneg _)
    _ ≤ ‖evZ v‖ := norm_evZ_ge_third v

theorem hensel_θ0 : ∃ z : Kv, fK.eval z = 0 ∧ ‖z - evZ θ0‖ ≤ (2⁻¹ : ℝ) ^ 33 := by
  have hd := norm_dfK_θ0
  have hf := norm_fK_θ0
  have hpos : (0 : ℝ) < (2⁻¹ : ℝ) ^ 7 := by positivity
  obtain ⟨z, hz, hle⟩ := hensel_of_norm_lt fK fK_coeff_le (evZ θ0) (norm_evZ_le_one θ0) (by
    calc ‖fK.eval (evZ θ0)‖ ≤ (2⁻¹ : ℝ) ^ 40 := hf
      _ < ((2⁻¹ : ℝ) ^ 7) ^ 2 := by norm_num
      _ ≤ ‖fK.derivative.eval (evZ θ0)‖ ^ 2 := by gcongr)
  refine ⟨z, hz, hle.trans ?_⟩
  rw [div_le_iff₀ (hpos.trans_le hd)]
  calc ‖fK.eval (evZ θ0)‖ ≤ (2⁻¹ : ℝ) ^ 40 := hf
    _ = (2⁻¹ : ℝ) ^ 33 * (2⁻¹ : ℝ) ^ 7 := by norm_num
    _ ≤ (2⁻¹ : ℝ) ^ 33 * ‖fK.derivative.eval (evZ θ0)‖ := by gcongr

/-- The image `θ⋆` of `θ` in `Kv`. -/
noncomputable def θstar : Kv := hensel_θ0.choose

theorem fK_θstar : fK.eval θstar = 0 := hensel_θ0.choose_spec.1

theorem norm_θstar_sub : ‖θstar - evZ θ0‖ ≤ (2⁻¹ : ℝ) ^ 33 := hensel_θ0.choose_spec.2

theorem norm_θstar_le_one : ‖θstar‖ ≤ 1 := by
  have h1 := norm_evZ_le_one θ0
  have h2 : ‖θstar - evZ θ0‖ ≤ 1 := norm_θstar_sub.trans (by norm_num)
  calc ‖θstar‖ = ‖(θstar - evZ θ0) + evZ θ0‖ := by rw [sub_add_cancel]
    _ ≤ max ‖θstar - evZ θ0‖ ‖evZ θ0‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le h2 h1

theorem fQ_eval₂_θstar : fQ.eval₂ (algebraMap ℚ Kv) θstar = 0 := by
  have h := fK_θstar
  rw [fK, ofListL_fL, eval_map] at h
  rw [fQ, eval₂_map]
  convert h using 2
  exact RingHom.ext_int _ _

/-- The embedding `σ : K21 → K_v`, `θ ↦ θ⋆`. -/
noncomputable def σ : K21 →+* Kv := AdjoinRoot.lift (algebraMap ℚ Kv) θstar fQ_eval₂_θstar

theorem σ_θ : σ θ = θstar := AdjoinRoot.lift_root _

theorem σ_ratCast (q : ℚ) : σ (q : K21) = (q : Kv) := map_ratCast σ q

end FurioLombardo.Discharge.M4Cert
