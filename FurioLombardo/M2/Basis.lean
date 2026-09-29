import FurioLombardo.M2.Field
import FurioLombardo.M2.BasisData
import FurioLombardo.M2.Poly

/-!
# The integral basis of lane M2 in K21

From the kernel checks of `FurioLombardo.M2.BasisData`: `elt a = Σ a_j w_j ∈ 𝓞 K21` with
`DD * elt a = (Σ a_j W_j)(θ)`, where `w_j = W_j(θ)/DD`.
-/

namespace FurioLombardo.M2

open Polynomial NumberField

theorem integral_all : ∀ j < 21, allZero (homogL fLow (WL.getD j []) DD (chiL.getD j [] ++ [1])) = true := by
  intro j hj
  interval_cases j
  · exact integral_0
  · exact integral_1
  · exact integral_2
  · exact integral_3
  · exact integral_4
  · exact integral_5
  · exact integral_6
  · exact integral_7
  · exact integral_8
  · exact integral_9
  · exact integral_10
  · exact integral_11
  · exact integral_12
  · exact integral_13
  · exact integral_14
  · exact integral_15
  · exact integral_16
  · exact integral_17
  · exact integral_18
  · exact integral_19
  · exact integral_20

/-! ## Values at θ -/

set_option linter.unusedSimpArgs false in
theorem aeval_fZ_eq {R : Type*} [CommRing R] (t : R) : aeval t fZ = evalZ t fL := by
  simp only [fZ, fL, evalZ, map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat, Int.cast_ofNat,
    Int.cast_neg, Int.cast_zero, Int.cast_one]
  ring

set_option linter.unusedSimpArgs false in
theorem aeval_derivative_fZ_eq {R : Type*} [CommRing R] (t : R) :
    aeval t (derivative fZ) = evalZ t fdL := by
  simp only [fZ, fdL, evalZ, derivative_sub, derivative_add, derivative_mul, derivative_X_pow,
    derivative_ofNat, derivative_X, map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat,
    Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one, map_natCast, Nat.cast_ofNat,
    zero_mul, zero_add, map_one, mul_one, derivative_C, map_zero]
  ring

theorem evalZ_root_fL : evalZ (AdjoinRoot.root fQ : K21) fL = 0 := by
  rw [← aeval_fZ_eq]; exact aeval_root_fZ

theorem evalZ_θ_fL : evalZ θ fL = 0 := by rw [← aeval_fZ_eq]; exact aeval_θ_fZ

theorem fLow_length : fLow.length = 21 := by decide

theorem root_fLow {R : Type*} [CommRing R] (t : R) (h : evalZ t fL = 0) :
    t ^ fLow.length + evalZ t fLow = 0 := by
  rw [fL_eq, evalZ_append] at h
  rw [← h]; simp; ring

/-! ## The elements `w_j` and `elt a` -/

/-- `W(θ) / DD` in K21. -/
noncomputable def wK (W : List ℤ) : K21 := evalZ (AdjoinRoot.root fQ : K21) W / (DD : K21)

theorem DD_ne_zero_K : (DD : K21) ≠ 0 := by
  exact_mod_cast DD_pos.1.ne'

theorem isIntegral_wK (W chi : List ℤ) (h : allZero (homogL fLow W DD (chi ++ [1])) = true) :
    IsIntegral ℤ (wK W) := by
  have hw : (DD : K21) * wK W = evalZ (AdjoinRoot.root fQ : K21) W := by
    unfold wK; rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self DD_ne_zero_K, mul_one]
  have key := evalZ_homogL (AdjoinRoot.root fQ : K21) (wK W) fLow W DD
    (root_fLow _ evalZ_root_fL) hw (chi ++ [1])
  rw [evalZ_eq_zero_of_forall _ _ ((allZero_iff _).mp h), mul_zero] at key
  have hv : evalZ (wK W) (chi ++ [1]) = 0 := by
    rcases mul_eq_zero.mp key.symm with h0 | h0
    · exact absurd (pow_eq_zero_iff (by simp) |>.mp h0) DD_ne_zero_K
    · exact h0
  refine ⟨toPoly ℤ (chi ++ [1]), (monic_toPoly _ (by simp)).1, ?_⟩
  rw [← aeval_def, aeval_toPoly]; exact hv

theorem isIntegral_wK_of_mem {W : List ℤ} (hW : W ∈ WL) : IsIntegral ℤ (wK W) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hW
  have hj' : j < 21 := WL_shape.1 ▸ hj
  have := integral_all j hj'
  rw [List.getD_eq_getElem _ _ hj] at this
  exact isIntegral_wK _ _ this

/-- `(Σ a_j W_j)(θ) / DD` in K21. -/
noncomputable def eltK (a : List ℤ) : K21 := evalZ (AdjoinRoot.root fQ : K21) (combo a WL) / (DD : K21)

theorem isIntegral_intCast_K (n : ℤ) : IsIntegral ℤ (n : K21) := by
  have := isIntegral_algebraMap (R := ℤ) (A := K21) (x := n)
  simpa using this

theorem isIntegral_combo_div : ∀ (a : List ℤ) (Ws : List (List ℤ)),
    (∀ W ∈ Ws, IsIntegral ℤ (wK W)) →
    IsIntegral ℤ (evalZ (AdjoinRoot.root fQ : K21) (combo a Ws) / (DD : K21))
  | [], _, _ => by simp [combo]; exact isIntegral_zero
  | _ :: _, [], _ => by simp [combo]; exact isIntegral_zero
  | a :: l, W :: Ws, hW => by
    have ih := isIntegral_combo_div l Ws (fun W' h => hW W' (by simp [h]))
    have h : evalZ (AdjoinRoot.root fQ : K21) (combo (a :: l) (W :: Ws)) / (DD : K21) =
        (a : K21) * wK W + evalZ (AdjoinRoot.root fQ : K21) (combo l Ws) / (DD : K21) := by
      simp only [combo, evalZ_addZ, evalZ_smulZ, wK]; ring
    rw [h]
    exact ((isIntegral_intCast_K a).mul (hW W (by simp))).add ih

theorem isIntegral_eltK (a : List ℤ) : IsIntegral ℤ (eltK a) :=
  isIntegral_combo_div a WL (fun _ h => isIntegral_wK_of_mem h)

/-- The algebraic integer `Σ a_j w_j`. -/
noncomputable def elt (a : List ℤ) : 𝓞 K21 := ⟨eltK a, isIntegral_eltK a⟩

theorem evalZ_coe_O (l : List ℤ) (x : 𝓞 K21) : ((evalZ x l : 𝓞 K21) : K21) = evalZ (x : K21) l :=
  evalZ_map (algebraMap (𝓞 K21) K21) x l

theorem DD_mul_elt (a : List ℤ) : (DD : 𝓞 K21) * elt a = evalZ θ (combo a WL) := by
  apply RingOfIntegers.coe_injective
  change ((DD : 𝓞 K21) : K21) * eltK a = ((evalZ θ (combo a WL) : 𝓞 K21) : K21)
  rw [evalZ_coe_O, coe_θ]
  rw [show ((DD : 𝓞 K21) : K21) = (DD : K21) from map_intCast (algebraMap (𝓞 K21) K21) DD]
  unfold eltK
  rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self DD_ne_zero_K, mul_one]

end FurioLombardo.M2
