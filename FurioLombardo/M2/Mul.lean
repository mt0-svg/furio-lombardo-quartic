import FurioLombardo.M2.Gen
import FurioLombardo.M2.Check2

/-!
# Soundness of the element checkers (lane M2)

`mulCheck a b z = true` gives `elt a * elt b = elt z`; `comboEq a l = true` gives `elt a = l(θ)`.
-/

namespace FurioLombardo.M2

open Polynomial NumberField

set_option exponentiation.threshold 1024

theorem comboK_eq : ∀ (a : List ℤ) (Ws : List (List ℤ)), comboK a Ws = combo a Ws
  | [], _ => by simp [comboK, combo]
  | _ :: _, [] => by simp [comboK, combo]
  | a :: l, W :: Ws => by simp [comboK, combo, comboK_eq l Ws]

theorem evalZ_H2 {R : Type*} [CommRing R] (t : R) (A B Z : List ℤ) (D : ℤ) :
    evalZ t (addZ (mulZ A B) (smulZ (-D) Z)) = evalZ t A * evalZ t B - D * evalZ t Z := by
  rw [evalZ_addZ, evalZ_mulZ, evalZ_smulZ, Int.cast_neg]; ring

theorem mulCheck_sound (a b z : List ℤ) (h : mulCheck a b z = true) :
    elt a * elt b = elt z := by
  unfold mulCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hz⟩, hab⟩, hbb⟩, hzb⟩, ⟨⟨hHv, hQv⟩, hQb⟩⟩ := h
  have hWb : ∀ W ∈ WL, ∀ x ∈ W, x.natAbs ≤ 2 ^ 77 := fun W hW => (WL_prop W hW).2
  have hA := natAbs_combo (2 ^ 100) (2 ^ 77) a WL ((allBounded_iff _ _).mp hab) hWb
  have hB := natAbs_combo (2 ^ 100) (2 ^ 77) b WL ((allBounded_iff _ _).mp hbb) hWb
  have hZ := natAbs_combo (2 ^ 200) (2 ^ 77) z WL ((allBounded_iff _ _).mp hzb) hWb
  rw [ha] at hA; rw [hb] at hB; rw [hz] at hZ
  have hAlen : (combo a WL).length ≤ 21 :=
    length_combo_le 21 a WL (fun W hW => (WL_prop W hW).1.le)
  have hmul := natAbs_mulZ _ _ (combo a WL) (combo b WL) hA hB
  have hsm := natAbs_smulZ (-DD) _ (combo z WL) hZ
  have hDD : (-DD).natAbs ≤ 2 ^ 68 := by rw [Int.natAbs_neg]; have := DD_pos; omega
  have hHb : ∀ x ∈ addZ (mulZ (combo a WL) (combo b WL)) (smulZ (-DD) (combo z WL)),
      x.natAbs ≤ 21 * (21 * 2 ^ 100 * 2 ^ 77) * (21 * 2 ^ 100 * 2 ^ 77) +
        2 ^ 68 * (21 * 2 ^ 200 * 2 ^ 77) := by
    intro x hx
    refine (natAbs_addZ _ _ _ _ hmul hsm x hx).trans (Nat.add_le_add ?_ ?_)
    · gcongr
    · gcongr
  have hfL : ∀ x ∈ fL, x.natAbs ≤ 1072 := (allBounded_iff _ _).mp fL_bound.2
  have hfQ := natAbs_mulZ _ _ fL _ hfL ((allBounded_iff _ _).mp hQb)
  rw [fL_bound.1] at hfQ
  have hv : evalZ ((2 : ℤ) ^ 512) (addZ (mulZ (combo a WL) (combo b WL)) (smulZ (-DD) (combo z WL))) =
      evalZ ((2 : ℤ) ^ 512) fL * evalZ ((2 : ℤ) ^ 512) (digitsZ kK 20
        ((dotZ a omL * dotZ b omL - DD * dotZ z omL) / Fk)) := by
    rw [evalZ_H2, ← dotZ_omL, ← dotZ_omL, ← dotZ_omL, ← evalI_eq, ← evalI_eq, ← tK_eq, ← Fk_eq,
      hQv]
    exact hHv
  have key := kron_mul 512 _ _ _ fL _ hHb hfQ (by norm_num) hv θ
  rw [evalZ_θ_fL, zero_mul, evalZ_H2, ← DD_mul_elt, ← DD_mul_elt, ← DD_mul_elt] at key
  have h2 : (DD : 𝓞 K21) ^ 2 * (elt a * elt b - elt z) = 0 := by linear_combination key
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) DD_ne_zero_O
  · exact sub_eq_zero.mp h

theorem comboEq_sound (a l : List ℤ) (h : comboEq a l = true) : elt a = evalZ θ l := by
  unfold comboEq at h
  have h0 := evalZ_eq_zero_of_forall θ _ ((allZero_iff _).mp h)
  rw [evalZ_addZ, evalZ_smulZ, comboK_eq, ← DD_mul_elt, Int.cast_neg] at h0
  have : (DD : 𝓞 K21) * (elt a - evalZ θ l) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h DD_ne_zero_O
  · exact sub_eq_zero.mp h

end FurioLombardo.M2
