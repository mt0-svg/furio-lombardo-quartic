import FurioLombardo.M1.Basic

/-!
# Soundness of the integer list polynomial operations

Evaluation `evalL t` turns `addL`, `smulL`, `subL`, `mulL` into ring operations, and `redL` into the
identity at a root of the monic modulus. So a kernel check of a list identity gives an identity in
any commutative ring where the evaluation point is a root of the modulus (for instance `θ` in K21).
-/

namespace FurioLombardo.M1

open Polynomial

variable {R : Type*} [CommRing R] (t : R)

@[simp] theorem evalL_nil : evalL t [] = 0 := rfl

@[simp] theorem evalL_cons (a : ℤ) (l : List ℤ) : evalL t (a :: l) = a + t * evalL t l := rfl

theorem evalL_addL : ∀ l m : List ℤ, evalL t (addL l m) = evalL t l + evalL t m
  | [], m => by simp [addL]
  | a :: l, [] => by simp [addL]
  | a :: l, b :: m => by
    simp only [addL, evalL_cons, evalL_addL l m, Int.cast_add]; ring

theorem evalL_smulL (c : ℤ) : ∀ l : List ℤ, evalL t (smulL c l) = c * evalL t l
  | [] => by simp [smulL]
  | a :: l => by
    have := evalL_smulL c l
    simp only [smulL, List.map_cons, evalL_cons, Int.cast_mul] at this ⊢
    rw [this]; ring

theorem evalL_subL (l m : List ℤ) : evalL t (subL l m) = evalL t l - evalL t m := by
  simp [subL, evalL_addL, evalL_smulL]; ring

theorem evalL_mulL : ∀ l m : List ℤ, evalL t (mulL l m) = evalL t l * evalL t m
  | [], m => by simp [mulL]
  | a :: l, m => by
    simp only [mulL, evalL_addL, evalL_smulL, evalL_cons, evalL_mulL l m, Int.cast_zero]; ring

theorem evalL_of_allZeroL : ∀ l : List ℤ, allZeroL l = true → evalL t l = 0
  | [], _ => rfl
  | a :: l, h => by
    simp only [allZeroL, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, evalL_of_allZeroL l h.2]

/-- Two lists with the same value: their difference is the zero list. -/
theorem evalL_eq_of_allZeroL_subL (l m : List ℤ) (h : allZeroL (subL l m) = true) :
    evalL t l = evalL t m := by
  have := evalL_of_allZeroL t _ h
  rw [evalL_subL] at this
  exact sub_eq_zero.mp this

theorem evalL_dropLast_add : ∀ r : List ℤ, r ≠ [] →
    evalL t r = evalL t r.dropLast + t ^ (r.length - 1) * (r.getLastD 0)
  | [a], _ => by simp
  | a :: b :: l, _ => by
    have ih := evalL_dropLast_add (b :: l) (List.cons_ne_nil b l)
    simp only [List.dropLast_cons_cons, evalL_cons, List.length_cons, List.getLastD_cons] at ih ⊢
    rw [ih]
    simp only [add_tsub_cancel_right]
    rw [pow_succ]; ring

/-- The evaluation of `mulXL gl r` is `t * evalL t r` when `t` is a root of `X ^ gl.length + gl`. -/
theorem evalL_mulXL (gl : List ℤ) (hroot : t ^ gl.length + evalL t gl = 0) (r : List ℤ) :
    evalL t (mulXL gl r) = t * evalL t r := by
  unfold mulXL
  split_ifs with h
  · rcases eq_or_ne r [] with rfl | hr
    · have hg : gl = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
      subst hg; simp [addL, smulL]
    · rw [evalL_addL, evalL_smulL, evalL_cons, evalL_dropLast_add t r hr]
      have hl : r.length - 1 + 1 = gl.length := by
        have : r.length ≠ 0 := by simpa using hr
        omega
      have hx : evalL t gl = -t ^ gl.length := by linear_combination hroot
      rw [hx, ← hl, pow_succ]
      push_cast; ring
  · simp

/-- Reduction modulo a monic polynomial with root `t` does not change the value at `t`. -/
theorem evalL_redL (gl : List ℤ) (hroot : t ^ gl.length + evalL t gl = 0) :
    ∀ l : List ℤ, evalL t (redL gl l) = evalL t l
  | [] => rfl
  | a :: l => by
    simp only [redL, evalL_addL, evalL_mulXL t gl hroot, evalL_redL gl hroot l, evalL_cons,
      evalL_nil, mul_zero, add_zero]

theorem evalL_ofListL (x : R) : ∀ l : List ℤ, (ofListL l).eval₂ (Int.castRingHom R) x = evalL x l
  | [] => by simp [ofListL]
  | a :: l => by
    simp only [ofListL, eval₂_add, eval₂_C, eval₂_mul, eval₂_X, evalL_ofListL x l, evalL_cons]
    simp

end FurioLombardo.M1
