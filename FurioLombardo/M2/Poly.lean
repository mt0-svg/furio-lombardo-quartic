import FurioLombardo.M2.PackedSpec

/-!
# Polynomials from coefficient lists (lane M2)

`toPoly R l` is the polynomial over `R` with integer coefficient list `l` (constant term first).
Its value at `t` is `evalZ t l`, it commutes with ring maps, and it is monic of degree
`l.length - 1` when the last entry is `1`.
-/

namespace FurioLombardo.M2

open Polynomial

/-- The polynomial with coefficient list `l` (constant term first), coefficients cast to `R`. -/
noncomputable def toPoly (R : Type*) [CommRing R] : List ℤ → R[X]
  | [] => 0
  | a :: l => C (a : R) + X * toPoly R l

section

variable {R : Type*} [CommRing R]

@[simp] theorem toPoly_nil : toPoly R [] = 0 := rfl

@[simp] theorem toPoly_cons (a : ℤ) (l : List ℤ) : toPoly R (a :: l) = C (a : R) + X * toPoly R l :=
  rfl

theorem aeval_toPoly {S : Type*} [CommRing S] [Algebra R S] (t : S) :
    ∀ l : List ℤ, aeval t (toPoly R l) = evalZ t l
  | [] => by simp
  | a :: l => by simp [aeval_toPoly t l]

theorem map_toPoly {R' : Type*} [CommRing R'] (f : R →+* R') :
    ∀ l : List ℤ, (toPoly R l).map f = toPoly R' l
  | [] => by simp
  | a :: l => by simp [map_toPoly f l]

theorem coeff_toPoly : ∀ (l : List ℤ) (i : ℕ), (toPoly R l).coeff i = ((l.getD i 0 : ℤ) : R)
  | [], i => by simp
  | a :: l, 0 => by simp
  | a :: l, i + 1 => by
    rw [toPoly_cons, coeff_add, coeff_C, coeff_X_mul, coeff_toPoly l i]; simp

theorem natDegree_toPoly_le (l : List ℤ) : (toPoly R l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_toPoly, List.getD_eq_default _ _ (by
    have : l.length - 1 < i := by exact_mod_cast hi
    omega)]
  simp

theorem monic_toPoly [Nontrivial R] (l : List ℤ) (hl : l.getLast? = some 1) :
    (toPoly R l).Monic ∧ (toPoly R l).natDegree = l.length - 1 := by
  have hne : l ≠ [] := by rintro rfl; simp at hl
  have hlast : l.getD (l.length - 1) 0 = 1 := by
    rw [List.getLast?_eq_getElem?] at hl
    rw [List.getD_eq_getElem?_getD, hl]; rfl
  have hc : (toPoly R l).coeff (l.length - 1) = 1 := by rw [coeff_toPoly, hlast]; simp
  refine ⟨monic_of_natDegree_le_of_coeff_eq_one _ (natDegree_toPoly_le l) hc, ?_⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_toPoly_le l) (by rw [hc]; exact one_ne_zero)

theorem evalN_eq_evalZ (t : R) : ∀ l : List ℕ, evalN t l = evalZ t (l.map fun x : ℕ => (x : ℤ))
  | [] => rfl
  | a :: l => by simp [evalN_eq_evalZ t l]

end

end FurioLombardo.M2
