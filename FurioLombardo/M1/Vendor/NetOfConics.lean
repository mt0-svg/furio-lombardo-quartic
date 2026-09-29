import Mathlib

/-!
# Nets of ternary conics: base points and the 6 × 6 determinant

A ternary quadratic form is a coefficient vector `c : Fin 6 → k` on the monomials
x², xy, xz, y², yz, z² in the coordinates `R 0, R 1, R 2`; a net is `C : Fin 3 → Fin 6 → k`.
`jacDet C R` is the Jacobian cubic J = det (∂(C i)/∂x_j) at `R` and `dJ C l R` its partial
derivative in `x_l` (`eval_pderiv_jacPoly` identifies it with the formal `MvPolynomial.pderiv`).

Main results, valid in every characteristic (including 2):
* `jacDet_eq_zero_of_common_zero`, `dJ_eq_zero_of_common_zero`: at a common zero of the net, J and
  its three partial derivatives vanish (a base point of the net is a singular point of the Jacobian
  curve).
* `sixDet_eq_zero_of_common_zero`: then the 6 × 6 determinant of the coefficients of
  C 0, C 1, C 2, ∂J/∂x, ∂J/∂y, ∂J/∂z vanishes.
* `eq_zero_of_map_sixDet_ne_zero`: reduction criterion. If a ring homomorphism to a field (a
  residue map) does not kill that determinant, the reduced net has no common zero. For a Bruin
  descent Q1 Q3 - Q2² = c F, this bounds the set S of primes where the descent class can have
  odd valuation.

Copy of the Toolbox module `Toolbox.NetOfConics` with the namespace renamed
FurioLombardo.M1.Vendor.NetOfConics (lane files of this project do not import Toolbox).
-/

namespace FurioLombardo.M1.Vendor.NetOfConics

variable {k : Type*} [CommRing k]

/-- The value at `R` of the ternary quadratic form with coefficients `c` on the monomials
x², xy, xz, y², yz, z². -/
def qev (c : Fin 6 → k) (R : Fin 3 → k) : k :=
  c 0 * R 0 ^ 2 + c 1 * (R 0 * R 1) + c 2 * (R 0 * R 2) + c 3 * R 1 ^ 2 + c 4 * (R 1 * R 2)
    + c 5 * R 2 ^ 2

/-- The Veronese vector (x², xy, xz, y², yz, z²) of `R`. -/
def veronese (R : Fin 3 → k) : Fin 6 → k :=
  ![R 0 ^ 2, R 0 * R 1, R 0 * R 2, R 1 ^ 2, R 1 * R 2, R 2 ^ 2]

/-- The gradient at `R` of the quadratic form with coefficients `c`. -/
def grad (c : Fin 6 → k) (R : Fin 3 → k) : Fin 3 → k :=
  ![2 * c 0 * R 0 + c 1 * R 1 + c 2 * R 2,
    c 1 * R 0 + 2 * c 3 * R 1 + c 4 * R 2,
    c 2 * R 0 + c 4 * R 1 + 2 * c 5 * R 2]

/-- The Jacobian matrix of the net `C` at `R`: row `i` is the gradient of `C i`. -/
def jac (C : Fin 3 → Fin 6 → k) (R : Fin 3 → k) : Matrix (Fin 3) (Fin 3) k :=
  Matrix.of fun i j => grad (C i) R j

/-- The Jacobian cubic of the net at `R`: J(R) = det (∂(C i)/∂x_j)(R). -/
def jacDet (C : Fin 3 → Fin 6 → k) (R : Fin 3 → k) : k :=
  (jac C R).det

/-- The unit vector `e_i`. -/
def unitv (i : Fin 3) : Fin 3 → k := Pi.single i 1

/-- The partial derivative ∂J/∂x_l at `R`. The entries of `jac C R` are linear in `R`, so this is
the sum over the columns `j` of the determinant of `jac C R` with column `j` replaced by column
`j` of `jac C (unitv l)`. -/
def dJ (C : Fin 3 → Fin 6 → k) (l : Fin 3) (R : Fin 3 → k) : k :=
  ∑ j : Fin 3, ((jac C R).updateCol j (fun i => jac C (unitv l) i j)).det

/-- Coefficients, on x², xy, xz, y², yz, z², of a function `f` that is a quadratic form, read off
from its values at the unit vectors and at their pairwise sums. -/
def coeffs (f : (Fin 3 → k) → k) : Fin 6 → k :=
  ![f (unitv 0), f (unitv 0 + unitv 1) - f (unitv 0) - f (unitv 1),
    f (unitv 0 + unitv 2) - f (unitv 0) - f (unitv 2),
    f (unitv 1), f (unitv 1 + unitv 2) - f (unitv 1) - f (unitv 2), f (unitv 2)]

/-- The 6 × 6 matrix whose rows are the coefficient vectors of `C 0, C 1, C 2` and of the three
partial derivatives of the Jacobian cubic. -/
def sixMatrix (C : Fin 3 → Fin 6 → k) : Matrix (Fin 6) (Fin 6) k :=
  Matrix.of ![C 0, C 1, C 2, coeffs (dJ C 0), coeffs (dJ C 1), coeffs (dJ C 2)]

/-- The value of a quadratic form is its coefficient vector paired with the Veronese vector. -/
theorem qev_eq_sum_veronese (c : Fin 6 → k) (R : Fin 3 → k) :
    qev c R = ∑ m, c m * veronese R m := by
  simp only [qev, veronese, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

/-- Euler's identity for the net: `(jac C R) R = 2 (qev (C i) R)_i`. -/
theorem jac_mulVec_self (C : Fin 3 → Fin 6 → k) (R : Fin 3 → k) :
    (jac C R).mulVec R = fun i => 2 * qev (C i) R := by
  funext i
  simp [Matrix.mulVec, dotProduct, jac, grad, qev, Fin.sum_univ_three]
  ring

/-- Symmetry of the Hessians: `jac C (e_l)` applied to `R` is column `l` of `jac C R`. -/
theorem jac_unitv_mulVec (C : Fin 3 → Fin 6 → k) (l : Fin 3) (R : Fin 3 → k) :
    (jac C (unitv l)).mulVec R = fun i => jac C R i l := by
  funext i
  fin_cases l <;> simp [Matrix.mulVec, dotProduct, jac, grad, unitv, Fin.sum_univ_three]

/-- `R a · J(R)` is twice the determinant of the Jacobian matrix with column `a` replaced by the
values of the forms at `R`. -/
theorem mul_jacDet (C : Fin 3 → Fin 6 → k) (R : Fin 3 → k) (a : Fin 3) :
    R a * jacDet C R = 2 * ((jac C R).updateCol a (fun i => qev (C i) R)).det := by
  fin_cases a <;>
  · simp [jacDet, jac, grad, qev, Matrix.det_fin_three]
    ring

/-- `R a · ∂J/∂x_l(R)` is an explicit combination of determinants: twice a sum of determinants
having the values of the forms at `R` as column `a`, plus the determinant of the Jacobian matrix
with column `a` replaced by its column `l`. -/
theorem mul_dJ (C : Fin 3 → Fin 6 → k) (R : Fin 3 → k) (a l : Fin 3) :
    R a * dJ C l R =
      2 * ∑ j ∈ Finset.univ.erase a,
          (((jac C R).updateCol j (fun i => jac C (unitv l) i j)).updateCol a
            (fun i => qev (C i) R)).det
        + ((jac C R).updateCol a (fun i => jac C R i l)).det := by
  fin_cases a <;> fin_cases l <;>
  · simp [dJ, jac, grad, qev, unitv, Matrix.det_fin_three, Fin.sum_univ_three,
      Finset.sum_erase_eq_sub]
    ring

/-- `∂J/∂x_l` is a quadratic form, and `coeffs` recovers its coefficients. -/
theorem qev_coeffs_dJ (C : Fin 3 → Fin 6 → k) (l : Fin 3) (R : Fin 3 → k) :
    qev (coeffs (dJ C l)) R = dJ C l R := by
  fin_cases l <;>
  · simp [qev, coeffs, dJ, jac, grad, unitv, Matrix.det_fin_three, Fin.sum_univ_three]
    ring

/-- The rows of `sixMatrix C` paired with the Veronese vector give the six quadrics at `R`. -/
theorem sixMatrix_mulVec_veronese (C : Fin 3 → Fin 6 → k) (R : Fin 3 → k) :
    (sixMatrix C).mulVec (veronese R) =
      ![qev (C 0) R, qev (C 1) R, qev (C 2) R, dJ C 0 R, dJ C 1 R, dJ C 2 R] := by
  funext r
  fin_cases r <;>
  simp [Matrix.mulVec, dotProduct, sixMatrix, ← qev_eq_sum_veronese, qev_coeffs_dJ]

/-- `∂J/∂x_l` commutes with ring homomorphisms. -/
theorem dJ_map {k' : Type*} [CommRing k'] (φ : k →+* k') (C : Fin 3 → Fin 6 → k) (l : Fin 3)
    (R : Fin 3 → k) :
    dJ (fun i m => φ (C i m)) l (fun j => φ (R j)) = φ (dJ C l R) := by
  fin_cases l <;>
  simp [dJ, jac, grad, unitv, Matrix.det_fin_three, Fin.sum_univ_three, map_ofNat]

/-- The coefficients of `∂J/∂x_l` commute with ring homomorphisms. -/
theorem coeffs_dJ_map {k' : Type*} [CommRing k'] (φ : k →+* k') (C : Fin 3 → Fin 6 → k)
    (l : Fin 3) :
    coeffs (dJ (fun i m => φ (C i m)) l) = fun m => φ (coeffs (dJ C l) m) := by
  have hu : ∀ v : Fin 3 → k, dJ (fun i m => φ (C i m)) l (fun j => φ (v j)) = φ (dJ C l v) :=
    fun v => dJ_map φ C l v
  have e1 : ∀ i : Fin 3, (unitv i : Fin 3 → k') = fun j => φ (unitv i j) := by
    intro i; funext j; simp only [unitv, Pi.single_apply]; split_ifs <;> simp
  have e2 : ∀ i i' : Fin 3,
      (unitv i + unitv i' : Fin 3 → k') = fun j => φ ((unitv i + unitv i' : Fin 3 → k) j) := by
    intro i i'; funext j; simp only [unitv, Pi.add_apply, Pi.single_apply]; split_ifs <;> simp
  funext m
  fin_cases m <;> simp only [coeffs, e2] <;> simp only [e1, hu] <;> simp

/-- The 6 × 6 determinant commutes with ring homomorphisms (for instance reduction modulo a
prime). -/
theorem sixDet_map {k' : Type*} [CommRing k'] (φ : k →+* k') (C : Fin 3 → Fin 6 → k) :
    φ (sixMatrix C).det = (sixMatrix (fun i m => φ (C i m))).det := by
  rw [RingHom.map_det]
  congr 1
  ext r m
  fin_cases r <;> simp [sixMatrix, coeffs_dJ_map]

section Field

variable {K : Type*} [Field K]

/-- A nonzero point has a nonzero Veronese vector. -/
theorem veronese_ne_zero (R : Fin 3 → K) (hR : R ≠ 0) : veronese R ≠ 0 := by
  intro h
  apply hR
  have h0 := congrFun h 0
  have h3 := congrFun h 3
  have h5 := congrFun h 5
  simp [veronese] at h0 h3 h5
  funext i
  fin_cases i <;> simp [h0, h3, h5]

/-- A nonzero point has a nonzero coordinate. -/
theorem exists_ne_zero_of_ne_zero (R : Fin 3 → K) (hR : R ≠ 0) : ∃ a, R a ≠ 0 :=
  Function.ne_iff.mp hR

/-- At a common zero of a net of conics the Jacobian cubic vanishes (any characteristic). -/
theorem jacDet_eq_zero_of_common_zero (C : Fin 3 → Fin 6 → K) (R : Fin 3 → K) (hR : R ≠ 0)
    (h : ∀ i, qev (C i) R = 0) : jacDet C R = 0 := by
  obtain ⟨a, ha⟩ := exists_ne_zero_of_ne_zero R hR
  have key := mul_jacDet C R a
  have hz : ((jac C R).updateCol a (fun i => qev (C i) R)).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero a (fun i => by simp [h])
  rw [hz, mul_zero] at key
  exact (mul_eq_zero.mp key).resolve_left ha

/-- **Base point lemma.** At a common zero of a net of conics, every partial derivative of the
Jacobian cubic vanishes (any characteristic): a base point is a singular point of the Jacobian
curve. -/
theorem dJ_eq_zero_of_common_zero (C : Fin 3 → Fin 6 → K) (R : Fin 3 → K) (hR : R ≠ 0)
    (h : ∀ i, qev (C i) R = 0) (l : Fin 3) : dJ C l R = 0 := by
  obtain ⟨a, ha⟩ := exists_ne_zero_of_ne_zero R hR
  have key := mul_dJ C R a l
  have hsum : ∑ j ∈ Finset.univ.erase a,
      (((jac C R).updateCol j (fun i => jac C (unitv l) i j)).updateCol a
        (fun i => qev (C i) R)).det = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact Matrix.det_eq_zero_of_column_eq_zero a (fun i => by simp [h])
  have hlast : ((jac C R).updateCol a (fun i => jac C R i l)).det = 0 := by
    by_cases hla : l = a
    · subst hla
      rw [Matrix.updateCol_eq_self]
      exact jacDet_eq_zero_of_common_zero C R hR h
    · exact Matrix.det_zero_of_column_eq (Ne.symm hla) (fun i => by
        simp [hla])
  rw [hsum, hlast, mul_zero, zero_add] at key
  exact (mul_eq_zero.mp key).resolve_left ha

/-- If three ternary quadratic forms have a common zero, the 6 × 6 determinant of the coefficients
of the forms and of the three partial derivatives of their Jacobian cubic vanishes (any
characteristic). -/
theorem sixDet_eq_zero_of_common_zero (C : Fin 3 → Fin 6 → K) (R : Fin 3 → K) (hR : R ≠ 0)
    (h : ∀ i, qev (C i) R = 0) : (sixMatrix C).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨veronese R, veronese_ne_zero R hR, ?_⟩
  rw [sixMatrix_mulVec_veronese]
  funext r
  fin_cases r <;> simp [h, dJ_eq_zero_of_common_zero C R hR h]

/-- A nonzero 6 × 6 determinant excludes common zeros of the net. -/
theorem eq_zero_of_sixDet_ne_zero (C : Fin 3 → Fin 6 → K) (hD : (sixMatrix C).det ≠ 0)
    (R : Fin 3 → K) (h : ∀ i, qev (C i) R = 0) : R = 0 := by
  by_contra hR
  exact hD (sixDet_eq_zero_of_common_zero C R hR h)

/-- **Reduction criterion.** For a net over a ring `A` and a ring homomorphism `φ : A → K` to a
field (for instance the residue map at a prime), if `φ` does not kill the 6 × 6 determinant, then
the reduced net has no common zero over `K`. -/
theorem eq_zero_of_map_sixDet_ne_zero {A : Type*} [CommRing A] (φ : A →+* K)
    (C : Fin 3 → Fin 6 → A)
    (hD : φ (sixMatrix C).det ≠ 0) (R : Fin 3 → K) (h : ∀ i, qev (fun m => φ (C i m)) R = 0) :
    R = 0 := by
  rw [sixDet_map] at hD
  exact eq_zero_of_sixDet_ne_zero _ hD R h

end Field

/-! ### The link with formal partial derivatives -/

open MvPolynomial in
/-- The quadratic form with coefficients `c` as a polynomial in `X 0, X 1, X 2`. -/
noncomputable def qpoly (c : Fin 6 → k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.C (c 0) * (X 0 * X 0) + MvPolynomial.C (c 1) * (X 0 * X 1)
    + MvPolynomial.C (c 2) * (X 0 * X 2) + MvPolynomial.C (c 3) * (X 1 * X 1)
    + MvPolynomial.C (c 4) * (X 1 * X 2) + MvPolynomial.C (c 5) * (X 2 * X 2)

open MvPolynomial in
/-- The Jacobian cubic of the net as a polynomial: det (∂ qpoly (C i) / ∂ X j). -/
noncomputable def jacPoly (C : Fin 3 → Fin 6 → k) : MvPolynomial (Fin 3) k :=
  (Matrix.of fun i j => pderiv j (qpoly (C i))).det

open MvPolynomial in
/-- Evaluating `qpoly c` gives `qev c`. -/
theorem eval_qpoly (c : Fin 6 → k) (R : Fin 3 → k) : eval R (qpoly c) = qev c R := by
  simp [qpoly, qev]
  ring

open MvPolynomial in
/-- The formal partial derivatives of `qpoly c` evaluate to `grad c`. -/
theorem eval_pderiv_qpoly (c : Fin 6 → k) (j : Fin 3) (R : Fin 3 → k) :
    eval R (pderiv j (qpoly c)) = grad c R j := by
  fin_cases j <;> simp [qpoly, grad, pderiv_X] <;> ring

open MvPolynomial in
/-- Evaluating `jacPoly C` gives `jacDet C`. -/
theorem eval_jacPoly (C : Fin 3 → Fin 6 → k) (R : Fin 3 → k) :
    eval R (jacPoly C) = jacDet C R := by
  simp only [jacPoly, jacDet, jac, Matrix.det_fin_three, Matrix.of_apply, map_add, map_sub, map_mul,
    eval_pderiv_qpoly]

open MvPolynomial in
/-- The second formal partial derivatives of `qpoly c` are the constants `grad c (unitv l) j`. -/
theorem eval_pderiv_pderiv_qpoly (c : Fin 6 → k) (l j : Fin 3) (R : Fin 3 → k) :
    eval R (pderiv l (pderiv j (qpoly c))) = grad c (unitv l) j := by
  fin_cases j <;> fin_cases l <;> simp [qpoly, grad, unitv, pderiv_X] <;> ring

open MvPolynomial in
/-- `dJ C l` is the formal partial derivative of the Jacobian cubic in `X l`, evaluated at `R`. -/
theorem eval_pderiv_jacPoly (C : Fin 3 → Fin 6 → k) (l : Fin 3) (R : Fin 3 → k) :
    eval R (pderiv l (jacPoly C)) = dJ C l R := by
  have h1 : ∀ c j, eval R (pderiv j (qpoly c)) = grad c R j :=
    fun c j => eval_pderiv_qpoly c j R
  have h2 : ∀ c j, eval R (pderiv l (pderiv j (qpoly c))) = grad c (unitv l) j :=
    fun c j => eval_pderiv_pderiv_qpoly c l j R
  simp only [jacPoly, Matrix.det_fin_three, Matrix.of_apply, map_add, map_sub, Derivation.leibniz,
    smul_eq_mul, map_mul, h1, h2]
  simp only [dJ, Fin.sum_univ_three, Matrix.det_fin_three, jac, Matrix.of_apply]
  simp
  ring

end FurioLombardo.M1.Vendor.NetOfConics
