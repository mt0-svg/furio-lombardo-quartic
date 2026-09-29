import FurioLombardo.M1.ZK
import FurioLombardo.M1.Vendor.NetOfConics
import FurioLombardo.Statement

/-!
# Kronecker expressions for nets of conics

The formulas of `Vendor.NetOfConics` (gradient, Jacobian, `dJ`, `coeffs`) written as Kronecker
expressions (`gradKE`, `det3KE`, `dJKE`, `coeffsKE`), so that the kernel can check the
coefficients of the partial derivatives of the Jacobian cubic of an explicit net. `evK_coeffsKE_dJKE`
says the expression evaluates to the coefficient of the ring formula.

Also the product of two ternary quadratic forms on the fifteen quartic monomials (`conv`, `m4`,
`qev_mul_qev`), with its Kronecker version `convKE`, used for the Bruin identity.
-/

namespace FurioLombardo.M1

open Kron Vendor.NetOfConics

/-! ## Nets of conics -/

/-- The gradient of a conic, as expressions. -/
def gradKE (c : Fin 6 → KE) (R : Fin 3 → KE) : Fin 3 → KE :=
  ![.add (.add (.mul (.mul (.int 2) (c 0)) (R 0)) (.mul (c 1) (R 1))) (.mul (c 2) (R 2)),
    .add (.add (.mul (c 1) (R 0)) (.mul (.mul (.int 2) (c 3)) (R 1))) (.mul (c 4) (R 2)),
    .add (.add (.mul (c 2) (R 0)) (.mul (c 4) (R 1))) (.mul (.mul (.int 2) (c 5)) (R 2))]

/-- The 3 × 3 determinant, as an expression (the formula of `Matrix.det_fin_three`). -/
def det3KE (a : Fin 3 → Fin 3 → KE) : KE :=
  KE.sub (KE.add (KE.add (KE.sub (KE.sub (.mul (.mul (a 0 0) (a 1 1)) (a 2 2))
    (.mul (.mul (a 0 0) (a 1 2)) (a 2 1))) (.mul (.mul (a 0 1) (a 1 0)) (a 2 2)))
    (.mul (.mul (a 0 1) (a 1 2)) (a 2 0))) (.mul (.mul (a 0 2) (a 1 0)) (a 2 1)))
    (.mul (.mul (a 0 2) (a 1 1)) (a 2 0))

/-- The unit vector `e_l`, as expressions. -/
def unitKE (l : Fin 3) : Fin 3 → KE := fun j => if j = l then .int 1 else .int 0

/-- `∂J/∂x_l` at `R`, as an expression. -/
def dJKE (C : Fin 3 → Fin 6 → KE) (l : Fin 3) (R : Fin 3 → KE) : KE :=
  .add (.add
    (det3KE fun i j => if j = 0 then gradKE (C i) (unitKE l) 0 else gradKE (C i) R j)
    (det3KE fun i j => if j = 1 then gradKE (C i) (unitKE l) 1 else gradKE (C i) R j))
    (det3KE fun i j => if j = 2 then gradKE (C i) (unitKE l) 2 else gradKE (C i) R j)

/-- Sum of two vectors of expressions. -/
def addKE (u v : Fin 3 → KE) : Fin 3 → KE := fun j => .add (u j) (v j)

/-- The coefficients of a quadratic form from its values, as expressions. -/
def coeffsKE (f : (Fin 3 → KE) → KE) : Fin 6 → KE :=
  ![f (unitKE 0), .sub (.sub (f (addKE (unitKE 0) (unitKE 1))) (f (unitKE 0))) (f (unitKE 1)),
    .sub (.sub (f (addKE (unitKE 0) (unitKE 2))) (f (unitKE 0))) (f (unitKE 2)),
    f (unitKE 1), .sub (.sub (f (addKE (unitKE 1) (unitKE 2))) (f (unitKE 1))) (f (unitKE 2)),
    f (unitKE 2)]

theorem evK_gradKE (c : Fin 6 → KE) (R : Fin 3 → KE) (j : Fin 3) :
    evK (gradKE c R j) = grad (fun m => evK (c m)) (fun i => evK (R i)) j := by
  fin_cases j <;> simp [gradKE, grad]

theorem evK_det3KE (a : Fin 3 → Fin 3 → KE) :
    evK (det3KE a) = (Matrix.of fun i j => evK (a i j)).det := by
  rw [Matrix.det_fin_three]
  simp [det3KE]

theorem evK_unitKE (l : Fin 3) : (fun j => evK (unitKE l j)) = (unitv l : Fin 3 → K21) := by
  funext j
  simp only [unitKE, unitv, Pi.single_apply]
  split_ifs <;> simp

theorem evK_dJKE (C : Fin 3 → Fin 6 → KE) (l : Fin 3) (R : Fin 3 → KE) :
    evK (dJKE C l R) = dJ (fun i m => evK (C i m)) l (fun j => evK (R j)) := by
  have hg : ∀ (c : Fin 6 → KE) (j : Fin 3),
      evK (gradKE c (unitKE l) j) = grad (fun m => evK (c m)) (unitv l) j := by
    intro c j
    rw [evK_gradKE, evK_unitKE]
  simp only [dJKE, evK_add, evK_det3KE, dJ, Fin.sum_univ_three]
  congr 2 <;> congr 1 <;> ext i j <;> fin_cases j <;>
    simp [Matrix.updateCol_apply, jac, hg, evK_gradKE]

theorem evK_addKE (u v : Fin 3 → KE) :
    (fun j => evK (addKE u v j)) = (fun j => evK (u j)) + (fun j => evK (v j)) := by
  funext j; simp [addKE]

theorem evK_coeffsKE (f : (Fin 3 → KE) → KE) (g : (Fin 3 → K21) → K21)
    (hf : ∀ R, evK (f R) = g (fun j => evK (R j))) (m : Fin 6) :
    evK (coeffsKE f m) = coeffs g m := by
  fin_cases m <;> simp [coeffsKE, coeffs, hf, evK_addKE, evK_unitKE]

theorem evK_coeffsKE_dJKE (C : Fin 3 → Fin 6 → KE) (l : Fin 3) (m : Fin 6) :
    evK (coeffsKE (dJKE C l) m) = coeffs (dJ (fun i m => evK (C i m)) l) m :=
  evK_coeffsKE _ _ (fun R => evK_dJKE C l R) m

/-! ## Products of two conics -/

/-- The fifteen quartic monomials `x^4, x^3 y, x^3 z, x^2 y^2, x^2 y z, x^2 z^2, x y^3, x y^2 z,
x y z^2, x z^3, y^4, y^3 z, y^2 z^2, y z^3, z^4`. -/
def m4 {k : Type*} [CommRing k] (R : Fin 3 → k) : Fin 15 → k :=
  ![R 0 ^ 4, R 0 ^ 3 * R 1, R 0 ^ 3 * R 2, R 0 ^ 2 * R 1 ^ 2, R 0 ^ 2 * R 1 * R 2,
    R 0 ^ 2 * R 2 ^ 2, R 0 * R 1 ^ 3, R 0 * R 1 ^ 2 * R 2, R 0 * R 1 * R 2 ^ 2, R 0 * R 2 ^ 3,
    R 1 ^ 4, R 1 ^ 3 * R 2, R 1 ^ 2 * R 2 ^ 2, R 1 * R 2 ^ 3, R 2 ^ 4]

/-- The pairs of conic monomials whose product is the quartic monomial `μ`. -/
def ctab : Fin 15 → List (Fin 6 × Fin 6) :=
  ![[(0, 0)], [(0, 1), (1, 0)], [(0, 2), (2, 0)], [(0, 3), (3, 0), (1, 1)],
    [(0, 4), (4, 0), (1, 2), (2, 1)], [(0, 5), (5, 0), (2, 2)], [(1, 3), (3, 1)],
    [(1, 4), (4, 1), (2, 3), (3, 2)], [(1, 5), (5, 1), (2, 4), (4, 2)], [(2, 5), (5, 2)],
    [(3, 3)], [(3, 4), (4, 3)], [(3, 5), (5, 3), (4, 4)], [(4, 5), (5, 4)], [(5, 5)]]

/-- Coefficients of the product of two conics. -/
def conv {k : Type*} [CommRing k] (a b : Fin 6 → k) (μ : Fin 15) : k :=
  ((ctab μ).map fun p => a p.1 * b p.2).sum

theorem qev_mul_qev {k : Type*} [CommRing k] (a b : Fin 6 → k) (R : Fin 3 → k) :
    qev a R * qev b R = ∑ μ, conv a b μ * m4 R μ := by
  simp only [qev, conv, ctab, m4, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

/-- Coefficients of `F` on the quartic monomials. -/
def fcoef : Fin 15 → ℤ := ![1, 3, 0, 0, -3, -3, 6, -6, 3, -2, 4, 2, 0, -5, 0]

theorem F_eq_sum {k : Type*} [CommRing k] (R : Fin 3 → k) :
    FurioLombardo.F (R 0) (R 1) (R 2) = ∑ μ, (fcoef μ : k) * m4 R μ := by
  simp only [FurioLombardo.F, fcoef, m4, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  ring

/-- Coefficients of the product of two conics, as expressions. -/
def convKE (a b : Fin 6 → KE) (μ : Fin 15) : KE :=
  KE.sum ((ctab μ).map fun p => .mul (a p.1) (b p.2))

theorem evK_convKE (a b : Fin 6 → KE) (μ : Fin 15) :
    evK (convKE a b μ) = conv (fun m => evK (a m)) (fun m => evK (b m)) μ := by
  simp [convKE, conv, evK_sum, List.map_map, Function.comp_def]

end FurioLombardo.M1
