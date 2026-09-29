import FurioLombardo.M2.Check

/-!
# Element checkers of lane M2 (special primes)

On coordinates `a` of `elt a = Σ a_j w_j` (integral basis `w_j = W_j(θ)/DD`):

* `mulCheck a b z`: `elt a * elt b = elt z`, by the Kronecker identity
  `A(2^512) B(2^512) - DD Z(2^512) = fZ(2^512) Q(2^512)` with the digits of `Q` bounded, where
  `A = Σ a_j W_j` (soundness: `FurioLombardo.M2.mulCheck_sound`);
* `comboEq a l`: `Σ a_j W_j = DD * l`, so `elt a = l(θ)`.
-/

namespace FurioLombardo.M2

/-- Kernel check of `elt a * elt b = elt z`. -/
def mulCheck (a b z : List ℤ) : Bool :=
  a.length == 21 && b.length == 21 && z.length == 21 &&
    allBounded (2 ^ 100) a && allBounded (2 ^ 100) b && allBounded (2 ^ 200) z &&
    (let Hv := dotZ a omL * dotZ b omL - DD * dotZ z omL
     let Qv := Hv / Fk
     let Ql := digitsZ kK 20 Qv
     Hv == Fk * Qv && evalI tK Ql == Qv && allBounded (2 ^ 480) Ql)

/-- `Σ_j a_j W_j` (the same function as `FurioLombardo.M2.combo`, which lives in a Mathlib file). -/
def comboK : List ℤ → List (List ℤ) → List ℤ
  | a :: l, W :: Ws => addZ (smulZ a W) (comboK l Ws)
  | _, _ => []

/-- Kernel check of `Σ a_j W_j = DD * l` (so `elt a = l(θ)`). -/
def comboEq (a l : List ℤ) : Bool := allZero (addZ (comboK a WL) (smulZ (-DD) l))

end FurioLombardo.M2
