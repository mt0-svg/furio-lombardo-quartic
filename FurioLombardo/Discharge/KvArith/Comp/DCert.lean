import FurioLombardo.Discharge.KvArith.Comp.BallOps
import FurioLombardo.Discharge.KvArith.Comp.Cantor

/-!
# The input and output programs of the D_i value certificate: the computational part (lane lean-kv-arith)

No Mathlib import. Straight line programs over any `Ops` for the Mumford data of `SelmerSpan.Dpt`
(`Ops.divW`, `Ops.divR1`, `Ops.divR0`: the remainder of `Σ g_j X^j` by `X² + pX + r`; `Ops.normN`,
`Ops.normA`: the radicands of `n` and `a`; `Ops.sqB`, `Ops.sqC`: the coefficients of `V`), the
coefficients 0 and 1 of the translate `F(X + a)` (`Ops.transC0`, `Ops.transC1`), and three certified comparisons on balls:
`Ball.nearOK` (`‖x - y‖ < ‖2y‖`), `Ball.normLe` (`‖x‖ ≤ ‖pv‖^n`), `Ball.normLeMul`
(`‖x‖ ‖pv‖^a ≤ ‖y‖`), with the error ball `Ball.errB`. Soundness: `KvArith/DCert.lean`.
-/

universe u

namespace FurioLombardo.Discharge.KvArith

section Programs

variable {A : Type u} (o : Ops A)

/-- The quotient coefficients `w4, ..., w0` of `Σ g_j X^j` by `X² + pX + r` (`SelmerSpan.divW`). -/
def Ops.divW (p r _g0 _g1 g2 g3 g4 g5 g6 : A) : A × A × A × A × A :=
  let w4 := g6
  let w3 := o.sub g5 (o.mul p w4)
  let w2 := o.sub (o.sub g4 (o.mul p w3)) (o.mul r w4)
  let w1 := o.sub (o.sub g3 (o.mul p w2)) (o.mul r w3)
  let w0 := o.sub (o.sub g2 (o.mul p w1)) (o.mul r w2)
  (w4, w3, w2, w1, w0)

/-- The coefficient of `X` of the remainder (`SelmerSpan.divR1`). -/
def Ops.divR1 (p r g0 g1 g2 g3 g4 g5 g6 : A) : A :=
  let w := o.divW p r g0 g1 g2 g3 g4 g5 g6
  o.sub (o.sub g1 (o.mul p w.2.2.2.2)) (o.mul r w.2.2.2.1)

/-- The constant coefficient of the remainder (`SelmerSpan.divR0`). -/
def Ops.divR0 (p r g0 g1 g2 g3 g4 g5 g6 : A) : A :=
  let w := o.divW p r g0 g1 g2 g3 g4 g5 g6
  o.sub g0 (o.mul r w.2.2.2.2)

/-- `Z0² - p Z1 Z0 + r Z1²` (`SelmerSpan.Nv`). -/
def Ops.normN (p r Z1 Z0 : A) : A :=
  o.add (o.sub (o.mul Z0 Z0) (o.mul (o.mul p Z1) Z0)) (o.mul r (o.mul Z1 Z1))

/-- `2 Z0 - p Z1 + 2 n` (the radicand of `SelmerSpan.av`). -/
def Ops.normA (p Z1 Z0 n : A) : A :=
  o.add (o.sub (o.mul (o.ofInt 2) Z0) (o.mul p Z1)) (o.mul (o.ofInt 2) n)

/-- `b = Z1 / (2a)` (`SelmerSpan.sqB`). -/
def Ops.sqB (Z1 a : A) : Option A := do
  let i ← o.inv (o.mul (o.ofInt 2) a)
  pure (o.mul Z1 i)

/-- `c = a/4 + b p/2` with `b = sqB Z1 a` given (`SelmerSpan.sqC`). -/
def Ops.sqC (p a b : A) : Option A := do
  let i4 ← o.inv (o.ofInt 4)
  let i2 ← o.inv (o.ofInt 2)
  pure (o.add (o.mul a i4) (o.mul (o.mul b p) i2))

/-- The constant coefficient `Σ_n a^n F_n` of `F(X + a)`. -/
def Ops.transC0 (a : Int) (F : Sext A) : A :=
  o.add (o.add (o.add (o.add (o.add (o.add F.f0 (o.mul (o.ofInt a) F.f1)) (o.mul (o.ofInt (a ^ 2)) F.f2))
    (o.mul (o.ofInt (a ^ 3)) F.f3)) (o.mul (o.ofInt (a ^ 4)) F.f4)) (o.mul (o.ofInt (a ^ 5)) F.f5))
    (o.mul (o.ofInt (a ^ 6)) F.f6)

/-- The coefficient of `X` `Σ_n (n + 1) a^n F_(n+1)` of `F(X + a)`. -/
def Ops.transC1 (a : Int) (F : Sext A) : A :=
  o.add (o.add (o.add (o.add (o.add F.f1 (o.mul (o.ofInt (2 * a)) F.f2)) (o.mul (o.ofInt (3 * a ^ 2)) F.f3))
    (o.mul (o.ofInt (4 * a ^ 3)) F.f4)) (o.mul (o.ofInt (5 * a ^ 4)) F.f5)) (o.mul (o.ofInt (6 * a ^ 5)) F.f6)

end Programs

/-- A 2 x 2 matrix in coordinates. -/
structure Mat2 (A : Type u) where
  /-- Entry `(0, 0)`. -/
  a00 : A
  /-- Entry `(0, 1)`. -/
  a01 : A
  /-- Entry `(1, 0)`. -/
  a10 : A
  /-- Entry `(1, 1)`. -/
  a11 : A
  deriving DecidableEq, Repr

namespace Ball

variable (k : Ctx)

/-- Certified `‖x - y‖ < ‖2y‖` for `x ∈ bx`, `y ∈ by`: the difference ball against the certified
nonzero ball of `2y`. -/
def nearOK (bx bY : Ball) : Bool :=
  let d := Ball.sub k bx bY
  let t := Ball.mul k (Ball.ofInt k 2) bY
  t.nz k && decide (vN k t.c + 3 * d.e < min (vN k d.c) d.r + 3 * t.e)

/-- Certified `‖x‖ ≤ ‖pv‖^n` for `x ∈ b`. -/
def normLe (b : Ball) (n : Nat) : Bool := decide (n + 3 * b.e ≤ min (vN k b.c) b.r)

/-- Certified `‖x‖ ‖pv‖^a ≤ ‖y‖` for `x ∈ bx`, `y ∈ by`. -/
def normLeMul (bx bY : Ball) (a : Nat) : Bool :=
  bY.nz k && decide (vN k bY.c + 3 * bx.e ≤ min (vN k bx.c) bx.r + a + 3 * bY.e)

/-- The ball `‖x‖ ≤ ‖pv‖^R` of scale 0 around 0. -/
def errB (R : Nat) : Ball := ⟨(0, 0, 0), 0, R, 3 * k.P⟩

end Ball

end FurioLombardo.Discharge.KvArith
