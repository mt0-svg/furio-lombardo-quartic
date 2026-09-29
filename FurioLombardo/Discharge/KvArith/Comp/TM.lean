import FurioLombardo.Discharge.KvArith.Comp.BallOps

/-!
# Taylor models over `K_v`: the computational part (lane lean-kv-arith, D2)

No Mathlib import. Semantics (`Encl`, pointwise enclosure on a set `H ⊆ pv^η O_v`) and soundness:
`KvArith/TM.lean`.
-/

namespace FurioLombardo.Discharge.KvArith

/-- Parameters of a Taylor model computation: ball context, domain exponent `η`, order `n`. -/
structure TCtx where
  /-- Ball context. -/
  k : Ctx
  /-- The variable lies in `pv^η O_v`. -/
  η : Nat
  /-- Order. -/
  n : Nat

/-- A Taylor model: coefficient balls (constant term first) and a remainder ball. -/
structure TM where
  /-- Coefficients. -/
  cs : List Ball
  /-- Remainder. -/
  R : Ball
  deriving DecidableEq, Repr

namespace TM

variable (T : TCtx)

/-- The zero ball. -/
def zeroB : Ball := Ball.ofInt T.k 0

/-- The ball `pv^(j η) O_v` of `h^j`. -/
def hpw (j : Nat) : Ball := ⟨(0, 0, 0), 0, min (j * T.η) (3 * T.k.P), 3 * T.k.P⟩

/-- A constant ball. -/
def cst (b : Ball) : TM := ⟨[b], zeroB T⟩

/-- An integer constant. -/
def ofInt (z : Int) : TM := cst T (Ball.ofInt T.k z)

/-- The variable `h`. -/
def var : TM := ⟨[zeroB T, Ball.ofInt T.k 1], zeroB T⟩

/-- Sum. -/
def add (M N : TM) : TM := ⟨(ballOps T.k).zipAdd M.cs N.cs, Ball.add T.k M.R N.R⟩

/-- Difference. -/
def sub (M N : TM) : TM := ⟨(ballOps T.k).zipSub M.cs N.cs, Ball.sub T.k M.R N.R⟩

/-- Negation. -/
def neg (M : TM) : TM := ⟨M.cs.map (Ball.neg T.k), Ball.neg T.k M.R⟩

/-- The ball of a polynomial part over `H`. -/
def pball (cs : List Ball) : Ball := (ballOps T.k).horner cs (hpw T 1)

/-- The ball of the values on `H`. -/
def ball (M : TM) : Ball := Ball.add T.k (pball T M.cs) (Ball.mul T.k (hpw T (T.n + 1)) M.R)

/-- Product. -/
def mul (M N : TM) : TM :=
  let C := (ballOps T.k).conv M.cs N.cs
  let hi := pball T (C.drop (T.n + 1))
  let R1 := Ball.add T.k hi (Ball.mul T.k M.R (pball T N.cs))
  let R2 := Ball.add T.k (Ball.mul T.k N.R (pball T M.cs))
    (Ball.mul T.k (hpw T (T.n + 1)) (Ball.mul T.k M.R N.R))
  ⟨C.take (T.n + 1), Ball.add T.k R1 R2⟩

/-- A remainder only: `⟨[], b⟩`, which encloses `h^(n+1) G(h)` for `G` with values in `b`. -/
def rem (b : Ball) : TM := ⟨[], b⟩

/-- Truncation to `n + 1` coefficients, the dropped part moved into the remainder. -/
def trunc (M : TM) : TM :=
  ⟨M.cs.take (T.n + 1), Ball.add T.k (pball T (M.cs.drop (T.n + 1))) M.R⟩

/-- Inverse with fixed coefficients: `P` the formal inverse of the coefficients (`Ops.invSeries` on
balls), so `F P = 1 + h^(n+1) ρ` exactly and `1/F = P - h^(n+1) ρ (1/F)`, with `1/F(h)` in the inverse of
the ball of `F` over `H`. -/
def inv (M : TM) : Option TM := do
  let M := trunc T M
  let gbi ← (ballOps T.k).inv (ball T M)
  let ds ← (ballOps T.k).invSeries T.n M.cs
  let E := mul T M ⟨ds, zeroB T⟩
  pure ⟨ds, Ball.neg T.k (Ball.mul T.k E.R gbi)⟩

/-- Square root with fixed coefficients near the root candidate `evN s / 2^es` of the constant
coefficient: `P` the formal square root (`Ops.sqrtSeries` from the ball `Ball.sqrt C₀` of the root of the
constant coefficient), so `A - P² = h^(n+1) ρ` exactly and `r - P = h^(n+1) ρ / (r + P)` for every branch
`r` with values in the returned ball `rb` of the roots over `H`, `r + P` certified nonzero. -/
def sqrt (M : TM) (s : N3) (es : Nat) : Option (TM × Ball) := do
  let M := trunc T M
  let r0 ← Ball.sqrt T.k (M.cs.headD (zeroB T)) s es
  let rb ← Ball.sqrt T.k (ball T M) s es
  let ps ← (ballOps T.k).sqrtSeries T.n M.cs r0
  let P : TM := ⟨ps, zeroB T⟩
  let di ← (ballOps T.k).inv (Ball.add T.k rb (ball T P))
  let D := sub T M (mul T P P)
  pure (⟨ps, Ball.mul T.k D.R di⟩, rb)

/-- Inclusion of Taylor models: the same number of coefficients, each coefficient ball and the remainder
ball included (`Ball.incl`). -/
def incl (M M' : TM) : Bool :=
  M.cs.length == M'.cs.length && (M.cs.zip M'.cs).all (fun p => Ball.incl T.k p.1 p.2) &&
    Ball.incl T.k M.R M'.R

/-- The ball of `(F h - Σ_{i<j} cᵢ hⁱ) / h^j` over `H` (for `j ≤ n + 1`). -/
def split (j : Nat) (M : TM) : Ball :=
  Ball.add T.k (pball T (M.cs.drop j)) (Ball.mul T.k (hpw T (T.n + 1 - j)) M.R)

end TM

/-- The Taylor model carrier. -/
def tmOps (T : TCtx) : Ops TM where
  add := TM.add T
  sub := TM.sub T
  neg := TM.neg T
  mul := TM.mul T
  inv := TM.inv T
  ofInt := TM.ofInt T

/-- The point of a disc with fixed coefficients: the root `u(h)` in the ball `U` of `F(t₀ + t₁ h, Y)`.
`P` is the formal root (`Ops.rootSeries` on balls from the ball `y0` of a root of `F(t₀, Y)`), so
`F(t₀ + t₁ h, P) = h^(n+1) ρ` exactly, and `u = P - F(t₀ + t₁ h, P) / G` with `G` the divided difference
of `F` in `Y` between `P(h)` and `u(h)` (`Ops.ddZ2` on the balls of `t₀ + t₁ h`, `P` and `U`), certified
nonzero. -/
def TM.root (T : TCtx) (F : List (List Int)) (t0 t1 y0 U : Ball) : Option TM := do
  let ps ← (ballOps T.k).rootSeries T.n F t0 t1 y0
  let Tt : TM := ⟨[t0, t1], TM.zeroB T⟩
  let P : TM := ⟨ps, TM.zeroB T⟩
  let Q := (tmOps T).hornerZ2 F Tt P
  let g ← (ballOps T.k).inv ((ballOps T.k).ddZ2 F (TM.ball T Tt) (TM.ball T P) U)
  pure ⟨ps, Ball.neg T.k (Ball.mul T.k Q.R g)⟩

end FurioLombardo.Discharge.KvArith
