import FurioLombardo.Discharge.KvArith.Comp.Ops

/-!
# Cantor's composition and reduction: the computational part (lane lean-kv-arith, D5)

No Mathlib import. Mumford pairs in coordinates and the programs `compAdd`, `compDbl`, `reduce4`,
`cantorAdd`, `cantorDbl`, `revD` over any `Ops`; relational soundness and the class statements:
`KvArith/Cantor.lean`.
-/

universe u

namespace FurioLombardo.Discharge.KvArith


/-- A Mumford pair `[X² + u₁X + u₀, v₁X + v₀]` in coordinates. -/
structure Mum (A : Type u) where
  /-- `u₀`. -/
  u0 : A
  /-- `u₁`. -/
  u1 : A
  /-- `v₀`. -/
  v0 : A
  /-- `v₁`. -/
  v1 : A
  deriving DecidableEq, Repr

/-- Coefficients `c₀, c₁, c₂, c₃` (a monic quartic `X⁴ + c₃X³ + ...`, or a cubic `c₃X³ + ...`). -/
structure Quart (A : Type u) where
  /-- `c₀`. -/
  c0 : A
  /-- `c₁`. -/
  c1 : A
  /-- `c₂`. -/
  c2 : A
  /-- `c₃`. -/
  c3 : A
  deriving DecidableEq, Repr

/-- The coefficients `f₀, ..., f₆` of a polynomial of degree at most 6. -/
structure Sext (A : Type u) where
  /-- `f₀`. -/
  f0 : A
  /-- `f₁`. -/
  f1 : A
  /-- `f₂`. -/
  f2 : A
  /-- `f₃`. -/
  f3 : A
  /-- `f₄`. -/
  f4 : A
  /-- `f₅`. -/
  f5 : A
  /-- `f₆`. -/
  f6 : A
  deriving DecidableEq, Repr

section Programs

variable {A : Type u} (o : Ops A)

/-- Composition of two pairs with coprime `u`'s: `(U, w)` with `U = u u'`. -/
def compAdd (D E : Mum A) : Option (Quart A × Quart A) := do
  let g0 := o.sub D.u0 E.u0
  let g1 := o.sub D.u1 E.u1
  let N := o.add (o.sub (o.mul g0 g0) (o.mul (o.mul g0 g1) E.u1)) (o.mul (o.mul g1 g1) E.u0)
  let Ni ← o.inv N
  let i0 := o.mul (o.sub g0 (o.mul g1 E.u1)) Ni
  let i1 := o.neg (o.mul g1 Ni)
  let d0 := o.sub E.v0 D.v0
  let d1 := o.sub E.v1 D.v1
  let k0 := o.sub (o.mul d0 i0) (o.mul (o.mul d1 i1) E.u0)
  let k1 := o.sub (o.add (o.mul d0 i1) (o.mul d1 i0)) (o.mul (o.mul d1 i1) E.u1)
  let U : Quart A := ⟨o.mul D.u0 E.u0, o.add (o.mul D.u0 E.u1) (o.mul D.u1 E.u0),
    o.add (o.add D.u0 (o.mul D.u1 E.u1)) E.u0, o.add D.u1 E.u1⟩
  let w : Quart A := ⟨o.add D.v0 (o.mul D.u0 k0), o.add (o.add D.v1 (o.mul D.u1 k0)) (o.mul D.u0 k1),
    o.add k0 (o.mul D.u1 k1), k1⟩
  pure (U, w)

/-- Composition of a pair with itself: `(U, w)` with `U = u²`. -/
def compDbl (f : Sext A) (D : Mum A) : Option (Quart A × Quart A) := do
  -- g = f - v²
  let g3 := f.f3
  let g2 := o.sub f.f2 (o.mul D.v1 D.v1)
  -- h = g div u (quartic)
  let h4 := f.f6
  let h3 := o.sub f.f5 (o.mul D.u1 h4)
  let h2 := o.sub (o.sub f.f4 (o.mul D.u1 h3)) (o.mul D.u0 h4)
  let h1 := o.sub (o.sub g3 (o.mul D.u1 h2)) (o.mul D.u0 h3)
  let h0 := o.sub (o.sub g2 (o.mul D.u1 h1)) (o.mul D.u0 h2)
  -- η = h mod u
  let q1 := o.sub h3 (o.mul D.u1 h4)
  let q0 := o.sub (o.sub h2 (o.mul D.u1 q1)) (o.mul D.u0 h4)
  let e1 := o.sub (o.sub h1 (o.mul D.u1 q0)) (o.mul D.u0 q1)
  let e0 := o.sub h0 (o.mul D.u0 q0)
  -- (2v)⁻¹ mod u
  let b0 := o.add D.v0 D.v0
  let b1 := o.add D.v1 D.v1
  let N := o.add (o.sub (o.mul b0 b0) (o.mul (o.mul b0 b1) D.u1)) (o.mul (o.mul b1 b1) D.u0)
  let Ni ← o.inv N
  let i0 := o.mul (o.sub b0 (o.mul b1 D.u1)) Ni
  let i1 := o.neg (o.mul b1 Ni)
  let k0 := o.sub (o.mul e0 i0) (o.mul (o.mul e1 i1) D.u0)
  let k1 := o.sub (o.add (o.mul e0 i1) (o.mul e1 i0)) (o.mul (o.mul e1 i1) D.u1)
  let U : Quart A := ⟨o.mul D.u0 D.u0, o.add (o.mul D.u0 D.u1) (o.mul D.u1 D.u0),
    o.add (o.add D.u0 (o.mul D.u1 D.u1)) D.u0, o.add D.u1 D.u1⟩
  let w : Quart A := ⟨o.add D.v0 (o.mul D.u0 k0), o.add (o.add D.v1 (o.mul D.u1 k0)) (o.mul D.u0 k1),
    o.add k0 (o.mul D.u1 k1), k1⟩
  pure (U, w)

/-- One reduction step: from `U` monic quartic and `w` cubic with `U ∣ f - w²` to a pair. -/
def reduce4 (f : Sext A) (U w : Quart A) : Option (Mum A) := do
  let g6 := o.sub f.f6 (o.mul w.c3 w.c3)
  let g5 := o.sub f.f5 (o.add (o.mul w.c2 w.c3) (o.mul w.c3 w.c2))
  let g4 := o.sub f.f4 (o.add (o.add (o.mul w.c1 w.c3) (o.mul w.c3 w.c1)) (o.mul w.c2 w.c2))
  let q1 := o.sub g5 (o.mul g6 U.c3)
  let q0 := o.sub (o.sub g4 (o.mul q1 U.c3)) (o.mul g6 U.c2)
  let li ← o.inv g6
  let s1 := o.mul q1 li
  let s0 := o.mul q0 li
  let t1 := o.neg (o.add (o.sub (o.mul w.c3 (o.sub (o.mul s1 s1) s0)) (o.mul w.c2 s1)) w.c1)
  let t0 := o.neg (o.add (o.sub (o.mul w.c3 (o.mul s1 s0)) (o.mul w.c2 s0)) w.c0)
  pure ⟨s0, s1, t0, t1⟩

/-- Cantor's addition of pairs with coprime `u`'s. -/
def cantorAdd (f : Sext A) (D E : Mum A) : Option (Mum A) := do
  let Uw ← compAdd o D E
  reduce4 o f Uw.1 Uw.2

/-- Cantor's doubling. -/
def cantorDbl (f : Sext A) (D : Mum A) : Option (Mum A) := do
  let Uw ← compDbl o f D
  reduce4 o f Uw.1 Uw.2

/-- The pair on the reversed model `X^6 f(1/X)`: `[X² + (u₁/u₀)X + 1/u₀, X³ v(1/X) mod u']`. -/
def revD (D : Mum A) : Option (Mum A) := do
  let p0 ← o.inv D.u0
  let p1 := o.mul D.u1 p0
  let t1 := o.sub (o.mul D.v0 (o.sub (o.mul p1 p1) p0)) (o.mul D.v1 p1)
  let t0 := o.sub (o.mul D.v0 (o.mul p1 p0)) (o.mul D.v1 p0)
  pure ⟨p0, p1, t0, t1⟩

/-- The opposite pair `[u, -v]`. -/
def Mum.neg (D : Mum A) : Mum A := ⟨D.u0, D.u1, o.neg D.v0, o.neg D.v1⟩

/-- The pair translated by `a`: `[u(X + a), v(X + a)]`, so `u(X + a) = X² + t₀X + t₁` gives R7's chart
coordinates `t = (u₁ + 2a, u₀ + a u₁ + a²)` and `v(X + a) = v₁X + (v₀ + a v₁)`. -/
def Mum.shift (a : A) (D : Mum A) : Mum A :=
  ⟨o.add (o.add D.u0 (o.mul a D.u1)) (o.mul a a), o.add D.u1 (o.add a a), o.add D.v0 (o.mul a D.v1), D.v1⟩

end Programs

/-- The reversed polynomial `X^6 f(1/X)` of a sextic. -/
def Sext.rev {A : Type u} (f : Sext A) : Sext A := ⟨f.f6, f.f5, f.f4, f.f3, f.f2, f.f1, f.f0⟩

end FurioLombardo.Discharge.KvArith
