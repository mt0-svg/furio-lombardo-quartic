import FurioLombardo.Discharge.KvArith.Comp.TM
import FurioLombardo.Discharge.M4Box.Comp.Cert

/-!
# The box programs of the per box statements: the computational part (lane lean-m4box, D9)

No Mathlib import. For a box `{X0 + 2^s Y}` of the disc `d` on the branch `e`, the Taylor models in
`h = 2^s Y` (domain exponent `3 s`) of:

* the disc point `p(h) = discPt d (X0 + h) (u h)`, `u` the root of `G1 d (X0 + h) Y` (`TM.root` on the
  coefficient list `G1L d`), and the radicand `Q1/δ` (or `Q3/δ`) and `Q2/δ` at `p(h)` (`boxP`);
* the lift: `y = TM.sqrt` of the radicand, its ball certified on the branch (`nearOK` against the
  reference root), the other coordinate `Q2/(δ y)`, and the pair of `φ_v(x(h))` (`boxPhi`, `apPhi`);
* the pair `R` of `E0 - φ_v(x(0))`, a ball run from the constant coefficients of the pair above (their
  balls hold the exact values at `h = 0`), and the sum `Q = φ_v(x(h)) + R`, translated by `a = k`, with
  `Amat t` for its chart coordinates `t = (Z.u1, Z.u0)` (`boxChart`).

`boxP`, `boxPhi`, `boxChart` are programs over any `Ops` carrier: their soundness is the relation lemma of
each, run on `tmOpsF` (the computation: `tmOps` with the valuation bounds recomputed), on truncated series times functions (`rel_tmOps`) and on `K_v`
at each point of the box. `constOK`, `tailOK`: the checks of `ConstCert`, `TailCert`. Soundness:
`M4Box/BoxTM.lean`.
-/

namespace FurioLombardo.Discharge.M4Box

open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Log

universe u v

/-! ## Maps of the records -/

/-- Entrywise image of a `Sym3`. -/
def Sym3.cmap {A : Type u} {B : Type v} (f : A → B) (m : Sym3 A) : Sym3 B :=
  ⟨f m.a00, f m.a01, f m.a02, f m.a11, f m.a12, f m.a22⟩

/-- Entrywise image of a pair. -/
def _root_.FurioLombardo.Discharge.KvArith.Mum.cmap {A : Type u} {B : Type v} (f : A → B) (D : Mum A) : Mum B :=
  ⟨f D.u0, f D.u1, f D.v0, f D.v1⟩

/-- Entrywise image of a sextic. -/
def _root_.FurioLombardo.Discharge.KvArith.Sext.cmap {A : Type u} {B : Type v} (f : A → B) (g : Sext A) : Sext B :=
  ⟨f g.f0, f g.f1, f g.f2, f g.f3, f g.f4, f g.f5, f g.f6⟩

/-- Entrywise image of a `Mat2`. -/
def _root_.FurioLombardo.Discharge.KvArith.Mat2.cmap {A : Type u} {B : Type v} (f : A → B) (m : Mat2 A) : Mat2 B :=
  ⟨f m.a00, f m.a01, f m.a10, f m.a11⟩

/-- `G1 d` as the list, over the powers of `X`, of its coefficient lists in `Y` (`Ops.hornerZ2`). -/
def G1L : Nat → List (List Int)
  | 1 => [[0, -5, 0, 8, 32], [-2, 6, -24, 48], [-6, -12], [0, 24], [8]]
  | 2 => [[-1, -1, -6, 16, 16], [-2, 6, -12, 24], [3, 12], [8, 12], [4]]
  | 3 => [[0, 13, 42, 48, 16], [1, 12, 24, 24], [9, 12], [14, 12], [4]]
  | 4 => [[1, 1, 0, -10], [3, -6, 6, -8], [0, -6, -12], [6], [4]]
  | 5 => [[7, -7, 0, -28], [19, -24, -12, -16], [30, -12, -24], [28], [8]]
  | _ => []

/-! ## The programs over `Ops` -/

section Programs

variable {A : Type u} (o : Ops A)

/-- The point `w = discPt d X Y`, the radicand `Q1/δ` (`wh`) or `Q3/δ`, and `Q2/δ`, with `idl = 1/δ`. -/
def boxP (d : Nat) (wh : Bool) (m0 m1 m2 : Sym3 A) (idl X Y : A) : (A × A × A) × A × A :=
  let w := discPtO o d X Y
  let q1 := Sym3.quad o m0 w.1 w.2.1 w.2.2
  let q2 := Sym3.quad o m1 w.1 w.2.1 w.2.2
  let q3 := Sym3.quad o m2 w.1 w.2.1 w.2.2
  (w, o.mul (if wh then q1 else q3) idl, o.mul q2 idl)

/-- The pair of `φ_v` at the point over `w` whose coordinate `r` (`wh`) or `s` is `y`, the other one
`Q2/(δ y)`: the input of `apInBall` (swapped model). -/
def boxPhi (wh : Bool) (prm : APPrm) (m0 m1 m2 : Sym3 A) (dl : A) (w : A × A × A) (q2d y : A) :
    Option (Mum A) := do
  let iy ← o.inv y
  let z := o.mul q2d iy
  apPhi o prm (if wh then ⟨m2, m1, m0, dl, w.1, w.2.1, w.2.2, z, y⟩
    else ⟨m2, m1, m0, dl, w.1, w.2.1, w.2.2, y, z⟩)

/-- The sum `Q = m + R` translated by `a` (its `u₁, u₀` are the chart coordinates), and `Amat t`. -/
def boxChart (f : Sext A) (a : A) (Am : Mat2 A) (m R : Mum A) : Option (Mum A × A × A) := do
  let Q ← cantorAdd o f m R
  let Z := Mum.shift o a Q
  pure (Z, o.add (o.mul Am.a00 Z.u1) (o.mul Am.a01 Z.u0), o.add (o.mul Am.a10 Z.u1) (o.mul Am.a11 Z.u0))

end Programs

/-! ## The Taylor model run of a box -/

/-- The valuation bounds of a Taylor model recomputed from the centres (`Ball.fresh`). -/
def TM.fresh (T : TCtx) (M : TM) : TM := ⟨M.cs.map (Ball.fresh T.k), Ball.fresh T.k M.R⟩

/-- The Taylor model carrier with the valuation bounds recomputed after each operation: with the stale
bounds of `tmOps` the products of `TM.ball` lose the valuation of the coefficients (the analogue of
`ballOpsF` for balls). -/
def tmOpsF (T : TCtx) : Ops TM where
  add M N := TM.fresh T (TM.add T M N)
  sub M N := TM.fresh T (TM.sub T M N)
  neg := TM.neg T
  mul M N := TM.fresh T (TM.mul T M N)
  inv M := (TM.inv T (TM.fresh T M)).map (TM.fresh T)
  ofInt := TM.ofInt T

/-- The data of a box run: twist `kk`, disc `d`, centre `c`, size `s` (`h = 2^s Y`), branch `e`, the root
`Y0` of `G1 d c Y0 ≡ 0 mod 2^N`, the square root candidate `(sR, eR)`, the Abel-Prym choice `prm`. -/
structure BoxSpec where
  kk : Nat
  d : Nat
  c : Int
  s : Nat
  e : BranchBox
  Y0 : Int
  N : Nat
  sR : N3
  eR : Nat
  prm : APPrm

/-- The Taylor model context of a box of size `s`: `h ∈ pv^(3s) O_v`. -/
def BoxSpec.ctx (B : BoxSpec) (k : Ctx) (n : Nat) : TCtx := ⟨k, 3 * B.s, n⟩

/-- The ball of the root `u(h)` over the box: `Y0` to `2^min N s`. -/
def BoxSpec.U (B : BoxSpec) (k : Ctx) : Ball := Ball.ofApprox k (B.Y0, 0, 0) (min B.N B.s)

/-- The first part of the run: the point `w`, the radicand and `Q2/δ` as Taylor models. -/
def boxRunP (T : TCtx) (B : BoxSpec) : Option ((TM × TM × TM) × TM × TM) := do
  let k := T.k
  let o := tmOpsF T
  let m0 ← mBall k 0
  let m1 ← mBall k 1
  let m2 ← mBall k 2
  let dl ← sigQ k (FurioLombardo.Discharge.M3a.Bruin.dL B.kk) 1
  let idl ← (ballOpsF k).inv dl
  let Yt ← TM.root T (G1L B.d) (Ball.ofInt k B.c) (Ball.ofInt k 1) (Ball.ofApprox k (B.Y0, 0, 0) B.N)
    (B.U k)
  let Yt := TM.fresh T Yt
  let Xt := o.add (TM.cst T (Ball.ofInt k B.c)) (TM.var T)
  pure (boxP o B.d B.e.wh (m0.cmap (TM.cst T)) (m1.cmap (TM.cst T)) (m2.cmap (TM.cst T))
    (TM.cst T idl) Xt Yt)

/-- **The Taylor model run of a box**: `Z` (the translated sum) and `Amat t`, from the balls `g` of the
sextic, `E` of `E0Mum`, `Am` of `Amat` (DCertData). -/
def boxRun (T : TCtx) (g : Sext Ball) (E : Mum Ball) (Am : Mat2 Ball) (B : BoxSpec) :
    Option (Mum TM × TM × TM) := do
  let k := T.k
  let o := tmOpsF T
  let bo := ballOpsF k
  let m0 ← mBall k 0
  let m1 ← mBall k 1
  let m2 ← mBall k 2
  let dl ← sigQ k (FurioLombardo.Discharge.M3a.Bruin.dL B.kk) 1
  let P ← boxRunP T B
  let yr ← TM.sqrt T P.2.1 B.sR B.eR
  if Ball.nearOK k yr.2 (Ball.ofApprox k B.e.rho k.P) then
    let m ← boxPhi o B.e.wh B.prm (m0.cmap (TM.cst T)) (m1.cmap (TM.cst T)) (m2.cmap (TM.cst T))
      (TM.cst T dl) P.1 P.2.2 (TM.fresh T yr.1)
    let R ← cantorAdd bo g E (Mum.neg bo (m.cmap fun M => M.cs.headD (TM.zeroB T)))
    boxChart o (g.cmap (TM.cst T)) (o.ofInt B.kk) (Am.cmap (TM.cst T)) m (R.cmap (TM.cst T))
  else none

/-! ## The checks -/

/-- The chart identification of `Z` over the box: `‖t‖ ≤ ‖pv‖^D` and the two conditions on `w` of
`resQ_chain_ne_zero`. -/
def chartOK (T : TCtx) (b : Ball) (aa M D : Nat) (Z : Mum TM) : Bool :=
  decide (M + 4 ≤ D) && decide (7 + 2 * aa ≤ D) && Ball.normLe T.k (TM.ball T Z.u1) D &&
    Ball.normLe T.k (TM.ball T Z.u0) D && Ball.nearOK T.k (TM.ball T Z.v0) b &&
    Ball.normLeMul T.k (TM.ball T Z.v1) b aa

/-- **The checks of a constant box**: the chart at depth `D` and `‖Amat t‖ ≤ ‖pv‖^need`. -/
def constOK (T : TCtx) (b : Ball) (aa M D need : Nat) (out : Mum TM × TM × TM) : Bool :=
  chartOK T b aa M D out.1 && Ball.normLe T.k (TM.ball T out.2.1) need &&
    Ball.normLe T.k (TM.ball T out.2.2) need

/-- The ball of `2 (Amat c1)_j - g_j`, `c1` the coefficients of `h` of the chart coordinates. -/
def tailG (T : TCtx) (Am : Mat2 Ball) (Z : Mum TM) (gl : Fin 6 → Int) (j : Fin 2) : Ball :=
  let k := T.k
  let c0 := Z.u1.cs.getD 1 (TM.zeroB T)
  let c1 := Z.u0.cs.getD 1 (TM.zeroB T)
  let x := if j = 0 then Ball.add k (Ball.mul k Am.a00 c0) (Ball.mul k Am.a01 c1)
    else Ball.add k (Ball.mul k Am.a10 c0) (Ball.mul k Am.a11 c1)
  Ball.sub k (Ball.mul k (Ball.ofInt k 2) x) (Ball.ofApprox k (lTriple gl j) k.P)

/-- **The checks of a tail box**: the chart at depth `D`, `‖c1‖ ≤ ‖pv‖^a1`, `‖S‖ ≤ ‖pv‖^aS` for the
quotient `S = (t - c0 - h c1)/h²`, and `2 Amat c1` within `‖pv‖^(3q)` of `g`. -/
def tailOK (T : TCtx) (b : Ball) (Am : Mat2 Ball) (aa M D a1 aS q : Nat) (gl : Fin 6 → Int)
    (out : Mum TM × TM × TM) : Bool :=
  let Z := out.1
  chartOK T b aa M D Z && decide (1 ≤ T.n) &&
    Ball.normLe T.k (Z.u1.cs.getD 1 (TM.zeroB T)) a1 && Ball.normLe T.k (Z.u0.cs.getD 1 (TM.zeroB T)) a1 &&
    Ball.normLe T.k (TM.split T 2 Z.u1) aS && Ball.normLe T.k (TM.split T 2 Z.u0) aS &&
    Ball.normLe T.k (tailG T Am Z gl 0) (3 * q) && Ball.normLe T.k (tailG T Am Z gl 1) (3 * q)

end FurioLombardo.Discharge.M4Box
