import FurioLombardo.Discharge.KvArith.Sigma
import FurioLombardo.Discharge.KvArith.Comp.DCert
import FurioLombardo.Discharge.KvArith.Comp.DChain
import FurioLombardo.Discharge.KvArith.Comp.DRun
import FurioLombardo.Discharge.M4Box.Comp.AbelPrym
import FurioLombardo.Discharge.SelmerSpan.Dpt
import FurioLombardo.Discharge.R7.ConcreteKv
import FurioLombardo.Discharge.M3a.AbelPrymDefs
import FurioLombardo.Discharge.M4Log.BranchData

/-!
# The ball programs of the value certificates (lane lean-m4box)

The programs only, no soundness: the input balls of the chain (`FvBall`, `gBall`, `bKBall`, `E0Ball`,
`AmatBall`), the balls of the points (`DBall` for the `D_i`, `phiBall` for `φ(x_i)` at the known lifts,
`apInBall` for the input of the Abel-Prym program at a box centre) and the final checks `finalOK`. The
certificate data files (DCertData, PhiCertData, CentreData) import this file and the other program files
only, so that splicing a proof into a soundness file (DInput.lean, DFinal.lean, PtValue.lean,
CentreValue.lean) does not rebuild them.
-/

open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.M4Cert
open FurioLombardo.Discharge.M3a.Bruin (QcL dL apUL apVL apUdN apDN)

namespace FurioLombardo.Discharge.M4Box

/-- The working precision of the D_i certificate: 600 bits (probe code/local-group). -/
def dCtx : Ctx := Ctx.ofP 600

-- Decidable equality of the input of the Abel-Prym program, for the checks `apInBall ... = some xb`.
deriving instance DecidableEq for Sym3
deriving instance DecidableEq for APIn

/-- The ball of `σ(m⁻¹ zkE l)`. -/
def sigQ (k : Ctx) (l : List ℤ) (m : ℕ) : Option Ball := do
  let s ← sigmaBall k l
  let i ← (ballOpsF k).inv (Ball.ofInt k m)
  pure ((ballOpsF k).mul i s)

/-- The balls of `Fv kk j = σ(zkE (FL kk j))`. -/
def FvBall (k : Ctx) (kk : ℕ) : Option (Sext Ball) := do
  let b0 ← sigmaBall k (SelmerSpan.FL kk 0)
  let b1 ← sigmaBall k (SelmerSpan.FL kk 1)
  let b2 ← sigmaBall k (SelmerSpan.FL kk 2)
  let b3 ← sigmaBall k (SelmerSpan.FL kk 3)
  let b4 ← sigmaBall k (SelmerSpan.FL kk 4)
  let b5 ← sigmaBall k (SelmerSpan.FL kk 5)
  let b6 ← sigmaBall k (SelmerSpan.FL kk 6)
  pure ⟨b0, b1, b2, b3, b4, b5, b6⟩

/-- The balls of the coefficients of `g = F/4`. -/
def gBall (k : Ctx) (F : Sext Ball) : Option (Sext Ball) := do
  let i ← (ballOpsF k).inv (Ball.ofInt k 4)
  let m := (ballOpsF k).mul
  pure ⟨m F.f0 i, m F.f1 i, m F.f2 i, m F.f3 i, m F.f4 i, m F.f5 i, m F.f6 i⟩

/-- The ball of `DptMum kk i`, from the balls `F` of `Fv kk` and the square root candidates
`(sN, eN)`, `(sA, eA)` of `n`, `a`. -/
def DBall (k : Ctx) (kk i : ℕ) (F : Sext Ball) (sN : N3) (eN : ℕ) (sA : N3) (eA : ℕ) :
    Option (Mum Ball) := do
  let o := ballOpsF k
  let p ← sigQ k (SelmerSpan.pLi kk i) (SelmerSpan.pMi kk i)
  let r ← sigQ k (SelmerSpan.rLi kk i) (SelmerSpan.rMi kk i)
  let Z1 := o.divR1 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6
  let Z0 := o.divR0 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6
  let n ← (o.normN p r Z1 Z0).sqrt k sN eN
  if Ball.nearOK k n (Ball.ofApprox k (SelmerSpan.hb1 kk i) (SelmerSpan.P1 kk i)) then
    let a ← (o.normA p Z1 Z0 n).sqrt k sA eA
    if Ball.nearOK k a (Ball.ofApprox k (SelmerSpan.hb2 kk i) (SelmerSpan.P2 kk i)) then
      let b ← o.sqB Z1 a
      let c ← o.sqC p a b
      pure ⟨r, p, c, b⟩
    else none
  else none

/-- The ball of `bK kk`, from the balls `g` of `(fRev kk)^σ` and the candidate `(sB, eB)`. -/
def bKBall (k : Ctx) (kk : Fin 2) (g : Sext Ball) (sB : N3) (eB : ℕ) : Option Ball := do
  let o := ballOpsF k
  let b ← (o.transC0 ((kk : ℕ) : ℤ) g).sqrt k sB eB
  if Ball.nearOK k (o.mul (o.ofInt 2) b) (Ball.ofApprox k (bT kk) 3) then pure b else none

/-- The ball of `E0Mum kk`, from the balls `g` of `(fRev kk)^σ` and `b` of `bK kk`. -/
def E0Ball (k : Ctx) (kk : Fin 2) (g : Sext Ball) (b : Ball) : Option (Mum Ball) := do
  let o := ballOpsF k
  let a : ℤ := (kk : ℕ)
  let i ← o.inv (o.mul (o.ofInt 2) (o.transC0 a g))
  let v1 := o.mul b (o.mul (o.transC1 a g) i)
  pure ⟨o.ofInt (a * a), o.ofInt (-(2 * a)), o.sub b (o.mul (o.ofInt a) v1), v1⟩

/-- The balls of the entries of `Amat kk`. -/
def AmatBall (k : Ctx) (kk : Fin 2) (g : Sext Ball) (b : Ball) : Option (Mat2 Ball) := do
  let o := ballOpsF k
  let a : ℤ := (kk : ℕ)
  let i ← o.inv (o.mul (o.ofInt 2) (o.transC0 a g))
  let g1 := o.neg (o.mul (o.transC1 a g) i)
  let bi ← o.inv b
  pure ⟨o.mul bi (o.ofInt a), o.mul bi (o.add (o.ofInt 1) (o.mul (o.ofInt a) g1)), bi, o.mul bi g1⟩

/-- The chain end translated by `a` (its `u₁, u₀` are the chart coordinates `t₀, t₁`, its `v₀, v₁`
the coefficients of the branch `w`). -/
def shiftB (k : Ctx) (a : ℕ) (R : Mum Ball) : Mum Ball :=
  Mum.shift (ballOpsF k) ((ballOpsF k).ofInt a) R

/-- The ball of `lamK k (D_i) j`: `(Amat t)_j` plus the error ball of radius `Err`, divided by
`2^J N`. -/
def lamBall (k : Ctx) (A : Mat2 Ball) (a : ℕ) (R : Mum Ball) (J Err : ℕ) (j : Fin 2) :
    Option Ball := do
  let o := ballOpsF k
  let s := shiftB k a R
  let x := if j = 0 then o.add (o.mul A.a00 s.u1) (o.mul A.a01 s.u0)
    else o.add (o.mul A.a10 s.u1) (o.mul A.a11 s.u0)
  let i ← o.inv (o.ofInt ((2 ^ J * dN : ℕ) : ℤ))
  pure (o.mul i (o.add x (Ball.errB k Err)))

/-- The integer triple of the coordinate `j` of a lattice vector `l : Fin 6 → ℤ`. -/
def lTriple (l : Fin 6 → ℤ) (j : Fin 2) : T3 :=
  (l (finProdFinEquiv (m := 2) (n := 3) (j, 0)), l (finProdFinEquiv (m := 2) (n := 3) (j, 1)),
    l (finProdFinEquiv (m := 2) (n := 3) (j, 2)))

/-- The checks on one coordinate: integral, and within `‖pv‖^(3q)` of the lattice triple. -/
def lamOK (k : Ctx) (lb : Ball) (lt : T3) (q : ℕ) : Bool :=
  Ball.normLe k lb 0 && Ball.normLe k (Ball.sub k lb (Ball.ofApprox k lt k.P)) (3 * q)

/-- The check of coordinate `j`: its ball exists and passes `lamOK`. -/
def lamCheck (k : Ctx) (A : Mat2 Ball) (a : ℕ) (R : Mum Ball) (J Err : ℕ) (j : Fin 2) (l : Fin 6 → ℤ)
    (q : ℕ) : Bool :=
  (lamBall k A a R J Err j).any fun lb => lamOK k lb (lTriple l j) q

/-- **The final checks** of the certificate of one point. -/
def finalOK (k : Ctx) (A : Mat2 Ball) (b : Ball) (a aa M : ℕ) (R : Mum Ball) (J Dd : ℕ)
    (l : Fin 6 → ℤ) (q : ℕ) : Bool :=
  let s := shiftB k a R
  decide (M + 4 ≤ Dd) && decide (7 + 2 * aa ≤ Dd) && Ball.normLe k s.u1 Dd && Ball.normLe k s.u0 Dd &&
    Ball.nearOK k s.v0 b && Ball.normLeMul k s.v1 b aa &&
    lamCheck k A a R J (2 * Dd - M - 3) 0 l q && lamCheck k A a R J (2 * Dd - M - 3) 1 l q

/-- The ball of `phiMum i`, from the balls of the `σ` images of its coefficients. -/
def phiBall (k : Ctx) (i : ℕ) : Option (Mum Ball) := do
  let u0 ← sigQ k (apUL i 0) (apUdN i)
  let u1 ← sigQ k (apUL i 1) (apUdN i)
  let v0 ← sigQ k (apVL i 0) (apDN i)
  let v1 ← sigQ k (apVL i 1) (apDN i)
  pure ⟨u0, u1, v0, v1⟩

/-- `discPt d X Y` on `Ops`, as a triple. -/
def discPtO {A : Type*} (o : Ops A) (d : ℕ) (X Y : A) : A × A × A :=
  if d = 1 then (o.mul (o.ofInt 2) X, o.mul (o.ofInt 2) Y, o.ofInt 1)
  else if d = 2 then (o.add (o.ofInt 1) (o.mul (o.ofInt 2) X), o.mul (o.ofInt 2) Y, o.ofInt 1)
  else if d = 3 then
    (o.add (o.ofInt 1) (o.mul (o.ofInt 2) X), o.add (o.ofInt 1) (o.mul (o.ofInt 2) Y), o.ofInt 1)
  else if d = 4 then (o.mul (o.ofInt 2) X, o.ofInt 1, o.mul (o.ofInt 2) Y)
  else if d = 5 then (o.add (o.ofInt 1) (o.mul (o.ofInt 2) X), o.ofInt 1, o.mul (o.ofInt 2) Y)
  else (o.ofInt 0, o.ofInt 0, o.ofInt 0)

/-- The ball of `σ(Mmat i)`. -/
def mBall (k : Ctx) (i : ℕ) : Option (Sym3 Ball) := do
  let a00 ← sigQ k (QcL i 0) 1
  let a01 ← sigQ k (QcL i 1) 2
  let a02 ← sigQ k (QcL i 2) 2
  let a11 ← sigQ k (QcL i 3) 1
  let a12 ← sigQ k (QcL i 4) 2
  let a22 ← sigQ k (QcL i 5) 1
  pure ⟨a00, a01, a02, a11, a12, a22⟩

/-- **The balls of the input at the point over `pKv d c` on the branch of `e`** (`e.wh`: the
coordinate `r` is the square root of `Q1/δ` near `ρ`; otherwise `s`, of `Q3/δ`). -/
def apInBall (k : Ctx) (kk d c : ℕ) (Y0 : ℤ) (N : ℕ) (e : BranchBox) (sR : N3) (eR : ℕ) :
    Option (APIn Ball) := do
  let o := ballOpsF k
  let m0 ← mBall k 0
  let m1 ← mBall k 1
  let m2 ← mBall k 2
  let dl ← sigQ k (dL kk) 1
  let w := discPtO o d (o.ofInt c) (Ball.ofApprox k (Y0, 0, 0) N)
  let q1 := Sym3.quad o m0 w.1 w.2.1 w.2.2
  let q2 := Sym3.quad o m1 w.1 w.2.1 w.2.2
  let q3 := Sym3.quad o m2 w.1 w.2.1 w.2.2
  let idl ← o.inv dl
  let rho := Ball.ofApprox k e.rho k.P
  if e.wh then
    let r ← (o.mul q1 idl).sqrt k sR eR
    if Ball.nearOK k r rho then
      let ir ← o.inv r
      pure ⟨m2, m1, m0, dl, w.1, w.2.1, w.2.2, o.mul (o.mul q2 idl) ir, r⟩
    else none
  else
    let s ← (o.mul q3 idl).sqrt k sR eR
    if Ball.nearOK k s rho then
      let is ← o.inv s
      pure ⟨m2, m1, m0, dl, w.1, w.2.1, w.2.2, s, o.mul (o.mul q2 idl) is⟩
    else none

end FurioLombardo.Discharge.M4Box
