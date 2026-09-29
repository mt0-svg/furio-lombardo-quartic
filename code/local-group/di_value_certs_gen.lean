import FurioLombardo.Discharge.M4Box.Comp.Cert
import FurioLombardo.M4.Data
import FurioLombardo.Discharge.M4Log.IntModelKv

/-!
# Generator of the D_i value certificates

Untrusted: it only searches the data that the kernel then checks. For each twist `kk` it runs the input balls
(`FvBall`, `gBall`, `bKBall`, `E0Ball`, `AmatBall`) and for each point `i` the ball `DBall`, the chain
`drun (ballOpsF dCtx) g D E (chainSteps J) D` and `finalOK`, with

* square root candidates `(s, es)` for `Ball.sqrt` by Newton's iteration on exact centres, started at the
  stored approximations (`SelmerSpan.hb1`, `hb2` for `n`, `a`; `bT kk / 2` for `b`) and accepted when
  `Ball.sqrt` succeeds and the check `nearOK` of the program passes;
* `J` the least number of rounds for which `finalOK` passes, with `Dd` the largest depth of the chart
  coordinates allowed by the balls.

`#eval report` prints one line per point; `#eval emit DIR` writes the Lean files of the certificates
(M4Box/DCertData). Run from lean/: `lake env lean ../code/local-group/di_value_certs_gen.lean`.
-/

open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box

namespace DcGen

def o : Ops Ball := ballOpsF dCtx

def showB (b : Ball) : String := s!"⟨({b.c.1}, {b.c.2.1}, {b.c.2.2}), {b.e}, {b.r}, {b.v}⟩"
def showM (R : Mum Ball) : String := s!"⟨{showB R.u0}, {showB R.u1}, {showB R.v0}, {showB R.v1}⟩"
def showS (F : Sext Ball) : String :=
  s!"⟨{showB F.f0}, {showB F.f1}, {showB F.f2}, {showB F.f3}, {showB F.f4}, {showB F.f5}, {showB F.f6}⟩"
def showA (A : Mat2 Ball) : String := s!"⟨{showB A.a00}, {showB A.a01}, {showB A.a10}, {showB A.a11}⟩"
def showN3 (c : N3) : String := s!"({c.1}, {c.2.1}, {c.2.2})"

/-- The centre as an exact ball. -/
def ex (b : Ball) : Ball := Ball.exactN dCtx b

/-- Newton's iteration for a square root of the centre of `c` from `x`, on exact centres. -/
def newton (c x : Ball) : Nat → Option Ball
  | 0 => some x
  | n + 1 => do
    let d := o.sub (o.mul x x) (ex c)
    let i ← o.inv (o.mul (o.ofInt 2) x)
    newton c (ex (o.sub x (o.mul d i))) n

/-- A candidate `(s, es)` with `Ball.sqrt dCtx c s es = some r` and `nearOK` of `r` (or of `2 r` when `twice`)
against `chk`; the root of Newton's iteration from `x0` or its negative, the least scale that works. -/
def sqrtCand (c x0 chk : Ball) (twice : Bool) : Option (N3 × Nat × Ball) := do
  let x ← newton c (ex x0) 14
  let xs := [x, ex (o.neg x)]
  xs.findSome? fun y => (List.range 12).findSome? fun d =>
    let s := smulN dCtx (2 ^ d) y.c
    let es := y.e + d
    match Ball.sqrt dCtx c s es with
    | some r =>
      let r' := if twice then o.mul (o.ofInt 2) r else r
      if Ball.nearOK dCtx r' chk then some (s, es, r) else none
    | none => none

/-- The radius of a ball as a depth (`r - 3e`, `0` below). -/
def depth (b : Ball) : Nat := min (vN dCtx b.c) b.r - 3 * b.e

structure TwistC where
  F : Sext Ball
  g : Sext Ball
  sB : N3
  eB : Nat
  b : Ball
  E : Mum Ball
  A : Mat2 Ball

def twistC (kk : Fin 2) : Except String TwistC := do
  let some F := FvBall dCtx kk | throw "FvBall"
  let some g := gBall dCtx F | throw "gBall"
  let c := o.transC0 ((kk : ℕ) : ℤ) g
  let some i2 := o.inv (o.ofInt 2) | throw "inv 2"
  let x0 := o.mul (Ball.ofApprox dCtx (FurioLombardo.Discharge.R7.ConcreteKv.bT kk) 3) i2
  let some (sB, eB, _) := sqrtCand c x0 (Ball.ofApprox dCtx (FurioLombardo.Discharge.R7.ConcreteKv.bT kk) 3) true | throw "sqrt b"
  let some b := bKBall dCtx kk g sB eB | throw "bKBall"
  let some E := E0Ball dCtx kk g b | throw "E0Ball"
  let some A := AmatBall dCtx kk g b | throw "AmatBall"
  return ⟨F, g, sB, eB, b, E, A⟩

structure PointC where
  sN : N3
  eN : Nat
  sA : N3
  eA : Nat
  D : Mum Ball
  J : Nat
  Dd : Nat
  R : Mum Ball
  rmin : Nat

def lOf (kk : Fin 2) : Fin 7 → Fin 6 → ℤ := if kk = 0 then FurioLombardo.M4.T0.lD else FurioLombardo.M4.T1.lD
def qOf (kk : Fin 2) : Fin 7 → ℕ := if kk = 0 then FurioLombardo.M4.T0.qD else FurioLombardo.M4.T1.qD

def pointC (kk : Fin 2) (i : Fin 7) (T : TwistC) : Except String PointC := do
  let F := T.F
  let some p := sigQ dCtx (FurioLombardo.Discharge.SelmerSpan.pLi kk i) (FurioLombardo.Discharge.SelmerSpan.pMi kk i) | throw "sigQ p"
  let some r := sigQ dCtx (FurioLombardo.Discharge.SelmerSpan.rLi kk i) (FurioLombardo.Discharge.SelmerSpan.rMi kk i) | throw "sigQ r"
  let Z1 := o.divR1 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6
  let Z0 := o.divR0 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6
  let x1 := Ball.ofApprox dCtx (FurioLombardo.Discharge.SelmerSpan.hb1 kk i) (FurioLombardo.Discharge.SelmerSpan.P1 kk i)
  let some (sN, eN, n) := sqrtCand (o.normN p r Z1 Z0) x1 x1 false | throw "sqrt n"
  let x2 := Ball.ofApprox dCtx (FurioLombardo.Discharge.SelmerSpan.hb2 kk i) (FurioLombardo.Discharge.SelmerSpan.P2 kk i)
  let some (sA, eA, _) := sqrtCand (o.normA p Z1 Z0 n) x2 x2 false | throw "sqrt a"
  let some D := DBall dCtx kk i F sN eN sA eA | throw "DBall"
  let some R0 := drun o T.g D T.E (chainSteps 0) D | throw "chain start"
  let aa := FurioLombardo.Discharge.M4Log.IntModelKv.aa kk
  let M := FurioLombardo.Discharge.M4Log.M0 kk
  let rec go (J : Nat) (R : Mum Ball) (fuel : Nat) : Except String PointC := do
    let s := shiftB dCtx kk R
    let Dd := min (depth s.u1) (depth s.u0)
    if finalOK dCtx T.A T.b kk aa M R J Dd (lOf kk i) (qOf kk i) then
      return ⟨sN, eN, sA, eA, D, J, Dd, R, min (min (depth R.u0) (depth R.u1)) (min (depth R.v0) (depth R.v1))⟩
    match fuel with
    | 0 => throw s!"no J up to {J}, last Dd {Dd}"
    | f + 1 =>
      let some R' := drun o T.g D T.E [0, 3] R | throw s!"chain round {J + 1}"
      go (J + 1) R' f
  go 0 R0 200

def report : IO Unit := do
  for kk in [0, 1] do
    let kk : Fin 2 := ⟨kk % 2, Nat.mod_lt _ (by decide)⟩
    match twistC kk with
    | .error e => IO.println s!"twist {kk}: FAIL {e}"
    | .ok T =>
      IO.println s!"twist {kk}: inputs ok, eB {T.eB}, depth b {depth T.b}"
      for i in List.finRange 7 do
        match pointC kk i T with
        | .error e => IO.println s!"  D_{i}: FAIL {e}"
        | .ok P => IO.println s!"  D_{i}: J {P.J}, steps {(chainSteps P.J).length}, Dd {P.Dd}, eN {P.eN}, eA {P.eA}, min depth of R {P.rmin}"

partial def chunksOf (C : Nat) (l : List Nat) : List (List Nat) :=
  if l.isEmpty then [] else l.take C :: chunksOf C (l.drop C)

def showL (l : List Nat) : String := toString l

def header (what : String) : String :=
  "/-\n" ++ what ++ "\nGenerated by code/local-group/di_value_certs_gen.lean (lane lean-m4box); every value is checked by the kernel.\n-/\n"

/-- The file of the inputs of twist `kk`. -/
def twistFile (kk : Fin 2) (T : TwistC) : String :=
  let n := s!"Tw{kk}"
  header s!"The input balls of the D_i value certificates of twist {kk}: `FvBall`, `gBall`, `bKBall`, `E0Ball`, `AmatBall`." ++
  "import FurioLombardo.Discharge.M4Box.Comp.Cert\n\n" ++
  s!"namespace FurioLombardo.Discharge.M4Box.DCertData.{n}\n\n" ++
  "open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box\n\n" ++
  s!"noncomputable def F : Sext Ball := {showS T.F}\n\n" ++
  s!"noncomputable def g : Sext Ball := {showS T.g}\n\n" ++
  s!"noncomputable def b : Ball := {showB T.b}\n\n" ++
  s!"noncomputable def E : Mum Ball := {showM T.E}\n\n" ++
  s!"noncomputable def A : Mat2 Ball := {showA T.A}\n\n" ++
  "set_option maxRecDepth 100000\n\n" ++
  s!"theorem hF : FvBall dCtx (({kk} : Fin 2) : ℕ) = some F := by decide +kernel\n\n" ++
  "theorem hg : gBall dCtx F = some g := by decide +kernel\n\n" ++
  s!"theorem hb : bKBall dCtx {kk} g {showN3 T.sB} {T.eB} = some b := by decide +kernel\n\n" ++
  s!"theorem hE : E0Ball dCtx {kk} g b = some E := by decide +kernel\n\n" ++
  s!"theorem hA : AmatBall dCtx {kk} g b = some A := by decide +kernel\n\n" ++
  s!"end FurioLombardo.Discharge.M4Box.DCertData.{n}\n"

/-- The file of the certificate of the point `i` of twist `kk`, chunks of `C` steps. -/
def pointFile (kk : Fin 2) (i : Fin 7) (T : TwistC) (P : PointC) (C : Nat) : Except String String := do
  let tw := s!"Tw{kk}"
  let n := s!"K{kk}I{i}"
  let T0 := if kk = 0 then "FurioLombardo.M4.T0" else "FurioLombardo.M4.T1"
  let cs := chunksOf C (chainSteps P.J)
  let mut body := ""
  let mut R := P.D
  let mut m := 0
  for c in cs do
    let some R' := drun o T.g P.D T.E c R | throw s!"chunk {m + 1}"
    m := m + 1
    body := body ++ s!"noncomputable def S{m} : Mum Ball := {showM R'}\n\n" ++
      s!"theorem ck{m} : drun (ballOpsF dCtx) {tw}.g D {tw}.E {showL c} {if m = 1 then "D" else s!"S{m - 1}"} = some S{m} := by\n  decide +kernel\n\n"
    R := R'
  unless R == P.R do throw "chunks disagree with the run"
  let nest := (cs.map showL).foldr (fun a acc => if acc = "" then a else s!"{a} ++ ({acc})") ""
  let rws := String.intercalate ", " ((List.range (m - 1)).map fun j => s!"drun_append, ck{j + 1}, Option.bind_some")
  return header s!"The D_{i} value certificate of twist {kk}: `DBall`, the chain in {m} chunks of at most {C} steps, `finalOK`\n(the bounds of `lamK_Dpt_of_cert` are in Values.lean)." ++
    s!"import FurioLombardo.Discharge.M4Box.DCertData.Twist{kk}\nimport FurioLombardo.M4.Data\nimport FurioLombardo.Discharge.M4Log.IntModelKv\n\n" ++
    s!"namespace FurioLombardo.Discharge.M4Box.DCertData.{n}\n\n" ++
    "open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log\n" ++
    "open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7.ConcreteKv\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    s!"noncomputable def D : Mum Ball := {showM P.D}\n\n" ++
    s!"theorem hD : DBall dCtx (({kk} : Fin 2) : ℕ) (({i} : Fin 7) : ℕ) {tw}.F {showN3 P.sN} {P.eN} {showN3 P.sA} {P.eA} =\n    some D := by\n  decide +kernel\n\n" ++
    body ++
    s!"theorem hsteps : chainSteps {P.J} = {nest} := by decide +kernel\n\n" ++
    s!"theorem hR : drun (ballOpsF dCtx) {tw}.g D {tw}.E (chainSteps {P.J}) D = some S{m} := by\n" ++
    s!"  rw [hsteps{if m > 1 then ", " ++ rws else ""}]\n  exact ck{m}\n\n" ++
    s!"theorem hfin : finalOK dCtx {tw}.A {tw}.b (({kk} : Fin 2) : ℕ) (IntModelKv.aa {kk}) (M0 {kk}) S{m} {P.J} {P.Dd}\n    ({T0}.lD {i}) ({T0}.qD {i}) = true := by\n  decide +kernel\n\n" ++
    s!"end FurioLombardo.Discharge.M4Box.DCertData.{n}\n"

/-- Write the files of the twists and points listed. -/
def emit (dir : String) (pts : List (Nat × Nat)) (C : Nat) : IO Unit := do
  for kk in [0, 1] do
    let kk : Fin 2 := ⟨kk % 2, Nat.mod_lt _ (by decide)⟩
    let .ok T := twistC kk | IO.println s!"twist {kk}: FAIL"
    IO.FS.writeFile s!"{dir}/Twist{kk}.lean" (twistFile kk T)
    for i in List.finRange 7 do
      if pts.contains ((kk : ℕ), (i : ℕ)) then
        match pointC kk i T with
        | .error e => IO.println s!"K{kk}I{i}: FAIL {e}"
        | .ok P =>
          match pointFile kk i T P C with
          | .error e => IO.println s!"K{kk}I{i}: FAIL {e}"
          | .ok s => IO.FS.writeFile s!"{dir}/K{kk}I{i}.lean" s; IO.println s!"K{kk}I{i}: written"

end DcGen

-- #eval DcGen.report
#eval DcGen.emit "FurioLombardo/Discharge/M4Box/DCertData" ((List.range 2).flatMap fun k => (List.range 7).map fun i => (k, i)) 10
