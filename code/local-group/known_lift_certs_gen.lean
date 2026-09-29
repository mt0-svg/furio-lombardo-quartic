import FurioLombardo.Discharge.M4Box.Comp.Cert
import FurioLombardo.M4.Data
import FurioLombardo.Discharge.M4Log.IntModelKv

/-!
# Generator of the value certificates of `φ(x_i)` at the four known lifts

Untrusted: it only searches the data that the kernel then checks. For the point `i` (`x_0`, `x_2` of twist 0,
`x_1`, `x_3` of twist 1) it runs the ball `phiBall dCtx i` of the pair of `φ(x_i)`, the chain
`drun (ballOpsF dCtx) g D E (chainSteps J) D` on the input balls of the twist (the same as for the `D_i`,
DCertData/Twist<k>.lean) and `finalOK` against the ball `(la, qa)` or `(lb, qb)` of M4, with `J` the least
number of rounds for which `finalOK` passes and `Dd` the largest depth of the chart coordinates allowed by the
balls.

`#eval report` prints one line per point; `#eval emit DIR C` writes the Lean files (M4Box/PhiCertData).
Run from lean/: `lake env lean ../code/local-group/known_lift_certs_gen.lean`.
-/

open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box

namespace PcGen

def o : Ops Ball := ballOpsF dCtx

def showB (b : Ball) : String := s!"⟨({b.c.1}, {b.c.2.1}, {b.c.2.2}), {b.e}, {b.r}, {b.v}⟩"
def showM (R : Mum Ball) : String := s!"⟨{showB R.u0}, {showB R.u1}, {showB R.v0}, {showB R.v1}⟩"

def ex (b : Ball) : Ball := Ball.exactN dCtx b

def newton (c x : Ball) : Nat → Option Ball
  | 0 => some x
  | n + 1 => do
    let d := o.sub (o.mul x x) (ex c)
    let i ← o.inv (o.mul (o.ofInt 2) x)
    newton c (ex (o.sub x (o.mul d i))) n

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

def depth (b : Ball) : Nat := min (vN dCtx b.c) b.r - 3 * b.e

structure TwistC where
  g : Sext Ball
  b : Ball
  E : Mum Ball
  A : Mat2 Ball

/-- The input balls of the twist, as DCertData/Twist<k>.lean holds them. -/
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
  return ⟨g, b, E, A⟩

/-- The twist of the point `i`, the name of its lift, the Lean names of its ball `(l, q)`. -/
def ptTw (i : Nat) : Fin 2 := if i = 0 ∨ i = 2 then 0 else 1
def ptX (i : Nat) : String := s!"x{i}"
def ptL (i : Nat) : String :=
  match i with
  | 0 => "FurioLombardo.M4.T0.la" | 2 => "FurioLombardo.M4.T0.lb"
  | 1 => "FurioLombardo.M4.T1.la" | _ => "FurioLombardo.M4.T1.lb"
def ptQ (i : Nat) : String :=
  match i with
  | 0 => "FurioLombardo.M4.T0.qa" | 2 => "FurioLombardo.M4.T0.qb"
  | 1 => "FurioLombardo.M4.T1.qa" | _ => "FurioLombardo.M4.T1.qb"
def lOf (i : Nat) : Fin 6 → ℤ :=
  match i with
  | 0 => FurioLombardo.M4.T0.la | 2 => FurioLombardo.M4.T0.lb
  | 1 => FurioLombardo.M4.T1.la | _ => FurioLombardo.M4.T1.lb
def qOf (i : Nat) : Nat :=
  match i with
  | 0 => FurioLombardo.M4.T0.qa | 2 => FurioLombardo.M4.T0.qb
  | 1 => FurioLombardo.M4.T1.qa | _ => FurioLombardo.M4.T1.qb

structure PointC where
  D : Mum Ball
  J : Nat
  Dd : Nat
  R : Mum Ball
  rmin : Nat

def pointC (i : Nat) (T : TwistC) : Except String PointC := do
  let kk := ptTw i
  let some D := phiBall dCtx i | throw "phiBall"
  let some R0 := drun o T.g D T.E (chainSteps 0) D | throw "chain start"
  let aa := FurioLombardo.Discharge.M4Log.IntModelKv.aa kk
  let M := FurioLombardo.Discharge.M4Log.M0 kk
  let rec go (J : Nat) (R : Mum Ball) (fuel : Nat) : Except String PointC := do
    let s := shiftB dCtx kk R
    let Dd := min (depth s.u1) (depth s.u0)
    if finalOK dCtx T.A T.b kk aa M R J Dd (lOf i) (qOf i) then
      return ⟨D, J, Dd, R, min (min (depth R.u0) (depth R.u1)) (min (depth R.v0) (depth R.v1))⟩
    match fuel with
    | 0 => throw s!"no J up to {J}, last Dd {Dd}"
    | f + 1 =>
      let some R' := drun o T.g D T.E [0, 3] R | throw s!"chain round {J + 1}"
      go (J + 1) R' f
  go 0 R0 200

def report : IO Unit := do
  for i in [0, 1, 2, 3] do
    match twistC (ptTw i) with
    | .error e => IO.println s!"x{i}: twist FAIL {e}"
    | .ok T =>
      match pointC i T with
      | .error e => IO.println s!"x{i}: FAIL {e}"
      | .ok P => IO.println s!"x{i}: twist {ptTw i}, J {P.J}, steps {(chainSteps P.J).length}, Dd {P.Dd}, min depth of R {P.rmin}, depth of D {min (min (depth P.D.u0) (depth P.D.u1)) (min (depth P.D.v0) (depth P.D.v1))}"

partial def chunksOf (C : Nat) (l : List Nat) : List (List Nat) :=
  if l.isEmpty then [] else l.take C :: chunksOf C (l.drop C)

def header (what : String) : String :=
  "/-\n" ++ what ++ "\nGenerated by code/local-group/known_lift_certs_gen.lean (lane lean-m4box); every value is checked by the kernel.\n-/\n"

/-- The file of the certificate of the point `i`, chunks of `C` steps. -/
def pointFile (i : Nat) (T : TwistC) (P : PointC) (C : Nat) : Except String String := do
  let kk := ptTw i
  let tw := s!"DCertData.Tw{kk}"
  let n := s!"P{i}"
  let x := ptX i
  let cs := chunksOf C (chainSteps P.J)
  let mut body := ""
  let mut R := P.D
  let mut m := 0
  for c in cs do
    let some R' := drun o T.g P.D T.E c R | throw s!"chunk {m + 1}"
    m := m + 1
    body := body ++ s!"noncomputable def S{m} : Mum Ball := {showM R'}\n\n" ++
      s!"theorem ck{m} : drun (ballOpsF dCtx) {tw}.g D {tw}.E {toString c} {if m = 1 then "D" else s!"S{m - 1}"} = some S{m} := by\n  decide +kernel\n\n"
    R := R'
  unless R == P.R do throw "chunks disagree with the run"
  let nest := (cs.map toString).foldr (fun a acc => if acc = "" then a else s!"{a} ++ ({acc})") ""
  let rws := String.intercalate ", " ((List.range (m - 1)).map fun j => s!"drun_append, ck{j + 1}, Option.bind_some")
  return header s!"The value certificate of `φ({x})` (twist {kk}): `phiBall`, the chain in {m} chunks of at most {C} steps,\n`finalOK` (the bounds of `lamK_of_cert` are in Values.lean)." ++
    s!"import FurioLombardo.Discharge.M4Box.DCertData.Twist{kk}\nimport FurioLombardo.M4.Data\nimport FurioLombardo.Discharge.M4Log.IntModelKv\n\n" ++
    s!"namespace FurioLombardo.Discharge.M4Box.PhiCertData.{n}\n\n" ++
    "open FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a.Bruin\n" ++
    "open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log\n" ++
    "open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7.ConcreteKv\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    s!"noncomputable def D : Mum Ball := {showM P.D}\n\n" ++
    s!"theorem hD : phiBall dCtx {i} = some D := by\n  decide +kernel\n\n" ++
    body ++
    s!"theorem hsteps : chainSteps {P.J} = {nest} := by decide +kernel\n\n" ++
    s!"theorem hR : drun (ballOpsF dCtx) {tw}.g D {tw}.E (chainSteps {P.J}) D = some S{m} := by\n" ++
    s!"  rw [hsteps{if m > 1 then ", " ++ rws else ""}]\n  exact ck{m}\n\n" ++
    s!"theorem hfin : finalOK dCtx {tw}.A {tw}.b (({kk} : Fin 2) : ℕ) (IntModelKv.aa {kk}) (M0 {kk}) S{m} {P.J} {P.Dd}\n    {ptL i} {ptQ i} = true := by\n  decide +kernel\n\n" ++
    s!"end FurioLombardo.Discharge.M4Box.PhiCertData.{n}\n"

def emit (dir : String) (C : Nat) : IO Unit := do
  for i in [0, 1, 2, 3] do
    match twistC (ptTw i) with
    | .error e => IO.println s!"x{i}: twist FAIL {e}"
    | .ok T =>
      match pointC i T with
      | .error e => IO.println s!"P{i}: FAIL {e}"
      | .ok P =>
        match pointFile i T P C with
        | .error e => IO.println s!"P{i}: FAIL {e}"
        | .ok s => IO.FS.writeFile s!"{dir}/P{i}.lean" s; IO.println s!"P{i}: written, J {P.J}, Dd {P.Dd}"

end PcGen

-- #eval PcGen.report
#eval PcGen.emit "FurioLombardo/Discharge/M4Box/PhiCertData" 10
