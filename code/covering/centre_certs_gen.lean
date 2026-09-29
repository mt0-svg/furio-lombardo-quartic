import FurioLombardo.Discharge.M4Box.CentreValue
import FurioLombardo.M4.Data

/-!
# Generator of the certificates of the constant box centres (`hCe`)

Untrusted: it only searches the data that the kernel then checks. For the constant box `i` of twist `kk`
(`T<kk>.constant`, entry `i` of the branch table):

* `Y0` with `2^N ∣ G1 d c Y0`, by lifting one bit at a time (`∂G1/∂Y` is odd);
* the square root candidate `(sR, eR)` of `Q1/δ` (or `Q3/δ`) by Newton's iteration from the reference root `ρ`
  of the box, accepted when `apInBall` succeeds;
* the choice `(kd, l, jN)` of the Abel-Prym program, the first for which the ball run succeeds;
* `J` the least number of rounds of the chain for which `finalOK` passes against `c.y + la` at `c.q`.

`#eval report kk fr upto` prints one line per box; `#eval emit DIR kk fr upto C` writes the Lean files
(M4Box/CentreData). Run from lean/:
`lake env lean ../code/covering/centre_certs_gen.lean`.
-/

open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log

namespace CcGen

def o : Ops Ball := ballOpsF dCtx

def showB (b : Ball) : String := s!"⟨({b.c.1}, {b.c.2.1}, {b.c.2.2}), {b.e}, {b.r}, {b.v}⟩"
def showM (R : Mum Ball) : String := s!"⟨{showB R.u0}, {showB R.u1}, {showB R.v0}, {showB R.v1}⟩"
def showS3 (m : Sym3 Ball) : String :=
  s!"⟨{showB m.a00}, {showB m.a01}, {showB m.a02}, {showB m.a11}, {showB m.a12}, {showB m.a22}⟩"
def showIn (x : APIn Ball) : String :=
  s!"⟨{showS3 x.n1}, {showS3 x.n2}, {showS3 x.n3}, {showB x.dl}, {showB x.p0}, {showB x.p1}, {showB x.p2}, {showB x.r}, {showB x.s}⟩"
def showN3 (c : N3) : String := s!"({c.1}, {c.2.1}, {c.2.2})"
def showBB (e : BranchBox) : String :=
  s!"⟨{e.disc}, {e.c}, {e.s}, {e.wh}, ({e.rho.1}, {e.rho.2.1}, {e.rho.2.2}), {e.e}⟩"

def ex (b : Ball) : Ball := Ball.exactN dCtx b

def newton (c x : Ball) : Nat → Option Ball
  | 0 => some x
  | n + 1 => do
    let d := o.sub (o.mul x x) (ex c)
    let i ← o.inv (o.mul (o.ofInt 2) x)
    newton c (ex (o.sub x (o.mul d i))) n

def depth (b : Ball) : Nat := min (vN dCtx b.c) b.r - 3 * b.e

structure TwistC where
  g : Sext Ball
  b : Ball
  E : Mum Ball
  A : Mat2 Ball

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

/-- The root of `G1 d c Y ≡ 0 mod 2^N`, one bit at a time. -/
def rootY (d c N : Nat) : Int := Id.run do
  let mut y : Int := 0
  for n in List.range N do
    if G1 d (c : Int) y % (2 : Int) ^ (n + 1) != 0 then y := y + (2 : Int) ^ n
  return y

def constOf (kk : Fin 2) : List FurioLombardo.M4.CBox :=
  if kk = 0 then FurioLombardo.M4.T0.constant else FurioLombardo.M4.T1.constant
def laOf (kk : Fin 2) : Fin 6 → ℤ := if kk = 0 then FurioLombardo.M4.T0.la else FurioLombardo.M4.T1.la
def TN (kk : Fin 2) : String := if kk = 0 then "FurioLombardo.M4.T0" else "FurioLombardo.M4.T1"

def NY : Nat := 600

structure CentreC where
  e : BranchBox
  Y0 : Int
  sR : N3
  eR : Nat
  xb : APIn Ball
  prm : APPrm
  mB : Mum Ball
  J : Nat
  Dd : Nat
  R : Mum Ball

def prms : List APPrm :=
  (List.range 3).flatMap fun jN => (List.range 5).flatMap fun kd => (List.range 3).map fun l => ⟨kd, l, jN⟩

def centreC (kk : Fin 2) (i : Nat) (T : TwistC) : Except String CentreC := do
  let some c := (constOf kk)[i]? | throw "no box"
  let some e := (branchTable kk)[i]? | throw "no table entry"
  unless e.disc = c.disc ∧ e.c = c.c ∧ e.s = c.s ∧ e.e = 0 do throw "table entry differs"
  let Y0 := rootY c.disc c.c NY
  -- the square root candidate: Newton from ρ on `Q1/δ` or `Q3/δ`, as in `apInBall`
  let some m0 := mBall dCtx 0 | throw "mBall 0"
  let some m1 := mBall dCtx 1 | throw "mBall 1"
  let some m2 := mBall dCtx 2 | throw "mBall 2"
  let some dl := sigQ dCtx (FurioLombardo.Discharge.M3a.Bruin.dL kk) 1 | throw "dl"
  let w := discPtO o c.disc (o.ofInt c.c) (Ball.ofApprox dCtx (Y0, 0, 0) NY)
  let q1 := Sym3.quad o m0 w.1 w.2.1 w.2.2
  let q3 := Sym3.quad o m2 w.1 w.2.1 w.2.2
  let _ := m1
  let some idl := o.inv dl | throw "inv dl"
  let rho := Ball.ofApprox dCtx e.rho dCtx.P
  let target := if e.wh then o.mul q1 idl else o.mul q3 idl
  let some (sR, eR, _) := sqrtCand target rho rho false | throw "sqrt"
  let some xb := apInBall dCtx kk c.disc c.c Y0 NY e sR eR | throw "apInBall"
  let some (prm, mB) := prms.findSome? fun prm => (apPhi o prm xb).map fun m => (prm, m) | throw "apPhi"
  let some R0 := drun o T.g mB T.E (chainSteps 0) mB | throw "chain start"
  let aa := IntModelKv.aa kk
  let M := M0 kk
  let l := c.y + laOf kk
  let rec go (J : Nat) (R : Mum Ball) (fuel : Nat) : Except String CentreC := do
    let s := shiftB dCtx kk R
    let Dd := min (depth s.u1) (depth s.u0)
    if finalOK dCtx T.A T.b kk aa M R J Dd l c.q then
      return ⟨e, Y0, sR, eR, xb, prm, mB, J, Dd, R⟩
    match fuel with
    | 0 => throw s!"no J up to {J}, last Dd {Dd}"
    | f + 1 =>
      let some R' := drun o T.g mB T.E [0, 3] R | throw s!"chain round {J + 1}"
      go (J + 1) R' f
  go 0 R0 200

def report (kk : Fin 2) (fr upto : Nat) : IO Unit := do
  match twistC kk with
  | .error e => IO.println s!"twist {kk}: FAIL {e}"
  | .ok T =>
    for i in List.range' fr (upto - fr) do
      match centreC kk i T with
      | .error e => IO.println s!"K{kk}C{i}: FAIL {e}"
      | .ok C => IO.println s!"K{kk}C{i}: prm ({C.prm.kd}, {C.prm.l}, {C.prm.jN}), J {C.J}, Dd {C.Dd}, eR {C.eR}"

partial def chunksOf (C : Nat) (l : List Nat) : List (List Nat) :=
  if l.isEmpty then [] else l.take C :: chunksOf C (l.drop C)

def header (what : String) : String :=
  "/-\n" ++ what ++ "\nGenerated by code/covering/centre_certs_gen.lean (lane lean-m4box); every value is checked by the kernel.\n-/\n"

def centreFile (kk : Fin 2) (i : Nat) (T : TwistC) (C : CentreC) (CH : Nat) : Except String String := do
  let some c := (constOf kk)[i]? | throw "no box"
  let tw := s!"DCertData.Tw{kk}"
  let n := s!"K{kk}C{i}"
  let cs := chunksOf CH (chainSteps C.J)
  let mut body := ""
  let mut R := C.mB
  let mut m := 0
  for ch in cs do
    let some R' := drun o T.g C.mB T.E ch R | throw s!"chunk {m + 1}"
    m := m + 1
    body := body ++ s!"noncomputable def S{m} : Mum Ball := {showM R'}\n\n" ++
      s!"theorem ck{m} : drun (ballOpsF dCtx) {tw}.g mB {tw}.E {toString ch} {if m = 1 then "mB" else s!"S{m - 1}"} = some S{m} := by\n  decide +kernel\n\n"
    R := R'
  unless R == C.R do throw "chunks disagree with the run"
  let nest := (cs.map toString).foldr (fun a acc => if acc = "" then a else s!"{a} ++ ({acc})") ""
  let rws := String.intercalate ", " ((List.range (m - 1)).map fun j => s!"drun_append, ck{j + 1}, Option.bind_some")
  return header s!"The certificate of the centre of the constant box {i} of twist {kk} (disc {c.disc}, centre {c.c}, size {c.s}):\n`apInBall`, `apPhi` with `(kd, l, jN) = ({C.prm.kd}, {C.prm.l}, {C.prm.jN})`, the chain in {m} chunks of at most {CH} steps, `finalOK`\n(`centreOK_of_run` is applied in Values{kk}.lean)." ++
    s!"import FurioLombardo.Discharge.M4Box.DCertData.Twist{kk}\nimport FurioLombardo.M4.Data\nimport FurioLombardo.Discharge.M4Log.IntModelKv\n\n" ++
    s!"namespace FurioLombardo.Discharge.M4Box.CentreData.{n}\n\n" ++
    "open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log\n" ++
    "open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7.ConcreteKv\n\n" ++
    "set_option maxRecDepth 100000\n\n" ++
    s!"noncomputable def xb : APIn Ball := {showIn C.xb}\n\n" ++
    s!"theorem hin : apInBall dCtx {kk} {c.disc} {c.c} ({C.Y0}) {NY} {showBB C.e} {showN3 C.sR} {C.eR} = some xb := by\n  decide +kernel\n\n" ++
    s!"noncomputable def mB : Mum Ball := {showM C.mB}\n\n" ++
    s!"theorem hphi : apPhi (ballOpsF dCtx) ⟨{C.prm.kd}, {C.prm.l}, {C.prm.jN}⟩ xb = some mB := by\n  decide +kernel\n\n" ++
    body ++
    s!"theorem hsteps : chainSteps {C.J} = {nest} := by decide +kernel\n\n" ++
    s!"theorem hR : drun (ballOpsF dCtx) {tw}.g mB {tw}.E (chainSteps {C.J}) mB = some S{m} := by\n" ++
    s!"  rw [hsteps{if m > 1 then ", " ++ rws else ""}]\n  exact ck{m}\n\n" ++
    s!"theorem hfin : finalOK dCtx {tw}.A {tw}.b (({kk} : Fin 2) : ℕ) (IntModelKv.aa {kk}) (M0 {kk}) S{m} {C.J} {C.Dd}\n    ({TN kk}.constant[{i}].y + {TN kk}.la) {TN kk}.constant[{i}].q = true := by\n  decide +kernel\n\n" ++
    s!"end FurioLombardo.Discharge.M4Box.CentreData.{n}\n"

/-- The certificate `K<kk>C<i>.cert` of Values<kk>.lean. -/
def certText (kk : Fin 2) (i : Nat) (C : CentreC) : Except String String := do
  let some c := (constOf kk)[i]? | throw "no box"
  let tw := s!"DCertData.Tw{kk}"
  let n := s!"K{kk}C{i}"
  return s!"theorem {n}.cert : CentreOK {kk} {TN kk}.la {TN kk}.qa {TN kk}.constant[{i}] :=\n" ++
    s!"  centreOK_of_run {kk} (e := {showBB C.e}) (by decide +kernel) (by decide +kernel)\n" ++
    s!"    (show IsDisc {c.disc} by unfold IsDisc; decide) (Y0 := {C.Y0}) (N := {NY}) (by decide +kernel) dCtx_ok\n" ++
    s!"    {n}.hin {n}.hphi {tw}.hF {tw}.hg {tw}.hb {tw}.hE {tw}.hA {n}.hR {n}.hfin\n\n"

/-- Values<kk>.lean: the certificates of the `n` centres, their conjunction over `T<kk>.constant`, and `HCentre`. -/
def valuesFile (kk : Fin 2) (n : Nat) (certs : String) : String :=
  let T := TN kk
  let imps := String.join ((List.range n).map fun i => s!"import FurioLombardo.Discharge.M4Box.CentreData.K{kk}C{i}\n")
  let exs := String.intercalate ", " ((List.range n).map fun i => s!"K{kk}C{i}.cert")
  header s!"The constant box centres of twist {kk}: the certificates `K{kk}C<i>.cert` of the {n} boxes of `T{kk}.constant` from the\ndata files K{kk}C<i>.lean (`centreOK_of_run`), and `HCentre` for `T{kk}.data` (`hCentre_of_ok`, the ball `(la, qa)` of\nPhiCertData)." ++
    "import FurioLombardo.Discharge.M4Box.CentreValue\nimport FurioLombardo.Discharge.M4Box.PhiCertData.Values\n" ++ imps ++ "\n" ++
    "namespace FurioLombardo.Discharge.M4Box.CentreData\n\n" ++
    "open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log\n" ++
    "open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7.ConcreteKv\n\n" ++
    certs ++
    s!"theorem constant_ok_{kk} : ∀ c ∈ {T}.data.constant, CentreOK {kk} {T}.data.la {T}.data.qa c := by\n" ++
    "  intro c hc\n  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc\n" ++
    s!"  have hi' : i < {n} := hi\n  interval_cases i\n  exacts [{exs}]\n\n" ++
    s!"/-- **`HCentre` for twist {kk}.** -/\ntheorem hCe_{kk} : FurioLombardo.M4.HCentre {T}.data (lamD {kk}) :=\n" ++
    s!"  hCentre_of_ok {kk} {T}.data (lamInt_of {kk} (DCertData.lamK_Dpt_le_one {kk})) (fun j => (PhiCertData.P{kk}.cert j).2)\n    constant_ok_{kk}\n\n" ++
    "end FurioLombardo.Discharge.M4Box.CentreData\n"

/-- Write the data files of the boxes `[fr, upto)` of twist `kk`, and Values<kk>.lean when the range is complete. -/
def emit (dir : String) (kk : Fin 2) (fr upto CH : Nat) : IO Unit := do
  match twistC kk with
  | .error e => IO.println s!"twist {kk}: FAIL {e}"
  | .ok T =>
    let mut certs := ""
    let mut ok := true
    for i in List.range' fr (upto - fr) do
      match centreC kk i T with
      | .error e => IO.println s!"K{kk}C{i}: FAIL {e}"; ok := false
      | .ok C =>
        match centreFile kk i T C CH, certText kk i C with
        | .ok s, .ok t =>
          IO.FS.writeFile s!"{dir}/K{kk}C{i}.lean" s; certs := certs ++ t
          IO.println s!"K{kk}C{i}: written, J {C.J}, Dd {C.Dd}"
        | .error e, _ | _, .error e => IO.println s!"K{kk}C{i}: FAIL {e}"; ok := false
    if ok && fr = 0 && upto = (constOf kk).length then
      IO.FS.writeFile s!"{dir}/Values{kk}.lean" (valuesFile kk upto certs)
      IO.println s!"Values{kk}: written, {upto} boxes"

end CcGen

-- #eval CcGen.report 0 0 82
-- #eval CcGen.report 1 0 22
#eval CcGen.emit "FurioLombardo/Discharge/M4Box/CentreData" 0 0 82 10
#eval CcGen.emit "FurioLombardo/Discharge/M4Box/CentreData" 1 0 22 10
