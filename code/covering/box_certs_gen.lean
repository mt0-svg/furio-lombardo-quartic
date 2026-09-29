import FurioLombardo.Discharge.M4Box.Comp.BoxTM
import FurioLombardo.M4.Data
import FurioLombardo.Discharge.M4Log.IntModelKv
import FurioLombardo.Discharge.M4Box.DiscRoot

/-!
# Generator of the per box certificates (D9)

Untrusted: it only searches the data that the kernel then checks. For the box `i` of twist `kk` (entry `i`
of the branch table: the constant boxes of `T<kk>.constant`, then the tails of `T<kk>.tails`):

* `Y0` with `2^N ∣ G1 d c Y0`, one bit at a time;
* the square root candidate `(sR, eR)` of the radicand at the centre, by Newton's iteration from the
  reference root `ρ` of the box;
* the order `n` and the Abel-Prym choice `prm`, the first for which `boxRun` succeeds;
* for a constant box the depth `D` of the chart coordinates over the box, against the need
  `3 (vM/3 + s)` of `Amat t`; for a tail `a1`, `aS` and the check of `g`.

`#eval report kk fr upto` prints one line per box. Run from lean/:
`lake env lean ../code/covering/box_certs_gen.lean`.
-/

open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log

namespace BcGen

def o : Ops Ball := ballOpsF dCtx

def ex (b : Ball) : Ball := Ball.exactN dCtx b

def newton (c x : Ball) : Nat → Option Ball
  | 0 => some x
  | n + 1 => do
    let d := o.sub (o.mul x x) (ex c)
    let i ← o.inv (o.mul (o.ofInt 2) x)
    newton c (ex (o.sub x (o.mul d i))) n

def depth (b : Ball) : Nat := min (vN dCtx b.c) b.r - 3 * b.e

def sqrtCand (c x0 chk : Ball) : Option (N3 × Nat × Ball) := do
  let x ← newton c (ex x0) 14
  let xs := [x, ex (o.neg x)]
  xs.findSome? fun y => (List.range 12).findSome? fun d =>
    let s := smulN dCtx (2 ^ d) y.c
    let es := y.e + d
    match Ball.sqrt dCtx c s es with
    | some r => if Ball.nearOK dCtx r chk then some (s, es, r) else none
    | none => none

structure TwistC where
  g : Sext Ball
  b : Ball
  E : Mum Ball
  A : Mat2 Ball

def sqrtCand2 (c x0 chk : Ball) : Option (N3 × Nat × Ball) := do
  let x ← newton c (ex x0) 14
  let xs := [x, ex (o.neg x)]
  xs.findSome? fun y => (List.range 12).findSome? fun d =>
    let s := smulN dCtx (2 ^ d) y.c
    let es := y.e + d
    match Ball.sqrt dCtx c s es with
    | some r => if Ball.nearOK dCtx (o.mul (o.ofInt 2) r) chk then some (s, es, r) else none
    | none => none

/-- The twist constants (the values of DCertData.Tw<kk>, recomputed: those are noncomputable). -/
def twistC (kk : Fin 2) : Except String TwistC := do
  let some F := FvBall dCtx kk | throw "FvBall"
  let some g := gBall dCtx F | throw "gBall"
  let c := o.transC0 ((kk : ℕ) : ℤ) g
  let some i2 := o.inv (o.ofInt 2) | throw "inv 2"
  let x0 := o.mul (Ball.ofApprox dCtx (FurioLombardo.Discharge.R7.ConcreteKv.bT kk) 3) i2
  let some (sB, eB, _) := sqrtCand2 c x0 (Ball.ofApprox dCtx (FurioLombardo.Discharge.R7.ConcreteKv.bT kk) 3) | throw "sqrt b"
  let some b := bKBall dCtx kk g sB eB | throw "bKBall"
  let some E := E0Ball dCtx kk g b | throw "E0Ball"
  let some A := AmatBall dCtx kk g b | throw "AmatBall"
  return ⟨g, b, E, A⟩

/-- The root of `G1 d c Y ≡ 0 mod 2^N`, one bit at a time. -/
def rootY (d : Nat) (c : Int) (N : Nat) : Int := Id.run do
  let mut y : Int := 0
  for n in List.range N do
    if G1 d c y % (2 : Int) ^ (n + 1) != 0 then y := y + (2 : Int) ^ n
  return y

def NY : Nat := 600

def prms : List APPrm :=
  (List.range 3).flatMap fun jN => (List.range 5).flatMap fun kd => (List.range 3).map fun l => ⟨kd, l, jN⟩

def constOf (kk : Fin 2) : List FurioLombardo.M4.CBox :=
  if kk = 0 then FurioLombardo.M4.T0.constant else FurioLombardo.M4.T1.constant
def tailsOf (kk : Fin 2) : List FurioLombardo.M4.TBox :=
  if kk = 0 then FurioLombardo.M4.T0.tails else FurioLombardo.M4.T1.tails

/-- The box of entry `i`: disc, centre, size, and `(vM, q, g)` for the need and the tail checks. -/
structure BoxI where
  d : Nat
  c : Int
  s : Nat
  vM : Nat
  tail : Option (Nat × Nat × (Fin 6 → Int))

def boxOf (kk : Fin 2) (i : Nat) : Option BoxI :=
  match (constOf kk)[i]? with
  | some c => some ⟨c.disc, c.c, c.s, c.vM, none⟩
  | none => match (tailsOf kk)[i - (constOf kk).length]? with
    | some b => some ⟨b.disc, b.Xi, b.s, b.vM, some (b.s0, b.q, b.g)⟩
    | none => none

/-- The spec of the box `i` at the centre: root, square root candidate. -/
def specOf (kk : Fin 2) (i : Nat) : Except String (BoxI × BoxSpec) := do
  let some bx := boxOf kk i | throw "no box"
  let some e := (branchTable kk)[i]? | throw "no table entry"
  unless e.disc = bx.d ∧ e.s = bx.s ∧ e.e = 0 do throw "table entry differs"
  let Y0 := rootY bx.d bx.c NY
  let some m0 := mBall dCtx 0 | throw "mBall 0"
  let some m2 := mBall dCtx 2 | throw "mBall 2"
  let some dl := sigQ dCtx (FurioLombardo.Discharge.M3a.Bruin.dL kk) 1 | throw "dl"
  let w := discPtO o bx.d (o.ofInt bx.c) (Ball.ofApprox dCtx (Y0, 0, 0) NY)
  let q1 := Sym3.quad o m0 w.1 w.2.1 w.2.2
  let q3 := Sym3.quad o m2 w.1 w.2.1 w.2.2
  let some idl := o.inv dl | throw "inv dl"
  let rho := Ball.ofApprox dCtx e.rho dCtx.P
  let target := if e.wh then o.mul q1 idl else o.mul q3 idl
  let some (sR, eR, _) := sqrtCand target rho rho | throw "sqrt"
  return (bx, ⟨kk, bx.d, bx.c, bx.s, e, Y0, NY, sR, eR, ⟨0, 0, 0⟩⟩)

def bstr (b : Ball) : String := s!"(v{vN dCtx b.c} e{b.e} r{b.r} sv{b.v})"

def tmstr (T : TCtx) (M : TM) : String :=
  let ds := M.cs.map fun b => toString (depth b)
  s!"[{String.intercalate " " ds} | R {depth M.R}] ball {depth (TM.ball T M)}"

def tmfull (T : TCtx) (M : TM) : String :=
  let ds := M.cs.map bstr
  s!"[{String.intercalate " " ds} | R {bstr M.R}] ball {bstr (TM.ball T M)} pball {bstr (TM.pball T M.cs)}"


/-- `boxRun` with the failing stage named. -/
def boxRunDbg (T : TCtx) (g : Sext Ball) (E : Mum Ball) (Am : Mat2 Ball) (B : BoxSpec) :
    Except String (Mum TM × TM × TM) := do
  let k := T.k
  let ot := tmOpsF T
  let bo := ballOpsF k
  let some m0 := mBall k 0 | throw "m0"
  let some m1 := mBall k 1 | throw "m1"
  let some m2 := mBall k 2 | throw "m2"
  let some dl := sigQ k (FurioLombardo.Discharge.M3a.Bruin.dL B.kk) 1 | throw "dl"
  let some idl := bo.inv dl | throw "idl"
  let some Yt := TM.root T (G1L B.d) (Ball.ofInt k B.c) (Ball.ofInt k 1) (Ball.ofApprox k (B.Y0, 0, 0) B.N)
    (B.U k) | throw "root"
  let Yt := TM.fresh T Yt
  let _ := idl
  let some P := boxRunP T B | throw "boxRunP"
  let Mt := TM.trunc T P.2.1
  let hd := Mt.cs.headD (TM.zeroB T)
  let bl := TM.ball T Mt
  let s1 := (Ball.sqrt k hd B.sR B.eR).isSome
  let s2 := (Ball.sqrt k bl B.sR B.eR).isSome
  let some yr := TM.sqrt T P.2.1 B.sR B.eR | throw s!"sqrt: radicand {tmstr T P.2.1}, Yt {tmstr T Yt}; head e {hd.e} r {hd.r} v {hd.v} sqrt {s1}; ball e {bl.e} r {bl.r} v {bl.v} sqrt {s2}; eR {B.eR} vs {vN k (redN k B.sR)}"
  unless Ball.nearOK k yr.2 (Ball.ofApprox k B.e.rho k.P) do throw s!"nearOK: rb depth {depth yr.2}"
  let some m := boxPhi ot B.e.wh B.prm (m0.cmap (TM.cst T)) (m1.cmap (TM.cst T)) (m2.cmap (TM.cst T))
      (TM.cst T dl) P.1 P.2.2 (TM.fresh T yr.1) | throw "boxPhi"
  let some R := cantorAdd bo g E (Mum.neg bo (m.cmap fun M => M.cs.headD (TM.zeroB T))) | throw "R"
  let some out := boxChart ot (g.cmap (TM.cst T)) (ot.ofInt B.kk) (Am.cmap (TM.cst T)) m (R.cmap (TM.cst T)) | throw "boxChart"
  return out

/-- The result of one order: the checks, and the line to print. -/
def eval1 (T0 : TwistC) (kk : Fin 2) (i : Nat) (bx : BoxI) (B : BoxSpec) (n : Nat) (out : Mum TM × TM × TM) :
    Bool × String :=
  let T := B.ctx dCtx n
  let aa := IntModelKv.aa kk
  let M := M0 kk
  let Z := out.1
  let D := min (depth (TM.ball T Z.u1)) (depth (TM.ball T Z.u0))
  let need := 3 * (bx.vM / 3 + bx.s)
  let dA := min (depth (TM.ball T out.2.1)) (depth (TM.ball T out.2.2))
  let ch := chartOK T T0.b aa M D Z
  match bx.tail with
  | none =>
    let ok := constOK T T0.b aa M D need out && decide (need + M + 3 ≤ 2 * D)
    (ok, s!"K{kk}B{i} const disc {bx.d} c {bx.c} s {bx.s}: n {n} prm ({B.prm.kd},{B.prm.l},{B.prm.jN}) D {D} (chart {ch}) Amat t {dA} need {need} 2D-need-M-3 {(2 * D : Int) - (need + M + 3)} ok {ok} | t0 {tmstr T Z.u1} t1 {tmstr T Z.u0}")
  | some (s0, q, gl) =>
    let a1 := min (depth (Z.u1.cs.getD 1 (TM.zeroB T))) (depth (Z.u0.cs.getD 1 (TM.zeroB T)))
    let aS := min (depth (TM.split T 2 Z.u1)) (depth (TM.split T 2 Z.u0))
    let gq := min (depth (tailG T T0.A Z gl 0)) (depth (tailG T T0.A Z gl 1))
    let d1 := min a1 (3 * bx.s + aS)
    let vq := 3 * (bx.vM / 3)
    let t1 := (3 * bx.s + d1 : Int) - (M + 4)
    let t2 := (3 * s0 + aS : Int) - vq
    let t3 := (3 * s0 + 2 * d1 : Int) - (vq + M + 3)
    let ok := tailOK T T0.b T0.A aa M D a1 aS q gl out && decide (0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ t3)
    (ok, s!"K{kk}B{i} tail disc {bx.d} Xi {bx.c} s {bx.s} s0 {s0}: n {n} prm ({B.prm.kd},{B.prm.l},{B.prm.jN}) D {D} (chart {ch}) a1 {a1} aS {aS} g {gq} vs 3q {3 * q} | T1 {t1} T2 {t2} T3 {t3} ok {ok} | t0 {tmstr T Z.u1} t1 {tmstr T Z.u0}")

/-- The first order of `ns` whose run passes the checks (with the first `prm` for which the run succeeds). -/
def search (T0 : TwistC) (kk : Fin 2) (i : Nat) (ns : List Nat) :
    Except String (BoxI × BoxSpec × Nat × (Mum TM × TM × TM) × String) := do
  let (bx, B) ← specOf kk i
  let mut last := s!"K{kk}B{i}: FAIL boxRun (disc {bx.d} c {bx.c} s {bx.s})"
  for n in ns do
    let T := B.ctx dCtx n
    match prms.findSome? fun prm => (boxRun T T0.g T0.E T0.A { B with prm := prm }).map fun out => (prm, out) with
    | none => pure ()
    | some (prm, out) =>
      let B' := { B with prm := prm }
      let (ok, line) := eval1 T0 kk i bx B' n out
      if ok then return (bx, B', n, out, line)
      last := line
  throw last

def report1 (T0 : TwistC) (kk : Fin 2) (i : Nat) (ns : List Nat) : IO Unit := do
  match search T0 kk i ns with
  | .error err => IO.println s!"{err} FAILED"
  | .ok (_, _, _, _, line) => IO.println line

def report (kk : Fin 2) (fr upto : Nat) (ns : List Nat) : IO Unit := do
  match twistC kk with
  | .error err => IO.println s!"twist {kk}: FAIL {err}"
  | .ok T0 =>
    for i in List.range' fr (upto - fr) do
      report1 T0 kk i ns


def showN3 (c : N3) : String := s!"({c.1}, {c.2.1}, {c.2.2})"
def showBB (e : BranchBox) : String :=
  s!"⟨{e.disc}, {e.c}, {e.s}, {e.wh}, ({e.rho.1}, {e.rho.2.1}, {e.rho.2.2}), {e.e}⟩"
def showSpec (B : BoxSpec) : String :=
  s!"⟨{B.kk}, {B.d}, {B.c}, {B.s}, {showBB B.e}, {B.Y0}, {B.N}, {showN3 B.sR}, {B.eR}, ⟨{B.prm.kd}, {B.prm.l}, {B.prm.jN}⟩⟩"

/-- The check line of box `i`: `(boxRun ...).any (constOK ...) = true` or `tailOK`. -/
def checkText (T0 : TwistC) (kk : Fin 2) (i : Nat) (ns : List Nat) : Except String String := do
  let (bx, B, n, out, _) ← search T0 kk i ns
  let T := B.ctx dCtx n
  let Z := out.1
  let D := min (depth (TM.ball T Z.u1)) (depth (TM.ball T Z.u0))
  let tw := s!"DCertData.Tw{kk}"
  let run := s!"(boxRun (BoxSpec.ctx {showSpec B} dCtx {n}) {tw}.g {tw}.E {tw}.A {showSpec B})"
  match bx.tail with
  | none =>
    let need := 3 * (bx.vM / 3 + bx.s)
    return s!"theorem K{kk}B{i}.ok : {run}.any (constOK (BoxSpec.ctx {showSpec B} dCtx {n}) {tw}.b {IntModelKv.aa kk} {M0 kk} {D} {need}) = true := by\n  decide +kernel\n"
  | some (_, q, gl) =>
    let a1 := min (depth (Z.u1.cs.getD 1 (TM.zeroB T))) (depth (Z.u0.cs.getD 1 (TM.zeroB T)))
    let aS := min (depth (TM.split T 2 Z.u1)) (depth (TM.split T 2 Z.u0))
    let _ := gl
    return s!"theorem K{kk}B{i}.ok : {run}.any (tailOK (BoxSpec.ctx {showSpec B} dCtx {n}) {tw}.b {tw}.A {IntModelKv.aa kk} {M0 kk} {D} {a1} {aS} {q} ({if kk = 0 then "FurioLombardo.M4.T0" else "FurioLombardo.M4.T1"}.tails[{i - (constOf kk).length}].g)) = true := by\n  decide +kernel\n"

def emitChecks (kk : Fin 2) (is : List Nat) (ns : List Nat) : IO Unit := do
  match twistC kk with
  | .error err => IO.println s!"twist {kk}: FAIL {err}"
  | .ok T0 =>
    for i in is do
      match checkText T0 kk i ns with
      | .error err => IO.println s!"-- K{kk}B{i}: {err}"
      | .ok t => IO.println t

def twName (kk : Fin 2) : String := if kk = 0 then "FurioLombardo.M4.T0" else "FurioLombardo.M4.T1"

def fileHead (kk : Fin 2) (i : Nat) (what chk : String) : String :=
  s!"/-\nThe box check of {what}: `boxRun` and `{chk}` in one kernel check\n" ++
  s!"(`constCert_of_ok`, `tailCert_of_ok` are applied in BoxData/Values{kk}.lean).\n" ++
  "Generated by code/covering/box_certs_gen.lean (lane lean-m4box); the check is done by the kernel.\n-/\n" ++
  s!"import FurioLombardo.Discharge.M4Box.DCertData.Twist{kk}\nimport FurioLombardo.Discharge.M4Box.Comp.BoxTM\n" ++
  "import FurioLombardo.M4.Data\nimport FurioLombardo.Discharge.M4Log.IntModelKv\n\n" ++
  s!"namespace FurioLombardo.Discharge.M4Box.BoxData.K{kk}B{i}\n\n" ++
  "open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log\n" ++
  "open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7.ConcreteKv\n\nset_option maxRecDepth 100000\n\n"

/-- The data file of box `i` (spec and kernel check) and its certificate in the Values file. -/
def dataText (T0 : TwistC) (kk : Fin 2) (i : Nat) (ns : List Nat) : Except String (String × String) := do
  let (bx, B, n, out, _) ← search T0 kk i ns
  let T := B.ctx dCtx n
  let Z := out.1
  let D := min (depth (TM.ball T Z.u1)) (depth (TM.ball T Z.u0))
  let tw := s!"DCertData.Tw{kk}"
  let nm := s!"K{kk}B{i}"
  let run := s!"(boxRun (B.ctx dCtx {n}) {tw}.g {tw}.E {tw}.A B).any"
  let common := s!"(by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)\n" ++
    s!"    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)\n" ++
    s!"    (show IsDisc {bx.d} by unfold IsDisc; decide) (by decide +kernel)\n" ++
    s!"    {tw}.hF {tw}.hg {tw}.hb {tw}.hE {tw}.hA"
  let spec := s!"noncomputable def B : BoxSpec :=\n  {showSpec B}\n\n"
  match bx.tail with
  | none =>
    let c := s!"{twName kk}.constant[{i}]"
    let what := s!"the constant box {i} of twist {kk} (disc {bx.d}, centre {bx.c}, size {bx.s}), order {n}"
    let file := fileHead kk i what "constOK" ++ spec ++
      s!"theorem ok : {run}\n    (constOK (B.ctx dCtx {n}) {tw}.b (IntModelKv.aa {kk}) (M0 {kk}) {D}\n" ++
      s!"      (3 * ({c}.vM / 3 + {c}.s))) = true := by\n  decide +kernel\n\n" ++
      s!"end FurioLombardo.Discharge.M4Box.BoxData.{nm}\n"
    let cert := s!"theorem {nm}.cert : ConstCert {kk} (IntModelKv.admM0 {kk}) {c} :=\n" ++
      s!"  constCert_of_ok {kk} {nm}.B {n} {common}\n    (by decide +kernel) {nm}.ok\n"
    return (file, cert)
  | some _ =>
    let j := i - (constOf kk).length
    let t := s!"{twName kk}.tails[{j}]"
    let a1 := min (depth (Z.u1.cs.getD 1 (TM.zeroB T))) (depth (Z.u0.cs.getD 1 (TM.zeroB T)))
    let aS := min (depth (TM.split T 2 Z.u1)) (depth (TM.split T 2 Z.u0))
    let what := s!"the tail box {j} of twist {kk} (disc {bx.d}, centre {bx.c}, size {bx.s}), order {n}"
    let file := fileHead kk i what "tailOK" ++ spec ++
      s!"theorem ok : {run}\n    (tailOK (B.ctx dCtx {n}) {tw}.b {tw}.A (IntModelKv.aa {kk}) (M0 {kk}) {D} {a1} {aS}\n" ++
      s!"      {t}.q {t}.g) = true := by\n  decide +kernel\n\n" ++
      s!"end FurioLombardo.Discharge.M4Box.BoxData.{nm}\n"
    let cert := s!"theorem {nm}.cert : TailCert {kk} (IntModelKv.admM0 {kk}) {t} :=\n" ++
      s!"  tailCert_of_ok {kk} {nm}.B {n} {common}\n    (by decide +kernel) (by decide +kernel) (by decide +kernel) {nm}.ok\n"
    return (file, cert)

def valuesText (kk : Fin 2) (certs : List String) : String :=
  let nc := (constOf kk).length
  let nt := (tailsOf kk).length
  let nb := nc + nt
  let imports := String.join ((List.range nb).map fun i =>
    s!"import FurioLombardo.Discharge.M4Box.BoxData.K{kk}B{i}\n")
  let cl := String.intercalate ", " ((List.range nc).map fun i => s!"K{kk}B{i}.cert")
  let tl := String.intercalate ", " ((List.range nt).map fun j => s!"K{kk}B{nc + j}.cert")
  s!"/-\nThe per box statements of twist {kk}: `ConstCert` for the {nc} boxes of `T{kk}.constant` and `TailCert` " ++
  s!"for the {nt} boxes of\n`T{kk}.tails`, from the checks `K{kk}B<i>.ok` of the data files K{kk}B<i>.lean " ++
  "(`constCert_of_ok`, `tailCert_of_ok`).\n" ++
  "Generated by code/covering/box_certs_gen.lean (lane lean-m4box); every value is checked by the kernel.\n-/\n" ++
  "import FurioLombardo.Discharge.M4Box.BoxOk\n" ++ imports ++
  "\nnamespace FurioLombardo.Discharge.M4Box.BoxData\n\n" ++
  "open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M4Box FurioLombardo.Discharge.M4Log\n" ++
  "open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7.ConcreteKv\n\n" ++
  String.intercalate "\n" certs ++
  s!"\ntheorem constCert_{kk} : ∀ c ∈ {twName kk}.data.constant, ConstCert {kk} (IntModelKv.admM0 {kk}) c := by\n" ++
  "  intro c hc\n  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc\n" ++
  s!"  have hi' : i < {nc} := hi\n  interval_cases i\n  exacts [{cl}]\n\n" ++
  s!"theorem tailCert_{kk} : ∀ b ∈ {twName kk}.data.tails, TailCert {kk} (IntModelKv.admM0 {kk}) b := by\n" ++
  "  intro b hb\n  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb\n" ++
  s!"  have hi' : i < {nt} := hi\n  interval_cases i\n  exacts [{tl}]\n\n" ++
  "end FurioLombardo.Discharge.M4Box.BoxData\n"

/-- Writes BoxData/K<kk>B<i>.lean for the boxes `is` of twist `kk` (all when `is` is empty) and, when
all boxes are written, BoxData/Values<kk>.lean. -/
def writeData (dir : System.FilePath) (kk : Fin 2) (is : List Nat) (ns : List Nat) : IO Unit := do
  match twistC kk with
  | .error err => throw (IO.userError s!"twist {kk}: {err}")
  | .ok T0 =>
    let nb := (constOf kk).length + (tailsOf kk).length
    let all := is.isEmpty
    let is := if all then List.range nb else is
    let mut certs : List String := []
    for i in is do
      match dataText T0 kk i ns with
      | .error err => throw (IO.userError s!"K{kk}B{i}: {err}")
      | .ok (file, cert) =>
        IO.FS.writeFile (dir / s!"K{kk}B{i}.lean") file
        certs := certs ++ [cert]
        IO.println s!"K{kk}B{i} written"
    if all then IO.FS.writeFile (dir / s!"Values{kk}.lean") (valuesText kk certs)

end BcGen

/-- `lake env lean --run ../code/covering/box_certs_gen.lean DIR [kk i ...]`. -/
def main (args : List String) : IO Unit := do
  let ns := [2, 3, 4, 5]
  match args with
  | [dir] => do BcGen.writeData dir 0 [] ns; BcGen.writeData dir 1 [] ns
  | dir :: kk :: is => BcGen.writeData dir (if kk = "0" then 0 else 1) (is.filterMap String.toNat?) ns
  | _ => throw (IO.userError "usage: box_certs_gen DIR [kk i ...]")
