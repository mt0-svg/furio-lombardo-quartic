import FurioLombardo.Discharge.SelmerBasis.PointGen
import FurioLombardo.Discharge.SelmerBasis.Count.KE
import FurioLombardo.Discharge.SelmerBasis.Echelon
import FurioLombardo.M2.SpecialData

/-!
# The data format at the place above 7 (lane selmer-p7, twist 1)

Frozen interface between the generator (code/selmer-local-conditions/local_data_w7.gp and lean_data_w7.gp,
files W7Data*.lean, W7Check*.lean) and
the hand-written soundness (W7Model.lean, W7Cert.lean) and glue (W7Place.lean). Every `ok` function
below is a `Bool` closed by `decide +kernel` in a W7Check file; the generator emulates each check node
for node (the precision of a `checkK` depends on the shape of its expression).

## The model

`σ = adicCoe w7`, `π = σ al7`, `‖2‖ = 1`, residue field `𝔽₃₄₃`. All lists are coordinates in lane M1's
integral basis (`zkE`), hence integral at `w7`.

* `r ∈ K_w7` is the square root of `σ ε` (`ε = epsK`) near `σ y0` (`M.y0`): `y0² - ε = al7^ny y0R`, `y0`
  a unit. The two embeddings of `L42` (`ω² = ε`) are `ι₊ : ω ↦ -r` (where `eN` is a square) and
  `ι₋ : ω ↦ r`.
* `S ∈ K_w7` is the square root of `ι₊ (4 eN) = σ (2 ea) - σ (2 eb) r` near `σ S0`:
  `S0² - (2 ea - 2 eb y0) = al7^ns S0R`, `S0` a unit.
* `A4 = ι₋ (4 eN) = σ (2 ea) + σ (2 eb) r` has `‖A4‖ = ‖π‖`: `2 ea + 2 eb y0 = al7 E4U`, `E4U` a unit.
  `F' = QF K_w7 A4 0` with `Z² = A4` (`Z = QF.mk 0 1`, a uniformizer of `F'`).

The five components of `K_w7[T]/(fRev 1)`, in this order (bits `2c`, `2c + 1` of a row for `c < 4`, bits
`8`, `9` for `F'`):

* `c = 0`: `T ↦ ι₊ α`; `c = 1`: `T ↦ ι₋ α` (`α = alphaR ∈ L42`, root of `q`);
* `c = 2`: `T ↦ ι_N (+) β`, `c = 3`: `T ↦ ι_N (-) β` (`β = betaR ∈ N84`, root of `h`), where
  `ι_N (±) : N84 → K_w7` extends `ι₊` by `Ω ↦ ± S` (`Ω = 2 ω_N`, `Ω² = 4 eN`);
* `c = 4`: `T ↦ ι' β` with `ι' : N84 → F'` extending `ι₋` by `Ω ↦ Z`.

The basis of `Fˣ / Fˣ²` is `π, -1` at `K_w7` and `Z, -1` at `F'`; a row bit pair `(a0, a1)` at a component
means `x · π^a0 · (-1)^a1` (or `x · Z^a0 · (-1)^a1`) is a square.

## Approximations

For `x = (x0, x1) : LC` (the element `x0 + x1 ω` of `L42`), `ι₊ x` is approximated by
`XLp M.y0 x = x0 - x1 y0` and `ι₋ x` by `XLm M.y0 x = x0 + x1 y0`; for `x = (X, X') : NC` (the element
`X + X' Ω` of `N84`, `SUnitTower.evN`), `ι_N (±) x` by `XNs M.y0 M.S0 b x = XLp X ± XLp X' · S0`
(`b = true` for `+`) and `ι' x = QF.mk (ι₋ X) (ι₋ X')` coordinatewise by `XLm`. All errors are at most
`‖π‖ ^ N` with `N = min M.ny M.ns` (`Model.N`).

## Powers of `al7`

`tab` lists `al7 ^ (2 ^ i)` (`tab_0 = al7`, `tab_{i+1} = tab_i ²`, `powOK`); `alPw tab d` is the product of
the `tab_i` over the bits of `d` (`d < 2 ^ tab.length`), so no `checkK` carries a chain of products.

## Certificates

* `KCert` at a component `K_w7`, for a value `x` approximated by `X`:
  `X · al7^a0 · (-1)^a1 = al7^(2h) U² + al7^n R` with `U` a unit, `2 h < n`, `2 h < N`.
* `FCert` at `F'`, for `x + y Z` approximated by `(X, Y)`: with `(X', Y') = (al7 E4U · Y, X)` if `a0`
  (the coordinates of `(x + y Z) Z = A4 y + x Z`) and `(X, Y)` otherwise,
  `X' · (-1)^a1 = al7^(j + 2h) E4U^j U² + al7^n R`, `Y' = al7^(j + 2h) Ry`, `U` a unit, `j + 2 h < n`,
  `j + 2 h < N`: then `x' (-1)^a1` is close to the square `A4^j (π^h U)²` of `F'` and `y' Z` is smaller.
* `PtSq`: a point of `y² = fRev 1 (x)` over `K_w7` at a global abscissa `x`, by the square certificate of
  `4 fRev_1(x)` (`Count.gE 1 (.lin x) 0`): `4 fRev_1(x) - T² = al7^(m+1) A`, `T² = al7^m B`, `B` a unit.
* `PairData`: the point `P_i1 + P_i2 - ∞` with `U = (X - x1)(X - x2) = X² + P X + R` (`zkE P = -(x1 + x2)`,
  `zkE R = x1 x2`, `x1 - x2 = al7^dv dW` with `dW` a unit), the values `Λ_L² U(α) = mkL tL`, `Λ_N² U(β) = mkN tN`
  (`PtData.okT` with `d = 1`; `U(α)`, `U(β)` are not integral, `Λ_L = 92`, `Λ_N = 368` clear the
  denominators), and the certificates of `Λ² U(τ)` at the five components (the square class of `U(τ)`).

## The names the generator emits (namespace `FurioLombardo.Discharge.SelmerBasis.W7`)

W7Data*.lean: `tab : List (List ℤ)` (9 entries, up to `al7^256`), `tabK : List ℕ` (the precisions of
`powOK`), `M : Model`, `pts : List PtSq` (4 points), `pairs : List PairData` (3 pairs, `(i1, i2) = (0, i)`),
`cL : List (KCert × KCert)` (29, components 0, 1 of `gensL s`), `cN : List (KCert × KCert × FCert)`
(53, components 2, 3, 4 of `gensN s`), and the `F₂` data `Akap` (2 rows: `al7`, `-1`), `Amu` (3 rows),
`cK : List FCert` (2, the scalars `al7` and `-1` at `F'`, approximations `(.lin al7, .int 0)` and
`(.int (-1), .int 0)`; at the four components `K_w7` their rows are `(1, 0)` and `(0, 1)` by hand),
`Cg` (82 rows), `QI`, `TI` (`nQI` forms and the left inverse of `IndepImage`), `QC` (5 forms, with
`dotRow 10 Cg QC = C7Rows`), all as `List ℕ`, `nQI : ℕ`.
W7Check*.lean: one `decide +kernel` per certificate (split as the kernel cost requires), gathered into
exactly these statements, which W7Place.lean consumes:

    theorem tab_len : tab.length = 9
    theorem tab_zero : tab.getD 0 [] = al7
    theorem ck_tab : ∀ i, i < 8 → powOK tab (tabK.getD i 0) i = true
    theorem ck_M : M.ok tab = true
    theorem ck_pt : ∀ i, i < 4 → (pts.getD i default).ok tab = true
    theorem ck_pair : ∀ i, i < 3 → (pairs.getD i default).okU tab pts = true ∧
      (pairs.getD i default).toPt.okT = true ∧ (pairs.getD i default).okC tab M = true
    theorem ck_L : ∀ s, s < 29 → okL tab M (cL.getD s default) s = true
    theorem ck_N : ∀ s, s < 53 → okN tab M (cN.getD s default) s = true
    theorem ck_K : ∀ i, i < 2 → (cK.getD i default).ok tab M.N M.E4U (kapXE i) (.int 0) = true
    theorem kap_bits : ∀ i, i < 2 → Akap.getD i 0 = kapLow i + 256 * (cK.getD i default).bits
    theorem mu_bits : ∀ i, i < 3 → Amu.getD i 0 = (pairs.getD i default).bits
    theorem cgL_bits : ∀ s, s < 29 → Cg.getD s 0 = bitsL (cL.getD s default)
    theorem cgN_bits : ∀ s, s < 53 → Cg.getD (29 + s) 0 = bitsN (cN.getD s default)
    theorem annI : annOK 10 (fun l => Akap.getD l 0) 2 (fun q => QI.getD q 0) nQI = true
    theorem leftInv : leftInvOK (fun q => dotRow 10 (fun i => Amu.getD i 0) (QI.getD q 0) 3) nQI 3
      (fun q => TI.getD q 0) = true
    theorem annCk : annOK 10 (fun l => Akap.getD l 0) 2 (fun q => QC.getD q 0) 5 = true
    theorem annCm : annOK 10 (fun i => Amu.getD i 0) 3 (fun q => QC.getD q 0) 5 = true
    theorem c7_rows : ∀ q, q < 5 → dotRow 10 (fun s => Cg.getD s 0) (QC.getD q 0) 82 =
      Assembly.C7Rows.getD q 0
-/

set_option autoImplicit false

namespace FurioLombardo.Discharge.SelmerBasis.W7

open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower
open FurioLombardo.M2.Special (al7)

/-! ## Powers of `al7` -/

/-- `∏_{bit i of d} tab_i` (lowest bit first; `int 1` for `d = 0`). -/
def alPw : List (List ℤ) → ℕ → KE
  | [], _ => .int 1
  | P :: tab, d =>
    if d = 0 then .int 1
    else if d % 2 = 1 then (if d / 2 = 0 then .lin P else .mul (.lin P) (alPw tab (d / 2)))
    else alPw tab (d / 2)

/-- `tab_{i+1} = tab_i ²` at precision `k`. -/
def powOK (tab : List (List ℤ)) (k i : ℕ) : Bool :=
  checkK k (.sub (.mul (.lin (tab.getD i [])) (.lin (tab.getD i []))) (.lin (tab.getD (i + 1) [])))

/-- `U · Ui = 1 + al7 · Uc` at precision `k` (`U` a unit at `w7`). -/
def unitOK (k : ℕ) (U Ui Uc : List ℤ) : Bool :=
  checkK k (.sub (.mul (.lin U) (.lin Ui)) (.add (.int 1) (.mul (.lin al7) (.lin Uc))))

/-- The sign `(-1)^b`. -/
def sgnE (b : Bool) : KE := .int (if b then -1 else 1)

/-! ## Approximations of the component values -/

/-- `x0 - x1 y0`, the approximation of `ι₊ (x0 + x1 ω)`. -/
def XLp (y0 : List ℤ) (x : LC) : KE := .sub x.1 (.mul x.2 (.lin y0))

/-- `x0 + x1 y0`, the approximation of `ι₋ (x0 + x1 ω)`. -/
def XLm (y0 : List ℤ) (x : LC) : KE := .add x.1 (.mul x.2 (.lin y0))

/-- `XLp X ± XLp X' · S0`, the approximation of `ι_N (±) (X + X' Ω)`. -/
def XNs (y0 S0 : List ℤ) (b : Bool) (x : NC) : KE :=
  if b then .add (XLp y0 x.1) (.mul (XLp y0 x.2) (.lin S0))
  else .sub (XLp y0 x.1) (.mul (XLp y0 x.2) (.lin S0))

/-! ## The model -/

/-- The global approximations of `r`, `S` and the unit part of `A4` (module docstring). -/
structure Model where
  y0 : List ℤ
  ny : ℕ
  y0R : List ℤ
  y0i : List ℤ
  y0c : List ℤ
  S0 : List ℤ
  ns : ℕ
  S0R : List ℤ
  S0i : List ℤ
  S0c : List ℤ
  E4U : List ℤ
  E4Ui : List ℤ
  E4Uc : List ℤ
  /-- the precisions of the six checks -/
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  k4 : ℕ
  k5 : ℕ
  k6 : ℕ
  deriving Inhabited

namespace Model

variable (tab : List (List ℤ)) (M : Model)

/-- The error exponent of every approximation. -/
def N : ℕ := min M.ny M.ns

/-- `y0² - ε = al7^ny y0R`. -/
def okY : Bool :=
  decide (M.ny < 2 ^ tab.length) &&
    checkK M.k1 (.sub (.sub (.mul (.lin M.y0) (.lin M.y0)) (.lin M3b.epsL)) (.mul (alPw tab M.ny) (.lin M.y0R)))

/-- `S0² - (2 ea - 2 eb y0) = al7^ns S0R`. -/
def okS : Bool :=
  decide (M.ns < 2 ^ tab.length) &&
    checkK M.k3 (.sub (.sub (.mul (.lin M.S0) (.lin M.S0))
      (.sub (.mul (.int 2) (.lin M3b.eaL)) (.mul (.mul (.int 2) (.lin M3b.ebL)) (.lin M.y0))))
      (.mul (alPw tab M.ns) (.lin M.S0R)))

/-- `2 ea + 2 eb y0 = al7 E4U`. -/
def okE : Bool :=
  checkK M.k5 (.sub (.add (.mul (.int 2) (.lin M3b.eaL)) (.mul (.mul (.int 2) (.lin M3b.ebL)) (.lin M.y0)))
    (.mul (.lin al7) (.lin M.E4U)))

/-- All the model checks (the units `y0`, `S0`, `E4U` included). -/
def ok : Bool :=
  M.okY tab && unitOK M.k2 M.y0 M.y0i M.y0c && M.okS tab && unitOK M.k4 M.S0 M.S0i M.S0c && M.okE &&
    unitOK M.k6 M.E4U M.E4Ui M.E4Uc

end Model

/-! ## Square certificates -/

/-- A square certificate at a component `K_w7` (module docstring). -/
structure KCert where
  a0 : Bool
  a1 : Bool
  h : ℕ
  U : List ℤ
  Ui : List ℤ
  Uc : List ℤ
  n : ℕ
  R : List ℤ
  k1 : ℕ
  k2 : ℕ
  deriving Inhabited

/-- `X · al7^a0 · (-1)^a1 = al7^(2h) U² + al7^n R`, `U` a unit, `2 h < n`, `2 h < N`. -/
def KCert.ok (tab : List (List ℤ)) (N : ℕ) (X : KE) (c : KCert) : Bool :=
  decide (2 * c.h < c.n) && decide (2 * c.h < N) && decide (c.n < 2 ^ tab.length) &&
    checkK c.k1 (.sub (.mul (.mul X (if c.a0 then .lin al7 else .int 1)) (sgnE c.a1))
      (.add (.mul (alPw tab (2 * c.h)) (.mul (.lin c.U) (.lin c.U))) (.mul (alPw tab c.n) (.lin c.R)))) &&
    unitOK c.k2 c.U c.Ui c.Uc

/-- The row bits `a0 + 2 a1` of a certificate. -/
def KCert.bits (c : KCert) : ℕ := (if c.a0 then 1 else 0) + (if c.a1 then 2 else 0)

/-- A square certificate at the component `F'` (module docstring). -/
structure FCert where
  a0 : Bool
  a1 : Bool
  j : ℕ
  h : ℕ
  U : List ℤ
  Ui : List ℤ
  Uc : List ℤ
  n : ℕ
  R : List ℤ
  Ry : List ℤ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  deriving Inhabited

/-- The coordinates `(X', Y')` of `(x + y Z) Z^a0`. -/
def FCert.X' (E4U : List ℤ) (X Y : KE) (c : FCert) : KE :=
  if c.a0 then .mul (.mul (.lin al7) (.lin E4U)) Y else X

def FCert.Y' (X Y : KE) (c : FCert) : KE := if c.a0 then X else Y

/-- `X' (-1)^a1 = al7^(j+2h) E4U^j U² + al7^n R`, `Y' = al7^(j+2h) Ry`, `U` a unit, `j + 2 h < n`,
`j + 2 h < N`. -/
def FCert.ok (tab : List (List ℤ)) (N : ℕ) (E4U : List ℤ) (X Y : KE) (c : FCert) : Bool :=
  decide (c.j + 2 * c.h < c.n) && decide (c.j + 2 * c.h < N) && decide (c.n < 2 ^ tab.length) &&
    checkK c.k1 (.sub (.mul (c.X' E4U X Y) (sgnE c.a1))
      (.add (.mul (.mul (alPw tab (c.j + 2 * c.h)) ((KE.lin E4U).pow c.j)) (.mul (.lin c.U) (.lin c.U)))
        (.mul (alPw tab c.n) (.lin c.R)))) &&
    unitOK c.k2 c.U c.Ui c.Uc &&
    checkK c.k3 (.sub (c.Y' X Y) (.mul (alPw tab (c.j + 2 * c.h)) (.lin c.Ry)))

def FCert.bits (c : FCert) : ℕ := (if c.a0 then 1 else 0) + (if c.a1 then 2 else 0)

/-! ## Points -/

/-- A point of `y² = fRev 1 (x)` over `K_w7` at the global abscissa `x` (module docstring). -/
structure PtSq where
  x : List ℤ
  T : List ℤ
  A : List ℤ
  B : List ℤ
  Bi : List ℤ
  Cb : List ℤ
  m : ℕ
  k1 : ℕ
  k2 : ℕ
  k3 : ℕ
  deriving Inhabited

/-- `4 fRev_1(x) - T² = al7^(m+1) A`, `T² = al7^m B`, `B` a unit. -/
def PtSq.ok (tab : List (List ℤ)) (p : PtSq) : Bool :=
  decide (p.m + 1 < 2 ^ tab.length) &&
    checkK p.k1 (.sub (.sub (Count.gE 1 (.lin p.x) 0) (.mul (.lin p.T) (.lin p.T)))
      (.mul (alPw tab (p.m + 1)) (.lin p.A))) &&
    checkK p.k2 (.sub (.mul (.lin p.T) (.lin p.T)) (.mul (alPw tab p.m) (.lin p.B))) &&
    unitOK p.k3 p.B p.Bi p.Cb

/-- The point `P_i1 + P_i2 - ∞` with its values and certificates (module docstring). -/
structure PairData where
  i1 : ℕ
  i2 : ℕ
  P : List ℤ
  R : List ℤ
  kP : ℕ
  kR : ℕ
  tL : List (List ℤ)
  tN : List (List ℤ)
  precT : ℕ
  /-- `Λ_L`, `Λ_N` of `PtData.okT`: `tL = Λ_L² U(α)`, `tN = Λ_N² U(β)` (positive) -/
  lamL : ℕ
  lamN : ℕ
  c0 : KCert
  c1 : KCert
  c2 : KCert
  c3 : KCert
  c4 : FCert
  /-- `x1 - x2 = al7^dv dW`, `dW` a unit (so `x1 ≠ x2`) -/
  dv : ℕ
  dW : List ℤ
  dWi : List ℤ
  dWc : List ℤ
  kd1 : ℕ
  kd2 : ℕ
  deriving Inhabited

namespace PairData

/-- The `PtData` of `U = X² + P X + R` (`d = 1`, `Λ_L = lamL`, `Λ_N = lamN`) read by `PtData.okT`. -/
def toPt (pd : PairData) : PtData :=
  { P := pd.P, R := pd.R, d := 1, Z1 := [], Z0 := [], nj := 0, nM := 0, n0 := [], nd := [], nR := [],
    aj := 0, aM := 0, a0 := [], ad := [], aR := [], prec := 0, lamL := pd.lamL, tL := pd.tL,
    lamN := pd.lamN, tN := pd.tN, precT := pd.precT }

/-- `zkE P = -(x1 + x2)`, `zkE R = x1 x2` for the abscissas of the points `i1`, `i2`, and
`x1 - x2 = al7^dv dW` with `dW` a unit, `lamL`, `lamN` positive. -/
def okU (tab : List (List ℤ)) (pts : List PtSq) (pd : PairData) : Bool :=
  decide (0 < pd.lamL) && decide (0 < pd.lamN) && decide (pd.i1 < pts.length) && decide (pd.i2 < pts.length) && decide (pd.dv < 2 ^ tab.length) &&
    checkK pd.kd1 (.sub (.sub (.lin (pts.getD pd.i1 default).x) (.lin (pts.getD pd.i2 default).x))
      (.mul (alPw tab pd.dv) (.lin pd.dW))) &&
    unitOK pd.kd2 pd.dW pd.dWi pd.dWc &&
    checkK pd.kP (.sub (.lin pd.P) (.sub (.int 0)
      (.add (.lin (pts.getD pd.i1 default).x) (.lin (pts.getD pd.i2 default).x)))) &&
    checkK pd.kR (.sub (.lin pd.R) (.mul (.lin (pts.getD pd.i1 default).x) (.lin (pts.getD pd.i2 default).x)))

/-- The five certificates of `U(τ)`. -/
def okC (tab : List (List ℤ)) (M : Model) (pd : PairData) : Bool :=
  pd.c0.ok tab M.N (XLp M.y0 (ofL pd.tL)) && pd.c1.ok tab M.N (XLm M.y0 (ofL pd.tL)) &&
    pd.c2.ok tab M.N (XNs M.y0 M.S0 true (ofN pd.tN)) && pd.c3.ok tab M.N (XNs M.y0 M.S0 false (ofN pd.tN)) &&
    pd.c4.ok tab M.N M.E4U (XLm M.y0 (ofN pd.tN).1) (XLm M.y0 (ofN pd.tN).2)

/-- The row of the point: `c.bits` at bits `2 c` (`c < 4`) and `8`. -/
def bits (pd : PairData) : ℕ :=
  pd.c0.bits + 4 * pd.c1.bits + 16 * pd.c2.bits + 64 * pd.c3.bits + 256 * pd.c4.bits

end PairData

/-! ## The generators -/

/-- The certificates of `gensL s` at the components 0, 1. -/
def okL (tab : List (List ℤ)) (M : Model) (cc : KCert × KCert) (s : ℕ) : Bool :=
  cc.1.ok tab M.N (XLp M.y0 (ofL (SUnitData.gL.getD s []))) &&
    cc.2.ok tab M.N (XLm M.y0 (ofL (SUnitData.gL.getD s [])))

/-- The certificates of `gensN s` at the components 2, 3, 4. -/
def okN (tab : List (List ℤ)) (M : Model) (cc : KCert × KCert × FCert) (s : ℕ) : Bool :=
  cc.1.ok tab M.N (XNs M.y0 M.S0 true (ofN (SUnitData.gN.getD s []))) &&
    cc.2.1.ok tab M.N (XNs M.y0 M.S0 false (ofN (SUnitData.gN.getD s []))) &&
    cc.2.2.ok tab M.N M.E4U (XLm M.y0 (ofN (SUnitData.gN.getD s [])).1)
      (XLm M.y0 (ofN (SUnitData.gN.getD s [])).2)

/-- The approximations of the scalars `al7` (`i = 0`) and `-1` (`i = 1`) at `F'` (exact). -/
def kapXE (i : ℕ) : KE := if i = 0 then .lin al7 else .int (-1)

/-- The rows of the scalars at the four components `K_w7`: `(1, 0)` for `al7`, `(0, 1)` for `-1`. -/
def kapLow (i : ℕ) : ℕ := if i = 0 then 85 else 170

/-- The row of `gensL s`: bits 0 .. 3. -/
def bitsL (cc : KCert × KCert) : ℕ := cc.1.bits + 4 * cc.2.bits

/-- The row of `gensN s`: bits 4 .. 9. -/
def bitsN (cc : KCert × KCert × FCert) : ℕ := 16 * cc.1.bits + 64 * cc.2.1.bits + 256 * cc.2.2.bits

end FurioLombardo.Discharge.SelmerBasis.W7
