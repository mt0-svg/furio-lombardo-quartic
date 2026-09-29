import FurioLombardo.Discharge.SelmerBasis.PlaceUCert
import FurioLombardo.Discharge.SelmerBasis.PointGen

/-!
# The place w2: the certificate formats and their kernel checks (lane selmer-w2)

The records and `Bool` checks of W2Unram.lean (`UCert1`, `certOKU1`, `RhoData`, `SqrtU`, the approximation
coordinates `X0L2`, `X1L2`, `X0N2`, `X1N2`), apart from their proofs, so that the data and check modules
(W2Data*.lean, W2Check*.lean) import no proof of W2Unram.lean.
-/

namespace FurioLombardo.Discharge.SelmerBasis.W2U

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.Tower

/-! ## Certificate data (kernel side) -/

/-- A square certificate at `F`: bits `a` (26 bits), `S = u + s ζ` with the unit coordinate
`(if ub then s else u) = 1 + al c0`, the remainder `al^n (R0 + R1 ζ)`, the truncation of the basis
product at `π^n`, and the `checkK` precision. -/
structure UCert1 where
  a : ℕ
  mh : ℕ
  ub : Bool
  u : List ℤ
  s : List ℤ
  c0 : List ℤ
  n : ℕ
  R0 : List ℤ
  R1 : List ℤ
  prec : ℕ
  deriving Inhabited

/-- Bit 0 of `a` (the factor `π`). -/
def bit0U (a : ℕ) : ℕ := if a.testBit 0 then 1 else 0

/-- `Σ_k f(p_k) al^(n + k + a0)` over a coefficient list, one `KE` sum. -/
def polyE (E : EisData) (f : ℤ × ℤ → ℤ) (a0 : ℕ) : ℕ → List (ℤ × ℤ) → KE
  | _, [] => .int 0
  | n, p :: P => .add (.mul (.int (f p)) (.lin (E.alP (n + a0)))) (polyE E f a0 (n + 1) P)

/-- The expansion of the basis product with bits `a`, truncated at `π^n`. -/
def trU (E : EisData) (a n : ℕ) : List (ℤ × ℤ) := (dpU (facU E.e a)).take n

/-- The coordinates `(1, ζ)` of `(X0 + X1 ζ)(P1 + P2 ζ)`. -/
def lhs1 (X0 X1 P1 P2 : KE) : KE × KE :=
  (.sub (.mul X0 P1) (.mul X1 P2), .add (.mul X0 P2) (.mul X1 (.add P1 P2)))

/-- The coordinates `(1, ζ)` of `al^(2 mh) (u + s ζ)² + al^n (R0 + R1 ζ)`. -/
def rhs1 (E : EisData) (c : UCert1) : KE × KE :=
  (.add (.mul (.sub (.mul (.lin c.u) (.lin c.u)) (.mul (.lin c.s) (.lin c.s))) (.lin (E.alP (2 * c.mh))))
      (.mul (.lin c.R0) (.lin (E.alP c.n))),
    .add (.mul (.add (.mul (.int 2) (.mul (.lin c.u) (.lin c.s))) (.mul (.lin c.s) (.lin c.s)))
        (.lin (E.alP (2 * c.mh))))
      (.mul (.lin c.R1) (.lin (E.alP c.n))))

/-- **The certificate check** of `x ≈ X0 + X1 ζ`. -/
def certOKU1 (E : EisData) (X0 X1 : KE) (c : UCert1) : Bool :=
  decide (2 * c.mh + 2 * E.e < c.n) && decide (c.n < E.alPow.length) &&
  checkK c.prec (.sub (.lin (if c.ub then c.s else c.u)) (.add (.int 1) (.mul (.lin E.al) (.lin c.c0)))) &&
  checkK c.prec (.sub (lhs1 X0 X1 (polyE E Prod.fst (bit0U c.a) 0 (trU E c.a c.n))
      (polyE E Prod.snd (bit0U c.a) 0 (trU E c.a c.n))).1 (rhs1 E c).1) &&
  checkK c.prec (.sub (lhs1 X0 X1 (polyE E Prod.fst (bit0U c.a) 0 (trU E c.a c.n))
      (polyE E Prod.snd (bit0U c.a) 0 (trU E c.a c.n))).2 (rhs1 E c).2)

/-- A Hensel certificate for `ρ` with `3 ρ² = -ε`: `r0 = al^j (1 + al d)`, `3 r0² + ε = al^n R`. -/
structure RhoData where
  j : ℕ
  d : List ℤ
  n : ℕ
  R : List ℤ
  prec : ℕ
  deriving Inhabited

/-- `r0 = al^j (1 + al d)`. -/
def RhoData.r0 (E : EisData) (S : RhoData) : KE :=
  .mul (.lin (E.alP S.j)) (.add (.int 1) (.mul (.lin E.al) (.lin S.d)))

/-- The kernel checks of a `RhoData`. -/
def RhoData.ok (E : EisData) (S : RhoData) : Bool :=
  decide (S.n < E.alPow.length) && decide (S.j < E.alPow.length) && decide (2 * E.e + 2 * S.j < S.n) &&
  checkK S.prec (.sub (.add (.mul (.int 3) (.mul (S.r0 E) (S.r0 E))) (.lin epsL))
    (.mul (.lin (E.alP S.n)) (.lin S.R)))

/-- A square root certificate for `iL2 (4 eN)`: `s0 = s00 + s01 ζ`, `s00 = al^j (1 + al d0)`,
`s01 = al^j d1`, and `s0² - Z0 = al^n (R0 + R1 ζ)` with `Z0 = (2 ea - 2 eb r0) + 4 eb r0 ζ`. -/
structure SqrtU where
  j : ℕ
  n : ℕ
  s00 : List ℤ
  s01 : List ℤ
  d0 : List ℤ
  d1 : List ℤ
  R0 : List ℤ
  R1 : List ℤ
  prec : ℕ
  deriving Inhabited

/-- The kernel checks of a `SqrtU`. -/
def SqrtU.ok (E : EisData) (SR : RhoData) (S : SqrtU) : Bool :=
  decide (S.n < E.alPow.length) && decide (S.j < E.alPow.length) &&
  decide (2 * E.e + 2 * S.j < S.n) && decide (S.n + SR.j ≤ SR.n) &&
  checkK S.prec (.sub (.lin S.s00) (.mul (.lin (E.alP S.j)) (.add (.int 1)
    (.mul (.lin E.al) (.lin S.d0))))) &&
  checkK S.prec (.sub (.lin S.s01) (.mul (.lin (E.alP S.j)) (.lin S.d1))) &&
  checkK S.prec (.sub (.sub (.sub (.mul (.lin S.s00) (.lin S.s00)) (.mul (.lin S.s01) (.lin S.s01)))
      (.mul (.int 2) (.sub (.lin eaL) (.mul (.lin ebL) (SR.r0 E)))))
    (.mul (.lin (E.alP S.n)) (.lin S.R0))) &&
  checkK S.prec (.sub (.sub (.add (.mul (.int 2) (.mul (.lin S.s00) (.lin S.s01)))
        (.mul (.lin S.s01) (.lin S.s01)))
      (.mul (.int 4) (.mul (.lin ebL) (SR.r0 E))))
    (.mul (.lin (E.alP S.n)) (.lin S.R1)))

/-- The coordinates approximating `iL2 (evL t) = (t1 - t2 ρ) + 2 t2 ρ ζ`. -/
def X0L2 (E : EisData) (SR : RhoData) (t : LC) : KE := .sub t.1 (.mul t.2 (SR.r0 E))

def X1L2 (E : EisData) (SR : RhoData) (t : LC) : KE := .mul (.int 2) (.mul t.2 (SR.r0 E))

/-- The coordinates approximating `iN2 b (evN t) = iL2 (evL t.1) ± iL2 (evL t.2) sU`, with
`sU ≈ s00 + s01 ζ` and `(p + q ζ)(s00 + s01 ζ) = (p s00 - q s01) + (p s01 + q (s00 + s01)) ζ`. -/
def X0N2 (E : EisData) (SR : RhoData) (S : SqrtU) (t : NC) (b : Bool) : KE :=
  .add (X0L2 E SR t.1) (.mul (.int (if b then 1 else -1))
    (.sub (.mul (X0L2 E SR t.2) (.lin S.s00)) (.mul (X1L2 E SR t.2) (.lin S.s01))))

def X1N2 (E : EisData) (SR : RhoData) (S : SqrtU) (t : NC) (b : Bool) : KE :=
  .add (X1L2 E SR t.1) (.mul (.int (if b then 1 else -1))
    (.add (.mul (X0L2 E SR t.2) (.lin S.s01)) (.mul (X1L2 E SR t.2) (.add (.lin S.s00) (.lin S.s01)))))

end FurioLombardo.Discharge.SelmerBasis.W2U
