import FurioLombardo.Discharge.SelmerBasis.PlaceUGen
import FurioLombardo.Discharge.SelmerBasis.PlaceWElem

/-!
# Square certificates at the unramified quadratic extension of an Eisenstein component

For a place `σ : K21 →+* Kw` with an Eisenstein component `F1 = CF σ E` (PlaceWCert.lean), the
unramified quadratic extension of `F1` is `F2 = F1(ζ)`, `ζ² = ζ - 1` (`QF F1 (-1) 1`, a field since
the residue field of `F1` is `𝔽₂`, `noRoot_model`). This is the quartic component at `v`.
Its uniformizer is `Y = cY σ E`, `‖2‖ = ‖Y‖ ^ (2 e)`, and the standard basis of `F2ˣ / F2ˣ²` is
`bU Y (2 e)` of PlaceUGen.lean.

* `zmul`, `dpU`, `facU`: the expansion of `∏ (1 + Y^t w)` (`w ∈ {1, ζ, 4 ζ}`) as a polynomial in `Y`
  over `ℤ[ζ]`, computed on integers; `evZL` its value.
* `certOKU`: four `checkK` identities (two `K21` coordinates of each `F1` coordinate) of
  `X · ∏ bU^a = Y^(2 mh) (u + s ζ)² + al^n R` with the product truncated at `Y^D`.
* `certOKU_isSquare`: a passing check makes `x · BaU a` a square for every `x` within `‖al‖^n` of
  the exact element `toU X0 X1 X2 X3`.
* `SqrtV`, `iNv`: `N84 →+* F2`, `ω_N ↦ (2 ζ - 1) ρ / 2` with `3 ρ² = -iL (4 eN)` (Hensel root in `F1`).
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis.Tower

/-! ## Polynomials in `Y` over `ℤ[ζ]`, `ζ² = ζ - 1` -/

/-- The product in `ℤ[ζ]`. -/
def zmul (p q : ℤ × ℤ) : ℤ × ℤ := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1 + p.2 * q.2)

/-- The sum of two coefficient lists. -/
def addZL : List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a.1 + b.1, a.2 + b.2) :: addZL p q

/-- Multiplication by `1 + Y^t w`. -/
def stepU (f : ℕ × (ℤ × ℤ)) (P : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  addZL P (List.replicate f.1 (0, 0) ++ P.map (zmul f.2))

/-- `∏ (1 + Y^t w)` over a list of factors `(t, w)`. -/
def dpU (F : List (ℕ × (ℤ × ℤ))) : List (ℤ × ℤ) := F.foldr stepU [(1, 0)]

/-- The factors of the basis product with bits `a`, `e` the ramification index of the base:
`1 + Y^(2 (j / 2) + 1) w_(j % 2)` for bit `j + 1` (`j < 2 e`, `w = ![1, ζ]`), and `1 + 4 ζ` for bit
`2 e + 1`. -/
def facU (e a : ℕ) : List (ℕ × (ℤ × ℤ)) :=
  ((List.range (2 * e)).filter fun j => a.testBit (j + 1)).map
      (fun j => (2 * (j / 2) + 1, if j % 2 = 0 then ((1 : ℤ), (0 : ℤ)) else (0, 1))) ++
    (if a.testBit (2 * e + 1) then [(0, ((0 : ℤ), (4 : ℤ)))] else [])

/-- The value `Σ_k (α_k + β_k z) y^k` of a coefficient list. -/
def evZL {R : Type*} [CommRing R] (y z : R) : List (ℤ × ℤ) → R
  | [] => 0
  | p :: P => ((p.1 : R) + (p.2 : R) * z) + y * evZL y z P

lemma evZL_addZL {R : Type*} [CommRing R] (y z : R) (P Q : List (ℤ × ℤ)) :
    evZL y z (addZL P Q) = evZL y z P + evZL y z Q := by
  induction P generalizing Q with
  | nil => simp [addZL, evZL]
  | cons a P ih =>
    cases Q with
    | nil => simp [addZL, evZL]
    | cons b Q =>
      simp [addZL, evZL, ih Q]
      ring

lemma evZL_replicate {R : Type*} [CommRing R] (y z : R) (t : ℕ) (L : List (ℤ × ℤ)) :
    evZL y z (List.replicate t (0, 0) ++ L) = y ^ t * evZL y z L := by
  induction t generalizing L with
  | zero => simp [evZL]
  | succ t ih =>
    simp [List.replicate_succ, evZL, ih]
    ring

lemma evZL_map_zmul {R : Type*} [CommRing R] (y z : R) (hz : z * z = z - 1) (w : ℤ × ℤ)
    (P : List (ℤ × ℤ)) : evZL y z (P.map (zmul w)) = ((w.1 : R) + (w.2 : R) * z) * evZL y z P := by
  induction P generalizing w with
  | nil => simp [evZL, zmul]
  | cons p P ih =>
    simp [evZL, List.map_cons, ih, zmul]
    push_cast
    ring_nf
    have hz' : z ^ 2 = z - 1 := by
      calc
        z ^ 2 = z * z := by ring
        _ = z - 1 := hz
    rw [hz']
    ring

lemma evZL_stepU {R : Type*} [CommRing R] (y z : R) (hz : z * z = z - 1)
    (f : ℕ × (ℤ × ℤ)) (P : List (ℤ × ℤ)) :
    evZL y z (stepU f P) = (1 + y ^ f.1 * ((f.2.1 : R) + (f.2.2 : R) * z)) * evZL y z P := by
  simp [stepU, evZL_addZL y z, evZL_replicate y z, evZL_map_zmul y z hz f.2 P]
  push_cast
  ring

section Ring

variable {R : Type*} [CommRing R] (y z : R)

theorem evZL_dpU (hz : z * z = z - 1) (F : List (ℕ × (ℤ × ℤ))) :
    evZL y z (dpU F) = (F.map fun f => 1 + y ^ f.1 * ((f.2.1 : R) + (f.2.2 : R) * z)).prod := by
  induction F with
  | nil =>
    simp [dpU, evZL, List.map, List.prod]
  | cons f F ih =>
    simp [dpU, List.foldr_cons, evZL_stepU y z hz f, List.map_cons, List.prod_cons]
    unfold dpU at ih
    rw [ih]

theorem evZL_take_drop (D : ℕ) (P : List (ℤ × ℤ)) :
    evZL y z P = evZL y z (P.take D) + y ^ D * evZL y z (P.drop D) := by
  induction' D with D ih generalizing P
  · simp [evZL]
  · match P with
    | [] => simp [evZL]
    | p :: P' =>
      simp only [List.take_succ_cons, List.drop_succ_cons, evZL]
      rw [ih P']
      ring

end Ring

theorem norm_evZL_le_one {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] {y z : R}
    (hy : ‖y‖ ≤ 1) (hz : ‖z‖ ≤ 1) (P : List (ℤ × ℤ)) : ‖evZL y z P‖ ≤ 1 := by
  induction P with
  | nil =>
      simp [evZL]
  | cons p P ih =>
      simp [evZL]
      have hy' : 0 ≤ ‖y‖ := norm_nonneg _
      have hz' : 0 ≤ ‖z‖ := norm_nonneg _
      have hnorm_evZL : 0 ≤ ‖evZL y z P‖ := norm_nonneg _
      have hnorm_p2 : 0 ≤ ‖(p.2 : R)‖ := norm_nonneg _
      calc
        ‖((p.1 : R) + (p.2 : R) * z) + y * evZL y z P‖ ≤
            max ‖((p.1 : R) + (p.2 : R) * z)‖ ‖y * evZL y z P‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max 1 1 := by
          refine max_le_max ?_ ?_
          · calc
              ‖((p.1 : R) + (p.2 : R) * z)‖ ≤ max ‖(p.1 : R)‖ ‖(p.2 : R) * z‖ :=
                IsUltrametricDist.norm_add_le_max _ _
              _ ≤ max 1 1 := by
                refine max_le_max (IsUltrametricDist.norm_intCast_le_one R p.1) ?_
                calc
                  ‖(p.2 : R) * z‖ ≤ ‖(p.2 : R)‖ * ‖z‖ := norm_mul_le _ _
                  _ ≤ 1 * 1 := mul_le_mul (IsUltrametricDist.norm_intCast_le_one R p.2) hz hz' (by norm_num)
                  _ = 1 := by norm_num
              _ = 1 := by norm_num
          · calc
              ‖y * evZL y z P‖ ≤ ‖y‖ * ‖evZL y z P‖ := norm_mul_le _ _
              _ ≤ 1 * 1 := mul_le_mul hy ih hnorm_evZL (by norm_num)
              _ = 1 := by norm_num
        _ = 1 := by norm_num

/-! ## The certificate -/

/-- A square certificate at `F2`: bits `a`, `S = Y^mh (u + s ζ)` with `u = u0 + u1 Y`,
`s = s0 + s1 Y`, the unit coordinate `(if ub then s0 else u0) = 1 + al c0`, the remainder
`al^n ((R00 + R01 Y) + (R10 + R11 Y) ζ)`, and the `checkK` precision. -/
structure UCert where
  a : ℕ
  mh : ℕ
  ub : Bool
  u0 : List ℤ
  u1 : List ℤ
  s0 : List ℤ
  s1 : List ℤ
  c0 : List ℤ
  n : ℕ
  R00 : List ℤ
  R01 : List ℤ
  R10 : List ℤ
  R11 : List ℤ
  prec : ℕ
  deriving Inhabited

/-- The terms of `(α + β ζ) Y^n x` on `1` and on `ζ`, `x = (X0 + X1 Y) + (X2 + X3 Y) ζ`. -/
def lhsUAux (X0 X1 X2 X3 : KE) (a0 : ℕ) : ℕ → List (ℤ × ℤ) → List (KE × ℕ) × List (KE × ℕ)
  | _, [] => ([], [])
  | n, p :: P =>
    let r := lhsUAux X0 X1 X2 X3 a0 (n + 1) P
    ((.mul (.int p.1) X0, n + a0) :: (.mul (.int p.1) X1, n + a0 + 1) ::
        (.mul (.int (-p.2)) X2, n + a0) :: (.mul (.int (-p.2)) X3, n + a0 + 1) :: r.1,
      (.mul (.int p.2) X0, n + a0) :: (.mul (.int p.2) X1, n + a0 + 1) ::
        (.mul (.int (p.1 + p.2)) X2, n + a0) :: (.mul (.int (p.1 + p.2)) X3, n + a0 + 1) :: r.2)

/-- The terms of `x ∏ bU^a`, the product truncated at `Y^D`. -/
def lhsU (E : EisData) (D : ℕ) (X0 X1 X2 X3 : KE) (a : ℕ) : List (KE × ℕ) × List (KE × ℕ) :=
  lhsUAux X0 X1 X2 X3 (if a.testBit 0 then 1 else 0) 0 ((dpU (facU (2 * E.e) a)).take D)

/-- The terms of `Y^(2 mh) (u + s ζ)² + al^n R` on `1` and on `ζ`. -/
def rhsU (E : EisData) (c : UCert) : List (KE × ℕ) × List (KE × ℕ) :=
  let u0 : KE := .lin c.u0
  let u1 : KE := .lin c.u1
  let s0 : KE := .lin c.s0
  let s1 : KE := .lin c.s1
  let m := 2 * c.mh
  let al : KE := .lin (E.alP c.n)
  ([(.sub (.mul u0 u0) (.mul s0 s0), m), (.mul (.int 2) (.sub (.mul u0 u1) (.mul s0 s1)), m + 1),
      (.sub (.mul u1 u1) (.mul s1 s1), m + 2), (.mul al (.lin c.R00), 0), (.mul al (.lin c.R01), 1)],
    [(.add (.mul (.int 2) (.mul u0 s0)) (.mul s0 s0), m),
      (.add (.mul (.int 2) (.add (.mul u0 s1) (.mul u1 s0))) (.mul (.int 2) (.mul s0 s1)), m + 1),
      (.add (.mul (.int 2) (.mul u1 s1)) (.mul s1 s1), m + 2), (.mul al (.lin c.R10), 0),
      (.mul al (.lin c.R11), 1)])

/-- **The certificate check** of `x = toU X0 X1 X2 X3` with truncation at `Y^D`. -/
def certOKU (E : EisData) (D : ℕ) (X0 X1 X2 X3 : KE) (c : UCert) : Bool :=
  decide (2 * c.mh + 4 * E.e < 2 * c.n) && decide (2 * c.n ≤ D) && decide (c.n < E.alPow.length) &&
  decide (D + 1 < E.Ypow.length) && decide (2 * c.mh + 2 < E.Ypow.length) &&
  checkK c.prec (.sub (.lin (if c.ub then c.s0 else c.u0)) (.add (.int 1) (.mul (.lin E.al) (.lin c.c0)))) &&
  checkK c.prec (.sub (lcE E 0 (lhsU E D X0 X1 X2 X3 c.a).1) (lcE E 0 (rhsU E c).1)) &&
  checkK c.prec (.sub (lcE E 1 (lhsU E D X0 X1 X2 X3 c.a).1) (lcE E 1 (rhsU E c).1)) &&
  checkK c.prec (.sub (lcE E 0 (lhsU E D X0 X1 X2 X3 c.a).2) (lcE E 0 (rhsU E c).2)) &&
  checkK c.prec (.sub (lcE E 1 (lhsU E D X0 X1 X2 X3 c.a).2) (lcE E 1 (rhsU E c).2))

/-- A square root certificate for `-iL (4 eN) / 3` in `F1`: `s0 = s00 + s01 Y` with
`s00 = al^j (1 + al d0)`, `s01 = al^j d1`, and `3 s0² + iL (4 eN) = al^n (R0 + R1 Y)`. -/
structure SqrtV where
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

/-- The kernel checks of a `SqrtV`. -/
def SqrtV.ok (E : EisData) (M : LModel) (S : SqrtV) : Bool :=
  decide (S.n < E.alPow.length) && decide (S.j + 1 < E.alPow.length) &&
  decide (2 * E.e + 2 * S.j < S.n) &&
  checkK S.prec (.sub (.lin S.s00) (.mul (.lin (E.alP S.j)) (.add (.int 1)
    (.mul (.lin E.al) (.lin S.d0))))) &&
  checkK S.prec (.sub (.lin S.s01) (.mul (.lin (E.alP S.j)) (.lin S.d1))) &&
  -- coordinate 1 of `3 s0² + (2 ea + 2 eb y) + 2 eb c Y`
  checkK S.prec (.sub (.add (.mul (.int 3) (.add (.mul (.lin S.s00) (.lin S.s00))
      (.mul (.mul (.lin S.s01) (.lin S.s01)) (.lin E.A))))
      (.mul (.int 2) (.add (.lin eaL) (.mul (.lin ebL) (.lin M.y)))))
    (.mul (.lin (E.alP S.n)) (.lin S.R0))) &&
  -- coordinate `Y`
  checkK S.prec (.sub (.add (.mul (.int 3) (.add (.mul (.int 2) (.mul (.lin S.s00) (.lin S.s01)))
      (.mul (.mul (.lin S.s01) (.lin S.s01)) (.lin E.B))))
      (.mul (.int 2) (.mul (.lin ebL) (.lin M.c))))
    (.mul (.lin (E.alP S.n)) (.lin S.R1))) &&
  decide (0 < E.e)

/-- The coordinates on `1, Y, ζ, Y ζ` of `iL (evL t.1) + iL (evL t.2) (2 ζ - 1) s0`,
`s0 = s00 + s01 Y`: `(X0 + X1 Y) = iL t.1 - iL t.2 · s0`, `(X2 + X3 Y) = 2 iL t.2 · s0`. -/
def XNv (E : EisData) (M : LModel) (S : SqrtV) (t : NC) : KE × KE × KE × KE :=
  let P0 : KE := .add (.mul (X0L M t.2) (.lin S.s00)) (.mul (.mul (X1L M t.2) (.lin S.s01)) (.lin E.A))
  let P1 : KE := .add (.add (.mul (X0L M t.2) (.lin S.s01)) (.mul (X1L M t.2) (.lin S.s00)))
    (.mul (.mul (X1L M t.2) (.lin S.s01)) (.lin E.B))
  (.sub (X0L M t.1) P0, .sub (X1L M t.1) P1, .mul (.int 2) P0, .mul (.int 2) P1)

section Place

variable {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw]
  {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r)]

/-- `X² - X + 1` has no root in `F1`. -/
theorem noRoot_CF (hW : WPlace σ E) : ∀ r : CF σ E, r ^ 2 ≠ -1 + 1 * r :=
  noRoot_model (qfE_res hW.unif hW.norm_A hW.norm_B hW.res)

variable [Fact (∀ r : CF σ E, r ^ 2 ≠ -1 + 1 * r)]

variable (σ E)

/-- The unramified quadratic extension `F2 = F1(ζ)`. -/
abbrev UF : Type _ := QF (CF σ E) (-1) 1

/-- `ζ`. -/
noncomputable def cZ : UF σ E := QF.mk (CF σ E) (-1) 1 0 1

/-- The element `(X0 + X1 Y) + (X2 + X3 Y) ζ`. -/
noncomputable def toU (X0 X1 X2 X3 : KE) : UF σ E :=
  QF.mk (CF σ E) (-1) 1 (toF σ E (evK X0) (evK X1)) (toF σ E (evK X2) (evK X3))

/-- The basis product `∏ bU^(bit i of a)` of `F2`. -/
noncomputable def BaU (a : ℕ) : UF σ E :=
  ∏ i : Fin (2 * (2 * E.e) + 2),
    bU (A := (-1 : CF σ E)) (B := 1) (cY σ E) (2 * E.e) i ^ (if a.testBit i then 1 else 0)

variable {σ E}

theorem cZ_mul_cZ : cZ σ E * cZ σ E = cZ σ E - 1 := by
  unfold cZ QF.mk
  show ((⟨0, 1⟩ : QuadraticAlgebra (CF σ E) (-1) 1) * (⟨0, 1⟩ : QuadraticAlgebra (CF σ E) (-1) 1) =
    (⟨0, 1⟩ : QuadraticAlgebra (CF σ E) (-1) 1) - 1)
  refine QuadraticAlgebra.ext ?_ ?_
  · simp [QuadraticAlgebra.re_one]
  · simp [QuadraticAlgebra.im_one]

/-- The basis product from the integer expansion. -/
theorem BaU_eq (a : ℕ) : BaU σ E a =
    algebraMap (CF σ E) (UF σ E) (cY σ E) ^ (if a.testBit 0 then 1 else 0) *
      evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) (dpU (facU (2 * E.e) a)) := by
  let e' := 2 * E.e
  let π := algebraMap (CF σ E) (UF σ E) (cY σ E)
  let ζ := cZ σ E
  have hζ : ζ * ζ = ζ - 1 := cZ_mul_cZ
  have h_evZL := evZL_dpU (R := UF σ E) π ζ hζ (facU e' a)
  rw [h_evZL]
  -- Goal: BaU σ E a = π ^ (if a.testBit 0 then 1 else 0) * ((facU e' a).map ...).prod
  have h_bitv_val : ∀ (i : Fin (2*e' + 2)), (bitv (2*e' + 2) a i).val = (if a.testBit i then 1 else 0) := by
    intro i
    unfold bitv
    by_cases h : a.testBit i
    · simp [h, ZMod.val_one]
    · simp [h, ZMod.val_zero]
  have bU_mid_eq : ∀ (i : ℕ), 1 ≤ i → i ≤ 2*e' →
      bU (A := (-1 : CF σ E)) (B := 1) (cY σ E) e' i = 1 + π ^ (2*((i-1)/2)+1) * (if (i-1) % 2 = 0 then 1 else ζ) := by
    intro i hi1 hi2
    unfold bU jU lU
    have hi0 : i ≠ 0 := by omega
    have hi_last : i ≠ 2*e' + 1 := by omega
    dsimp [π, ζ, cZ]
    simp [hi0, hi_last]
  have h_facU_map : ((facU e' a).map fun f => 1 + π ^ f.1 * ((f.2.1 : UF σ E) + (f.2.2 : UF σ E) * ζ)).prod =
      (((List.range (2*e')).filter fun j => a.testBit (j + 1)).map
        (fun j => 1 + π ^ (2*(j/2)+1) * (if j % 2 = 0 then 1 else ζ))).prod *
      (if a.testBit (2*e' + 1) then 1 + 4*ζ else 1) := by
    unfold facU
    rw [List.map_append, List.prod_append]
    by_cases h : a.testBit (2*e' + 1)
    · rw [ite_eq_left h]
      rw [List.map_map]
      have h_singleton : (List.map (fun f => 1 + π ^ f.1 * ((f.2.1 : UF σ E) + (f.2.2 : UF σ E) * ζ))
          [(0, ((0 : ℤ), (4 : ℤ)))]).prod = 1 + 4*ζ := by
        simp
      rw [h_singleton]
      have h_eq : (fun (f : ℕ × ℤ × ℤ) => 1 + π ^ f.1 * ((f.2.1 : UF σ E) + (f.2.2 : UF σ E) * ζ)) ∘
                 (fun (j : ℕ) => (2*(j/2)+1, if j % 2 = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ)))) =
                 (fun (j : ℕ) => 1 + π ^ (2*(j/2)+1) * (if j % 2 = 0 then 1 else ζ)) := by
        ext j
        simp
        by_cases hj : j % 2 = 0
        · simp [hj]
        · simp [hj]
      rw [h_eq]
      simp [h]
    · rw [ite_eq_right h]
      rw [List.map_map]
      have h_eq : (fun (f : ℕ × ℤ × ℤ) => 1 + π ^ f.1 * ((f.2.1 : UF σ E) + (f.2.2 : UF σ E) * ζ)) ∘
                 (fun (j : ℕ) => (2*(j/2)+1, if j % 2 = 0 then ((1 : ℤ), (0 : ℤ)) else ((0 : ℤ), (1 : ℤ)))) =
                 (fun (j : ℕ) => 1 + π ^ (2*(j/2)+1) * (if j % 2 = 0 then 1 else ζ)) := by
        ext j
        simp
        by_cases hj : j % 2 = 0
        · simp [hj]
        · simp [hj]
      rw [h_eq]
      simp [h]
  calc
    BaU σ E a = ∏ i : Fin (2*e' + 2), bU (A := (-1 : CF σ E)) (B := 1) (cY σ E) e' i ^ (if a.testBit i then 1 else 0) := rfl
    _ = ∏ i : Fin (2*e' + 2), bU (A := (-1 : CF σ E)) (B := 1) (cY σ E) e' i ^ ((bitv (2*e' + 2) a i).val) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [h_bitv_val i]
    _ = ∏ i : Fin (2*e' + 2),
        (if (i : ℕ) = 0 then π else if (i : ℕ) = 2*e' + 1 then 1 + 4 * ζ else
          1 + π ^ (2*(((i : ℕ)-1)/2)+1) * (if ((i : ℕ)-1) % 2 = 0 then 1 else ζ)) ^ ((bitv (2*e' + 2) a i).val) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      by_cases hi0 : (i : ℕ) = 0
      · rw [hi0]; unfold bU π; rfl
      · by_cases hi_last : (i : ℕ) = 2*e' + 1
        · rw [hi_last]; unfold bU ζ cZ; rfl
        · have h_ge1 : 1 ≤ (i : ℕ) := by
            have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
            omega
          have h_le : (i : ℕ) ≤ 2*e' := by
            have h_lt : (i : ℕ) < 2*e' + 2 := i.2
            omega
          rw [bU_mid_eq (i : ℕ) h_ge1 h_le]
          simp [hi0, hi_last]
    _ = π ^ (if a.testBit 0 then 1 else 0) *
        (((List.range (2*e')).filter fun j => a.testBit (j + 1)).map
          (fun j => 1 + π ^ (2*(j/2)+1) * (if j % 2 = 0 then 1 else ζ))).prod *
        (1 + 4*ζ) ^ (if a.testBit (2*e' + 1) then 1 else 0) := by
      rw [prod_bits_basis (2*e') π (1 + 4*ζ) (fun j => 1 + π ^ (2*(j/2)+1) * (if j % 2 = 0 then 1 else ζ)) a]
    _ = π ^ (if a.testBit 0 then 1 else 0) * ((facU e' a).map fun f => 1 + π ^ f.1 * ((f.2.1 : UF σ E) + (f.2.2 : UF σ E) * ζ)).prod := by
      have h_pow : (1 + 4*ζ) ^ (if a.testBit (2*e' + 1) then 1 else 0) = (if a.testBit (2*e' + 1) then 1 + 4*ζ else 1) := by
        by_cases h : a.testBit (2*e' + 1)
        · simp [h]
        · simp [h]
      rw [h_pow, h_facU_map, mul_assoc]


/-- The value `Σ σ(s_p) Y^(n_p)` in `F1` of a list of terms. -/
noncomputable def sumT (L : List (KE × ℕ)) : CF σ E :=
  (L.map fun p => algebraMap Kw (CF σ E) (σ (evK p.1)) * cY σ E ^ p.2).sum

/-- The value of the left terms. -/
theorem sum_lhsUAux (X0 X1 X2 X3 : KE) (a0 : ℕ) (n : ℕ) (P : List (ℤ × ℤ)) :
    QF.mk (CF σ E) (-1) 1 (sumT (σ := σ) (E := E) (lhsUAux X0 X1 X2 X3 a0 n P).1)
        (sumT (σ := σ) (E := E) (lhsUAux X0 X1 X2 X3 a0 n P).2) =
      toU σ E X0 X1 X2 X3 * algebraMap (CF σ E) (UF σ E) (cY σ E) ^ (n + a0) *
        evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) P := by
  have hqf : ∀ u v : CF σ E, QF.mk (CF σ E) (-1) 1 u v =
      algebraMap (CF σ E) (UF σ E) u + algebraMap (CF σ E) (UF σ E) v * cZ σ E := fun u v => by
    rw [qf_mk_eq]; rfl
  have hζ : cZ σ E * cZ σ E = cZ σ E - 1 := cZ_mul_cZ
  have hsum : ∀ (t : KE × ℕ) (L : List (KE × ℕ)), sumT (σ := σ) (E := E) (t :: L) =
      algebraMap Kw (CF σ E) (σ (evK t.1)) * cY σ E ^ t.2 + sumT (σ := σ) (E := E) L := fun t L => by
    simp [sumT]
  induction P generalizing n with
  | nil =>
    rw [hqf]
    simp [lhsUAux, sumT, evZL]
  | cons p P ih =>
    have ih' := ih (n + 1)
    rw [hqf] at ih' ⊢
    simp only [lhsUAux, hsum, evZL]
    rw [toU, hqf, toF_eq, toF_eq] at ih' ⊢
    simp only [evK_mul, evK_int, map_add, map_mul, map_pow, map_intCast, map_neg,
      Int.cast_neg, Int.cast_add] at ih' ⊢
    linear_combination ih' - ((p.2 : UF σ E) * (algebraMap (CF σ E) (UF σ E)
      (algebraMap Kw (CF σ E) (σ (evK X2))) + algebraMap (CF σ E) (UF σ E)
      (algebraMap Kw (CF σ E) (σ (evK X3))) * algebraMap (CF σ E) (UF σ E) (cY σ E)) *
      algebraMap (CF σ E) (UF σ E) (cY σ E) ^ (n + a0)) * hζ

/-- The value of the right terms. -/
theorem sum_rhsU (hW : WPlace σ E) (c : UCert) (hn : c.n < E.alPow.length) :
    QF.mk (CF σ E) (-1) 1 (sumT (σ := σ) (E := E) (rhsU E c).1) (sumT (σ := σ) (E := E) (rhsU E c).2) =
      (algebraMap (CF σ E) (UF σ E) (cY σ E) ^ c.mh *
          QF.mk (CF σ E) (-1) 1 (toF σ E (zkE c.u0) (zkE c.u1)) (toF σ E (zkE c.s0) (zkE c.s1))) ^ 2 +
        algebraMap (CF σ E) (UF σ E) (algebraMap Kw (CF σ E) (σ (zkE E.al) ^ c.n)) *
          QF.mk (CF σ E) (-1) 1 (toF σ E (zkE c.R00) (zkE c.R01)) (toF σ E (zkE c.R10) (zkE c.R11)) := by
  let b := algebraMap (CF σ E) (UF σ E)
  let aM := algebraMap Kw (CF σ E)
  have hqf_mk_eq' : ∀ (u v : CF σ E), QF.mk (CF σ E) (-1) 1 u v = b u + b v * cZ σ E := by
    intro u v
    rw [qf_mk_eq (A := -1) (B := 1) u v]
    rfl
  have htoF_eq' : ∀ (u v : K21), toF σ E u v = aM (σ u) + aM (σ v) * cY σ E := by
    intro u v
    rw [toF_eq u v]
  have hcZ_mul_cZ : cZ σ E * cZ σ E = cZ σ E - 1 := cZ_mul_cZ (σ := σ) (E := E)
  have hok_alP : zkE (E.alP c.n) = zkE E.al ^ c.n := EisData.ok_alP hW.ok c.n hn
  -- rewrite both sides using qf_mk_eq' and toF_eq'
  simp only [hqf_mk_eq', htoF_eq']
  -- unfold rhsU, sumT, and simplify
  simp only [rhsU, sumT, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    evK_mul, evK_sub, evK_add, evK_int, evK_lin]
  -- rewrite zkE (E.alP c.n)
  rw [hok_alP]
  -- push σ, aM, b through operations, but keep b and aM as ring homomorphisms
  simp only [map_mul, map_add, map_sub, map_pow, map_intCast, b, aM]
  -- Now both sides are polynomials in b(aM(σ(zkE l))) and b(cY σ E) and cZ σ E
  -- Use ring to expand both sides and show equality
  ring_nf
  -- Clean up zero terms
  simp only [map_zero, zero_mul, add_zero]
  -- The goal is LHS = RHS. Replace cZ^2 with cZ - 1 using cZ_mul_cZ.
  have h_cZ_sq : cZ σ E ^ 2 = cZ σ E - 1 := by
    rw [sq, cZ_mul_cZ (σ := σ) (E := E)]
  rw [h_cZ_sq]
  ring_nf

theorem lhsUAux_idx (X0 X1 X2 X3 : KE) (a0 : ℕ) (n : ℕ) (P : List (ℤ × ℤ)) :
    ∀ p, p ∈ (lhsUAux X0 X1 X2 X3 a0 n P).1 ∨ p ∈ (lhsUAux X0 X1 X2 X3 a0 n P).2 →
      p.2 ≤ n + P.length + a0 := by
  induction P generalizing n with
  | nil =>
    intro p hp
    simp [lhsUAux] at hp
  | cons q P ih =>
    intro p hp
    simp only [lhsUAux, List.mem_cons, List.length_cons] at hp ⊢
    rcases hp with (h | h | h | h | h) | (h | h | h | h | h)
    · rw [h]; omega
    · rw [h]; omega
    · rw [h]; omega
    · rw [h]; omega
    · have := ih (n + 1) p (Or.inl h); omega
    · rw [h]; omega
    · rw [h]; omega
    · rw [h]; omega
    · rw [h]; omega
    · have := ih (n + 1) p (Or.inr h); omega

theorem rhsU_idx (c : UCert) (h : 2 * c.mh + 2 < E.Ypow.length) :
    ∀ p, p ∈ (rhsU E c).1 ∨ p ∈ (rhsU E c).2 → p.2 < E.Ypow.length := by
  intro p hp
  simp only [rhsU, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;> omega

omit [Fact (∀ r : CF σ E, r ^ 2 ≠ -1 + 1 * r)] in
/-- The sums of two term lists agree when the checks of their coordinates pass. -/
theorem sumT_eq_of_checks (hW : WPlace σ E) {L R : List (KE × ℕ)} {prec : ℕ}
    (hL : ∀ p ∈ L, p.2 < E.Ypow.length) (hR : ∀ p ∈ R, p.2 < E.Ypow.length)
    (h0 : checkK prec (.sub (lcE E 0 L) (lcE E 0 R)) = true)
    (h1 : checkK prec (.sub (lcE E 1 L) (lcE E 1 R)) = true) :
    sumT (σ := σ) (E := E) L = sumT (σ := σ) (E := E) R :=
  (toF_lcE hW _ hL).symm.trans
    ((congrArg₂ (toF σ E) (evK_eq_of_check _ _ _ h0) (evK_eq_of_check _ _ _ h1)).trans (toF_lcE hW _ hR))

theorem norm_toF_eq_one (hW : WPlace σ E) {a c0 : List ℤ} (h : zkE a = 1 + zkE E.al * zkE c0)
    (b : List ℤ) : ‖toF σ E (zkE a) (zkE b)‖ = 1 := by
  have h_norm_a : ‖σ (zkE a)‖ = 1 := by
    rw [h, map_add, map_one, map_mul]
    have h_lt : ‖σ (zkE E.al) * σ (zkE c0)‖ < 1 := by
      calc
        ‖σ (zkE E.al) * σ (zkE c0)‖ = ‖σ (zkE E.al)‖ * ‖σ (zkE c0)‖ := norm_mul _ _
        _ ≤ ‖σ (zkE E.al)‖ * 1 := mul_le_mul_of_nonneg_left (hW.int c0) (norm_nonneg _)
        _ = ‖σ (zkE E.al)‖ := mul_one _
        _ < 1 := hW.unif.norm_lt_one
    have h_ne : ‖(1 : Kw)‖ ≠ ‖σ (zkE E.al) * σ (zkE c0)‖ := by
      rw [norm_one]
      exact (ne_of_lt h_lt).symm
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne, norm_one]
    exact max_eq_left h_lt.le
  have h_norm_prod_lt_one : ‖σ (zkE b)‖ * ‖cY σ E‖ < 1 := by
    have h1 : ‖σ (zkE b)‖ ≤ 1 := hW.int b
    have h2 : ‖cY σ E‖ < 1 := norm_cY_lt_one hW
    calc
      ‖σ (zkE b)‖ * ‖cY σ E‖ ≤ 1 * ‖cY σ E‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖cY σ E‖ := one_mul _
      _ < 1 := h2
  rw [toF, qfE_norm hW.unif hW.norm_A hW.norm_B (σ (zkE a)) (σ (zkE b))]
  rw [h_norm_a]
  exact max_eq_left h_norm_prod_lt_one.le

theorem norm_remU_le_aux_cZ (hW : WPlace σ E) : ‖cZ σ E‖ ≤ 1 := by
  have hcZ : cZ σ E = QF.mk (CF σ E) (-1) 1 0 1 := rfl
  rw [hcZ]
  have hres : ∀ y : CF σ E, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1 :=
    qfE_res hW.unif (WPlace.norm_A hW) (WPlace.norm_B hW) hW.res
  have hA : ‖(-1 : CF σ E) + 1‖ < 1 := by
    rw [show (-1 : CF σ E) + 1 = 0 by ring, norm_zero]; exact zero_lt_one
  have hB : ‖(1 : CF σ E) - 1‖ < 1 := by
    rw [show (1 : CF σ E) - 1 = 0 by ring, norm_zero]; exact zero_lt_one
  have hqf := qfU_norm hres hA hB (0 : CF σ E) (1 : CF σ E)
  rw [hqf]
  simp

theorem norm_remU_le_aux_toU (hW : WPlace σ E) (X0 X1 X2 X3 : KE) :
    ‖toU σ E X0 X1 X2 X3‖ ≤ 1 := by
  have hres : ∀ y : CF σ E, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1 :=
    qfE_res hW.unif (WPlace.norm_A hW) (WPlace.norm_B hW) hW.res
  have hA : ‖(-1 : CF σ E) + 1‖ < 1 := by
    rw [show (-1 : CF σ E) + 1 = 0 by ring, norm_zero]; exact zero_lt_one
  have hB : ‖(1 : CF σ E) - 1‖ < 1 := by
    rw [show (1 : CF σ E) - 1 = 0 by ring, norm_zero]; exact zero_lt_one
  have hqf := qfU_norm hres hA hB (toF σ E (evK X0) (evK X1)) (toF σ E (evK X2) (evK X3))
  rw [toU, hqf]
  exact max_le (norm_toF_le_one hW X0 X1) (norm_toF_le_one hW X2 X3)

theorem norm_remU_le_aux_QF_mk (hW : WPlace σ E) (u v : CF σ E)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖QF.mk (CF σ E) (-1) 1 u v‖ ≤ 1 := by
  have hres : ∀ y : CF σ E, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1 :=
    qfE_res hW.unif (WPlace.norm_A hW) (WPlace.norm_B hW) hW.res
  have hA : ‖(-1 : CF σ E) + 1‖ < 1 := by
    rw [show (-1 : CF σ E) + 1 = 0 by ring, norm_zero]; exact zero_lt_one
  have hB : ‖(1 : CF σ E) - 1‖ < 1 := by
    rw [show (1 : CF σ E) - 1 = 0 by ring, norm_zero]; exact zero_lt_one
  have hqf := qfU_norm hres hA hB u v
  rw [hqf]
  exact max_le hu hv

theorem norm_remU_le_aux_BaU (hW : WPlace σ E) (a : ℕ) :
    ‖BaU σ E a‖ ≤ 1 := by
  rw [BaU_eq a]
  rw [norm_mul]
  have hcY : ‖cY σ E‖ ≤ 1 := (norm_cY_lt_one hW).le
  have hcY_nonneg : 0 ≤ ‖cY σ E‖ := norm_nonneg _
  have hcY_le_one : ‖cY σ E‖ ≤ 1 := hcY
  have hcY_pow : ‖algebraMap (CF σ E) (UF σ E) (cY σ E) ^ (if a.testBit 0 then 1 else 0)‖ ≤ 1 := by
    rw [norm_pow, QF.norm_algebraMap (K := CF σ E) (a := -1) (b := 1)]
    exact pow_le_one₀ hcY_nonneg hcY_le_one
  have h_evZL : ‖evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) (dpU (facU (2 * E.e) a))‖ ≤ 1 := by
    apply norm_evZL_le_one
    · rw [QF.norm_algebraMap (K := CF σ E) (a := -1) (b := 1)]; exact hcY
    · exact norm_remU_le_aux_cZ hW
  simpa [mul_one] using mul_le_mul hcY_pow h_evZL (norm_nonneg _) (by positivity)

theorem norm_remU_le [ProperSpace Kw] (hW : WPlace σ E) {D : ℕ} {X0 X1 X2 X3 : KE} {c : UCert}
    (hD : 2 * c.n ≤ D) (x : UF σ E) (hx : ‖x - toU σ E X0 X1 X2 X3‖ ≤ ‖σ (zkE E.al)‖ ^ c.n)
    (a0 : ℕ) (P : List (ℤ × ℤ)) :
    ‖(x - toU σ E X0 X1 X2 X3) * BaU σ E c.a +
        toU σ E X0 X1 X2 X3 * algebraMap (CF σ E) (UF σ E) (cY σ E) ^ a0 *
          (algebraMap (CF σ E) (UF σ E) (cY σ E) ^ D *
            evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) P) +
        algebraMap (CF σ E) (UF σ E) (algebraMap Kw (CF σ E) (σ (zkE E.al) ^ c.n)) *
          QF.mk (CF σ E) (-1) 1 (toF σ E (zkE c.R00) (zkE c.R01)) (toF σ E (zkE c.R10) (zkE c.R11))‖ ≤
      ‖cY σ E‖ ^ (2 * c.n) := by
  have hcY_nonneg : 0 ≤ ‖cY σ E‖ := norm_nonneg _
  have hcY_le_one : ‖cY σ E‖ ≤ 1 := (norm_cY_lt_one hW).le
  have hcY_pow_a0_le_one : ‖cY σ E‖ ^ a0 ≤ 1 := pow_le_one₀ hcY_nonneg hcY_le_one
  have hcY_pow_D_le : ‖cY σ E‖ ^ D ≤ ‖cY σ E‖ ^ (2 * c.n) :=
    pow_le_pow_of_le_one hcY_nonneg hcY_le_one hD
  have h_alg_cY : ‖algebraMap (CF σ E) (UF σ E) (cY σ E)‖ = ‖cY σ E‖ :=
    QF.norm_algebraMap (K := CF σ E) (a := -1) (b := 1) (cY σ E)
  have h_sigma_eq : ‖σ (zkE E.al)‖ ^ c.n = ‖cY σ E‖ ^ (2 * c.n) := by
    rw [← norm_tC hW, norm_tC_eq hW]
    rw [← pow_mul]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
  · -- Goal 1: ‖(x - toU) * BaU‖ ≤ ‖cY‖ ^ (2 * c.n)
    rw [norm_mul]
    refine (mul_le_mul hx (norm_remU_le_aux_BaU hW c.a) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)).trans ?_
    rw [mul_one]
    rw [h_sigma_eq]
  · -- Goal 2: ‖toU * algebraMap(cY)^a0 * (algebraMap(cY)^D * evZL)‖ ≤ ‖cY‖ ^ (2 * c.n)
    rw [norm_mul, norm_mul, norm_mul]
    rw [norm_pow, norm_pow, h_alg_cY]
    have h_toU : ‖toU σ E X0 X1 X2 X3‖ ≤ 1 := norm_remU_le_aux_toU hW X0 X1 X2 X3
    have h_evZL : ‖evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) P‖ ≤ 1 :=
      norm_evZL_le_one (by rw [h_alg_cY]; exact hcY_le_one) (norm_remU_le_aux_cZ hW) P
    have h_prod : ‖toU σ E X0 X1 X2 X3‖ * (‖cY σ E‖ ^ a0 * (‖cY σ E‖ ^ D *
        ‖evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) P‖)) ≤ ‖cY σ E‖ ^ D := by
      have h_inner : ‖cY σ E‖ ^ a0 * (‖cY σ E‖ ^ D *
          ‖evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) P‖) ≤
          1 * (‖cY σ E‖ ^ D * 1) := by
        have h₂ : ‖cY σ E‖ ^ D * ‖evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) P‖ ≤
            ‖cY σ E‖ ^ D * 1 :=
          mul_le_mul_of_nonneg_left h_evZL (pow_nonneg hcY_nonneg _)
        refine mul_le_mul hcY_pow_a0_le_one h₂
          (mul_nonneg (pow_nonneg hcY_nonneg _) (norm_nonneg _)) zero_le_one
      have h_outer : ‖toU σ E X0 X1 X2 X3‖ * (‖cY σ E‖ ^ a0 * (‖cY σ E‖ ^ D *
          ‖evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) P‖)) ≤
          1 * (1 * (‖cY σ E‖ ^ D * 1)) := by
        refine mul_le_mul h_toU h_inner
          (mul_nonneg (pow_nonneg hcY_nonneg _) (mul_nonneg (pow_nonneg hcY_nonneg _) (norm_nonneg _))) zero_le_one
      simpa [mul_one, one_mul] using h_outer
    simpa [mul_assoc] using h_prod.trans hcY_pow_D_le
  · -- Goal 3: ‖algebraMap (σ(zkE E.al)^c.n) * QF.mk ...‖ ≤ ‖cY‖ ^ (2 * c.n)
    rw [norm_mul]
    rw [QF.norm_algebraMap (K := CF σ E) (a := -1) (b := 1)]
    rw [QF.norm_algebraMap (K := Kw) (a := σ (zkE E.A)) (b := σ (zkE E.B))]
    rw [norm_pow]
    have h_QF_mk : ‖QF.mk (CF σ E) (-1) 1 (toF σ E (zkE c.R00) (zkE c.R01))
        (toF σ E (zkE c.R10) (zkE c.R11))‖ ≤ 1 :=
      norm_remU_le_aux_QF_mk hW (toF σ E (zkE c.R00) (zkE c.R01)) (toF σ E (zkE c.R10) (zkE c.R11))
        (norm_toF_le_one hW (.lin c.R00) (.lin c.R01)) (norm_toF_le_one hW (.lin c.R10) (.lin c.R11))
    have h_sigma_pow : ‖σ (zkE E.al)‖ ^ c.n ≤ ‖cY σ E‖ ^ (2 * c.n) := by
      rw [h_sigma_eq]
    refine (mul_le_mul h_sigma_pow h_QF_mk (norm_nonneg _) (by positivity)).trans ?_
    rw [mul_one]


/-- **Square certificate at `F2`.** -/
theorem certOKU_isSquare [ProperSpace Kw] (hW : WPlace σ E) {D : ℕ} {X0 X1 X2 X3 : KE} {c : UCert}
    (hc : certOKU E D X0 X1 X2 X3 c = true) (x : UF σ E)
    (hx : ‖x - toU σ E X0 X1 X2 X3‖ ≤ ‖σ (zkE E.al)‖ ^ c.n) :
    IsSquare (x * BaU σ E c.a) := by
  simp only [certOKU, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hD⟩, hnl⟩, hDl⟩, hmhl⟩, hu⟩, h00⟩, h01⟩, h10⟩, h11⟩ := hc
  set a0 := if c.a.testBit 0 then 1 else 0 with ha0
  set P := dpU (facU (2 * E.e) c.a) with hP
  have ha01 : a0 ≤ 1 := by rw [ha0]; split_ifs <;> omega
  -- the identity of the checks
  have hLi := lhsUAux_idx X0 X1 X2 X3 a0 0 (P.take D)
  have hlen : (P.take D).length ≤ D := List.length_take_le _ _
  have hL1 : ∀ p ∈ (lhsU E D X0 X1 X2 X3 c.a).1, p.2 < E.Ypow.length := fun p hp => by
    have := hLi p (Or.inl hp); omega
  have hL2 : ∀ p ∈ (lhsU E D X0 X1 X2 X3 c.a).2, p.2 < E.Ypow.length := fun p hp => by
    have := hLi p (Or.inr hp); omega
  have hR1 : ∀ p ∈ (rhsU E c).1, p.2 < E.Ypow.length := fun p hp => rhsU_idx c hmhl p (Or.inl hp)
  have hR2 : ∀ p ∈ (rhsU E c).2, p.2 < E.Ypow.length := fun p hp => rhsU_idx c hmhl p (Or.inr hp)
  have hid := congrArg₂ (QF.mk (CF σ E) (-1) 1) (sumT_eq_of_checks hW hL1 hR1 h00 h01)
    (sumT_eq_of_checks hW hL2 hR2 h10 h11)
  rw [lhsU, sum_lhsUAux, sum_rhsU hW c hnl, zero_add] at hid
  -- the basis product
  have hBa : BaU σ E c.a = algebraMap (CF σ E) (UF σ E) (cY σ E) ^ a0 *
      (evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) (P.take D) +
        algebraMap (CF σ E) (UF σ E) (cY σ E) ^ D *
          evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) (P.drop D)) := by
    rw [BaU_eq, ← evZL_take_drop]
  -- the remainder
  set t := (x - toU σ E X0 X1 X2 X3) * BaU σ E c.a +
      toU σ E X0 X1 X2 X3 * algebraMap (CF σ E) (UF σ E) (cY σ E) ^ a0 *
        (algebraMap (CF σ E) (UF σ E) (cY σ E) ^ D *
          evZL (algebraMap (CF σ E) (UF σ E) (cY σ E)) (cZ σ E) (P.drop D)) +
      algebraMap (CF σ E) (UF σ E) (algebraMap Kw (CF σ E) (σ (zkE E.al) ^ c.n)) *
        QF.mk (CF σ E) (-1) 1 (toF σ E (zkE c.R00) (zkE c.R01)) (toF σ E (zkE c.R10) (zkE c.R11))
    with htdef
  have ht : ‖t‖ ≤ ‖cY σ E‖ ^ (2 * c.n) := norm_remU_le hW hD x hx a0 (P.drop D)
  have hxB : x * BaU σ E c.a =
      (algebraMap (CF σ E) (UF σ E) (cY σ E) ^ c.mh *
        QF.mk (CF σ E) (-1) 1 (toF σ E (zkE c.u0) (zkE c.u1)) (toF σ E (zkE c.s0) (zkE c.s1))) ^ 2 +
      algebraMap (CF σ E) (UF σ E) (cY σ E ^ (2 * c.n) * 0) +
      algebraMap (CF σ E) (UF σ E) (cY σ E ^ (2 * c.n) * 0) * QF.mk (CF σ E) (-1) 1 0 1 + t := by
    rw [htdef, hBa]
    simp only [mul_zero, map_zero, zero_mul, add_zero]
    linear_combination hid
  -- the unit
  have hunit : ‖toF σ E (zkE c.u0) (zkE c.u1)‖ = 1 ∨ ‖toF σ E (zkE c.s0) (zkE c.s1)‖ = 1 := by
    have e := evK_eq_of_check _ _ _ hu
    simp only [evK_lin, evK_add, evK_mul, evK_int, Int.cast_one] at e
    cases hub : c.ub
    · rw [hub] at e; exact Or.inl (norm_toF_eq_one hW e _)
    · rw [hub] at e; exact Or.inr (norm_toF_eq_one hW e _)
  exact isSquare_of_unram_cert (K := CF σ E) (A := -1) (B := 1) (π := cY σ E)
    (qfE_normUnif hW.unif hW.norm_A hW.norm_B) (qfE_res hW.unif hW.norm_A hW.norm_B hW.res)
    (by simp) (by simp) (qfE_two hW.unif hW.norm_A hW.norm_B hW.two)
    (norm_toF_le_one hW (.lin c.u0) (.lin c.u1)) (norm_toF_le_one hW (.lin c.s0) (.lin c.s1)) hunit
    (by simp) (by simp) (by omega) (by omega) ht hxB


/-! ## `N84 →+* F2` -/

section ModelV

variable {M : LModel}

theorem exists_sV [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtV}
    (hS : S.ok E M = true) :
    ∃ s : CF σ E, 3 * s ^ 2 = -iL σ E M hM (4 * eN) ∧
      ‖s - toF σ E (zkE S.s00) (zkE S.s01)‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  simp only [SqrtV.ok, Bool.and_eq_true] at hS
  rcases hS with ⟨h_left, he_pos⟩
  rcases h_left with ⟨h_left', hI1⟩
  rcases h_left' with ⟨h_left'', hI0⟩
  rcases h_left'' with ⟨h_left''', hs01⟩
  rcases h_left''' with ⟨h_left'''', hs00⟩
  rcases h_left'''' with ⟨h_left''''', hn⟩
  rcases h_left''''' with ⟨hnl, hjl⟩
  have hnl_lt : S.n < E.alPow.length := by
    simpa [decide_eq_true_eq] using hnl
  have hjl_lt : S.j + 1 < E.alPow.length := by
    simpa [decide_eq_true_eq] using hjl
  have hjl_lt' : S.j < E.alPow.length := by omega
  have hn_lt : 2 * E.e + 2 * S.j < S.n := by
    simpa [decide_eq_true_eq] using hn
  have he_pos' : 0 < E.e := by
    simpa [decide_eq_true_eq] using he_pos
  have e00 : zkE S.s00 = zkE E.al ^ S.j * (1 + zkE E.al * zkE S.d0) := by
    have := evK_eq_of_check _ _ _ hs00
    simp only [evK_lin, evK_mul, evK_add, evK_int, Int.cast_one] at this
    rw [this, EisData.ok_alP hW.ok _ hjl_lt']
  have e01 : zkE S.s01 = zkE E.al ^ S.j * zkE S.d1 := by
    have := evK_eq_of_check _ _ _ hs01
    simp only [evK_lin, evK_mul] at this
    rw [this, EisData.ok_alP hW.ok _ hjl_lt']
  have e0 := evK_eq_of_check _ _ _ hI0
  have e1 := evK_eq_of_check _ _ _ hI1
  simp only [evK_lin, evK_mul, evK_add, evK_int, Int.cast_ofNat,
    EisData.ok_alP hW.ok _ hnl_lt] at e0 e1
  set π := σ (zkE E.al) with hπdef
  have hπ1 := hW.unif.norm_lt_one
  have hπ0 : 0 < ‖π‖ := norm_pos_iff.mpr hW.unif.ne_zero
  set s0 := toF σ E (zkE S.s00) (zkE S.s01) with hs0
  set z := -(iL σ E M hM (4 * eN)) / 3 with hz
  have hzF : iL σ E M hM (4 * eN) = toF σ E (2 * zkE eaL + 2 * zkE ebL * zkE M.y) (2 * zkE ebL * zkE M.c) :=
    iL_four_eN hM
  have h3norm : ‖(3 : CF σ E)‖ = 1 := by
    have h2 : ‖(2 : CF σ E)‖ < 1 := by
      rw [show (2 : CF σ E) = algebraMap Kw (CF σ E) 2 from (map_ofNat _ 2).symm, QF.norm_algebraMap,
        hW.two]
      exact pow_lt_one₀ hπ0.le hπ1 he_pos'.ne'
    have h1 : ‖(1 : CF σ E)‖ = 1 := by simp
    have hne : ‖(1 : CF σ E)‖ ≠ ‖(2 : CF σ E)‖ := by
      rw [h1]
      exact (ne_of_lt h2).symm
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    simpa [h1, h2.le, show (3 : CF σ E) = (1 : CF σ E) + (2 : CF σ E) by norm_num] using this
  have hz1 : ‖z‖ ≤ 1 := by
    rw [hz, norm_div, norm_neg, h3norm, div_one]
    rw [hzF]
    have := norm_toF_le_one hW (.add (.mul (.int 2) (.lin eaL)) (.mul (.mul (.int 2) (.lin ebL)) (.lin M.y)))
      (.mul (.mul (.int 2) (.lin ebL)) (.lin M.c))
    simp only [evK_lin, evK_mul, evK_add, evK_int, Int.cast_ofNat] at this
    exact this
  have hs0n : ‖s0‖ = ‖π‖ ^ S.j := by
    rw [hs0, e00, e01, toF_smul, norm_mul, QF.norm_algebraMap, norm_toF_unit hW, map_pow, norm_pow,
      mul_one]
  have hs01 : ‖s0‖ ≤ 1 := by rw [hs0n]; exact pow_le_one₀ hπ0.le hπ1.le
  have h2F : ‖(2 : CF σ E)‖ = ‖π‖ ^ E.e := by
    rw [show (2 : CF σ E) = algebraMap Kw (CF σ E) 2 from (map_ofNat _ 2).symm, QF.norm_algebraMap,
      hW.two]
  have h2s0 : ‖2 * s0‖ = ‖π‖ ^ (E.e + S.j) := by rw [norm_mul, h2F, hs0n, pow_add]
  have hdiff : s0 ^ 2 - z = (algebraMap Kw (CF σ E) (π ^ S.n) * toF σ E (zkE S.R0) (zkE S.R1)) / 3 := by
    rw [hz, hzF]
    have hsum : 3 * s0 ^ 2 + toF σ E (2 * zkE eaL + 2 * zkE ebL * zkE M.y) (2 * zkE ebL * zkE M.c) =
        algebraMap Kw (CF σ E) (π ^ S.n) * toF σ E (zkE S.R0) (zkE S.R1) := by
      have h3toF (u v : K21) : toF σ E (3 * u) (3 * v) = 3 * toF σ E u v := by
        rw [toF_smul]
        simp [map_ofNat]
      rw [sq, hs0, toF_mul, ← h3toF]
      have hsub' : ∀ u v u' v' : K21, toF σ E u v + toF σ E u' v' = toF σ E (u + u') (v + v') := by
        intro u v u' v'; simp only [toF_eq, map_add]; ring
      rw [hsub']
      rw [← map_pow, ← toF_smul]
      congr 1
      · linear_combination e0
      · linear_combination e1
    have h3 : (3 : CF σ E) ≠ 0 := by
      intro h
      rw [h] at h3norm
      simp at h3norm
    calc
      s0 ^ 2 - (-(toF σ E (2 * zkE eaL + 2 * zkE ebL * zkE M.y) (2 * zkE ebL * zkE M.c)) / 3)
          = (3 * s0 ^ 2 + toF σ E (2 * zkE eaL + 2 * zkE ebL * zkE M.y) (2 * zkE ebL * zkE M.c)) / 3 := by
        field_simp [h3]
        ring
      _ = (algebraMap Kw (CF σ E) (π ^ S.n) * toF σ E (zkE S.R0) (zkE S.R1)) / 3 := by rw [hsum]
  have hdn : ‖s0 ^ 2 - z‖ ≤ ‖π‖ ^ S.n := by
    rw [hdiff, norm_div, h3norm, div_one, norm_mul, QF.norm_algebraMap, norm_pow]
    have := norm_toF_le_one hW (.lin S.R0) (.lin S.R1)
    simp only [evK_lin] at this
    exact mul_le_of_le_one_right (by positivity) this
  have hlt : ‖s0 ^ 2 - z‖ < ‖2 * s0‖ ^ 2 := by
    rw [h2s0, ← pow_mul]
    exact lt_of_le_of_lt hdn (pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 (by omega))
  obtain ⟨s, hs, hsn⟩ := exists_sqrt_near hz1 hs01 hlt
  refine ⟨s, ?_, hsn.trans ?_⟩
  · rw [hs, hz]
    have h3 : (3 : CF σ E) ≠ 0 := by
      intro h
      rw [h] at h3norm
      simp at h3norm
    field_simp [h3]
  · rw [h2s0, div_le_iff₀ (pow_pos hπ0 _), ← pow_add]
    have hle : E.e + S.j ≤ S.n := by
      have hsum : E.e + S.j ≤ 2 * E.e + 2 * S.j := by omega
      exact Nat.le_of_lt (lt_of_le_of_lt hsum hn_lt)
    calc ‖s0 ^ 2 - z‖ ≤ ‖π‖ ^ S.n := hdn
      _ = ‖π‖ ^ (S.n - E.e - S.j + (E.e + S.j)) := by
        congr 1
        rw [Nat.sub_sub, Nat.sub_add_cancel hle]

variable (σ E M)

/-- The square root `ρ` of `-iL (4 eN) / 3`. -/
noncomputable def sV [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) (S : SqrtV)
    (hS : S.ok E M = true) : CF σ E :=
  (exists_sV hW hM hS).choose

variable {σ E M}

theorem sV_sq [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtV}
    (hS : S.ok E M = true) : 3 * sV σ E M hW hM S hS ^ 2 = -iL σ E M hM (4 * eN) :=
  (exists_sV hW hM hS).choose_spec.1

theorem sV_near [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtV}
    (hS : S.ok E M = true) :
    ‖sV σ E M hW hM S hS - toF σ E (zkE S.s00) (zkE S.s01)‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) :=
  (exists_sV hW hM hS).choose_spec.2

/-- `((2 ζ - 1) ρ / 2)² = iL eN`. -/
theorem uNv_sq [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtV}
    (hS : S.ok E M = true) :
    ((2 * cZ σ E - 1) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) / 2) *
        ((2 * cZ σ E - 1) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) / 2) =
      ((algebraMap (CF σ E) (UF σ E)).comp (iL σ E M hM)) eN +
        ((algebraMap (CF σ E) (UF σ E)).comp (iL σ E M hM)) 0 *
          ((2 * cZ σ E - 1) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) / 2) := by
  have hzero : ((algebraMap (CF σ E) (UF σ E)).comp (iL σ E M hM)) 0 = 0 := by simp
  rw [hzero, zero_mul, add_zero]
  have hcZ_sq : cZ σ E * cZ σ E = cZ σ E - 1 := cZ_mul_cZ
  have h2cZ_sub_one_sq : (2 * cZ σ E - 1) ^ 2 = -3 := by
    calc
      (2 * cZ σ E - 1) ^ 2 = (2 * cZ σ E - 1) * (2 * cZ σ E - 1) := by ring
      _ = 4 * (cZ σ E * cZ σ E) - 4 * cZ σ E + 1 := by ring
      _ = 4 * (cZ σ E - 1) - 4 * cZ σ E + 1 := by rw [hcZ_sq]
      _ = -3 := by ring
  have hkey : iL σ E M hM eN = -3 * sV σ E M hW hM S hS ^ 2 / 4 := by
    have h := sV_sq hW hM hS
    have h4 : iL σ E M hM (4 * eN) = 4 * iL σ E M hM eN := by rw [map_mul, map_ofNat]
    rw [h4] at h
    have hneg : 4 * iL σ E M hM eN = -3 * sV σ E M hW hM S hS ^ 2 := by
      calc
        4 * iL σ E M hM eN = -(-(4 * iL σ E M hM eN)) := by ring
        _ = -(3 * sV σ E M hW hM S hS ^ 2) := by rw [← h]
        _ = -3 * sV σ E M hW hM S hS ^ 2 := by ring
    have h4ne : (4 : CF σ E) ≠ 0 := by
      have h2ne : (2 : CF σ E) ≠ 0 := two_ne_zero_CF hW
      intro h4
      have hsq : (2 : CF σ E) * (2 : CF σ E) = 0 := by
        calc
          (2 : CF σ E) * (2 : CF σ E) = (4 : CF σ E) := by norm_num
          _ = 0 := h4
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hsq with h | h
      · exact h2ne h
      · exact h2ne h
    apply (eq_div_iff_mul_eq h4ne).mpr
    rw [mul_comm]
    exact hneg
  calc
    ((2 * cZ σ E - 1) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) / 2) *
        ((2 * cZ σ E - 1) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) / 2)
        = ((2 * cZ σ E - 1) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) / 2) ^ 2 := by ring
    _ = ((2 * cZ σ E - 1) ^ 2 * (algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS)) ^ 2) / 4 := by
      field_simp
      ring
    _ = ((-3) * (algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS)) ^ 2) / 4 := by rw [h2cZ_sub_one_sq]
    _ = algebraMap (CF σ E) (UF σ E) ((-3) * sV σ E M hW hM S hS ^ 2 / 4) := by
      simpa using (calc
        algebraMap (CF σ E) (UF σ E) ((-3) * sV σ E M hW hM S hS ^ 2 / 4)
            = algebraMap (CF σ E) (UF σ E) ((-3) * sV σ E M hW hM S hS ^ 2) / algebraMap (CF σ E) (UF σ E) 4 := by rw [map_div₀ (algebraMap (CF σ E) (UF σ E))]
        _ = (algebraMap (CF σ E) (UF σ E) (-3)) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS ^ 2) / algebraMap (CF σ E) (UF σ E) 4 := by rw [map_mul (algebraMap (CF σ E) (UF σ E))]
        _ = algebraMap (CF σ E) (UF σ E) (-3) * (algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS)) ^ 2 / algebraMap (CF σ E) (UF σ E) 4 := by rw [map_pow (algebraMap (CF σ E) (UF σ E))]
        _ = (-3) * (algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS)) ^ 2 / 4 := by
          have h3 : algebraMap (CF σ E) (UF σ E) (3 : CF σ E) = (3 : UF σ E) :=
            map_natCast (algebraMap (CF σ E) (UF σ E)) 3
          have h4 : algebraMap (CF σ E) (UF σ E) (4 : CF σ E) = (4 : UF σ E) :=
            map_natCast (algebraMap (CF σ E) (UF σ E)) 4
          have hneg3 : algebraMap (CF σ E) (UF σ E) (-3) = (-3 : UF σ E) := by
            rw [map_neg (algebraMap (CF σ E) (UF σ E)), h3]
          rw [hneg3, h4]
      ).symm
    _ = algebraMap (CF σ E) (UF σ E) (iL σ E M hM eN) := by rw [hkey]
    _ = ((algebraMap (CF σ E) (UF σ E)).comp (iL σ E M hM)) eN := rfl

variable (σ E M)

/-- **`N84 →+* F2`**, `ω_N ↦ (2 ζ - 1) ρ / 2`. -/
noncomputable def iNv [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) (S : SqrtV)
    (hS : S.ok E M = true) : N84 →+* UF σ E :=
  qaLift ((algebraMap (CF σ E) (UF σ E)).comp (iL σ E M hM))
    ((2 * cZ σ E - 1) * algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) / 2) (uNv_sq hW hM hS)

variable {σ E M}

theorem iNv_algebraMap [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtV}
    (hS : S.ok E M = true) (x : K21) :
    iNv σ E M hW hM S hS (algebraMap K21 N84 x) =
      algebraMap (CF σ E) (UF σ E) (algebraMap Kw (CF σ E) (σ x)) := by
  have h : algebraMap K21 N84 x = algebraMap L42 N84 (algebraMap K21 L42 x) := rfl
  rw [h]
  unfold iNv
  rw [qaLift_algebraMap]
  simp
  rw [iL_algebraMap hM x]

/-- `‖2ζ - 1‖ ≤ 1` for the root `ζ = cZ` of `ζ² = ζ - 1`. -/
theorem norm_two_cZ_sub_one_le_one [ProperSpace Kw] (_hW : WPlace σ E) : ‖(2 : UF σ E) * cZ σ E - 1‖ ≤ 1 := by
  have h_poly : cZ σ E * cZ σ E = cZ σ E - 1 := cZ_mul_cZ (σ := σ) (E := E)
  have h_norm_cZ_le_one : ‖cZ σ E‖ ≤ 1 := by
    by_contra! h
    have h_one_lt : 1 < ‖cZ σ E‖ := by linarith
    have h_sq_gt : ‖cZ σ E‖ < ‖cZ σ E * cZ σ E‖ := by
      rw [norm_mul]
      nlinarith
    have h_sub_le : ‖cZ σ E - 1‖ ≤ max (‖cZ σ E‖) (‖(1 : UF σ E)‖) := by
      have h_add := IsUltrametricDist.norm_add_le_max (cZ σ E) (-1)
      rw [sub_eq_add_neg]
      simpa [norm_neg, norm_one] using h_add
    have h_max_eq : max (‖cZ σ E‖) (‖(1 : UF σ E)‖) = ‖cZ σ E‖ := by
      rw [norm_one, max_eq_left (by linarith)]
    rw [h_max_eq] at h_sub_le
    rw [← h_poly] at h_sub_le
    linarith
  have h_expr : (2 : UF σ E) * cZ σ E - 1 = cZ σ E + cZ σ E * cZ σ E := by
    rw [h_poly]
    ring
  rw [h_expr]
  have h_add := IsUltrametricDist.norm_add_le_max (cZ σ E) (cZ σ E * cZ σ E)
  have h_sq_le : ‖cZ σ E * cZ σ E‖ ≤ 1 := by
    rw [norm_mul]
    have h_mul := mul_le_mul h_norm_cZ_le_one h_norm_cZ_le_one (norm_nonneg _) (by positivity)
    simpa [mul_one] using h_mul
  have h_max_le_one : max (‖cZ σ E‖) (‖cZ σ E * cZ σ E‖) ≤ 1 :=
    max_le h_norm_cZ_le_one h_sq_le
  have h_le_one : ‖cZ σ E + cZ σ E * cZ σ E‖ ≤ 1 := by
    linarith
  linarith

/-- The approximation `XNv` of `iNv (evN t)`. -/
theorem norm_iNv_evN_sub [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtV}
    (hS : S.ok E M = true) (t : NC) :
    ‖iNv σ E M hW hM S hS (evN t) - toU σ E (XNv E M S t).1 (XNv E M S t).2.1 (XNv E M S t).2.2.1
        (XNv E M S t).2.2.2‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  set s0 := toF σ E (zkE S.s00) (zkE S.s01)
  have hN : iNv σ E M hW hM S hS (evN t) =
      algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.1)) +
      algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2)) * ((2 : UF σ E) * cZ σ E - 1) *
        algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) := by
    rw [iNv, qaLift_apply]
    have him : (evN t).im = (2 : L42) * evL t.2 := by
      ext <;> simp [evN, evL, two_mul, mul_comm, add_comm]
    rw [show (evN t).re = evL t.1 from rfl, him, map_mul, map_ofNat]
    simp only [RingHom.comp_apply]
    have h2 : (2 : UF σ E) ≠ 0 :=
      (map_ne_zero (algebraMap (CF σ E) (UF σ E))).mpr (two_ne_zero_CF hW)
    field_simp [h2]
  have hX : toU σ E (XNv E M S t).1 (XNv E M S t).2.1 (XNv E M S t).2.2.1 (XNv E M S t).2.2.2 =
      algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.1)) +
      algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2)) * ((2 : UF σ E) * cZ σ E - 1) *
        algebraMap (CF σ E) (UF σ E) s0 := by
    rw [toU, XNv]
    simp only [evK_add, evK_sub, evK_mul, evK_lin, evK_int]
    rw [iL_evL hM t.1, iL_evL hM t.2]
    have hs0 : s0 = toF σ E (zkE S.s00) (zkE S.s01) := rfl
    rw [mul_right_comm (algebraMap (CF σ E) (UF σ E) (toF σ E (evK (X0L M t.2)) (evK (X1L M t.2))))
      ((2 : UF σ E) * cZ σ E - 1), ← map_mul, hs0, toF_mul, qf_mk_eq]
    simp only [cZ, toF_eq, map_sub, map_add, map_mul, map_intCast]
    push_cast
    ring
  rw [hN, hX]
  have hL : ‖algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2))‖ ≤ 1 := by
    rw [QF.norm_algebraMap, iL_evL hM]
    exact norm_toF_le_one hW (X0L M t.2) (X1L M t.2)
  have hcZ : ‖(2 : UF σ E) * cZ σ E - 1‖ ≤ 1 :=
    norm_two_cZ_sub_one_le_one hW
  have hdiff : (algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.1)) +
      algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2)) * ((2 : UF σ E) * cZ σ E - 1) *
        algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS)) -
      (algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.1)) +
      algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2)) * ((2 : UF σ E) * cZ σ E - 1) *
        algebraMap (CF σ E) (UF σ E) s0) =
      algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2)) * ((2 : UF σ E) * cZ σ E - 1) *
        (algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) -
        algebraMap (CF σ E) (UF σ E) s0) := by
    ring
  rw [hdiff]
  calc
    ‖algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2)) * ((2 : UF σ E) * cZ σ E - 1) *
        (algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) -
        algebraMap (CF σ E) (UF σ E) s0)‖
        = ‖algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2))‖ * ‖(2 : UF σ E) * cZ σ E - 1‖ *
          ‖algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) -
          algebraMap (CF σ E) (UF σ E) s0‖ := by
      simp [norm_mul]
    _ ≤ 1 * 1 * ‖algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) -
        algebraMap (CF σ E) (UF σ E) s0‖ := by
      have hposA : 0 ≤ ‖algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2))‖ := by
        apply norm_nonneg
      have hposB : 0 ≤ ‖(2 : UF σ E) * cZ σ E - 1‖ := by
        apply norm_nonneg
      have hprod : ‖algebraMap (CF σ E) (UF σ E) (iL σ E M hM (evL t.2))‖ *
          ‖(2 : UF σ E) * cZ σ E - 1‖ ≤ 1 * 1 := by
        nlinarith
      have hposCD : 0 ≤ ‖algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) -
          algebraMap (CF σ E) (UF σ E) s0‖ := by
        apply norm_nonneg
      nlinarith
    _ = ‖algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS) -
        algebraMap (CF σ E) (UF σ E) s0‖ := by ring
    _ = ‖algebraMap (CF σ E) (UF σ E) (sV σ E M hW hM S hS - s0)‖ := by rw [map_sub]
    _ = ‖sV σ E M hW hM S hS - s0‖ := by rw [QF.norm_algebraMap]
    _ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := sV_near hW hM hS

end ModelV

end Place

end FurioLombardo.Discharge.SelmerBasis
