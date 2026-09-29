import Mathlib
import FurioLombardo.Discharge.M3a.ConcreteRoute
import FurioLombardo.Discharge.M3a.LocalLead
import FurioLombardo.Discharge.M3a.LocalFacts
import FurioLombardo.Discharge.M4Cert.Bridge
import FurioLombardo.Discharge.M3a.K1Concrete

/-!
# The concrete route at the completion `K_v` of lane M4's certificate discharge

`σ = FurioLombardo.Discharge.M4Cert.σ : K21 → K_v`. With the twist predicate
`M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k)` and the disc and parameter maps `liftDisc`,
`liftPar` of the lifts, lane M4's certificate discharge proves `HExcl` (`hExcl_T0_Mmat`,
`hExcl_T1_Mmat`), `TailGood` (`tailGood_T0_Mmat`, `tailGood_T1_Mmat`) and the first two conjuncts
of `LiftDisc` (`liftTwist_Mmat`); the three local facts at `v` are `localFacts_Kv` (LocalLead.lean,
LocalFacts.lean). The rest of `M4Rest` is the bundle `M4RestKv`: the balls, the centres, the analytic
branch, `HKnown`, `HSelLoc` and the logarithm part `LogBranch` of `LiftDisc`. Its weak form `M4RestKvW`
(M4Box/ChainM3a.lean) is proved for both twists in M4Box/Final.lean (`m4RestKvW_0`, `m4RestKvW_1`).

* `Bruin.T0.twistRoute_Kv`, `Bruin.T1.twistRoute_Kv`: `TwistRoute` of each twist from the Selmer
  data, the local independence, `LogChartFin lam` and `M4RestKv`, for any Abel-Prym map `φ`; (K1)
  is the theorem `Bruin.poonenSchaefer_fRev` (K1Concrete.lean), no longer an input;
* `Bruin.onlyFourPoints_Kv`: the frozen statement from M1's descent and `TwistInputsKv` for the two
  twists.
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.Analytic (LogChartFin satOf)

namespace FurioLombardo.Discharge.M3a

/-- The logarithm part of `LiftDisc`. -/
def LogBranch {k : Type*} [Field k] [Algebra ℚ k] {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k}
    (y : Lift M1 M2 M3 δ → Fin 6 → ℤ_[2]) (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2]))
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (disc : Lift M1 M2 M3 δ → ℕ)
    (par : Lift M1 M2 M3 δ → ℤ_[2]) : Prop :=
  ∀ x, y x - lamD (disc x) (par x) ∈ S ∨ y x + lamD (disc x) (par x) ∈ S

namespace Bruin

open FurioLombardo.M1
open FurioLombardo.Discharge.M4Cert (Kv liftDisc liftPar liftTwist_Mmat hExcl_T0_Mmat hExcl_T1_Mmat
  tailGood_T0_Mmat tailGood_T1_Mmat)

attribute [local instance] goodSextic_fRev_Kv

/-- What is left of `M4Rest` at `K_v`, with `Twist`, `disc`, `par` fixed by lane M4's certificate
discharge. -/
structure M4RestKv (k : Fin 2) (D : FurioLombardo.M4.TwistData)
    (φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k))
    (xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k))
    (lam : Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)) →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)))
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop where
  hBD : FurioLombardo.M4.HBallD D (fun i => lam (Dpt i))
  hBP : FurioLombardo.M4.HBallPhi D (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xa)
    (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xb)
  hCe : FurioLombardo.M4.HCentre D lamD
  hAC : FurioLombardo.M4.HAntiConst D lamD
  hAT : FurioLombardo.M4.HAntiTail D lamD
  hKn : FurioLombardo.M4.HKnown D
    (satOf (latL lam Dpt) (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xa)
      (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xb)) lamD
  hSel : FurioLombardo.M4.HSelLoc (iotaA FurioLombardo.Discharge.M4Cert.σ (fRev k)) Dpt D
  hLog : LogBranch (liftLog FurioLombardo.Discharge.M4Cert.σ (fRev k) φ xa lam)
    (satOf (latL lam Dpt) (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xa)
      (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xb)) lamD liftDisc liftPar

/-- `M4Rest` from `M4RestKv`, given `HExcl` and `TailGood` for the twist. -/
theorem M4RestKv.toM4Rest {k : Fin 2} {D : FurioLombardo.M4.TwistData} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    {lam : Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)) →+ (Fin 6 → ℤ_[2])}
    {Dpt : Fin 7 → Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ))}
    {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]} (h : M4RestKv k D φ xa xb lam Dpt lamD)
    (hEx : FurioLombardo.M4.HExcl D
      (FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k)))
    (hTail : TailGood Pa Pb D (liftDisc (M1 := Mmat 0) (M2 := Mmat 1) (M3 := Mmat 2) (δ := δ k))
      liftPar) :
    M4Rest FurioLombardo.Discharge.M4Cert.σ (fRev k) (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb φ xa
      xb lam Dpt D lamD (FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k))
      liftDisc liftPar :=
  { hBD := h.hBD
    hBP := h.hBP
    hCe := h.hCe
    hAC := h.hAC
    hAT := h.hAT
    hKn := h.hKn
    hEx := hEx
    hSel := h.hSel
    hDisc := fun x => ⟨(liftTwist_Mmat (δ k) x).1, (liftTwist_Mmat (δ k) x).2, h.hLog x⟩
    hTail := hTail }

/-- The hypotheses at `K_v` for the twist `k`: the Selmer bound with the local images of
its generators, the local independence of the `x - T` images of the `D_i`, a logarithm with
`LogChartFin` and `M4RestKv`. -/
def TwistInputsKv (k : Fin 2) (D : FurioLombardo.M4.TwistData)
    (φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k))
    (xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) : Prop :=
  ∃ (lam : Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)) →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)))
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]),
    (∃ g : Fin 4 → H (fRev k), SelmerSpan (fRev k) g ∧
      ∀ j, Hmap FurioLombardo.Discharge.M4Cert.σ (fRev k) (g j) =
        ∏ i, muJ ((fRev k).map FurioLombardo.Discharge.M4Cert.σ) (Additive.toMul (Dpt i)) ^
          D.SB i j) ∧
    (∀ c : Fin 7 → ℤ,
      ∏ i, muJ ((fRev k).map FurioLombardo.Discharge.M4Cert.σ) (Additive.toMul (Dpt i)) ^ c i = 1 →
        ∀ i, (2 : ℤ) ∣ c i) ∧
    LogChartFin lam ∧ M4RestKv k D φ xa xb lam Dpt lamD

/-- `TwistInputs` from `TwistInputsKv`, given `HExcl` and `TailGood` for the twist. -/
theorem twistInputs_of_Kv {k : Fin 2} {D : FurioLombardo.M4.TwistData} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    (hEx : FurioLombardo.M4.HExcl D
      (FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k)))
    (hTail : TailGood Pa Pb D (liftDisc (M1 := Mmat 0) (M2 := Mmat 1) (M3 := Mmat 2) (δ := δ k))
      liftPar)
    (h : TwistInputsKv k D φ xa xb) : TwistInputs k D Pa Pb φ xa xb := by
  obtain ⟨lam, Dpt, lamD, hspan, hind, hchart, hM⟩ := h
  exact ⟨Kv, inferInstance, FurioLombardo.Discharge.M4Cert.σ, inferInstance, lam, Dpt, lamD,
    FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k), liftDisc, liftPar,
    localFacts_Kv k, poonenSchaefer_fRev k, hspan, hind, hchart, hM.toM4Rest hEx hTail⟩

/-- **The route of the twist δ0 at `K_v`.** -/
theorem T0.twistRoute_Kv {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 → Jac (fRev 0)}
    (h : TwistInputsKv 0 FurioLombardo.M4.T0.data φ x0 x2) :
    TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) δ0 (0, 0, 1) (2, 0, 1) :=
  twistRoute_of_twistInputs FurioLombardo.M4.T0.checks
    (fun hBD hBP ha hb => Q0.quarter hBD hBP ha hb) FurioLombardo.M4.T0.hSBL
    (twistInputs_of_Kv hExcl_T0_Mmat tailGood_T0_Mmat h)

/-- **The route of the twist δ1 at `K_v`.** -/
theorem T1.twistRoute_Kv {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1 → Jac (fRev 1)}
    (h : TwistInputsKv 1 FurioLombardo.M4.T1.data φ x1 x3) :
    TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) δ1 (1, 1, 1) (-1, 0, 1) :=
  twistRoute_of_twistInputs FurioLombardo.M4.T1.checks
    (fun hBD hBP ha hb => Q1.quarter hBD hBP ha hb) FurioLombardo.M4.T1.hSBL
    (twistInputs_of_Kv hExcl_T1_Mmat tailGood_T1_Mmat h)

/-- **The frozen statement from the inputs at `K_v`.** M1's descent for Bruin's quadrics and, for
each twist, `TwistInputsKv` (with lane M4's data and the known lifts) give
`FurioLombardo.OnlyFourPoints`, for any Abel-Prym maps `φ0`, `φ1` satisfying the inputs. -/
theorem onlyFourPoints_Kv (hdesc : Descent K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 δ1)
    (φ0 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 → Jac (fRev 0))
    (φ1 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1 → Jac (fRev 1))
    (h0 : TwistInputsKv 0 FurioLombardo.M4.T0.data φ0 x0 x2)
    (h1 : TwistInputsKv 1 FurioLombardo.M4.T1.data φ1 x1 x3) : FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_of_route hdesc (T0.twistRoute_Kv h0) (T1.twistRoute_Kv h1)

end Bruin

end FurioLombardo.Discharge.M3a
