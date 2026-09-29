import Mathlib
import FurioLombardo.Discharge.M4Box.ChainM3a
import FurioLombardo.Discharge.R7.Consumer

/-!
# The consumer of R7 with the box inputs in the weak form

`onlyFourPoints_of_chartLog_weak` is `FurioLombardo.Discharge.M3a.Bruin.onlyFourPoints_of_chartLog`
with `M4RestKv` replaced by `M4RestKvW` (the fields `hAC : HAntiConst`, `hAT : HAntiTail` replaced
by `hCL : HConstLip`, `hTQ : HTailQuad`, all other fields identical). `M4RestKv.toW` derives
`M4RestKvW` from `M4RestKv` (`hConstLip_of_anti`, `hTailQuad_of_anti`), so the weak consumer is
implied by the old inputs (`onlyFourPoints_of_chartLog_of_old`).

On the way: `onlyFourPoints_phiKW` (ConcretePhi.lean), `twistInputsKvW_of_selmerBasis`
(SelmerSpan/Basis.lean), `twistInputsKvW_of_selmerBasis_chartLog` (R7/Consumer.lean).
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin
open FurioLombardo.Discharge.Analytic (LogChartFin)
open FurioLombardo.Discharge.M4Cert (σ)

namespace FurioLombardo.Discharge.M4Box

/-- **The old inputs give the weak ones.** -/
theorem M4RestKv.toW {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    (hD : FurioLombardo.M4.TwistChecks D)
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    {lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2])}
    {Dpt : Fin 7 → Additive (Jac ((fRev k).map σ))} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    (h : M4RestKv k D φ xa xb lam Dpt lamD) : M4RestKvW k D φ xa xb lam Dpt lamD :=
  { hBD := h.hBD
    hBP := h.hBP
    hCe := h.hCe
    hCL := hConstLip_of_anti hD h.hAC
    hTQ := hTailQuad_of_anti hD h.hAT
    hKn := h.hKn
    hSel := h.hSel
    hLog := h.hLog }

/-- `onlyFourPoints_phiK` with `TwistInputsKvW`. -/
theorem onlyFourPoints_phiKW (hdesc : Descent K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 δ1)
    (h0 : TwistInputsKvW 0 FurioLombardo.M4.T0.data (phiK 0) x0 x2)
    (h1 : TwistInputsKvW 1 FurioLombardo.M4.T1.data (phiK 1) x1 x3) :
    FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_KvW hdesc (phiK 0) (phiK 1) h0 h1

/-- `SelmerSpan.twistInputsKv_of_selmerBasis` with `M4RestKvW`. -/
theorem twistInputsKvW_of_selmerBasis {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    {lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2])} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    (hB : FurioLombardo.Discharge.SelmerSpan.SelmerBasisK21 k D.SB) (hL : LogChartFin lam)
    (hM : M4RestKvW k D φ xa xb lam (FurioLombardo.Discharge.SelmerSpan.Dpt k) lamD) :
    TwistInputsKvW k D φ xa xb :=
  ⟨lam, FurioLombardo.Discharge.SelmerSpan.Dpt k, lamD, hB,
    FurioLombardo.Discharge.SelmerSpan.indep_Dpt k, hL, hM⟩

/-- `twistInputsKv_of_selmerBasis_chartLog` with `M4RestKvW`. -/
theorem twistInputsKvW_of_selmerBasis_chartLog {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    {lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2])} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    (hB : FurioLombardo.Discharge.SelmerSpan.SelmerBasisK21 k D.SB)
    (hlam : FurioLombardo.Discharge.R7.ChartLog k lam)
    (hM : M4RestKvW k D φ xa xb lam (FurioLombardo.Discharge.SelmerSpan.Dpt k) lamD) :
    TwistInputsKvW k D φ xa xb :=
  twistInputsKvW_of_selmerBasis hB hlam.logChartFin hM

/-- **The frozen statement from the Selmer bases and one normalized logarithm per twist, box
inputs in the weak form.** For each twist `k`, `SelmerBasisK21 k` and a logarithm `lam` with
`ChartLog k lam` and `M4RestKvW` at the points `Dpt k`, for the Abel-Prym map `phiK k` and the
known lifts, give `FurioLombardo.OnlyFourPoints`. -/
theorem onlyFourPoints_of_chartLog_weak
    (hB0 : FurioLombardo.Discharge.SelmerSpan.SelmerBasisK21 0 FurioLombardo.M4.T0.data.SB)
    (hB1 : FurioLombardo.Discharge.SelmerSpan.SelmerBasisK21 1 FurioLombardo.M4.T1.data.SB)
    (h0 : ∃ (lam : Additive (Jac ((fRev 0).map σ)) →+ (Fin 6 → ℤ_[2]))
      (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]), FurioLombardo.Discharge.R7.ChartLog 0 lam ∧
        M4RestKvW 0 FurioLombardo.M4.T0.data (phiK 0) x0 x2 lam
          (FurioLombardo.Discharge.SelmerSpan.Dpt 0) lamD)
    (h1 : ∃ (lam : Additive (Jac ((fRev 1).map σ)) →+ (Fin 6 → ℤ_[2]))
      (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]), FurioLombardo.Discharge.R7.ChartLog 1 lam ∧
        M4RestKvW 1 FurioLombardo.M4.T1.data (phiK 1) x1 x3 lam
          (FurioLombardo.Discharge.SelmerSpan.Dpt 1) lamD) :
    FurioLombardo.OnlyFourPoints := by
  obtain ⟨lam0, lamD0, hc0, hm0⟩ := h0
  obtain ⟨lam1, lamD1, hc1, hm1⟩ := h1
  exact onlyFourPoints_phiKW (descent_Mmat FurioLombardo.M2.Proved.clK21TwoTorsionTrivial)
    (twistInputsKvW_of_selmerBasis_chartLog hB0 hc0 hm0)
    (twistInputsKvW_of_selmerBasis_chartLog hB1 hc1 hm1)

/-- The hypotheses of `onlyFourPoints_of_chartLog` (with `M4RestKv`) give its conclusion through
the weak consumer. -/
theorem onlyFourPoints_of_chartLog_of_old
    (hB0 : FurioLombardo.Discharge.SelmerSpan.SelmerBasisK21 0 FurioLombardo.M4.T0.data.SB)
    (hB1 : FurioLombardo.Discharge.SelmerSpan.SelmerBasisK21 1 FurioLombardo.M4.T1.data.SB)
    (h0 : ∃ (lam : Additive (Jac ((fRev 0).map σ)) →+ (Fin 6 → ℤ_[2]))
      (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]), FurioLombardo.Discharge.R7.ChartLog 0 lam ∧
        M4RestKv 0 FurioLombardo.M4.T0.data (phiK 0) x0 x2 lam
          (FurioLombardo.Discharge.SelmerSpan.Dpt 0) lamD)
    (h1 : ∃ (lam : Additive (Jac ((fRev 1).map σ)) →+ (Fin 6 → ℤ_[2]))
      (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]), FurioLombardo.Discharge.R7.ChartLog 1 lam ∧
        M4RestKv 1 FurioLombardo.M4.T1.data (phiK 1) x1 x3 lam
          (FurioLombardo.Discharge.SelmerSpan.Dpt 1) lamD) :
    FurioLombardo.OnlyFourPoints := by
  obtain ⟨lam0, lamD0, hc0, hm0⟩ := h0
  obtain ⟨lam1, lamD1, hc1, hm1⟩ := h1
  exact onlyFourPoints_of_chartLog_weak hB0 hB1
    ⟨lam0, lamD0, hc0, M4RestKv.toW FurioLombardo.M4.T0.checks hm0⟩
    ⟨lam1, lamD1, hc1, M4RestKv.toW FurioLombardo.M4.T1.checks hm1⟩

end FurioLombardo.Discharge.M4Box
