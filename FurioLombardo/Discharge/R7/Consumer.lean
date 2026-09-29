import FurioLombardo.Discharge.R7.Transfer
import FurioLombardo.Discharge.M3a.ConcretePhi
import FurioLombardo.Discharge.SelmerSpan.Basis
import FurioLombardo.M1.DescentM3a
import FurioLombardo.M2.ZimmertProved

/-!
# R7 in the assembly: `TwistInputsKv` with `ChartLog` in place of `LogChartFin`

`M3a.Bruin.TwistInputsKv` asks for one logarithm `lam` with both `LogChartFin lam` and
`M4RestKv ... lam ...`. R7 proves `LogChartFin` for every `lam` that is a nondegenerate linear
image of the chart logarithm (`R7.ChartLog`, `R7.ChartLog.logChartFin`), so the `LogChartFin`
conjunct can be replaced by this comparison: in the chart coordinates of some admissible exponent,
`lam` is `ℤ_[2]`-linear and injective (up to a nonzero scalar).

* `twistInputsKv_of_chartLog`: `TwistInputsKv` from the Selmer data, the independence, `ChartLog`
  and `M4RestKv` for the same `lam`;
* `twistInputsKv_of_selmerBasis_chartLog`: the same at the points `SelmerSpan.Dpt k`, where the
  independence is proved;
* `onlyFourPoints_of_chartLog`: the frozen statement from, for each twist, `SelmerBasisK21` and a
  `lam` with `ChartLog` and `M4RestKv` (Abel-Prym map `phiK k`, the known lifts). The descent of
  Bruin's quadrics is lane M1's `descent_Mmat` with lane M2's `Proved.clK21TwoTorsionTrivial`.
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.M4Cert (σ)

namespace FurioLombardo.Discharge.M3a.Bruin

/-- **`TwistInputsKv` from `ChartLog`.** -/
theorem twistInputsKv_of_chartLog {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    (lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]))
    (hlam : FurioLombardo.Discharge.R7.ChartLog k lam)
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map σ))) (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2])
    (hspan : ∃ g : Fin 4 → H (fRev k), SelmerSpan (fRev k) g ∧
      ∀ j, Hmap σ (fRev k) (g j) =
        ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ D.SB i j)
    (hind : ∀ c : Fin 7 → ℤ,
      ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i)
    (hM : M4RestKv k D φ xa xb lam Dpt lamD) : TwistInputsKv k D φ xa xb :=
  ⟨lam, Dpt, lamD, hspan, hind, hlam.logChartFin, hM⟩

/-- **`TwistInputsKv` at the points `Dpt k`, from `SelmerBasisK21` and `ChartLog`.** -/
theorem twistInputsKv_of_selmerBasis_chartLog {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    {lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2])} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    (hB : FurioLombardo.Discharge.SelmerSpan.SelmerBasisK21 k D.SB)
    (hlam : FurioLombardo.Discharge.R7.ChartLog k lam)
    (hM : M4RestKv k D φ xa xb lam (FurioLombardo.Discharge.SelmerSpan.Dpt k) lamD) :
    TwistInputsKv k D φ xa xb :=
  FurioLombardo.Discharge.SelmerSpan.twistInputsKv_of_selmerBasis hB hlam.logChartFin hM

/-- **The frozen statement from the Selmer bases and one normalized logarithm per twist.** For
each twist `k`, `SelmerBasisK21 k` and a logarithm `lam` with `ChartLog k lam` and `M4RestKv` at the
points `Dpt k`, for the Abel-Prym map `phiK k` and the known lifts, give
`FurioLombardo.OnlyFourPoints`. -/
theorem onlyFourPoints_of_chartLog
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
  exact onlyFourPoints_phiK (descent_Mmat FurioLombardo.M2.Proved.clK21TwoTorsionTrivial)
    (twistInputsKv_of_selmerBasis_chartLog hB0 hc0 hm0)
    (twistInputsKv_of_selmerBasis_chartLog hB1 hc1 hm1)

end FurioLombardo.Discharge.M3a.Bruin
