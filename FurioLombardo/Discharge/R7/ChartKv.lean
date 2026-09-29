import Mathlib
import FurioLombardo.Discharge.R7.Psi
import FurioLombardo.Discharge.R7.LogChart

/-!
# `LogChartFin` for `Jac F` over `Kv` from a base point (item R7, assembly)

A `SetupKv` is the genericity data of a base point `P0 = (a, V0(0))` for a translated model
`f = F(X + a)` over `Kv` (`Formal.lean`), with the scaling pair fixed to `(OKv, pv)`. For such data,
an admissible exponent `M` (`Setup.exists_adm`) gives the integral formal group law
`S.fglO` over `OKv` and the injective chart `S.psi : Points → Jac F`
(`Psi.lean`). Under the finite index hypothesis `HFinIdx` for this chart (a theorem,
`FinIdx.hFinIdx_of_setupKv`, FinIdx/Assembly.lean), there is
`lam : Additive (Jac F) →+ ℤ_[2]^6` with `Analytic.LogChartFin lam`
(`logChartFin_of_setupKv`).
-/

open Polynomial
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall
open FurioLombardo.Discharge.M4Cert

namespace FurioLombardo.Discharge.R7

/-- The genericity data of a base point over `Kv` (the fields of `Setup` after `O`, `π`). -/
structure SetupKv where
  f : Kv[X]
  hf : f.natDegree ≤ 6
  V0 : Kv[X]
  hV0d : V0.degree < 4
  hV00 : V0.coeff 0 ≠ 0
  c0 : Kv
  hc0 : c0 ≠ 0
  w0 : Kv[X]
  hw0m : w0.Monic
  hw0d : w0.natDegree = 2
  hfV0 : f - V0 ^ 2 = C c0 * (X ^ 4 * w0)
  hw00 : w0.coeff 0 ≠ 0

/-- The `Setup` of a `SetupKv`, with `O = OKv` and `π = pv`. -/
noncomputable abbrev SetupKv.toSetup (D : SetupKv) : Setup Kv where
  O := unitBall Kv
  π := pvO
  hπ0 := isUniformizer_pv.ne_zero
  hbd := isUniformizer_pv.exists_pow_mul_mem
  h2 := two_ne_zero
  f := D.f
  hf := D.hf
  V0 := D.V0
  hV0d := D.hV0d
  hV00 := D.hV00
  c0 := D.c0
  hc0 := D.hc0
  w0 := D.w0
  hw0m := D.hw0m
  hw0d := D.hw0d
  hfV0 := D.hfV0
  hw00 := D.hw00

/-- **`LogChartFin` for `Jac F` from a base point**, under the hypothesis `HFinIdx` (a
theorem: `FinIdx.hFinIdx_of_setupKv`) for the chart of the base point. The logarithm is explicit on
the image of the ball `B1 Φ (pv ^ 4)`: there it is the index `[Jac F : ψ(B1)]` times the
coordinates of the scaled logarithm `logVal` of `Φ = S.fglO`, the formal group law of the chart. -/
theorem logChartFin_of_setupKv (D : SetupKv) [GoodSextic D.f] (F : Kv[X]) [GoodSextic F] (a : Kv)
    (hF : D.f.comp (X - C a) = F) {M : ℕ} (hM : D.toSetup.Adm M)
    (hH : HFinIdx (D.toSetup.fglO hM.good) (D.toSetup.psi hF hM) (pvO ^ (3 + 1))) :
    ∃ lam : Additive (Jac F) →+ (Fin 6 → ℤ_[2]), Analytic.LogChartFin lam ∧
      ∃ H' : AddSubgroup (Additive (Jac F)),
        (H' : Set (Additive (Jac F))) = D.toSetup.psi hF hM ''
          (FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)) :
            Set (D.toSetup.fglO hM.good).Points) ∧
        H'.FiniteIndex ∧
        ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)),
          ∀ y : Fin 2 → OKv, (∀ j, (z j : OKv) = pvO ^ (3 + 1) * y j) →
            lam (D.toSetup.psi hF hM z) = H'.index • coordEquiv
              (FurioLombardo.Vendor.Toolbox.FormalGroup.logVal (D.toSetup.fglO hM.good) (unitBall Kv).subtype
                (pvO ^ (3 + 1)) y) :=
  exists_logChartFin_of_chart _ _ (D.toSetup.psi_injective hF hM) hH

end FurioLombardo.Discharge.R7
