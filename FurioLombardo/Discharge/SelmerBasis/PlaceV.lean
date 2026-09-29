import FurioLombardo.Discharge.SelmerSpan.Basis
import FurioLombardo.Discharge.SelmerBasis.Interfaces

/-!
# The place `v`: the local Props of Interfaces.lean at `M4Cert.σ : K21 →+* Kv`

* `indepImage_v`: `IndepImage` at `v` for the points `Dpt k` (lane SelmerSpan's `indep_Dpt`, with
  natural exponents).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.SelmerSpan

attribute [local instance] goodSextic_fRev_Kv

/-- **`IndepImage` at `v`.** -/
theorem indepImage_v (k : Fin 2) :
    IndepImage ((fRev k).map σ) (fun i => Additive.toMul (Dpt k i)) := by
  intro c hc i
  have h := indep_Dpt k (fun i => (c i : ℤ)) (by simpa only [zpow_natCast] using hc) i
  exact_mod_cast h

end FurioLombardo.Discharge.SelmerBasis
