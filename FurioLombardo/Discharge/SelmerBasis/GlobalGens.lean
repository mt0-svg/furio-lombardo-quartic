import FurioLombardo.Discharge.SelmerBasis.SUnitDefs
import FurioLombardo.Discharge.SelmerBasis.GlobalCRT
import FurioLombardo.Discharge.M3a.ConcreteDefs
import FurioLombardo.M3a.XminusT

/-!
# The global generators `gK k s` of `H (fRev k)` (frozen interface for the local conditions)

`gK k s` is the class of the unit `Pgen s (T)` of `K21[T]/(fRev k)`. `isUnit_Pgen` comes from the
isomorphism `K21[T]/(fRev k) ≅ L42 × N84`, `T ↦ (α, β)` (GlobalCRT.lean); the local conditions only
need `gKu_coe`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a.Bruin

/-- `Pgen s (T)` is a unit of `K21[T]/(fRev k)`. -/
theorem isUnit_Pgen (k : Fin 2) (s : Fin 82) : IsUnit (AdjoinRoot.mk (fRev k) (Pgen s)) :=
  GlobalK21.isUnit_mk_Pgen k s

/-- The unit `Pgen s (T)`. -/
noncomputable def gKu (k : Fin 2) (s : Fin 82) : (AdjoinRoot (fRev k))ˣ := (isUnit_Pgen k s).unit

theorem gKu_coe (k : Fin 2) (s : Fin 82) :
    (gKu k s : AdjoinRoot (fRev k)) = AdjoinRoot.mk (fRev k) (Pgen s) :=
  (isUnit_Pgen k s).unit_spec

/-- **The global generator `s` of `H (fRev k)`.** -/
noncomputable def gK (k : Fin 2) (s : Fin 82) : H (fRev k) := QuotientGroup.mk (gKu k s)

end FurioLombardo.Discharge.SelmerBasis
