import FurioLombardo.M2.Main
import FurioLombardo.Discharge.M3b.Main

/-!
# Lane M2 results on lane M1's field

`FurioLombardo.M1.K21` and `FurioLombardo.M2.K21` are both `AdjoinRoot fQ` for the same
polynomial text, so they agree by unfolding (`k21_eq`). The results of `Main.lean` are restated on
M1's field, in the forms consumed by lane M1 (`ClK21TwoTorsionTrivial`) and by the M3b discharge
(`ClTwoTrivial`, `IsPrincipalIdealRing`, `RouteRClassInputs`). The only hypothesis is
`ZimmertBoundK21`; `zimmertBound_M1` states it on M1's field. ZimmertMain.lean has the same
results under `ZimmertSatz2K21` (Zimmert's Satz 2 for K21) instead, and ZimmertProved.lean with no
hypothesis.
-/

namespace FurioLombardo.M2

open NumberField

/-- The two copies of `fZ` are the same polynomial. -/
theorem fZ_eq : FurioLombardo.M2.fZ = FurioLombardo.M1.fZ := rfl

/-- The two copies of `fQ` are the same polynomial. -/
theorem fQ_eq : FurioLombardo.M2.fQ = FurioLombardo.M1.fQ := rfl

/-- The two copies of K21 are the same type. -/
theorem k21_eq : FurioLombardo.M2.K21 = FurioLombardo.M1.K21 := rfl

/-- The named hypothesis of lane M2 is the class bound 100618 on M1's field. -/
theorem zimmertBound_M1 : ZimmertBoundK21 ↔ ClassBound FurioLombardo.M1.K21 100618 :=
  Iff.rfl

/-- `h(K21) = 1` on M1's field, under Zimmert's bound. -/
theorem isPrincipalIdealRing_M1K21 (hZ : ZimmertBoundK21) :
    IsPrincipalIdealRing (𝓞 FurioLombardo.M1.K21) :=
  isPrincipalIdealRing_K21 hZ

/-- The class number of M1's K21 is 1, under Zimmert's bound. -/
theorem classNumber_M1K21 (hZ : ZimmertBoundK21) : classNumber FurioLombardo.M1.K21 = 1 :=
  classNumber_K21 hZ

/-- `Cl(K21)[2] = 1` in the form of lane M3b, under Zimmert's bound. -/
theorem clTwoTrivial_M1K21 (hZ : ZimmertBoundK21) :
    FurioLombardo.M3b.ClTwoTrivial FurioLombardo.M1.K21 :=
  clK21TwoTorsionTrivial hZ

/-- The M3b discharge closes under Zimmert's bound: the inputs of route R on
`K21 ⊂ L42 ⊂ N84`. -/
theorem routeRClassInputs_M2 (hZ : ZimmertBoundK21) :
    FurioLombardo.M3b.RouteRClassInputs FurioLombardo.M1.K21 FurioLombardo.Discharge.M3b.L42
      FurioLombardo.Discharge.M3b.N84 :=
  haveI := isPrincipalIdealRing_M1K21 hZ
  FurioLombardo.Discharge.M3b.routeRClassInputs_of_pid

/-- `Cl(L42)[2] = 1` and `Cl(N84)[2] = 1`, under Zimmert's bound. -/
theorem classGroups_L42_N84_M2 (hZ : ZimmertBoundK21) :
    FurioLombardo.M3b.ClTwoTrivial FurioLombardo.Discharge.M3b.L42 ∧
      FurioLombardo.M3b.ClTwoTrivial FurioLombardo.Discharge.M3b.N84 :=
  FurioLombardo.Discharge.M3b.classGroups_L42_N84 (clTwoTrivial_M1K21 hZ)

end FurioLombardo.M2
