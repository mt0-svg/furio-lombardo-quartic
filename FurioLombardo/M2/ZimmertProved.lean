import FurioLombardo.M2.ZimmertMain
import FurioLombardo.M2.Zimmert.Satz2

/-!
# h(K21) = 1 with no hypothesis (lane M2)

`zimmertSatz2K21 : ZimmertSatz2K21` is the instance `K = K21`, `α = 1/12` of
`Zimmert.zimmert_satz2_half` (Zimmert's Satz 2 at `γ = 1/2`, proved in
FurioLombardo/M2/Zimmert/ on top of AINTLIB's class theta functions). Every theorem of
ZimmertMain.lean then holds unconditionally; they are restated here in the namespace
`FurioLombardo.M2.Proved`.
-/

namespace FurioLombardo.M2

open NumberField

/-- The named hypothesis of lane M2 is a theorem. -/
theorem zimmertSatz2K21 : ZimmertSatz2K21 :=
  fun C => Zimmert.zimmert_satz2_half C (by norm_num) (by norm_num)

namespace Proved

/-- Every ideal class of `𝓞 K21` contains an integral ideal of norm at most 120000. -/
theorem classBound_K21 : ClassBound K21 120000 := classBound_of_zimmertSatz2 zimmertSatz2K21

/-- `h(K21) = 1`. -/
theorem isPrincipalIdealRing_K21 : IsPrincipalIdealRing (𝓞 K21) :=
  isPrincipalIdealRing_K21_of_zimmertSatz2 zimmertSatz2K21

/-- The class number of K21 is 1. -/
theorem classNumber_K21 : classNumber K21 = 1 := classNumber_K21_of_zimmertSatz2 zimmertSatz2K21

/-- The named hypothesis of lane M1. -/
theorem clK21TwoTorsionTrivial : FurioLombardo.M1.ClK21TwoTorsionTrivial :=
  clK21TwoTorsionTrivial_of_zimmertSatz2 zimmertSatz2K21

/-- `h = 1` on lane M1's field. -/
theorem isPrincipalIdealRing_M1K21 : IsPrincipalIdealRing (𝓞 FurioLombardo.M1.K21) :=
  isPrincipalIdealRing_M1K21_of_zimmertSatz2 zimmertSatz2K21

theorem classNumber_M1K21 : classNumber FurioLombardo.M1.K21 = 1 :=
  classNumber_M1K21_of_zimmertSatz2 zimmertSatz2K21

/-- `Cl(K21)[2] = 1` in the form of lane M3b. -/
theorem clTwoTrivial_M1K21 : FurioLombardo.M3b.ClTwoTrivial FurioLombardo.M1.K21 :=
  clTwoTrivial_M1K21_of_zimmertSatz2 zimmertSatz2K21

/-- The class group inputs of route R on `K21 ⊂ L42 ⊂ N84`. -/
theorem routeRClassInputs : FurioLombardo.M3b.RouteRClassInputs FurioLombardo.M1.K21
    FurioLombardo.Discharge.M3b.L42 FurioLombardo.Discharge.M3b.N84 :=
  routeRClassInputs_of_zimmertSatz2 zimmertSatz2K21

/-- `Cl(L42)[2] = 1` and `Cl(N84)[2] = 1`. -/
theorem classGroups_L42_N84 :
    FurioLombardo.M3b.ClTwoTrivial FurioLombardo.Discharge.M3b.L42 ∧
      FurioLombardo.M3b.ClTwoTrivial FurioLombardo.Discharge.M3b.N84 :=
  classGroups_L42_N84_of_zimmertSatz2 zimmertSatz2K21

end Proved

end FurioLombardo.M2
