import FurioLombardo.Discharge.M3b.RamL
import FurioLombardo.Discharge.M3b.Signs

/-!
# The named inputs of lane M3b proved for the concrete tower `K21 ⊂ L42 ⊂ N84`

`FurioLombardo.M3b.RouteRClassInputs K21 L42 N84` holds as soon as `Cl(K21)[2] = 1` (the field
`clK`, lane M2's class number one): the degrees are 2 (`finrank_L42`, `finrank_N84`), and
`ramL`, `dyadicL`, `ramN`, `signsN` are `ramBound_L42`, `dyadic_L42`, `ramBound_N84`,
`signPattern_N84`. With the top theorem of lane M3b this gives `Cl(L42)[2] = 1` and
`Cl(N84)[2] = 1`. Lane M2 supplies `clK`: `clTwoTrivial_of_pid` with
`FurioLombardo.M2.Proved.isPrincipalIdealRing_M1K21` (`Discharge.SelmerBasis.clTwoTrivial_K21`,
SelmerBasis/SUnitSpan.lean).
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 NumberField

/-- The inputs of route R on `K21 ⊂ L42 ⊂ N84`, given `Cl(K21)[2] = 1`. -/
theorem routeRClassInputs (hK : FurioLombardo.M3b.ClTwoTrivial K21) :
    FurioLombardo.M3b.RouteRClassInputs K21 L42 N84 :=
  ⟨finrank_L42, finrank_N84, hK, ramBound_L42, dyadic_L42, ramBound_N84, signPattern_N84⟩

/-- A principal ideal ring has `Cl[2] = 1`. -/
theorem clTwoTrivial_of_pid [IsPrincipalIdealRing (𝓞 K21)] :
    FurioLombardo.M3b.ClTwoTrivial K21 := by
  intro c _
  have : Subsingleton (ClassGroup (𝓞 K21)) := by
    rw [← Fintype.card_le_one_iff_subsingleton, ← classNumber,
      (classNumber_eq_one_iff).mpr ‹_›]
  exact Subsingleton.elim _ _

/-- The inputs of route R on `K21 ⊂ L42 ⊂ N84`, given `h(K21) = 1`. -/
theorem routeRClassInputs_of_pid [IsPrincipalIdealRing (𝓞 K21)] :
    FurioLombardo.M3b.RouteRClassInputs K21 L42 N84 :=
  routeRClassInputs clTwoTrivial_of_pid

/-- `Cl(L42)[2] = 1` and `Cl(N84)[2] = 1` from `Cl(K21)[2] = 1`. -/
theorem classGroups_L42_N84 (hK : FurioLombardo.M3b.ClTwoTrivial K21) :
    FurioLombardo.M3b.ClTwoTrivial L42 ∧ FurioLombardo.M3b.ClTwoTrivial N84 :=
  FurioLombardo.M3b.routeR_classGroups (routeRClassInputs hK)

end FurioLombardo.Discharge.M3b
