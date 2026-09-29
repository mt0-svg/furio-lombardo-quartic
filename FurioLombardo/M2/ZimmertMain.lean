import FurioLombardo.M2.ZimmertBound
import FurioLombardo.M2.ZimmertNum
import FurioLombardo.M2.Discr
import FurioLombardo.M2.Bridge

/-!
# h(K21) = 1 under Zimmert's Satz 2 for K21 (lane M2)

The only hypothesis is `ZimmertSatz2K21` (Zimmert.lean): Zimmert's Satz 2 (Invent. Math. 62
(1981), 367-380) for the field K21 at `γ = 1/2`, `α = 1/12`, stated with Mathlib's
`NumberField.discr`, `InfinitePlace.nrRealPlaces`, `InfinitePlace.nrComplexPlaces`,
`Real.Gamma` and its derivative. Proved in Lean: the signature `(3, 9)` (Signature.lean),
`|discr K21| ≤ 2^22 7^27` (Discr.lean), the closed form and the lower bound of
`zimmertS2 3 9 (1/2) (1/12)` (ZimmertNum.lean), hence the class bound 120000
(`classBound_of_zimmertSatz2`), and the kernel certificates for every prime of norm at most
`Bnd = 120000` (Main.lean). The results are restated on lane M1's field `FurioLombardo.M1.K21`
(the same type, `k21_eq`) in the forms used by lane M1 and by the M3b discharge. ZimmertProved.lean
proves `ZimmertSatz2K21` and restates them with no hypothesis (namespace `FurioLombardo.M2.Proved`).
-/

namespace FurioLombardo.M2

open NumberField

open scoped nonZeroDivisors

/-- Zimmert's Satz 2 for K21 gives an ideal of norm at most 120000 in every class. -/
theorem classBound_of_zimmertSatz2 (hZ : ZimmertSatz2K21) : ClassBound K21 120000 :=
  classBound_of_zimmertSatz2_aux zimmertS2_half_ge abs_discr_K21_le hZ

/-- `h(K21) = 1` under Zimmert's Satz 2 for K21. -/
theorem isPrincipalIdealRing_K21_of_zimmertSatz2 (hZ : ZimmertSatz2K21) :
    IsPrincipalIdealRing (𝓞 K21) :=
  isPrincipalIdealRing_of_classBound (ClassBound.mono (classBound_of_zimmertSatz2 hZ) (by decide))

/-- The class number of K21 is 1 under Zimmert's Satz 2 for K21. -/
theorem classNumber_K21_of_zimmertSatz2 (hZ : ZimmertSatz2K21) : classNumber K21 = 1 :=
  haveI := isPrincipalIdealRing_K21_of_zimmertSatz2 hZ
  classNumber_eq_one_iff.mpr inferInstance

theorem classGroup_two_torsion_K21_of_zimmertSatz2 (hZ : ZimmertSatz2K21)
    (c : ClassGroup (𝓞 K21)) (hc : c ^ 2 = 1) : c = 1 :=
  haveI := isPrincipalIdealRing_K21_of_zimmertSatz2 hZ
  classGroup_sq_eq_one_imp c hc

/-- Lane M2 discharges the named hypothesis of lane M1, under Zimmert's Satz 2 for K21. -/
theorem clK21TwoTorsionTrivial_of_zimmertSatz2 (hZ : ZimmertSatz2K21) :
    FurioLombardo.M1.ClK21TwoTorsionTrivial :=
  fun c hc => classGroup_two_torsion_K21_of_zimmertSatz2 hZ c hc

/-- The named hypothesis, stated on lane M1's field. -/
theorem zimmertSatz2_M1 : ZimmertSatz2K21 ↔
    ∀ C : ClassGroup (𝓞 FurioLombardo.M1.K21), ∃ I : (Ideal (𝓞 FurioLombardo.M1.K21))⁰,
      ClassGroup.mk0 I = C ∧
      zimmertS2 (InfinitePlace.nrRealPlaces FurioLombardo.M1.K21)
          (InfinitePlace.nrComplexPlaces FurioLombardo.M1.K21) (1 / 2) (1 / 12)
        ≤ Real.log (Real.sqrt |(discr FurioLombardo.M1.K21 : ℝ)| /
            (Ideal.absNorm (I : Ideal (𝓞 FurioLombardo.M1.K21)) : ℝ)) :=
  Iff.rfl

/-- `h(K21) = 1` on M1's field, under Zimmert's Satz 2 for K21. -/
theorem isPrincipalIdealRing_M1K21_of_zimmertSatz2 (hZ : ZimmertSatz2K21) :
    IsPrincipalIdealRing (𝓞 FurioLombardo.M1.K21) :=
  isPrincipalIdealRing_K21_of_zimmertSatz2 hZ

/-- The class number of M1's K21 is 1, under Zimmert's Satz 2 for K21. -/
theorem classNumber_M1K21_of_zimmertSatz2 (hZ : ZimmertSatz2K21) :
    classNumber FurioLombardo.M1.K21 = 1 :=
  classNumber_K21_of_zimmertSatz2 hZ

/-- `Cl(K21)[2] = 1` in the form of lane M3b, under Zimmert's Satz 2 for K21. -/
theorem clTwoTrivial_M1K21_of_zimmertSatz2 (hZ : ZimmertSatz2K21) :
    FurioLombardo.M3b.ClTwoTrivial FurioLombardo.M1.K21 :=
  clK21TwoTorsionTrivial_of_zimmertSatz2 hZ

/-- The inputs of route R on `K21 ⊂ L42 ⊂ N84`, under Zimmert's Satz 2 for K21. -/
theorem routeRClassInputs_of_zimmertSatz2 (hZ : ZimmertSatz2K21) :
    FurioLombardo.M3b.RouteRClassInputs FurioLombardo.M1.K21 FurioLombardo.Discharge.M3b.L42
      FurioLombardo.Discharge.M3b.N84 :=
  haveI := isPrincipalIdealRing_M1K21_of_zimmertSatz2 hZ
  FurioLombardo.Discharge.M3b.routeRClassInputs_of_pid

/-- `Cl(L42)[2] = 1` and `Cl(N84)[2] = 1`, under Zimmert's Satz 2 for K21. -/
theorem classGroups_L42_N84_of_zimmertSatz2 (hZ : ZimmertSatz2K21) :
    FurioLombardo.M3b.ClTwoTrivial FurioLombardo.Discharge.M3b.L42 ∧
      FurioLombardo.M3b.ClTwoTrivial FurioLombardo.Discharge.M3b.N84 :=
  FurioLombardo.Discharge.M3b.classGroups_L42_N84 (clTwoTrivial_M1K21_of_zimmertSatz2 hZ)

end FurioLombardo.M2
