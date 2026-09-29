import FurioLombardo.M2.Hypotheses
import FurioLombardo.M2.Generic
import FurioLombardo.M2.Special45613
import FurioLombardo.M1.Hypotheses

/-!
# h(K21) = 1 from a class bound (lane M2)

Every prime `P` of `𝓞 K21` above `p ≤ Bnd = 120000` with `p ^ f(P) ≤ Bnd` is principal: the
special primes 2, 7, 45613 by `special_two`, `special_seven`, `special_45613`, every other prime by
the kernel certificates of `Data/P000` to `Data/P119` (`generic_prime`). So a class bound `Bnd`
gives `h(K21) = 1` through the frame `isPrincipalIdealRing_of_bound`
(`isPrincipalIdealRing_of_classBound`), hence `Cl(K21)[2] = 0`, the named hypothesis
`FurioLombardo.M1.ClK21TwoTorsionTrivial` of lane M1 (`FurioLombardo.M1.K21` and
`FurioLombardo.M2.K21` are the same term up to unfolding). The versions below take the named
hypothesis `ZimmertBoundK21` (class bound 100618); ZimmertMain.lean has the versions under
Zimmert's Satz 2 for K21 (`ZimmertSatz2K21`), which gives the class bound 120000, and
ZimmertProved.lean the versions with no hypothesis.
-/

namespace FurioLombardo.M2

open NumberField Ideal

/-- Every class bound up to `Bnd = 120000` gives `h(K21) = 1`. -/
theorem isPrincipalIdealRing_of_classBound (hB : ClassBound K21 Bnd) :
    IsPrincipalIdealRing (𝓞 K21) := by
  refine isPrincipalIdealRing_of_bound Bnd hB (fun p hp hpB P hP hPB => ?_)
  by_cases h2 : p = 2
  · subst h2; exact special_two P hP
  by_cases h7 : p = 7
  · subst h7; exact special_seven P hP
  by_cases h45 : p = 45613
  · subst h45; exact special_45613 P hP hPB
  have hs : isSpecial p = false := by simp [isSpecial, h2, h7, h45]
  exact generic_prime p hp hpB hs P hP hPB

theorem isPrincipalIdealRing_K21 (hZ : ZimmertBoundK21) : IsPrincipalIdealRing (𝓞 K21) :=
  isPrincipalIdealRing_of_classBound (ClassBound.mono (K := K21) hZ (by decide))

theorem classNumber_K21 (hZ : ZimmertBoundK21) : classNumber K21 = 1 :=
  haveI := isPrincipalIdealRing_K21 hZ
  classNumber_eq_one_iff.mpr inferInstance

theorem classGroup_two_torsion_K21 (hZ : ZimmertBoundK21) (c : ClassGroup (𝓞 K21))
    (hc : c ^ 2 = 1) : c = 1 :=
  haveI := isPrincipalIdealRing_K21 hZ
  classGroup_sq_eq_one_imp c hc

/-- Lane M2 discharges the named hypothesis of lane M1, under Zimmert's bound. -/
theorem clK21TwoTorsionTrivial (hZ : ZimmertBoundK21) :
    FurioLombardo.M1.ClK21TwoTorsionTrivial :=
  fun c hc => classGroup_two_torsion_K21 hZ c hc

end FurioLombardo.M2
