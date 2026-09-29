import FurioLombardo.M1.Basic

/-!
# The named hypothesis of lane M1

`Cl(K21)[2] = 0`. Discharged by lane M2 (class group of `K21`):
`FurioLombardo.M2.Proved.clK21TwoTorsionTrivial` (M2/ZimmertProved.lean).
-/

namespace FurioLombardo.M1

open NumberField

/-- The class group of `K21` has no element of order 2. -/
def ClK21TwoTorsionTrivial : Prop :=
  ∀ c : ClassGroup (𝓞 K21), c ^ 2 = 1 → c = 1

end FurioLombardo.M1
