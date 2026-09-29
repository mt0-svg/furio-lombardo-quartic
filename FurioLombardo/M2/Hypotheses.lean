import FurioLombardo.M2.Frame
import FurioLombardo.M2.Field

/-!
# The named hypothesis of lane M2

Zimmert's bound for K21: every ideal class of `𝓞 K21` contains an integral ideal of absolute
norm at most 100618. K21 is the degree 21 field `ℚ[X]/(fZ)` of `Field.lean`. The value is
Zimmert's bound (Zimmert 1981, Satz 2) for the signature and discriminant of K21 as transcribed in
code/second-implementations/class-number/zimmert_bounds.gp (100618.7; a second implementation gives
99932, so the larger value is the weaker hypothesis). It is not proved in Lean (Mathlib only has the
Minkowski bound, about 4.04e7 for K21), and the proof of the frozen statement does not use it:
ZimmertMain.lean replaces this hypothesis by `ZimmertSatz2K21` (Zimmert.lean), the statement of
Zimmert's Satz 2 for K21 at one parameter pair, and proves the class bound 120000 from it;
ZimmertProved.lean proves `ZimmertSatz2K21`.
-/

namespace FurioLombardo.M2

open NumberField

/-- Zimmert's bound for K21: every ideal class contains an integral ideal of norm at most 100618. -/
def ZimmertBoundK21 : Prop := ClassBound K21 100618

end FurioLombardo.M2
