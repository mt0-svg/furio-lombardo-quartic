import FurioLombardo.Statement
import FurioLombardo.Discharge.M4Box.Final

/-!
# Conjecture 1.6 of Furio and Lombardo

`FurioLombardo.conjecture_1_6 : FurioLombardo.Conjecture`: the rational points of the plane quartic
`C` are `[0 : 0 : 1]`, `[1 : 1 : 1]`, `[2 : 0 : 1]` and `[-1 : 0 : 1]`.

The statement is frozen in `FurioLombardo.Statement`: `Conjecture`, its open part
`OnlyFourPoints` and their equivalence `conjecture_iff_onlyFourPoints`. The proof enters through
`FurioLombardo.Discharge.M4Box.onlyFourPoints` (Discharge/M4Box/Final.lean).
-/

namespace FurioLombardo

/-- **Conjecture 1.6** of Furio and Lombardo (arXiv 2507.17967v3), in the form of
`FurioLombardo.Statement`: a nonzero rational triple lies on `C` if and only if it is a nonzero
multiple of one of the four listed triples. Theorem 1.2 of the paper. -/
theorem conjecture_1_6 : Conjecture :=
  conjecture_iff_onlyFourPoints.mpr Discharge.M4Box.onlyFourPoints

/-- Every rational point of `C` is one of the four listed points. -/
theorem onlyFourPoints : OnlyFourPoints := Discharge.M4Box.onlyFourPoints

end FurioLombardo
