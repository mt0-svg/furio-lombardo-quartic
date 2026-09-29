import FurioLombardo.M2.ZimmertDefs
import FurioLombardo.M2.Frame
import FurioLombardo.M2.Field

/-!
# Zimmert's Satz 2 for K21, the named hypothesis of lane M2

R. Zimmert, *Ideale kleiner Norm in Idealklassen und eine Regulatorabschätzung*, Invent. Math. 62
(1981) 367-380, Satz 2 (see `FurioLombardo.M2.zimmertS2`): every ideal class of a number field
with `r₁` real places, `r₂` complex places and discriminant `D` contains an integral ideal `𝔞`
with `log (|D| ^ (1/2) / N 𝔞) ≥ zimmertS2 r₁ r₂ γ α` for all `γ > α > 0`.
`ZimmertSatz2K21` is this statement for `K = K21` at the single point `γ = 1/2`, `α = 1/12`. It is
proved: `zimmertSatz2K21` (ZimmertProved.lean) is the instance of `Zimmert.zimmert_satz2_half`
(Zimmert/Satz2.lean, Satz 2 at `γ = 1/2` for every number field, through AINTLIB's class theta
functions). Everything specific to K21 that turns it into a class bound (the signature, the
discriminant, the value of `zimmertS2 3 9 (1/2) (1/12)`) is proved in Lean
(`FurioLombardo.M2.classBound_of_zimmertSatz2`).
-/

namespace FurioLombardo.M2

open NumberField

open scoped nonZeroDivisors

/-- Zimmert's Satz 2 for K21 at `γ = 1/2`, `α = 1/12`. -/
def ZimmertSatz2K21 : Prop :=
  ∀ C : ClassGroup (𝓞 K21), ∃ I : (Ideal (𝓞 K21))⁰, ClassGroup.mk0 I = C ∧
    zimmertS2 (InfinitePlace.nrRealPlaces K21) (InfinitePlace.nrComplexPlaces K21) (1 / 2) (1 / 12)
      ≤ Real.log (Real.sqrt |(discr K21 : ℝ)| / (Ideal.absNorm (I : Ideal (𝓞 K21)) : ℝ))

end FurioLombardo.M2
