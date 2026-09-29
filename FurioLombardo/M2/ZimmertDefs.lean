import Mathlib

/-!
# Zimmert's function `S₂` (lane M2)

R. Zimmert, *Ideale kleiner Norm in Idealklassen und eine Regulatorabschätzung*, Invent. Math. 62
(1981) 367-380, Satz 2: a number field of degree `n = r₁ + 2 r₂` with `r₁` real places, `r₂`
complex places and discriminant of absolute value `d` has in every ideal class an integral ideal
`𝔞` with, for all `γ > α > 0`,

  `log (d ^ (1/2) / N 𝔞) ≥ r₁ (-Γ'/Γ((1 + γ)/2) - log Γ(1/2 + γ) + log Γ(1 + γ) + (1/2) log π)`
  `  + r₂ (-2 Γ'/Γ(1 + γ) + 2 log 2 + log (1/2 + γ) + log π)`
  `  - 2/(γ - α) - log ((1 + α⁻¹) (1 + γ⁻¹)⁻² (1 + (2γ - α)⁻¹)⁻¹)`.

`zimmertS2 r₁ r₂ γ α` is the right-hand side, with `Γ'/Γ` the logarithmic derivative of
`Real.Gamma`. The transcription is tested against all 21 entries of Zimmert's Table 1 in
code/second-implementations/class-number/zimmert_bounds.gp.
-/

namespace FurioLombardo.M2

open Real

/-- The logarithmic derivative `Γ'/Γ` of the real Gamma function. -/
noncomputable def logDerivGamma (x : ℝ) : ℝ := deriv Real.Gamma x / Real.Gamma x

/-- The right-hand side of Zimmert's Satz 2. -/
noncomputable def zimmertS2 (r₁ r₂ : ℕ) (γ α : ℝ) : ℝ :=
  r₁ * (-logDerivGamma ((1 + γ) / 2) - Real.log (Real.Gamma (1 / 2 + γ))
        + Real.log (Real.Gamma (1 + γ)) + Real.log π / 2)
  + r₂ * (-2 * logDerivGamma (1 + γ) + 2 * Real.log 2 + Real.log (1 / 2 + γ) + Real.log π)
  - 2 / (γ - α)
  - Real.log ((1 + α⁻¹) * ((1 + γ⁻¹) ^ 2)⁻¹ * (1 + (2 * γ - α)⁻¹)⁻¹)

end FurioLombardo.M2
