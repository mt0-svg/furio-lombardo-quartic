import Mathlib
import FurioLombardo.M2.ZimmertDefs

/-!
# Zimmert's Satz 1 at `γ = 1/2`: definitions (lane M2)

R. Zimmert, *Ideale kleiner Norm in Idealklassen und eine Regulatorabschätzung*, Invent. Math. 62
(1981) 367-380, Satz 1 and the proof of Satz 2, specialised to `γ = 1/2`. Notation:

* `Rz α β s = (s + α) / ((s + β) (s + 1 - β) (s + 1 - α))`, Zimmert's `R` at `γ = 1/2`;
* `rz α β s = (s + α) / ((s + 1 - β) (s + 1 - α))`, so that `Rz = rz / (s + β)`;
* `Gz a b s = Γ(s/2)^a Γ((s+1)/2)^b`, the Gamma factor of the functional equation;
* `iG1 a b s = Γ(s/2 + 1)⁻¹^a Γ((s+3)/2)⁻¹^b`, the entire function `1/G₁`;
* `dser μ s = Σ μ_j^{-s}` and its real version `dserR`;
* `ZData a b ιf ιg`: a pair of Dirichlet series `D_ν`, `D_μ` with completed functions
  `Λf s = Lf s - κ/s + κ/(s-1)`, `Λg s = Lg s - κ/s + κ/(s-1)` related by `Lf s = Lg (1 - s)`.
-/

namespace FurioLombardo.M2.Zimmert

open Complex

/-- Zimmert's rational function `R` at `γ = 1/2`. -/
noncomputable def Rz (α β : ℝ) (s : ℂ) : ℂ :=
  (s + α) / ((s + β) * (s + 1 - β) * (s + 1 - α))

/-- `Rz` without its pole at `-β`. -/
noncomputable def rz (α β : ℝ) (s : ℂ) : ℂ :=
  (s + α) / ((s + 1 - β) * (s + 1 - α))

/-- The Gamma factor `Γ(s/2)^a Γ((s+1)/2)^b`. -/
noncomputable def Gz (a b : ℕ) (s : ℂ) : ℂ :=
  Gamma (s / 2) ^ a * Gamma ((s + 1) / 2) ^ b

/-- The entire function `1/G₁(s) = Γ(s/2 + 1)⁻¹^a Γ((s+3)/2)⁻¹^b`. -/
noncomputable def iG1 (a b : ℕ) (s : ℂ) : ℂ :=
  (Gamma (s / 2 + 1))⁻¹ ^ a * (Gamma ((s + 3) / 2))⁻¹ ^ b

/-- The Dirichlet series `Σ μ_j^{-s}`. -/
noncomputable def dser {ι : Type*} (μ : ι → ℝ) (s : ℂ) : ℂ :=
  ∑' j, ((μ j : ℝ) : ℂ) ^ (-s)

/-- The Dirichlet series `Σ μ_j^{-σ}` at a real point. -/
noncomputable def dserR {ι : Type*} (μ : ι → ℝ) (σ : ℝ) : ℝ :=
  ∑' j, μ j ^ (-σ)

/-- The data of Zimmert's Satz 1 (Gamma factor `Γ(s/2)^a Γ((s+1)/2)^b`, conductor `A`). -/
structure ZData (a b : ℕ) (ιf ιg : Type*) where
  A : ℝ
  hA : 0 < A
  ν : ιf → ℝ
  μ : ιg → ℝ
  hν : ∀ i, 1 ≤ ν i
  hμ : ∀ j, 1 ≤ μ j
  hνs : ∀ σ : ℝ, 1 < σ → Summable fun i => ν i ^ (-σ)
  hμs : ∀ σ : ℝ, 1 < σ → Summable fun j => μ j ^ (-σ)
  Lf : ℂ → ℂ
  Lg : ℂ → ℂ
  κ : ℂ
  hLf : Differentiable ℂ Lf
  hfe : ∀ s, Lf s = Lg (1 - s)
  hstrip : ∀ σ₁ σ₂ : ℝ, ∃ M : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Lf s‖ ≤ M
  hdf : ∀ s : ℂ, 1 < s.re → Lf s - κ / s + κ / (s - 1) = (A : ℂ) ^ s * Gz a b s * dser ν s
  hdg : ∀ s : ℂ, 1 < s.re → Lg s - κ / s + κ / (s - 1) = (A : ℂ) ^ s * Gz a b s * dser μ s

namespace ZData

variable {a b : ℕ} {ιf ιg : Type*} (D : ZData a b ιf ιg)

/-- The completed function of the `f` side. -/
noncomputable def Λf (s : ℂ) : ℂ := D.Lf s - D.κ / s + D.κ / (s - 1)

/-- The completed function of the `g` side. -/
noncomputable def Λg (s : ℂ) : ℂ := D.Lg s - D.κ / s + D.κ / (s - 1)

end ZData

/-- Zimmert's choice of `x` at `γ = 1/2` (it kills the residues at `1` and `0`). -/
noncomputable def xz (a b : ℕ) (A α β : ℝ) : ℝ :=
  A * (α * (1 + β) * (2 - β) * (2 - α)) / (β * (1 - β) * (1 - α) * (1 + α))
    * (Real.Gamma (3 / 2) ^ a / Real.Gamma (3 / 2) ^ b)

/-- `T_β = G(1+β)/G₁(-β)` at `γ = 1/2`. -/
noncomputable def Tz (a b : ℕ) (β : ℝ) : ℝ :=
  Real.Gamma ((1 + β) / 2) ^ a * Real.Gamma (1 + β / 2) ^ b
    / (Real.Gamma (1 - β / 2) ^ a * Real.Gamma ((3 - β) / 2) ^ b)

end FurioLombardo.M2.Zimmert
