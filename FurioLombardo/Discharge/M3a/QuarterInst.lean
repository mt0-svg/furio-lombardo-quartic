import Mathlib
import FurioLombardo.Discharge.M3a.Quarter

/-!
# `Quarter` for the twists δ0 and δ1

The five finite facts on lane M4's data used by `quarter_of_cert` (`UG (H Ui) = 4`, `dl = 6`,
`4 ∣ A0`, `8 ∤ A0`, `4 ∣ B0`), checked by `decide +kernel`, and the resulting `Quarter` for each
twist, from lane M4's certified balls (`HBallD`, `HBallPhi`) alone.

Values (recomputed with PARI/GP, code/genus2-curves/quarter_values.gp): for δ0, `A0 = la0 - la2 - la3 - la4 =
-76284505075044 ≡ 4 (mod 8)`, `B0 = -115463846914100 ≡ 0 (mod 4)`; for δ1, `A0 = la1 - la3 =
-13135422575433308 ≡ 4 (mod 8)`, `B0 = -39756005661732 ≡ 0 (mod 4)`.
-/

open FurioLombardo.M4
open FurioLombardo.Discharge.Analytic (satOf isSatOf_satOf)

namespace FurioLombardo.Discharge.M3a

namespace Q0

theorem hUGE : FurioLombardo.M4.T0.UG * (FurioLombardo.M4.T0.H * FurioLombardo.M4.T0.Ui) =
    (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide +kernel

theorem hdl6 : FurioLombardo.M4.T0.dl = 6 := by decide +kernel

theorem hA4 : (4 : ℤ) ∣ FurioLombardo.M4.T0.UG.mulVec FurioLombardo.M4.T0.la 0 := by
  decide +kernel

theorem hA8 : ¬ (8 : ℤ) ∣ FurioLombardo.M4.T0.UG.mulVec FurioLombardo.M4.T0.la 0 := by
  decide +kernel

theorem hB4 : (4 : ℤ) ∣ FurioLombardo.M4.T0.UG.mulVec FurioLombardo.M4.T0.lb 0 := by
  decide +kernel

/-- **Quarter for the twist δ0.** -/
theorem quarter {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]}
    (hBD : HBallD FurioLombardo.M4.T0.data ℓ) (hBP : HBallPhi FurioLombardo.M4.T0.data a b)
    (ha : a ∈ Submodule.span ℤ_[2] (Set.range ℓ)) (hb : b ∈ Submodule.span ℤ_[2] (Set.range ℓ)) :
    FurioLombardo.M3a.Route.Quarter (Submodule.span ℤ_[2] (Set.range ℓ))
      (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) a b :=
  quarter_of_cert FurioLombardo.M4.T0.checks hBD hBP ha hb hUGE hdl6 hA4 hA8 hB4

end Q0

namespace Q1

theorem hUGE : FurioLombardo.M4.T1.UG * (FurioLombardo.M4.T1.H * FurioLombardo.M4.T1.Ui) =
    (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide +kernel

theorem hdl6 : FurioLombardo.M4.T1.dl = 6 := by decide +kernel

theorem hA4 : (4 : ℤ) ∣ FurioLombardo.M4.T1.UG.mulVec FurioLombardo.M4.T1.la 0 := by
  decide +kernel

theorem hA8 : ¬ (8 : ℤ) ∣ FurioLombardo.M4.T1.UG.mulVec FurioLombardo.M4.T1.la 0 := by
  decide +kernel

theorem hB4 : (4 : ℤ) ∣ FurioLombardo.M4.T1.UG.mulVec FurioLombardo.M4.T1.lb 0 := by
  decide +kernel

/-- **Quarter for the twist δ1.** -/
theorem quarter {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]}
    (hBD : HBallD FurioLombardo.M4.T1.data ℓ) (hBP : HBallPhi FurioLombardo.M4.T1.data a b)
    (ha : a ∈ Submodule.span ℤ_[2] (Set.range ℓ)) (hb : b ∈ Submodule.span ℤ_[2] (Set.range ℓ)) :
    FurioLombardo.M3a.Route.Quarter (Submodule.span ℤ_[2] (Set.range ℓ))
      (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) a b :=
  quarter_of_cert FurioLombardo.M4.T1.checks hBD hBP ha hb hUGE hdl6 hA4 hA8 hB4

end Q1

end FurioLombardo.Discharge.M3a
