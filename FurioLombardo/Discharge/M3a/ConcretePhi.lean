import Mathlib
import FurioLombardo.Discharge.M3a.ConcreteKv
import FurioLombardo.Discharge.M3a.AbelPrymTotal

/-!
# The route at `K_v` with the concrete Abel-Prym map

`Bruin.phiK k` is Bruin's Abel-Prym map `D_δ(K21) → Jac (fRev k)` of the twist `k` on the reversed
model (WP4: `AbelPrym.phiRev` for the Bruin matrices, the twist `δ k` and the sextic `fRev k`). It
is given by a certificate at every point (`Bruin.phiRev_eq_cls`, so the fallback value of
`bruinPhi` is never used), it sends the covering involution to the inverse (`phiK_inv`), and its
values at the known lifts are explicit (`Bruin.phiRev_x0`, `phiRev_x2`, `phiRev_x1`,
`phiRev_x3`, AbelPrymKnown.lean).

`Bruin.onlyFourPoints_phiK`: the frozen statement from M1's descent and `TwistInputsKv` for the
two twists with `φ = phiK k` and the known lifts.
-/

open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.M3a.Bruin

open FurioLombardo.M1

/-- Bruin's Abel-Prym map of the twist `k`, on the reversed model `Y² = fRev k`. -/
noncomputable abbrev phiK (k : Fin 2) :
    DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k) :=
  AbelPrym.phiRev (Mmat 0) (Mmat 1) (Mmat 2) (δ k) (fRev k)

/-- `φ ∘ ι = -φ` for the covering involution `ι : (p, r, s) ↦ (p, -r, -s)`. -/
theorem phiK_inv (k : Fin 2) (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    phiK k x.inv = (phiK k x)⁻¹ :=
  AbelPrym.phiRev_inv x

/-- **The frozen statement from the inputs at `K_v`, with the concrete Abel-Prym map.** -/
theorem onlyFourPoints_phiK (hdesc : Descent K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 δ1)
    (h0 : TwistInputsKv 0 FurioLombardo.M4.T0.data (phiK 0) x0 x2)
    (h1 : TwistInputsKv 1 FurioLombardo.M4.T1.data (phiK 1) x1 x3) :
    FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_Kv hdesc (phiK 0) (phiK 1) h0 h1

end FurioLombardo.Discharge.M3a.Bruin
