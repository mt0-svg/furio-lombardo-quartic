import Mathlib
import FurioLombardo.Discharge.R7.FinIdx.Comp
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLimRoot
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLimFibre
import FurioLombardo.Discharge.R7.FinIdx.PencilAux

/-!
# PENCIL: unbounded families (R7)

For a proper normed field `K`, `GoodSextic g`, a rich supply of pairs over split quadratics
`(X - s1)(X - s2)` (`hpts`), and a family `D n ∈ Z` of unbounded size, there are a pair `T ∈ Z`,
a subsequence and a limit `y* ∈ Z` of `comp (D n) T`. Cases: bounded `t` (Lemma A at a double
root `α`), `|t| → ∞` with `|t1| ≪ |t0|²` (impossible: scaling and `ℓ` not a square), and
`|t1| ≥ ε |t0|²` (reflection `reflect 6`, Lemma A at `α = 0`).
-/

open Polynomial Filter Topology
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.PolyLim

namespace FurioLombardo.Discharge.R7.FinIdx

variable {K : Type*} [NormedField K] [ProperSpace K] {g : K[X]} [GoodSextic g]

/-- **PENCIL.** -/
theorem pencil
    (hpts : ∀ A : Finset K, ∃ s1 s2 : K, s1 ∉ A ∧ s2 ∉ A ∧ s1 ≠ s2 ∧ s1 ≠ 0 ∧ s2 ≠ 0 ∧
      ∃ vT : K[X], InZ g ⟨![-(s1 + s2), s1 * s2], vT⟩)
    {Dn : ℕ → MPair K} (hZ : ∀ n, InZ g (Dn n))
    (hinf : Tendsto (fun n => dsize (Dn n)) atTop atTop) :
    ∃ T : MPair K, InZ g T ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, res2 (Dn (φ n)).t T.t ≠ 0) ∧
      ∃ ys : MPair K, InZ g ys ∧ DTendsto atTop (fun n => comp g (Dn (φ n)) T) ys := by
  exact pencil_finish hZ (pencil_core hpts hZ hinf)

end FurioLombardo.Discharge.R7.FinIdx
