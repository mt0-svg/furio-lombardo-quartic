import Mathlib
import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.MvPSeries

/-!
# Evaluation of power series is Lipschitz for closed ideals

`FurioLombardo.Vendor.Toolbox.EvalLip.eval_sub_mem`: over a complete local ring `O` with the adic topology, for `z, z'`
in the maximal ideal with `z i - z' i ∈ I` for every variable (`I` a closed ideal), the values
`eval z H` and `eval z' H` of a power series `H` differ by an element of `I`. With `I = 𝔪ᵏ` this
gives the continuity of evaluation in the points.

Origin: written for this formalization (continuity of the chart of a genus 2 Jacobian,
`FurioLombardo.Discharge.R7.FinIdx.Chart`).
-/

namespace FurioLombardo.Vendor.Toolbox.EvalLip

open FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman

/-- **Evaluation is Lipschitz for closed ideals**: `z - z' ∈ I^σ` gives
`eval z H - eval z' H ∈ I`. -/
theorem eval_sub_mem {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
    [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
    [T2Space O] [IsTopologicalRing O] {σ : Type*} [Finite σ] (H : MvPowerSeries σ O)
    {z z' : σ → O} (hz : ∀ i, z i ∈ IsLocalRing.maximalIdeal O)
    (hz' : ∀ i, z' i ∈ IsLocalRing.maximalIdeal O) {I : Ideal O} (hI : IsClosed (I : Set O))
    (h : ∀ i, z i - z' i ∈ I) : MvPSeries.eval z H - MvPSeries.eval z' H ∈ I := by
  have h1 := MvPSeries.hasSum_eval (MvPSeries.hasEval_of_mem hz) H
  have h2 := MvPSeries.hasSum_eval (MvPSeries.hasEval_of_mem hz') H
  have h3 := h1.sub h2
  rw [← h3.tsum_eq]
  refine tsum_mem hI fun d => ?_
  rw [← mul_sub]
  refine Ideal.mul_mem_left _ _ ?_
  rw [← Ideal.Quotient.eq]
  simp only [Finsupp.prod, map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Ideal.Quotient.eq.mpr (h s)]

end FurioLombardo.Vendor.Toolbox.EvalLip
