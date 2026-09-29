import Mathlib

/-!
# Finite index from sequences

`FurioLombardo.Vendor.Toolbox.GroupTheory.finiteIndex_of_seq`: a subgroup `H` of an additive commutative group has finite
index as soon as every sequence has two distinct terms whose difference lies in `H` (an injective
sequence of cosets, from `Infinite.natEmbedding`, would contradict it). This turns a finite index
statement into a sequential compactness argument, with no topology on the group.

Origin: written for this formalization (finite index of the chart ball of a genus 2 Jacobian over
a 2-adic field, `FurioLombardo.Discharge.R7.FinIdx.Assembly`).
-/

namespace FurioLombardo.Vendor.Toolbox.GroupTheory

/-- **Finite index from sequences**: if every sequence has two distinct terms with difference in
`H`, then `H` has finite index. -/
theorem finiteIndex_of_seq {B : Type*} [AddCommGroup B] (H : AddSubgroup B)
    (hT : ∀ x : ℕ → B, ∃ n m, n ≠ m ∧ x n - x m ∈ H) : H.FiniteIndex := by
  rw [AddSubgroup.finiteIndex_iff_finite_quotient]
  by_contra hfin
  have hinf : Infinite (B ⧸ H) := not_finite_iff_infinite.mp hfin
  let e := Infinite.natEmbedding (B ⧸ H)
  obtain ⟨n, m, hnm, hmem⟩ := hT fun n => Quotient.out (e n)
  apply hnm
  apply e.injective
  rw [← QuotientAddGroup.out_eq' (e n), ← QuotientAddGroup.out_eq' (e m)]
  refine QuotientAddGroup.eq.mpr ?_
  have := H.neg_mem hmem
  rwa [neg_sub, sub_eq_neg_add] at this

end FurioLombardo.Vendor.Toolbox.GroupTheory
