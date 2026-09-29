import Mathlib
import FurioLombardo.Discharge.M3a.Reduction

/-!
# The 2-torsion of `Jac f` (discharge of M3a, WP1)

For a field `K` and `f : K[X]` with `GoodSextic f`:

* `ideal_eq_of_mul_self_eq`: in a Dedekind domain, `I² = J²` implies `I = J`;
* `jac_sq_eq_one`: a point `c` of `Jac f` with `c² = 1` is `1` or the class of `⟨u, Y⟩` for a
  monic quadratic divisor `u` of `f`.

Proof of the second: by `jac_eq_one_or_reduced`, `c = [J]` with `J = ⟨u, Y - v⟩`, `deg u = 2`,
`deg v < 2`. Then `J² = (γ)`, and the norm `p² - q² f` of `γ = p + qY` is associated to `u²`, of
degree 4; since the leading coefficient of `f` is not a square, `q ≠ 0` would give degree at least
6, so `γ = p ∈ K[X]` is fixed by the conjugation, and `J² = conj(J)²` gives `J = conj(J) = ⟨u, Y + v⟩`.
Then `2v = (Y + v) - (Y - v)` lies in `⟨u, Y + v⟩ ∩ K[X] ⊆ (u)`, so `v = 0` by degrees, and
`u ∣ f`.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.M3a

variable {K : Type*} [Field K]

/-- Cancellation of squares of ideals in a Dedekind domain. -/
theorem ideal_eq_of_mul_self_eq {R : Type*} [CommRing R] [IsDedekindDomain R] {I J : Ideal R}
    (h : I * I = J * J) : I = J := by
  have h2 : I ^ 2 = J ^ 2 := by rw [sq, sq, h]
  apply le_antisymm
  · rw [← Ideal.dvd_iff_le]
    exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp (dvd_of_eq h2.symm)
  · rw [← Ideal.dvd_iff_le]
    exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp (dvd_of_eq h2)

/-- Classification of the 2-torsion of `A(K) = Jac f`: `c² = 1` implies `c = 1` or
`c = [⟨u, Y⟩]` for a monic quadratic divisor `u` of `f`. -/
theorem jac_sq_eq_one (f : K[X]) [GoodSextic f] {c : Jac f} (hc : c ^ 2 = 1) :
    c = 1 ∨ ∃ (u : K[X]) (hu : u.Monic), u.natDegree = 2 ∧ u ∣ f ∧
      (c : Pic f) = ClassGroup.mk0 (mumford0 f hu.ne_zero 0) := by
  rcases jac_eq_one_or_reduced f c with h1 | ⟨u, v, w, hu, hdeg, hv, hw, hcM⟩
  · exact Or.inl h1
  right
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have hcop := exists_coprime_of_squarefree GoodSextic.squarefree hw
  set φ := algebraMap K[X] (CoordRing f) with hφ
  -- `J²` is principal
  have hc2 : ((c ^ 2 : Jac f) : Pic f) = 1 := by rw [hc]; rfl
  rw [Subgroup.coe_pow, hcM, sq, ← map_mul] at hc2
  obtain ⟨γ, hγ⟩ := (ClassGroup.mk0_eq_one_iff (mumford0 f hu.ne_zero v *
    mumford0 f hu.ne_zero v).2).mp hc2
  have hJJ : mumford f u v * mumford f u v = Ideal.span {γ} := hγ
  -- the norm of `γ` has degree 4, so `γ ∈ K[X]`
  have hN := congrArg (Ideal.relNorm K[X]) hJJ
  rw [map_mul, relNorm_mumford f hu hw hcop, relNorm_span_singleton,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton] at hN
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f γ
  rw [norm_smul_basis] at hN
  have hdN : (p ^ 2 - q ^ 2 * f).natDegree = 4 := by
    rw [← natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hN),
      natDegree_mul hu.ne_zero hu.ne_zero, hdeg]
  have hq : q = 0 := by
    by_contra hq
    have := six_le_natDegree_sq_sub_sq_mul (p := p) GoodSextic.not_isSquare_leadingCoeff
      (GoodSextic.natDegree_eq (f := f)) hq
    omega
  subst hq
  rw [zero_smul, add_zero, smul_eq, mul_one] at hJJ
  -- `J² = conj(J)²`, so `J = conj(J)`
  have hJJ' : mumford f u (-v) * mumford f u (-v) = Ideal.span {φ p} := by
    have h := congrArg (Ideal.map (conj f)) hJJ
    rwa [Ideal.map_mul, map_conj_mumford, Ideal.map_span, Set.image_singleton,
      AlgEquiv.commutes] at h
  have hMM : mumford f u v = mumford f u (-v) := ideal_eq_of_mul_self_eq (hJJ.trans hJJ'.symm)
  -- `2v ∈ ⟨u, Y + v⟩ ∩ K[X] ⊆ (u)`
  have hmem : Yc f - φ v ∈ mumford f u (-v) :=
    hMM ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hmem2 : Yc f - φ (-v) ∈ mumford f u (-v) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have h2v : φ (2 * v) ∈ mumford f u (-v) := by
    have e : Yc f - φ (-v) - (Yc f - φ v) = φ (2 * v) := by
      rw [map_neg, map_mul, map_ofNat]; ring
    rw [← e]; exact Ideal.sub_mem _ hmem2 hmem
  have hdvd : u ∣ 2 * v :=
    dvd_of_algebraMap_mem_mumford (by rw [neg_sq, hw]; exact dvd_mul_right u w) h2v
  have hC2 : (2 : K[X]) = C 2 := (map_ofNat C 2).symm
  have h2v0 : 2 * v = 0 := by
    refine eq_zero_of_dvd_of_degree_lt hdvd ?_
    rw [hC2, degree_C_mul h2, degree_eq_natDegree hu.ne_zero, hdeg]
    exact hv
  have hv0 : v = 0 := by
    rcases mul_eq_zero.mp h2v0 with h | h
    · rw [hC2, C_eq_zero] at h; exact absurd h h2
    · exact h
  subst hv0
  exact ⟨u, hu, hdeg, ⟨-w, by linear_combination -hw⟩, hcM⟩

end FurioLombardo.Discharge.M3a
