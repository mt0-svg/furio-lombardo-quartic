/-
Lane M3b (furio-lombardo-quartic): the data of Chevalley's ambiguous class number formula for a
quadratic extension `L/K` of number fields, and its arithmetic.

Chevalley's formula (Chevalley 1933; see Gras, *Class Field Theory*, II.6.2.3, or Lemmermeyer,
*The ambiguous class number formula revisited*) for a cyclic extension `L/K` of degree `n` reads
`|Cl(L)^G| = h_K * ∏_v e_v / (n * [E_K : E_K ∩ N(L^×)])`, the product over all places of `K`.
For `n = 2` the product is `2^t`, `t` the number of places of `K` (finite and real) ramified in
`L`. The formula itself is proved in `FurioLombardo.M3b.Formula` (`chevalley_formula`).

This file: the subgroup `normUnits K L` of units of `K` that are norms from `L`, the facts that
its index is a power of 2 and is at least the size of the image of any character that kills it,
the ramified places and their number `ramifiedPlaceCount K L`, the arithmetic core
`eq_of_chevalley_arith`, and the nontrivial involution of a quadratic extension. Only the easy
inequality of the local norm theory is ever needed (a global norm is a local norm), never Hasse's
norm theorem.
-/
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup
import FurioLombardo.M3b.FixedPoints

open NumberField

namespace FurioLombardo.M3b


section NumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The units of `K` that are norms of elements of `L`, that is `E_K ∩ N_{L/K}(L^×)`. -/
def normUnits : Subgroup (𝓞 K)ˣ where
  carrier := {u | ∃ x : L, Algebra.norm K x = ((u : 𝓞 K) : K)}
  mul_mem' := by
    rintro u v ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by simp [map_mul, hx, hy]⟩
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro u ⟨x, hx⟩
    refine ⟨x⁻¹, ?_⟩
    rw [Algebra.norm_inv, hx]
    have h := congrArg (algebraMap (𝓞 K) K) (Units.mul_inv u)
    simp only [map_mul, map_one] at h
    exact (eq_inv_of_mul_eq_one_right h).symm

theorem mem_normUnits (u : (𝓞 K)ˣ) :
    u ∈ normUnits K L ↔ ∃ x : L, Algebra.norm K x = ((u : 𝓞 K) : K) := Iff.rfl

/-- The finite primes of `K` ramified in `L`. -/
def ramifiedPrimes : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  {P | ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.under (𝓞 K) = P.asIdeal ∧
    1 < Q.ramificationIdx (𝓞 K)}

/-- The real places of `K` ramified in `L` (below a complex place of `L`). -/
def ramifiedRealPlaces : Set (InfinitePlace K) :=
  {v | v.IsReal ∧ ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v ∧ w.IsComplex}

/-- The number `t` of places of `K`, finite and real, ramified in `L`. -/
noncomputable def ramifiedPlaceCount : ℕ :=
  (ramifiedPrimes K L).ncard + (ramifiedRealPlaces K L).ncard

end NumberFields

section Index

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Squares of units are norms: `N_{L/K}(u) = u^2` for `u ∈ K`. -/
theorem sq_mem_normUnits (h2 : Module.finrank K L = 2) (u : (𝓞 K)ˣ) :
    u ^ 2 ∈ normUnits K L := by
  refine ⟨algebraMap K L ((u : 𝓞 K) : K), ?_⟩
  rw [Algebra.norm_algebraMap, h2]
  simp

/-- The index `[E_K : E_K ∩ N(L^×)]`, when finite, is a power of 2. -/
theorem exists_index_normUnits_eq_two_pow (h2 : Module.finrank K L = 2)
    (hfin : (normUnits K L).index ≠ 0) : ∃ k : ℕ, (normUnits K L).index = 2 ^ k := by
  have : (normUnits K L).FiniteIndex := ⟨hfin⟩
  have hp : IsPGroup 2 ((𝓞 K)ˣ ⧸ normUnits K L) := by
    intro q
    refine ⟨1, ?_⟩
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact sq_mem_normUnits h2 u
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  exact ⟨k, by rw [Subgroup.index, hk]⟩

/-- A character that kills the norms bounds the index from below. -/
theorem card_range_dvd_index {M : Type*} [Group M] (χ : (𝓞 K)ˣ →* M)
    (hχ : normUnits K L ≤ χ.ker) :
    Nat.card χ.range ∣ (normUnits K L).index := by
  rw [← Subgroup.index_ker]
  exact Subgroup.index_dvd_of_le hχ

end Index

section Deduction

/-- Arithmetic core: `a * i * 2 = h * 2^t`, `i = 2^k`, `2^t ≤ 2 i` and `h` odd force `a = h`. -/
theorem eq_of_chevalley_arith {a i h t k : ℕ} (hC : a * i * 2 = h * 2 ^ t) (hk : i = 2 ^ k)
    (hle : 2 ^ t ≤ 2 * i) (hh : Odd h) : a = h := by
  subst hk
  have htk : t ≤ k + 1 := by
    have : 2 ^ t ≤ 2 ^ (k + 1) := by rw [pow_succ]; linarith
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le htk
  have h2 : a * 2 ^ m * 2 ^ t = h * 2 ^ t := by
    calc a * 2 ^ m * 2 ^ t = a * 2 ^ (t + m) := by ring
      _ = a * 2 ^ (k + 1) := by rw [hm]
      _ = a * 2 ^ k * 2 := by ring
      _ = h * 2 ^ t := hC
  have h3 : a * 2 ^ m = h := Nat.eq_of_mul_eq_mul_right (by positivity) h2
  cases m with
  | zero => simpa using h3
  | succ m =>
    exfalso
    rw [← h3, pow_succ] at hh
    exact (Nat.not_even_iff_odd.2 hh) ⟨a * 2 ^ m, by ring⟩

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- For a quadratic extension of number fields there is a nontrivial automorphism, and it is
an involution. -/
theorem exists_involution (h2 : Module.finrank K L = 2) :
    ∃ σ : L ≃ₐ[K] L, σ ≠ 1 ∧ σ * σ = 1 := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ, -⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 hcard
  refine ⟨σ, hσ, ?_⟩
  have := pow_card_eq_one' (G := L ≃ₐ[K] L) (x := σ)
  rwa [hcard, sq] at this

end Deduction

end FurioLombardo.M3b
