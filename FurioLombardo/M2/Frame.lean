import Mathlib

/-!
# Principal ideal rings from a bound on ideal classes (lane M2)

Mathlib's `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`
with the Minkowski bound replaced by any natural number `B` such that every ideal class contains
an integral ideal of absolute norm at most `B` (for K21, `B = 120000`: `classBound_of_zimmertSatz2`
with `zimmertSatz2K21`).
The proofs follow Mathlib's.
-/

namespace FurioLombardo.M2

open NumberField Ideal Nat

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Every ideal class contains an integral ideal of absolute norm at most `B`. -/
def ClassBound (K : Type*) [Field K] [NumberField K] (B : ℕ) : Prop :=
  ∀ C : ClassGroup (𝓞 K), ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
    absNorm (I : Ideal (𝓞 K)) ≤ B

/-- A class bound stays a class bound when it is raised. -/
theorem ClassBound.mono {B B' : ℕ} (h : ClassBound K B) (hB : B ≤ B') : ClassBound K B' :=
  fun C => let ⟨I, hI, hn⟩ := h C; ⟨I, hI, hn.trans hB⟩

theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le_bound (B : ℕ) (hB : ClassBound K B)
    (h : ∀ ⦃I : (Ideal (𝓞 K))⁰⦄, absNorm (I : Ideal (𝓞 K)) ≤ B →
      Submodule.IsPrincipal (I : Ideal (𝓞 K))) : IsPrincipalIdealRing (𝓞 K) := by
  rw [← classNumber_eq_one_iff, classNumber, Fintype.card_eq_one_iff]
  refine ⟨1, fun C ↦ ?_⟩
  obtain ⟨I, rfl, hI⟩ := hB C
  simpa [← ClassGroup.mk0_eq_one_iff] using h hI

theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime_bound (B : ℕ)
    (hB : ClassBound K B)
    (h : ∀ ⦃I : (Ideal (𝓞 K))⁰⦄, (I : Ideal (𝓞 K)).IsPrime →
      absNorm (I : Ideal (𝓞 K)) ≤ B → Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le_bound B hB (fun I hI ↦ ?_)
  rw [← mem_isPrincipalSubmonoid_iff,
    ← Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  refine Submonoid.multiset_prod_mem _ _ (fun J hJ ↦ mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hJ0 : J = 0
  · simpa [hJ0] using! bot_isPrincipal
  rw [← Subtype.coe_mk J (mem_nonZeroDivisors_of_ne_zero hJ0)]
  refine h (((Ideal.mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mp hJ).1) ?_
  exact (le_of_dvd (absNorm_pos_of_nonZeroDivisors I) <|
    absNorm_dvd_absNorm_of_le <| le_of_dvd <|
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hJ).trans hI

/-- The frame of lane M2: if every ideal class has an integral ideal of norm at most `B` and every
prime ideal `P` above a prime `p ≤ B` with `p ^ f(P) ≤ B` is principal, then `𝓞 K` is a principal
ideal ring. -/
theorem isPrincipalIdealRing_of_bound (B : ℕ) (hB : ClassBound K B)
    (h : ∀ p : ℕ, p.Prime → p ≤ B → ∀ (P : Ideal (𝓞 K)),
      P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) → p ^ P.inertiaDeg ℤ ≤ B →
      Submodule.IsPrincipal P) : IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime_bound B hB <|
    fun ⟨P, HP⟩ hP hPN ↦ ?_
  obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal <| under ℤ P
  have hp0 : p ≠ 0 := fun h ↦ nonZeroDivisors.coe_ne_zero ⟨P, HP⟩ <|
    eq_bot_of_under_eq_bot (R := ℤ) <| by simpa only [hp, submodule_span_eq, span_singleton_eq_bot]
  have hpprime := (span_singleton_prime hp0).mp
  simp only [← submodule_span_eq, ← hp] at hpprime
  have hlies : P.LiesOver (span {p}) := by
    rcases abs_choice p with h | h <;>
    simpa [h, span_singleton_neg p, ← submodule_span_eq, ← hp] using over_under P
  have hspan : span {↑p.natAbs} = span {p} := by
    rcases abs_choice p with h | h <;> simp [h]
  have hple : p.natAbs ^ P.inertiaDeg ℤ ≤ B := by
    have : P.IsMaximal := hP.isMaximal (by simpa using HP.2)
    have : (span {p}).IsMaximal := (hpprime (.under ℤ P)).isMaximal_span_singleton
    rw [natAbs_pow_inertiaDeg p P]
    exact hPN
  have hpabsprime := Int.prime_iff_natAbs_prime.mp (hpprime (hP.under _))
  have hpos : 0 < P.inertiaDeg ℤ := by
    have := (isPrime_of_prime (prime_span_singleton_iff.mpr <|
      hpprime (hP.under _))).isMaximal <| by simp [((hpprime (hP.under _))).ne_zero]
    exact inertiaDeg_pos ..
  refine h _ hpabsprime (le_trans (le_self_pow₀ hpabsprime.one_lt.le hpos.ne') hple) _
    ⟨hP, ?_⟩ hple
  exact hspan ▸ hlies

/-- A principal ideal ring has no nontrivial ideal class of order 2. -/
theorem classGroup_sq_eq_one_imp [IsPrincipalIdealRing (𝓞 K)] (c : ClassGroup (𝓞 K))
    (_ : c ^ 2 = 1) : c = 1 := by
  have : Subsingleton (ClassGroup (𝓞 K)) := by
    rw [← Fintype.card_le_one_iff_subsingleton, ← classNumber, (classNumber_eq_one_iff).mpr ‹_›]
  exact Subsingleton.elim _ _

end FurioLombardo.M2
