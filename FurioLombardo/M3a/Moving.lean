import Mathlib

/-!
# The moving lemma in Dedekind domains (lane M3a)

For a Dedekind domain `R` and a nonzero ideal `J`, every ideal class contains an integral ideal
coprime to `J` (`exists_mk0_eq_sup_eq_top`), and two such representatives of the same class
differ by principal ideals with generators coprime to `J` (`exists_coprime_generators`).
These are used to define the `x - T` map on the whole class group.
-/

open scoped nonZeroDivisors

namespace FurioLombardo.M3a

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- In a Dedekind domain, `I ≤ I * P` forces `I = ⊥` or `P = ⊤`. -/
theorem not_le_mul_of_ne_top {I P : Ideal R} (hI : I ≠ ⊥) (hP : P ≠ ⊤) : ¬ I ≤ I * P := by
  intro h
  have heq : I * P = I * ⊤ := by rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h
  exact hP (mul_left_cancel₀ (by simpa using hI) heq)

/-- Avoidance: an element of `I` outside `I * P` for finitely many maximal ideals `P`. -/
theorem exists_mem_forall_notMem_mul
    {I : Ideal R} (hI : I ≠ ⊥) (s : Finset (Ideal R)) (hs : ∀ P ∈ s, P.IsMaximal) :
    ∃ a ∈ I, a ≠ 0 ∧ ∀ P ∈ s, a ∉ I * P := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨a, ha, ha0, by simp⟩
  have hA : ∀ P ∈ s, ∃ x ∈ I, x ∉ I * P := fun P hP =>
    Set.not_subset.mp (FurioLombardo.M3a.not_le_mul_of_ne_top hI (hs P hP).ne_top)
  choose! A hAI hAnot using hA
  have hB : ∀ P ∈ s, ∃ b ∈ ∏ Q ∈ s.erase P, Q, b - 1 ∈ P := fun P hP => by
    have hcop : IsCoprime P (∏ Q ∈ s.erase P, Q) := by
      apply IsCoprime.prod_right
      intro Q hQ
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne (hs P hP) (hs Q (Finset.mem_of_mem_erase hQ))
        (Finset.ne_of_mem_erase hQ).symm
    rw [Ideal.isCoprime_iff_sup_eq] at hcop
    have h1 : (1 : R) ∈ P ⊔ ∏ Q ∈ s.erase P, Q := by rw [hcop]; exact Submodule.mem_top
    obtain ⟨p, hp, b, hb, hpb⟩ := Submodule.mem_sup.mp h1
    refine ⟨b, hb, ?_⟩
    have : b - 1 = -p := by rw [← hpb]; ring
    rw [this]; exact P.neg_mem hp
  choose! B hBprod hB1 using hB
  set a := ∑ P ∈ s, B P * A P with ha
  have key : ∀ P ∈ s, a - A P ∈ I * P := by
    intro P hP
    have hsplit : a - A P = A P * (B P - 1) + ∑ Q ∈ s.erase P, A Q * B Q := by
      rw [ha, ← Finset.add_sum_erase s _ hP]
      simp only [mul_comm (B _) (A _)]
      ring
    rw [hsplit]
    refine Ideal.add_mem _ (Ideal.mul_mem_mul (hAI P hP) (hB1 P hP)) (Ideal.sum_mem _ ?_)
    intro Q hQ
    have hQs : Q ∈ s := Finset.mem_of_mem_erase hQ
    have hPQ : P ∈ s.erase Q := Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hQ).symm, hP⟩
    have hle : ∏ Q' ∈ s.erase Q, Q' ≤ P :=
      (Ideal.prod_le_inf).trans (Finset.inf_le hPQ)
    exact Ideal.mul_mem_mul (hAI Q hQs) (hle (hBprod Q hQs))
  refine ⟨a, Ideal.sum_mem _ fun P hP => I.mul_mem_left _ (hAI P hP), ?_, ?_⟩
  · intro h0
    obtain ⟨P, hP⟩ := hne
    have := key P hP
    rw [h0, zero_sub, Submodule.neg_mem_iff] at this
    exact hAnot P hP this
  · intro P hP haP
    have := Ideal.sub_mem _ haP (key P hP)
    rw [sub_sub_cancel] at this
    exact hAnot P hP this

/-- The maximal ideals containing a nonzero ideal form a finite set. -/
theorem exists_finset_maximal_of_ne_bot
    {J : Ideal R} (hJ : J ≠ ⊥) :
    ∃ s : Finset (Ideal R), (∀ P ∈ s, P.IsMaximal) ∧ ∀ M : Ideal R, M.IsMaximal → J ≤ M → M ∈ s := by
  classical
  set s := ((UniqueFactorizationMonoid.normalizedFactors J).toFinset).filter (λ P => P.IsMaximal) with hs
  refine ⟨s, ?_, ?_⟩
  · intro P hP
    rw [hs] at hP
    rcases Finset.mem_filter.mp hP with ⟨hP_mem, hP_max⟩
    rw [Multiset.mem_toFinset] at hP_mem
    have hP_prime : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hP_mem).1
    have hP_ne_bot : P ≠ ⊥ := by
      intro hP_eq_bot
      apply hJ
      have hJP : J ≤ P := ((Ideal.mem_normalizedFactors_iff hJ).mp hP_mem).2
      rw [hP_eq_bot] at hJP
      exact bot_unique hJP
    exact Ideal.IsPrime.isMaximal hP_prime hP_ne_bot
  · intro M hM_max hJM
    have hM_prime : M.IsPrime := hM_max.isPrime
    have hM_ne_bot : M ≠ ⊥ := by
      intro hM_eq_bot
      apply hJ
      have h : J ≤ ⊥ := hM_eq_bot ▸ hJM
      exact bot_unique h
    have hM_dvd_J : M ∣ J := by
      rw [Ideal.dvd_iff_le]
      exact hJM
    have hM_irred : Irreducible M := by
      have hM_prime' : Prime M := Ideal.prime_of_isPrime hM_ne_bot hM_prime
      exact hM_prime'.irreducible
    have h_exists := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hJ hM_irred hM_dvd_J
    rcases h_exists with ⟨Q, hQ_mem, hQ_assoc⟩
    have hM_eq_Q : M = Q := (associated_iff_eq.mp hQ_assoc)
    rw [hs]
    have hQ_mem_finset : Q ∈ ((UniqueFactorizationMonoid.normalizedFactors J).toFinset).filter (λ P => P.IsMaximal) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · rw [Multiset.mem_toFinset]
        exact hQ_mem
      · have hQ_prime : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hJ).mp hQ_mem).1
        have hQ_ne_bot : Q ≠ ⊥ := by
          intro hQ_eq_bot
          apply hJ
          have hJQ : J ≤ Q := ((Ideal.mem_normalizedFactors_iff hJ).mp hQ_mem).2
          rw [hQ_eq_bot] at hJQ
          exact bot_unique hJQ
        exact Ideal.IsPrime.isMaximal hQ_prime hQ_ne_bot
    rw [hM_eq_Q]
    exact hQ_mem_finset

/-- A nonzero ideal times an ideal avoiding finitely many maximal ideals is principal. -/
theorem exists_span_eq_mul_avoid
    {I : Ideal R} (hI : I ≠ ⊥) (s : Finset (Ideal R)) (hs : ∀ P ∈ s, P.IsMaximal) :
    ∃ c : R, c ≠ 0 ∧ ∃ I' : Ideal R, Ideal.span {c} = I * I' ∧ ∀ P ∈ s, ¬ I' ≤ P := by
  obtain ⟨a, haI, ha0, ha_not⟩ := FurioLombardo.M3a.exists_mem_forall_notMem_mul hI s hs
  have hspan : Ideal.span {a} ≤ I := by simpa using haI
  have hdiv : I ∣ Ideal.span {a} := (Ideal.dvd_iff_le.mpr hspan)
  rcases hdiv with ⟨I', hI'⟩
  refine ⟨a, ha0, I', hI', ?_⟩
  intro P hP hI'P
  have h_mul : I * I' ≤ I * P := Ideal.mul_mono_right hI'P
  have ha_mem : a ∈ I * I' := by
    rw [← hI']
    exact Ideal.mem_span_singleton_self a
  have ha_mem' : a ∈ I * P := h_mul ha_mem
  exact ha_not P hP ha_mem'

/-- The moving lemma: every ideal class contains an integral ideal coprime to `J`. -/
theorem exists_mk0_eq_sup_eq_top (c : ClassGroup R) {J : Ideal R} (hJ : J ≠ ⊥) :
    ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = c ∧ (I : Ideal R) ⊔ J = ⊤ := by
  obtain ⟨s, hsmax, hsJ⟩ := exists_finset_maximal_of_ne_bot hJ
  obtain ⟨I0, hI0⟩ := ClassGroup.mk0_surjective c⁻¹
  obtain ⟨c', hc'0, I', hspan, hI'⟩ :=
    exists_span_eq_mul_avoid (nonZeroDivisors.ne_zero I0.2) s hsmax
  have hI'ne : I' ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hspan
    exact hc'0 hspan
  set I1 : (Ideal R)⁰ := ⟨I', mem_nonZeroDivisors_of_ne_zero hI'ne⟩
  refine ⟨I1, ?_, ?_⟩
  · have hprin : ClassGroup.mk0 (I0 * I1) = 1 := by
      rw [ClassGroup.mk0_eq_one_iff (I0 * I1).2]
      exact ⟨⟨c', by rw [Submonoid.coe_mul]; exact hspan.symm⟩⟩
    rw [map_mul, hI0] at hprin
    rw [← inv_inv c, eq_inv_iff_mul_eq_one, mul_comm]
    exact hprin
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hI' M (hsJ M hM (le_sup_right.trans hle)) (le_sup_left.trans hle)

/-- Two representatives coprime to `J` of the same class differ by principal ideals with
generators coprime to `J`. -/
theorem exists_coprime_generators
    {J : Ideal R} (hJ : J ≠ ⊥) {I I' : (Ideal R)⁰} (hI : (I : Ideal R) ⊔ J = ⊤)
    (hI' : (I' : Ideal R) ⊔ J = ⊤) (h : ClassGroup.mk0 I = ClassGroup.mk0 I') :
    ∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} ⊔ J = ⊤ ∧ Ideal.span {y} ⊔ J = ⊤ ∧
      Ideal.span {x} * (I : Ideal R) = Ideal.span {y} * (I' : Ideal R) := by
  obtain ⟨I'', hcl, hI''⟩ := exists_mk0_eq_sup_eq_top (ClassGroup.mk0 I)⁻¹ hJ
  have hp : ((I : Ideal R) * I'').IsPrincipal := by
    have := (ClassGroup.mk0_eq_one_iff (I * I'').2).mp (by rw [map_mul, hcl, mul_inv_cancel])
    rwa [Submonoid.coe_mul] at this
  have hp' : ((I' : Ideal R) * I'').IsPrincipal := by
    have := (ClassGroup.mk0_eq_one_iff (I' * I'').2).mp (by rw [map_mul, hcl, h, mul_inv_cancel])
    rwa [Submonoid.coe_mul] at this
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hp'
  replace hc : (I : Ideal R) * I'' = Ideal.span {c} := hc
  replace hd : (I' : Ideal R) * I'' = Ideal.span {d} := hd
  have hcop : ∀ A B : Ideal R, A ⊔ J = ⊤ → B ⊔ J = ⊤ → A * B ⊔ J = ⊤ := by
    intro A B hA hB
    rw [← Ideal.isCoprime_iff_sup_eq] at hA hB ⊢
    exact hA.mul_left hB
  have hne : ∀ A : (Ideal R)⁰, (A : Ideal R) ≠ ⊥ := fun A => nonZeroDivisors.ne_zero A.2
  refine ⟨d, c, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact (mul_ne_zero (hne I') (hne I'')) (by rw [hd, Ideal.span_singleton_eq_bot.mpr rfl]; rfl)
  · rintro rfl
    exact (mul_ne_zero (hne I) (hne I'')) (by rw [hc, Ideal.span_singleton_eq_bot.mpr rfl]; rfl)
  · rw [← hd]; exact hcop _ _ hI' hI''
  · rw [← hc]; exact hcop _ _ hI hI''
  · rw [← hc, ← hd]; ring

end FurioLombardo.M3a
