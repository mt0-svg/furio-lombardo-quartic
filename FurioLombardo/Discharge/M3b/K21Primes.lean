import FurioLombardo.Discharge.M3b.K21Defs
import FurioLombardo.M1.Norms

/-!
# The primes `(la)`, `(lc)` above 2 and `(pi7)` above 7 of `K21`

`la = gO 12` (e = 3), `lc = gO 14` (e = 6), `pi7 = gO 15` (e = 7, f = 3) in M1's numbering.
The absolute norms are the absolute values of the element norms (M1/Norms.lean). An ideal of prime
absolute norm is maximal. For `(pi7)`: a maximal ideal `Q ⊇ (pi7)` has absolute norm `7 ^ m` with
`m ≤ 3`; if `m ≤ 2` then `x ^ 49 = x` on the residue field `𝓞 K21 ⧸ Q`, which contradicts
`(θ ^ 49 - θ) u7 = 1 + 7 v7` (`residue_seven`, `7 ∈ Q`); so `m = 3` and `Q = (pi7)`.
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 NumberField

theorem absNorm_span_gO12 : Ideal.absNorm (Ideal.span {gO 12} : Ideal (𝓞 K21)) = 2 := by
  rw [Ideal.absNorm_span_singleton]; exact natAbs_nZ_la

theorem absNorm_span_gO14 : Ideal.absNorm (Ideal.span {gO 14} : Ideal (𝓞 K21)) = 2 := by
  rw [Ideal.absNorm_span_singleton]; exact natAbs_nZ_lc

theorem absNorm_span_gO15 : Ideal.absNorm (Ideal.span {gO 15} : Ideal (𝓞 K21)) = 343 := by
  rw [Ideal.absNorm_span_singleton]; exact natAbs_nZ_pi7

/-- An ideal of `𝓞 K21` of prime absolute norm is maximal. -/
theorem isMaximal_of_absNorm_prime {I : Ideal (𝓞 K21)} (h : Nat.Prime (Ideal.absNorm I)) :
    I.IsMaximal := by
  refine (Ideal.isPrime_of_irreducible_absNorm h).isMaximal ?_
  rintro rfl
  rw [Ideal.absNorm_bot] at h
  exact Nat.not_prime_zero h

theorem isMaximal_span_gO12 : (Ideal.span {gO 12} : Ideal (𝓞 K21)).IsMaximal :=
  isMaximal_of_absNorm_prime (by rw [absNorm_span_gO12]; exact Nat.prime_two)

theorem isMaximal_span_gO14 : (Ideal.span {gO 14} : Ideal (𝓞 K21)).IsMaximal :=
  isMaximal_of_absNorm_prime (by rw [absNorm_span_gO14]; exact Nat.prime_two)

/-- A maximal ideal containing `7` has more than `49` residues. -/
theorem absNorm_ne_of_seven_mem {Q : Ideal (𝓞 K21)} (hQ : Q.IsMaximal) (h7 : (7 : 𝓞 K21) ∈ Q)
    (hc : Ideal.absNorm Q = 7 ∨ Ideal.absNorm Q = 49) : False := by
  let _ := Ideal.Quotient.field Q
  have hcard : Nat.card (𝓞 K21 ⧸ Q) = Ideal.absNorm Q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 K21 ⧸ Q) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]; rcases hc with h | h <;> rw [h] <;> norm_num
  let _ := Fintype.ofFinite (𝓞 K21 ⧸ Q)
  have hpow : ∀ x : 𝓞 K21 ⧸ Q, x ^ 49 = x := by
    intro x
    have hx := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hcard] at hx
    rcases hc with h | h
    · rw [h] at hx
      rw [show 49 = 7 * 7 by norm_num, pow_mul, hx, hx]
    · rw [h] at hx; exact hx
  have h := congrArg (Ideal.Quotient.mk Q) residue_seven
  rw [map_mul, map_sub, map_pow, hpow, sub_self, zero_mul, map_add, map_one, map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr h7, zero_mul, add_zero] at h
  exact zero_ne_one h

theorem isMaximal_span_gO15 : (Ideal.span {gO 15} : Ideal (𝓞 K21)).IsMaximal := by
  have hI : Ideal.absNorm (Ideal.span {gO 15} : Ideal (𝓞 K21)) = 343 := absNorm_span_gO15
  have hne : (Ideal.span {gO 15} : Ideal (𝓞 K21)) ≠ ⊤ := by
    intro h; rw [h, Ideal.absNorm_top] at hI; norm_num at hI
  obtain ⟨Q, hQ, hIQ⟩ := Ideal.exists_le_maximal _ hne
  have h7 : (7 : 𝓞 K21) ∈ Q := by
    apply hIQ
    rw [seven_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) 7 (by norm_num))
  have hdvd : Ideal.absNorm Q ∣ 7 ^ 3 := by
    rw [show (7 : ℕ) ^ 3 = 343 by norm_num, ← hI]; exact Ideal.absNorm_dvd_absNorm_of_le hIQ
  obtain ⟨m, hm, hQm⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hdvd
  have hQ3 : Ideal.absNorm Q = 343 := by
    interval_cases m
    · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using hQm)) hQ.ne_top
    · exact (absNorm_ne_of_seven_mem hQ h7 (Or.inl (by simpa using hQm))).elim
    · exact (absNorm_ne_of_seven_mem hQ h7 (Or.inr (by simpa using hQm))).elim
    · simpa using hQm
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hIQ
  have hJ1 : Ideal.absNorm J = 1 := by
    have := congrArg Ideal.absNorm hJ
    rw [map_mul, hI, hQ3] at this
    omega
  rw [Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top] at hJ
  rw [hJ]; exact hQ

end FurioLombardo.Discharge.M3b
