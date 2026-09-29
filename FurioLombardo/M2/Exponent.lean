import FurioLombardo.M2.Basis

/-!
# The index of `ℤ[θ]` away from `ResZ` (lane M2)

Mathlib's `conductor_mul_differentIdeal` puts `fZ'(θ)` in the conductor of `ℤ[θ]`; with
`U fZ + V fZ' = ResZ` (kernel check `resultant_check`) so is `ResZ`. Hence a prime `p` not
dividing `ResZ` does not divide `RingOfIntegers.exponent θ`, the hypothesis of Mathlib's
Dedekind-Kummer theorem `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`.
-/

namespace FurioLombardo.M2

open Polynomial NumberField RingOfIntegers Ideal

theorem derivative_mem_conductor : aeval θ (derivative (minpoly ℤ θ)) ∈ conductor ℤ θ := by
  have hx : Algebra.adjoin ℚ {algebraMap (𝓞 K21) K21 θ} = ⊤ := by
    rw [show algebraMap (𝓞 K21) K21 θ = AdjoinRoot.root fQ from rfl]
    exact AdjoinRoot.adjoinRoot_eq_top
  have h := conductor_mul_differentIdeal ℤ ℚ K21 θ hx
  have hmem : aeval θ (derivative (minpoly ℤ θ)) ∈ conductor ℤ θ * differentIdeal ℤ (𝓞 K21) := by
    rw [h]; exact mem_span_singleton_self _
  exact (Ideal.mul_le_left : conductor ℤ θ * differentIdeal ℤ (𝓞 K21) ≤ conductor ℤ θ) hmem

theorem ResZ_eq : (ResZ : 𝓞 K21) = evalZ θ VL * evalZ θ fdL := by
  have h := evalZ_eq_zero_of_forall θ _ ((allZero_iff _).mp resultant_check)
  simp only [evalZ_addZ, evalZ_mulZ, evalZ_θ_fL, evalZ_cons, evalZ_nil, mul_zero, add_zero,
    zero_add, Int.cast_neg] at h
  linear_combination -h

theorem ResZ_mem_conductor : (ResZ : 𝓞 K21) ∈ conductor ℤ θ := by
  rw [ResZ_eq, ← aeval_derivative_fZ_eq, ← minpoly_θ]
  exact mul_mem_left _ _ derivative_mem_conductor

theorem not_dvd_exponent (p : ℕ) [hp : Fact p.Prime] (h : ¬ (p : ℤ) ∣ ResZ) :
    ¬ p ∣ exponent θ := by
  rw [not_dvd_exponent_iff, codisjoint_iff, eq_top_iff_one]
  have h1 : ResZ ∈ comap (algebraMap ℤ (𝓞 K21)) (conductor ℤ θ) := by
    rw [mem_comap, algebraMap_int_eq, eq_intCast]; exact ResZ_mem_conductor
  obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd).mpr h
  rw [← huv, add_comm]
  exact Submodule.add_mem_sup (mul_mem_left _ _ h1) (mul_mem_left _ _ (mem_span_singleton_self _))

theorem DD_dvd_ResZ' : DD ∣ ResZ := Int.dvd_of_emod_eq_zero DD_dvd_ResZ

end FurioLombardo.M2
