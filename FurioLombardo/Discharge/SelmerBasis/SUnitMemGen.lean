import FurioLombardo.M1.SelmerBound

/-!
# Membership in `K(S, 2)` (pieces (c) and (e), generic part)

For a number field `F` and a set `S` of primes of `𝓞 F`:

* `mem_selmerGroup_of_even_count`: a unit with even multiplicity at every prime outside `S` has
  its class in `K(S, 2)` (the hypothesis of `SUnitSpan`);
* `mem_selmerGroup_of_mul_eq`: if `x w = 2^a 7^b` with `x, w ∈ 𝓞 F` and every prime outside `S`
  avoids `2` and `7`, the class of `x` is in `K(S, 2)` (`x` is a unit outside `S`).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField IsDedekindDomain FurioLombardo.M1
open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

/-- Even multiplicities outside `S` put the class in `K(S, 2)`. -/
theorem mem_selmerGroup_of_even_count (S : Set (HeightOneSpectrum (𝓞 F))) (x : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      Even (FractionalIdeal.count F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F)))) :
    (QuotientGroup.mk x : SqClass F) ∈ selmerGroup (K := F) (S := S) (n := 2) := by
  intro v hv
  rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff, FractionalIdeal.toAdd_valuationOfNeZero,
    Int.dvd_neg]
  exact even_iff_two_dvd.mp (h v hv)

/-- A divisor of `2^a 7^b` is a unit outside the primes above `2` and `7`. -/
theorem mem_selmerGroup_of_mul_eq (S : Set (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → (2 : 𝓞 F) ∉ v.asIdeal ∧ (7 : 𝓞 F) ∉ v.asIdeal)
    (x w : 𝓞 F) (a b : ℕ) (hxw : x * w = 2 ^ a * 7 ^ b) (hx : (x : F) ≠ 0) :
    (QuotientGroup.mk (Units.mk0 (x : F) hx) : SqClass F) ∈
      selmerGroup (K := F) (S := S) (n := 2) := by
  intro v hv
  rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hxv : x ∉ v.asIdeal := fun hx' => by
    have h27 : (2 : 𝓞 F) ^ a * 7 ^ b ∈ v.asIdeal := hxw ▸ v.asIdeal.mul_mem_right w hx'
    rcases v.isPrime.mem_or_mem h27 with h | h
    · exact (hS v hv).1 (v.isPrime.mem_of_pow_mem a h)
    · exact (hS v hv).2 (v.isPrime.mem_of_pow_mem b h)
  have h1 : v.valuationOfNeZero (Units.mk0 (x : F) hx) = 1 := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq_iff, Units.val_mk0, WithZero.coe_one]
    change v.valuation F (algebraMap (𝓞 F) F x) = 1
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hxv
  rw [h1, toAdd_one]
  exact dvd_zero _

end FurioLombardo.Discharge.SelmerBasis
