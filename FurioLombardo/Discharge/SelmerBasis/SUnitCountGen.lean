import Mathlib

/-!
# Primes over a prime in a quadratic extension of number fields (piece (b), generic part)

`K ⊂ L` number fields with `[L : K] = 2`, `p` a nonzero maximal ideal of `𝓞 K`.

* `ncard_primesOver_mul_le`: if every prime above `p` has `e f ≥ k`, then `#primes · k ≤ 2`
  (the fundamental identity `∑ e f = [L : K]`).
* `two_le_ramificationIdx_of_eisenstein`: a root `γ ∈ 𝓞 L` of `X² + b X + c` with `b ∈ p = (g)`,
  `c = g u`, `u ∉ p` gives `e ≥ 2` at every prime above `p` (`γ ∈ P`, so `c ∈ P²`, so `g ∈ P²`).
* `two_le_inertiaDeg_of_inert`: `|𝓞 K / p| = 2` and a root `γ` of `X² + b X + c` with
  `b ≡ c ≡ 1 (mod p)` give `f ≥ 2` (`γ² + γ + 1 = 0` has no root in `F₂`).
* `inertiaDeg_eq_one_of_two_le_ramificationIdx`, `mem_of_quadratic_mem`, `ncard_biUnion_le`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField IsDedekindDomain

section Gen

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The fundamental identity in a quadratic extension, as a bound on the number of primes. -/
theorem ncard_primesOver_mul_le (h2 : Module.finrank K L = 2) (p : Ideal (𝓞 K)) [p.IsMaximal]
    (hp : p ≠ ⊥) (k : ℕ)
    (hk : ∀ P ∈ p.primesOver (𝓞 L), k ≤ P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K)) :
    (p.primesOver (𝓞 L)).ncard * k ≤ 2 := by
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L, h2] at hsum
  rw [← hsum, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← smul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ fun q _ => hk q.1 q.2

/-- **Eisenstein criterion for ramification.** -/
theorem two_le_ramificationIdx_of_eisenstein (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (g : 𝓞 K) (hg : p = Ideal.span {g}) (γ : 𝓞 L) (b c u : 𝓞 K)
    (hγ : γ ^ 2 + algebraMap (𝓞 K) (𝓞 L) b * γ + algebraMap (𝓞 K) (𝓞 L) c = 0)
    (hb : b ∈ p) (hc : c = g * u) (hu : u ∉ p) (P : Ideal (𝓞 L)) (hP : P ∈ p.primesOver (𝓞 L)) :
    2 ≤ P.ramificationIdx (𝓞 K) := by
  have hPp : P.IsPrime := hP.1
  have : P.LiesOver p := hP.2
  have hcomap : P.comap (algebraMap (𝓞 K) (𝓞 L)) = p := by
    rw [← Ideal.under_def, ← hP.2.over]
  have hgp : g ∈ p := hg ▸ Ideal.mem_span_singleton_self g
  have hcp : c ∈ p := hc ▸ p.mul_mem_right u hgp
  have hbP : algebraMap (𝓞 K) (𝓞 L) b ∈ P := by rw [← Ideal.mem_comap, hcomap]; exact hb
  have hcP : algebraMap (𝓞 K) (𝓞 L) c ∈ P := by rw [← Ideal.mem_comap, hcomap]; exact hcp
  have hγP : γ ∈ P := by
    have h2 : γ ^ 2 = -(algebraMap (𝓞 K) (𝓞 L) b * γ + algebraMap (𝓞 K) (𝓞 L) c) := by
      linear_combination hγ
    exact hPp.mem_of_pow_mem 2 (h2 ▸ P.neg_mem_iff.mpr (P.add_mem (P.mul_mem_right _ hbP) hcP))
  have hc2 : algebraMap (𝓞 K) (𝓞 L) c ∈ P ^ 2 := by
    have h2 : algebraMap (𝓞 K) (𝓞 L) c = -(γ * γ + algebraMap (𝓞 K) (𝓞 L) b * γ) := by
      linear_combination hγ
    rw [h2, pow_two]
    exact (P * P).neg_mem_iff.mpr ((P * P).add_mem (Ideal.mul_mem_mul hγP hγP)
      (Ideal.mul_mem_mul hbP hγP))
  have hmap0 : p.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot hmap0
    (Ideal.map_le_of_le_comap (by rw [hcomap]))
  let w : HeightOneSpectrum (𝓞 L) := ⟨P, hPp, hP0⟩
  have hu' : algebraMap (𝓞 K) (𝓞 L) u ∉ P := by
    rw [← Ideal.mem_comap, hcomap]; exact hu
  have hg2 : algebraMap (𝓞 K) (𝓞 L) g ∈ P ^ 2 := by
    have h1 := (w.intValuation_le_pow_iff_mem _ 2).mpr hc2
    have hv1 : w.intValuation (algebraMap (𝓞 K) (𝓞 L) u) = 1 :=
      HeightOneSpectrum.intValuation_eq_one_iff.mpr hu'
    rw [hc, map_mul, map_mul, hv1, mul_one] at h1
    exact (w.intValuation_le_pow_iff_mem _ 2).mp h1
  have hmap : p.map (algebraMap (𝓞 K) (𝓞 L)) ≤ P ^ 2 := by
    rw [hg, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hg2
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p P hmap0]
  have hfin : FiniteMultiplicity P (p.map (algebraMap (𝓞 K) (𝓞 L))) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 hPp) hmap0
  exact hfin.le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.mpr hmap)

/-- **Inertia criterion.** -/
theorem two_le_inertiaDeg_of_inert (p : Ideal (𝓞 K)) [p.IsMaximal] (hcard : Ideal.absNorm p = 2)
    (γ : 𝓞 L) (b c : 𝓞 K)
    (hγ : γ ^ 2 + algebraMap (𝓞 K) (𝓞 L) b * γ + algebraMap (𝓞 K) (𝓞 L) c = 0)
    (hb : 1 - b ∈ p) (hc : 1 - c ∈ p) (P : Ideal (𝓞 L)) (hP : P ∈ p.primesOver (𝓞 L)) :
    2 ≤ P.inertiaDeg (𝓞 K) := by
  have hPp : P.IsPrime := hP.1
  have : P.LiesOver p := hP.2
  have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
    (algebraMap (𝓞 K) (𝓞 L)) (fun x => Algebra.IsIntegral.isIntegral x) P
    (by rw [← Ideal.under_def, ← hP.2.over]; infer_instance)
  letI : Field (𝓞 K ⧸ p) := Ideal.Quotient.field p
  letI : Field (𝓞 L ⧸ P) := Ideal.Quotient.field P
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
  by_contra hlt
  have hpos : 0 < Module.finrank (𝓞 K ⧸ p) (𝓞 L ⧸ P) := by
    have := Ideal.inertiaDeg_pos P (𝓞 K)
    rwa [Ideal.inertiaDeg_eq_of_isMaximal p P] at this
  have h1 : Module.finrank (𝓞 K ⧸ p) (𝓞 L ⧸ P) = 1 := by omega
  -- the residue field of `P` is the image of `𝓞 K ⧸ p`
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K ⧸ p, algebraMap (𝓞 K ⧸ p) (𝓞 L ⧸ P) a = Ideal.Quotient.mk P γ := by
    have htop := Subalgebra.bot_eq_top_of_finrank_eq_one (F := 𝓞 K ⧸ p) (E := 𝓞 L ⧸ P) h1
    have hmem : Ideal.Quotient.mk P γ ∈ (⊥ : Subalgebra (𝓞 K ⧸ p) (𝓞 L ⧸ P)) :=
      htop ▸ Algebra.mem_top
    exact Algebra.mem_bot.mp hmem
  have hcard2 : Nat.card (𝓞 K ⧸ p) = 2 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hcard]
  have h01 : ∀ x : 𝓞 K ⧸ p, x = 0 ∨ x = 1 := by
    classical
    have : Fintype (𝓞 K ⧸ p) := Fintype.ofFinite _
    intro x
    by_contra! hx
    have h3 : ({0, 1, x} : Finset (𝓞 K ⧸ p)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hx.1.symm, zero_ne_one]),
        Finset.card_pair (Ne.symm hx.2)]
    have := Finset.card_le_univ ({0, 1, x} : Finset (𝓞 K ⧸ p))
    rw [h3, Fintype.card_eq_nat_card, hcard2] at this
    omega
  have hb' : Ideal.Quotient.mk p b = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk p), ← map_sub, ← neg_sub, map_neg,
      neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hb
  have hc' : Ideal.Quotient.mk p c = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk p), ← map_sub, ← neg_sub, map_neg,
      neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hc
  have hmk : ∀ x : 𝓞 K, Ideal.Quotient.mk P (algebraMap (𝓞 K) (𝓞 L) x) =
      algebraMap (𝓞 K ⧸ p) (𝓞 L ⧸ P) (Ideal.Quotient.mk p x) := fun x => rfl
  have heq := congrArg (Ideal.Quotient.mk P) hγ
  simp only [map_add, map_mul, map_pow, map_zero, hmk, hb', hc', map_one, ← ha] at heq
  have h2 : (1 : 𝓞 K ⧸ p) + 1 = 0 := by
    rcases h01 (1 + 1) with h | h
    · exact h
    · exact absurd (by simpa using h) (one_ne_zero (α := 𝓞 K ⧸ p))
  have heq' : algebraMap (𝓞 K ⧸ p) (𝓞 L ⧸ P) (a ^ 2 + a + 1) = 0 := by
    simpa [map_add, map_pow, mul_one, one_mul] using heq
  replace heq' := (map_eq_zero_iff (algebraMap (𝓞 K ⧸ p) (𝓞 L ⧸ P))
    (algebraMap (𝓞 K ⧸ p) (𝓞 L ⧸ P)).injective).mp heq'
  rcases h01 a with rfl | rfl
  · simp at heq'
  · have : (1 : 𝓞 K ⧸ p) ^ 2 + 1 + 1 = 1 := by rw [one_pow, add_assoc, h2, add_zero]
    rw [this] at heq'
    exact one_ne_zero heq'

/-- In a quadratic extension, `e ≥ 2` forces `f = 1`. -/
theorem inertiaDeg_eq_one_of_two_le_ramificationIdx (h2 : Module.finrank K L = 2)
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal (𝓞 L)) (hP : P ∈ p.primesOver (𝓞 L))
    (he : 2 ≤ P.ramificationIdx (𝓞 K)) : P.inertiaDeg (𝓞 K) = 1 := by
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L, h2] at hsum
  have hle : P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K) ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun q : p.primesOver (𝓞 L) =>
      q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨P, hP⟩)
  have : P.IsPrime := hP.1
  have hf := Ideal.inertiaDeg_pos P (𝓞 K)
  nlinarith

/-- An integral root of `X² - t X + n` with `t, n ∈ p` lies in every prime above `p`. -/
theorem mem_of_quadratic_mem (p : Ideal (𝓞 K)) (z : 𝓞 L) (t n : 𝓞 K)
    (hz : z ^ 2 - algebraMap (𝓞 K) (𝓞 L) t * z + algebraMap (𝓞 K) (𝓞 L) n = 0)
    (ht : t ∈ p) (hn : n ∈ p) (P : Ideal (𝓞 L)) (hP : P ∈ p.primesOver (𝓞 L)) : z ∈ P := by
  have : P.IsPrime := hP.1
  have hle : p ≤ P.comap (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [← Ideal.under_def, ← hP.2.over]
  have htP : algebraMap (𝓞 K) (𝓞 L) t ∈ P := hle ht
  have hnP : algebraMap (𝓞 K) (𝓞 L) n ∈ P := hle hn
  have hz2 : z ^ 2 ∈ P := by
    have : z ^ 2 = algebraMap (𝓞 K) (𝓞 L) t * z - algebraMap (𝓞 K) (𝓞 L) n := by
      linear_combination hz
    rw [this]
    exact P.sub_mem (P.mul_mem_right _ htP) hnP
  exact this.mem_of_pow_mem 2 hz2

end Gen

/-- A union over a finite index set of at most `n` elements of sets of at most `k` elements. -/
theorem ncard_biUnion_le {α β : Type*} (T : Set α) (hT : T.Finite) (n k : ℕ) (hTn : T.ncard ≤ n)
    (X : α → Set β) (hX : ∀ Q ∈ T, (X Q).Finite ∧ (X Q).ncard ≤ k) :
    (⋃ Q ∈ T, X Q).Finite ∧ (⋃ Q ∈ T, X Q).ncard ≤ n * k := by
  refine ⟨hT.biUnion fun Q hQ => (hX Q hQ).1, ?_⟩
  calc (⋃ Q ∈ T, X Q).ncard = (⋃ Q ∈ hT.toFinset, X Q).ncard := by simp
    _ ≤ ∑ Q ∈ hT.toFinset, (X Q).ncard := hT.toFinset.set_ncard_biUnion_le X
    _ ≤ hT.toFinset.card • k :=
        Finset.sum_le_card_nsmul _ _ _ fun Q hQ => (hX Q (by simpa using hQ)).2
    _ = T.ncard * k := by rw [smul_eq_mul, Set.ncard_eq_toFinset_card T hT]
    _ ≤ n * k := Nat.mul_le_mul_right k hTn

end FurioLombardo.Discharge.SelmerBasis
