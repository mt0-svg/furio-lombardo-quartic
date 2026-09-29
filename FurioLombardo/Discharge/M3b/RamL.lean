import FurioLombardo.Discharge.M3b.Fields
import FurioLombardo.Discharge.M3b.K21Primes
import FurioLombardo.Discharge.M3b.DataK21
import FurioLombardo.Discharge.M3b.Ramification
import FurioLombardo.Discharge.M3b.QuadReal
import FurioLombardo.M3b.Hypotheses

/-!
# `ramL`: at most two places of `K21` ramify in `L42 = K21(√ε)`

* Finite places. `x, y ∈ 𝓞 K21` (DataK21.lean) with `x² - ε = lb²⁴ y` (kernel identity `ck_xy`),
  and `c₀ = e₀ la³ lc⁶`, so that `c₀ lb¹² = 2` (M1's `two_eq`). Then `γ = (x + ω) / lb¹²` is a root
  of `X² - c₀ x X + y`, whose discriminant is `c₀² ε`. A prime of `K21` ramified in `L42` contains
  it (`disc_mem_of_ramified`), hence contains `la` or `lc` (`ε`, `e₀` are units), hence is
  `(la)` or `(lc)` (maximal ideals, K21Primes.lean).
* Real places. `ε > 0` at every real embedding of `K21` (K21Real.lean), so no real place ramifies
  (`neg_of_mem_ramifiedRealPlaces`).
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 FurioLombardo.M1.Kron NumberField QuadraticAlgebra Polynomial
  IsDedekindDomain

theorem ck_xy : checkK 8192 (.sub (.sub (.mul (.lin xCL) (.lin xCL)) (.lin epsL))
    (.mul ((gE 13).pow 24) (.lin yCL))) = true := by decide +kernel

/-- `x` in `𝓞 K21`. -/
noncomputable def xO : 𝓞 K21 := zkO xCL

/-- `y` in `𝓞 K21`. -/
noncomputable def yO : 𝓞 K21 := zkO yCL

theorem xO_sq_sub : xO ^ 2 - epsO = gO 13 ^ 24 * yO := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_xy
  simp only [evK_mul, evK_sub, evK_lin, evK_pow, evK_gE] at h
  simp only [map_sub, map_mul, map_pow]
  rw [sq]
  exact h

/-- `c₀ = 2 / lb¹² = e₀ la³ lc⁶`. -/
noncomputable def c0 : 𝓞 K21 := eO 0 * gO 12 ^ 3 * gO 14 ^ 6

theorem c0_mul : c0 * gO 13 ^ 12 = 2 := by rw [two_eq, c0]; ring

theorem gO13_ne_zero : gO 13 ≠ 0 := by
  intro h
  have h2 := two_eq
  rw [h] at h2
  simp at h2

theorem disc_eq : (-(c0 * xO)) ^ 2 - 4 * yO = c0 ^ 2 * epsO := by
  apply mul_left_cancel₀ (pow_ne_zero 24 gO13_ne_zero)
  have h1 := c0_mul
  have h2 := xO_sq_sub
  linear_combination (c0 ^ 2 * gO 13 ^ 24) * h2 + (gO 13 ^ 24 * yO * (c0 * gO 13 ^ 12 + 2)) * h1

/-- `γ = (x + ω) / lb¹²` in `L42`. -/
noncomputable def γL : L42 :=
  (algebraMap K21 L42 (xO : K21) + ω) * (algebraMap K21 L42 (gO 13 : K21) ^ 12)⁻¹

theorem lbL_ne_zero : algebraMap K21 L42 (gO 13 : K21) ^ 12 ≠ 0 := by
  apply pow_ne_zero
  rw [_root_.map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]
  exact gO13_ne_zero

theorem γL_mul : γL * algebraMap K21 L42 (gO 13 : K21) ^ 12 = algebraMap K21 L42 (xO : K21) + ω := by
  rw [γL, mul_assoc, inv_mul_cancel₀ lbL_ne_zero, mul_one]

theorem γL_eq : γL ^ 2 + algebraMap (𝓞 K21) L42 (-(c0 * xO)) * γL + algebraMap (𝓞 K21) L42 yO = 0 := by
  set ι := algebraMap K21 L42
  have hc : ((c0 : K21) * (gO 13 : K21) ^ 12) = 2 := by
    have h := congrArg (algebraMap (𝓞 K21) K21) c0_mul
    rw [map_mul, map_pow, map_ofNat] at h
    exact h
  have hxy : (xO : K21) ^ 2 - (epsO : K21) = (gO 13 : K21) ^ 24 * (yO : K21) := by
    have h := congrArg (algebraMap (𝓞 K21) K21) xO_sq_sub
    rw [map_sub, map_mul, map_pow, map_pow] at h
    exact h
  have e1 : ι (c0 : K21) * ι (gO 13 : K21) ^ 12 = 2 := by
    rw [← map_pow, ← map_mul, hc, map_ofNat]
  have e2 : ι (xO : K21) ^ 2 - ι (epsO : K21) = ι (gO 13 : K21) ^ 24 * ι (yO : K21) := by
    rw [← map_pow, ← map_sub, hxy, map_mul, map_pow]
  have e3 : (ω : L42) * ω = ι (epsO : K21) := omega_mul_omega_zero
  have hγl := γL_mul
  have hb : algebraMap (𝓞 K21) L42 (-(c0 * xO)) = -(ι (c0 : K21) * ι (xO : K21)) := by
    rw [map_neg, map_mul]; rfl
  have hc' : algebraMap (𝓞 K21) L42 yO = ι (yO : K21) := rfl
  rw [hb, hc']
  have hne : (ι (gO 13 : K21) ^ 12) ^ 2 ≠ 0 := pow_ne_zero 2 lbL_ne_zero
  apply (mul_left_inj' hne).mp
  linear_combination (γL * ι (gO 13 : K21) ^ 12 + (ι (xO : K21) + ω) -
      ι (c0 : K21) * ι (xO : K21) * ι (gO 13 : K21) ^ 12) * hγl +
    (-(ι (xO : K21) * (ι (xO : K21) + ω))) * e1 - e2 + e3

theorem isIntegral_γL : IsIntegral ℤ γL := isIntegral_of_quadratic γL _ _ γL_eq

/-- `γ` in `𝓞 L42`. -/
noncomputable def γO : 𝓞 L42 := ⟨γL, isIntegral_γL⟩

theorem γO_eq : γO ^ 2 + algebraMap (𝓞 K21) (𝓞 L42) (-(c0 * xO)) * γO +
    algebraMap (𝓞 K21) (𝓞 L42) yO = 0 := by
  apply RingOfIntegers.coe_injective
  rw [map_add, map_add, map_mul, map_pow, map_zero]
  exact γL_eq

theorem adjoin_γL : Algebra.adjoin K21 {algebraMap (𝓞 L42) L42 γO} = ⊤ := by
  have hγ : algebraMap (𝓞 L42) L42 γO = γL := rfl
  rw [hγ, eq_top_iff, ← adjoin_omega_eq_top (R := K21) (a := epsK) (b := 0)]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  have hω : (ω : L42) = γL * algebraMap K21 L42 ((gO 13 : K21) ^ 12) -
      algebraMap K21 L42 (xO : K21) := by
    rw [map_pow, γL_mul]; ring
  rw [hω]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Algebra.subset_adjoin rfl)
    (Subalgebra.algebraMap_mem _ _)) (Subalgebra.algebraMap_mem _ _)

theorem γO_not_mem : γO ∉ (algebraMap (𝓞 K21) (𝓞 L42)).range := by
  rintro ⟨k, hk⟩
  have hk' : algebraMap K21 L42 (k : K21) = γL := congrArg (algebraMap (𝓞 L42) L42) hk
  have hω : (ω : L42) = algebraMap K21 L42 ((k : K21) * (gO 13 : K21) ^ 12 - (xO : K21)) := by
    rw [map_sub, map_mul, hk', map_pow, γL_mul]; ring
  have := congrArg QuadraticAlgebra.im hω
  rw [QuadraticAlgebra.algebraMap_eq, im_omega] at this
  exact one_ne_zero this

/-- A prime of `K21` ramified in `L42` is `(la)` or `(lc)`. -/
theorem ramifiedPrimes_L42 (P : HeightOneSpectrum (𝓞 K21))
    (hP : P ∈ FurioLombardo.M3b.ramifiedPrimes K21 L42) :
    P.asIdeal = Ideal.span {gO 12} ∨ P.asIdeal = Ideal.span {gO 14} := by
  obtain ⟨Q, hQp, hQP, hQe⟩ := hP
  have hmem := disc_mem_of_ramified γO (-(c0 * xO)) yO γO_eq adjoin_γL γO_not_mem Q hQe
  have hP' : (-(c0 * xO)) ^ 2 - 4 * yO ∈ P.asIdeal := by
    rw [← hQP]; exact hmem
  rw [disc_eq] at hP'
  have hPp := P.isPrime
  have hnu : ∀ u : 𝓞 K21, IsUnit u → u ∉ P.asIdeal := fun u hu h =>
    hPp.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hε : IsUnit epsO := IsUnit.of_mul_eq_one _ epsO_mul_inv
  have he0 : IsUnit (eO 0) := IsUnit.of_mul_eq_one _ (eO_mul_eIO 0 (by norm_num))
  have hc0 : c0 ∈ P.asIdeal := by
    rcases hPp.mem_or_mem hP' with h | h
    · exact hPp.mem_of_pow_mem 2 h
    · exact absurd h (hnu _ hε)
  have hlalc : gO 12 ∈ P.asIdeal ∨ gO 14 ∈ P.asIdeal := by
    rw [c0] at hc0
    rcases hPp.mem_or_mem hc0 with h | h
    · rcases hPp.mem_or_mem h with h' | h'
      · exact absurd h' (hnu _ he0)
      · exact Or.inl (hPp.mem_of_pow_mem 3 h')
    · exact Or.inr (hPp.mem_of_pow_mem 6 h)
  rcases hlalc with h | h
  · left
    exact (isMaximal_span_gO12.eq_of_le hPp.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr h)).symm
  · right
    exact (isMaximal_span_gO14.eq_of_le hPp.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr h)).symm

theorem ncard_ramifiedPrimes_L42 : (FurioLombardo.M3b.ramifiedPrimes K21 L42).ncard ≤ 2 := by
  calc (FurioLombardo.M3b.ramifiedPrimes K21 L42).ncard
      ≤ ({Ideal.span {gO 12}, Ideal.span {gO 14}} : Set (Ideal (𝓞 K21))).ncard := by
        refine Set.ncard_le_ncard_of_injOn HeightOneSpectrum.asIdeal ?_ ?_ (Set.toFinite _)
        · intro P hP
          rcases ramifiedPrimes_L42 P hP with h | h
          · rw [h]; exact Set.mem_insert _ _
          · rw [h]; exact Set.mem_insert_of_mem _ rfl
        · intro P _ P' _ h
          exact HeightOneSpectrum.ext h
    _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]

/-- No real place of `K21` ramifies in `L42`: `ε > 0` at every real embedding. -/
theorem ramifiedRealPlaces_L42 : FurioLombardo.M3b.ramifiedRealPlaces K21 L42 = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨h, hneg⟩ := neg_of_mem_ramifiedRealPlaces (a := epsK) v hv
  obtain ⟨k, hk⟩ := exists_eq_realEmb (InfinitePlace.embedding_of_isReal h)
  rw [hk] at hneg
  exact (lt_asymm hneg (realEmb_epsK_pos k)).elim

/-- **ramL**: at most two places of `K21` ramify in `L42`. -/
theorem ramBound_L42 : FurioLombardo.M3b.RamBound K21 L42 2 := by
  unfold FurioLombardo.M3b.RamBound FurioLombardo.M3b.ramifiedPlaceCount
  rw [ramifiedRealPlaces_L42, Set.ncard_empty, add_zero]
  exact ncard_ramifiedPrimes_L42

end FurioLombardo.Discharge.M3b
