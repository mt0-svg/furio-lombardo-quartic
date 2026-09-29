import FurioLombardo.Discharge.M3b.Fields
import FurioLombardo.Discharge.M3b.K21Primes
import FurioLombardo.Discharge.M3b.Ramification
import FurioLombardo.Discharge.M3b.QuadReal
import FurioLombardo.M3b.Hypotheses

/-!
# `ramN`: at most four places of `L42` ramify in `N84 = L42(√e')`

* Integral elements of `L42` (DataL.lean): `x_L = (al + be ω) / 2`, `n_L = (aln + ben ω) / 2`,
  `e' = (ea + eb ω) / 2` and its conjugate, integral because their traces and norms are integers
  of `K21` (kernel identities `ck_nx`, `ck_nn`, `ck_norm_eN`), with `x_L² - e' = 4 n_L`
  (`ck_re`, `ck_im`).
* Finite places. `γ = (x_L + ω') / 2 ∈ 𝓞 N84` is a root of `X² - x_L X + n_L`, of discriminant
  `e'`; so a prime `P` of `L42` ramified in `N84` contains `e'`, hence `m = e' ē'` and
  `pi7 = m / um` (kernel identity `ck_m_pi7`, `um` a unit), so `P` lies over `(pi7)` and
  `|𝓞 L42 / P| ≥ |𝓞 K21 / (pi7)| = 343`. Since `N(e') = m` and `|N(pi7)| = 343`, the ideal `(e')`
  has absolute norm 343 (`absNorm_relNorm`), so `P = (e')`: at most one prime ramifies.
* Real places. A ramified real place `v` of `L42` has `e' < 0` (`neg_of_mem_ramifiedRealPlaces`).
  Two such places above the same real embedding of `K21` are equal: otherwise their embeddings
  differ by `ω ↦ -ω` and the product of the two values of `e'` is `m < 0`. So at most three.
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 FurioLombardo.M1.Kron NumberField QuadraticAlgebra Polynomial
  IsDedekindDomain InfinitePlace

/-! ### Kernel identities in `K21` -/

theorem ck_nx : checkK 2048 (.sub (.sub (.mul (.lin alL) (.lin alL))
    (.mul (.lin epsL) (.mul (.lin beL) (.lin beL)))) (.mul (.int 4) (.lin nxL))) = true := by
  decide +kernel

theorem ck_nn : checkK 2048 (.sub (.sub (.mul (.lin alnL) (.lin alnL))
    (.mul (.lin epsL) (.mul (.lin benL) (.lin benL)))) (.mul (.int 4) (.lin nnL))) = true := by
  decide +kernel

theorem ck_re : checkK 2048 (.sub (.sub (.add (.mul (.lin alL) (.lin alL))
    (.mul (.lin epsL) (.mul (.lin beL) (.lin beL)))) (.mul (.int 2) (.lin eaL)))
    (.mul (.int 8) (.lin alnL))) = true := by
  decide +kernel

theorem ck_im : checkK 2048 (.sub (.sub (.mul (.lin alL) (.lin beL)) (.lin ebL))
    (.mul (.int 4) (.lin benL))) = true := by
  decide +kernel

theorem ck_m_pi7 : checkK 2048 (.sub (.lin mL) (.mul (.lin umL) (gE 15))) = true := by
  decide +kernel

theorem ck_um_inv : checkK 2048 (.sub (.mul (.lin umL) (.lin umInvL)) (.int 1)) = true := by
  decide +kernel

/-- `Q(a, b, c) : a² - ε b² = 4 c` in `K21`, from a kernel check. -/
theorem norm_ident {a b c : List ℤ}
    (h : checkK 2048 (.sub (.sub (.mul (.lin a) (.lin a))
      (.mul (.lin epsL) (.mul (.lin b) (.lin b)))) (.mul (.int 4) (.lin c))) = true) :
    zkE a ^ 2 - epsK * zkE b ^ 2 = 4 * zkE c := by
  have h' := evK_eq_of_check _ _ _ h
  simp only [evK_mul, evK_sub, evK_lin, evK_int] at h'
  rw [epsK_eq, sq, sq, h']
  push_cast
  ring

/-! ### Integral elements of `L42` -/

theorem coe_neg_OK (α : 𝓞 K21) : ((-α : 𝓞 K21) : K21) = -(α : K21) :=
  map_neg (algebraMap (𝓞 K21) K21) α

/-- `(α + β ω) / 2 ∈ 𝓞 L42` when `α² - ε β² = 4 n` with `α, β, n` integral. -/
theorem isIntegral_half (α β n : 𝓞 K21)
    (h : (α : K21) ^ 2 - epsK * (β : K21) ^ 2 = 4 * (n : K21)) :
    IsIntegral ℤ (⟨(α : K21) / 2, (β : K21) / 2⟩ : L42) := by
  refine isIntegral_of_quadratic (K := K21) _ (-α) n ?_
  have h1 := mk_half_sq (a := epsK) (α : K21) (β : K21) (n : K21) h
  have e0 : ∀ b : 𝓞 K21, algebraMap (𝓞 K21) L42 b = algebraMap K21 L42 (b : K21) := fun _ => rfl
  rw [e0, e0, coe_neg_OK, map_neg]
  linear_combination h1

/-- `x_L`, `n_L`, `e'`, `ē'` in `𝓞 L42`. -/
noncomputable def xLO : 𝓞 L42 := ⟨⟨zkE alL / 2, zkE beL / 2⟩, isIntegral_half (zkO alL) (zkO beL)
  (zkO nxL) (norm_ident ck_nx)⟩

noncomputable def nLO : 𝓞 L42 := ⟨⟨zkE alnL / 2, zkE benL / 2⟩, isIntegral_half (zkO alnL)
  (zkO benL) (zkO nnL) (norm_ident ck_nn)⟩

noncomputable def eNO : 𝓞 L42 := ⟨eN, isIntegral_half (zkO eaL) (zkO ebL) (zkO mL)
  (norm_ident ck_norm_eN)⟩

theorem star_eN_eq : star eN = (⟨zkE eaL / 2, ((-zkO ebL : 𝓞 K21) : K21) / 2⟩ : L42) := by
  rw [coe_neg_OK]
  ext
  · simp [eN, eaK]
  · simp [eN, ebK]; ring

theorem star_eN_integral : IsIntegral ℤ (star eN) := by
  rw [star_eN_eq]
  exact isIntegral_half (zkO eaL) (-zkO ebL) (zkO mL) (by
    rw [coe_neg_OK, neg_sq]; exact norm_ident ck_norm_eN)

noncomputable def eNsO : 𝓞 L42 := ⟨star eN, star_eN_integral⟩

theorem xLO_sq_sub : xLO ^ 2 - eNO = 4 * nLO := by
  have hre := evK_eq_of_check _ _ _ ck_re
  have him := evK_eq_of_check _ _ _ ck_im
  simp only [evK_mul, evK_sub, evK_add, evK_lin, evK_int] at hre him
  apply RingOfIntegers.coe_injective
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  show (⟨zkE alL / 2, zkE beL / 2⟩ : L42) ^ 2 - eN = 4 * ⟨zkE alnL / 2, zkE benL / 2⟩
  ext
  · simp only [sq, re_mul, re_sub, eN, eaK, re_ofNat, im_ofNat]
    rw [← epsK_eq] at hre
    push_cast at hre
    linear_combination hre / 4
  · simp only [sq, im_mul, im_sub, eN, ebK, re_ofNat, im_ofNat, zero_mul, add_zero, mul_zero]
    push_cast at him
    linear_combination him / 2

theorem eNO_mul_star : eNO * eNsO = algebraMap (𝓞 K21) (𝓞 L42) (zkO mL) := by
  apply RingOfIntegers.coe_injective
  rw [map_mul]
  show eN * star eN = algebraMap K21 L42 (zkE mL)
  rw [← algebraMap_norm_eq_mul_star, norm_eN]
  rfl

/-! ### The prime `(e')` of `L42` -/

theorem mO_eq : zkO mL = zkO umL * gO 15 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_m_pi7
  simp only [evK_mul, evK_lin, evK_gE] at h
  rw [map_mul]
  exact h

theorem isUnit_um : IsUnit (zkO umL) := by
  refine IsUnit.of_mul_eq_one (zkO umInvL) ?_
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_um_inv
  simp only [evK_mul, evK_lin, evK_int, Int.cast_one] at h
  rw [map_mul, map_one]
  exact h

theorem intNorm_eNO : Algebra.intNorm (𝓞 K21) (𝓞 L42) eNO = zkO mL := by
  apply RingOfIntegers.coe_injective
  have h := Algebra.algebraMap_intNorm (A := 𝓞 K21) (K := K21) (L := L42) (B := 𝓞 L42) eNO
  rw [h]
  show Algebra.norm K21 eN = zkE mL
  rw [algebra_norm_eq, norm_eN]
  rfl

theorem absNorm_span_eNO : Ideal.absNorm (Ideal.span {eNO} : Ideal (𝓞 L42)) = 343 := by
  rw [← Ideal.absNorm_relNorm (𝓞 K21), Ideal.relNorm_singleton, intNorm_eNO, mO_eq,
    Ideal.span_singleton_mul_left_unit isUnit_um, absNorm_span_gO15]

/-- A prime of `L42` containing `e'` lies over `(pi7)`. -/
theorem comap_eq_of_eNO_mem (P : Ideal (𝓞 L42)) [hP : P.IsPrime] (h : eNO ∈ P) :
    P.comap (algebraMap (𝓞 K21) (𝓞 L42)) = Ideal.span {gO 15} := by
  have hm : zkO mL ∈ P.comap (algebraMap (𝓞 K21) (𝓞 L42)) := by
    rw [Ideal.mem_comap, ← eNO_mul_star]
    exact P.mul_mem_right _ h
  rw [mO_eq] at hm
  have hp : (P.comap (algebraMap (𝓞 K21) (𝓞 L42))).IsPrime := Ideal.comap_isPrime _ _
  have h15 : gO 15 ∈ P.comap (algebraMap (𝓞 K21) (𝓞 L42)) := by
    rcases hp.mem_or_mem hm with h' | h'
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h' isUnit_um) hp.ne_top
    · exact h'
  exact (isMaximal_span_gO15.eq_of_le hp.ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr h15)).symm

/-- A prime of `L42` containing `e'` has at least 343 elements in its residue ring. -/
theorem absNorm_ge_of_eNO_mem (P : Ideal (𝓞 L42)) [hP : P.IsPrime] (h : eNO ∈ P) :
    343 ≤ Ideal.absNorm P := by
  have hc := comap_eq_of_eNO_mem P h
  have hne : P ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.mem_bot] at h
    have := congrArg (fun z : 𝓞 L42 => ((z : L42) : L42).re) h
    simp only [eNO] at this
    have h2 : (eN : L42) ≠ 0 := by
      intro h0
      exact not_isSquare_eN ⟨0, by rw [h0, mul_zero]⟩
    exact h2 (by
      have : (⟨eN, _⟩ : 𝓞 L42) = 0 := h
      exact congrArg (fun z : 𝓞 L42 => (z : L42)) this)
  have hfin : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hfin ⊢
  have : Finite (𝓞 L42 ⧸ P) := Nat.finite_of_card_ne_zero hfin
  have hinj := Ideal.quotientMap_injective (I := P) (f := algebraMap (𝓞 K21) (𝓞 L42))
  have h343 : Nat.card (𝓞 K21 ⧸ P.comap (algebraMap (𝓞 K21) (𝓞 L42))) = 343 := by
    rw [hc, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, absNorm_span_gO15]
  rw [← h343]
  exact Nat.card_le_card_of_injective _ hinj

/-- A prime of `L42` containing `e'` is `(e')`. -/
theorem eq_span_of_eNO_mem (P : Ideal (𝓞 L42)) [hP : P.IsPrime] (h : eNO ∈ P) :
    P = Ideal.span {eNO} := by
  have hle : Ideal.span {eNO} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr h
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hn := absNorm_span_eNO
  rw [hJ, map_mul] at hn
  have hge := absNorm_ge_of_eNO_mem P h
  have hJ1 : Ideal.absNorm J = 1 := by
    have hJ0 : Ideal.absNorm J ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hn; norm_num at hn
    have : Ideal.absNorm P * Ideal.absNorm J ≥ 343 * Ideal.absNorm J :=
      Nat.mul_le_mul_right _ hge
    omega
  rw [Ideal.absNorm_eq_one_iff] at hJ1
  rw [hJ, hJ1, Ideal.mul_top]

/-! ### The ramified primes of `N84 / L42` -/

/-- `γ = (x_L + ω) / 2` in `N84`. -/
noncomputable def γN : N84 := (algebraMap L42 N84 (xLO : L42) + ω) * (2 : N84)⁻¹

theorem γN_mul : γN * 2 = algebraMap L42 N84 (xLO : L42) + ω := by
  rw [γN, mul_assoc, inv_mul_cancel₀ (two_ne_zero), mul_one]

theorem γN_eq : γN ^ 2 + algebraMap (𝓞 L42) N84 (-xLO) * γN + algebraMap (𝓞 L42) N84 nLO = 0 := by
  set ι := algebraMap L42 N84
  have hx : ((xLO : L42) : L42) ^ 2 - (eNO : L42) = 4 * (nLO : L42) := by
    have h := congrArg (algebraMap (𝓞 L42) L42) xLO_sq_sub
    rw [map_sub, map_mul, map_pow, map_ofNat] at h
    exact h
  have e2 : ι (xLO : L42) ^ 2 - ι eN = 4 * ι (nLO : L42) := by
    have hx' : ((xLO : L42)) ^ 2 - eN = 4 * (nLO : L42) := hx
    rw [← map_pow, ← map_sub, hx', map_mul, map_ofNat]
  have e3 : (ω : N84) * ω = ι eN := omega_mul_omega_zero
  have hγ := γN_mul
  have hb : algebraMap (𝓞 L42) N84 (-xLO) = -ι (xLO : L42) := by rw [map_neg]; rfl
  have hc : algebraMap (𝓞 L42) N84 nLO = ι (nLO : L42) := rfl
  rw [hb, hc]
  have hne : (2 : N84) ^ 2 ≠ 0 := pow_ne_zero 2 two_ne_zero
  apply (mul_left_inj' hne).mp
  linear_combination (γN * 2 + (ι (xLO : L42) + ω) - 2 * ι (xLO : L42)) * hγ - e2 + e3

noncomputable def γNO : 𝓞 N84 := ⟨γN, isIntegral_of_quadratic (K := L42) γN _ _ γN_eq⟩

theorem γNO_eq : γNO ^ 2 + algebraMap (𝓞 L42) (𝓞 N84) (-xLO) * γNO +
    algebraMap (𝓞 L42) (𝓞 N84) nLO = 0 := by
  apply RingOfIntegers.coe_injective
  rw [map_add, map_add, map_mul, map_pow, map_zero]
  exact γN_eq

theorem adjoin_γN : Algebra.adjoin L42 {algebraMap (𝓞 N84) N84 γNO} = ⊤ := by
  have hγ : algebraMap (𝓞 N84) N84 γNO = γN := rfl
  rw [hγ, eq_top_iff, ← adjoin_omega_eq_top (R := L42) (a := eN) (b := 0)]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  have hω : (ω : N84) = γN * algebraMap L42 N84 2 - algebraMap L42 N84 (xLO : L42) := by
    rw [map_ofNat, γN_mul]; ring
  rw [hω]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Algebra.subset_adjoin rfl)
    (Subalgebra.algebraMap_mem _ _)) (Subalgebra.algebraMap_mem _ _)

theorem γNO_not_mem : γNO ∉ (algebraMap (𝓞 L42) (𝓞 N84)).range := by
  rintro ⟨k, hk⟩
  have hk' : algebraMap L42 N84 (k : L42) = γN := congrArg (algebraMap (𝓞 N84) N84) hk
  have hω : (ω : N84) = algebraMap L42 N84 ((k : L42) * 2 - (xLO : L42)) := by
    rw [map_sub, map_mul, hk', map_ofNat, γN_mul]; ring
  have := congrArg QuadraticAlgebra.im hω
  rw [QuadraticAlgebra.algebraMap_eq, im_omega] at this
  exact one_ne_zero this

theorem disc_γN : (-xLO) ^ 2 - 4 * nLO = eNO := by
  rw [neg_sq, ← xLO_sq_sub]; ring

/-- A prime of `L42` ramified in `N84` is `(e')`. -/
theorem ramifiedPrimes_N84 (P : HeightOneSpectrum (𝓞 L42))
    (hP : P ∈ FurioLombardo.M3b.ramifiedPrimes L42 N84) : P.asIdeal = Ideal.span {eNO} := by
  obtain ⟨Q, hQp, hQP, hQe⟩ := hP
  have hmem := disc_mem_of_ramified γNO (-xLO) nLO γNO_eq adjoin_γN γNO_not_mem Q hQe
  have hP' : (-xLO) ^ 2 - 4 * nLO ∈ P.asIdeal := by
    rw [← hQP]; exact hmem
  rw [disc_γN] at hP'
  have := P.isPrime
  exact eq_span_of_eNO_mem P.asIdeal hP'

theorem ncard_ramifiedPrimes_N84 : (FurioLombardo.M3b.ramifiedPrimes L42 N84).ncard ≤ 1 := by
  calc (FurioLombardo.M3b.ramifiedPrimes L42 N84).ncard
      ≤ ({Ideal.span {eNO}} : Set (Ideal (𝓞 L42))).ncard := by
        refine Set.ncard_le_ncard_of_injOn HeightOneSpectrum.asIdeal ?_ ?_ (Set.toFinite _)
        · intro P hP
          rw [ramifiedPrimes_N84 P hP]; exact Set.mem_singleton _
        · intro P _ P' _ h
          exact HeightOneSpectrum.ext h
    _ = 1 := Set.ncard_singleton _

/-! ### The ramified real places of `N84 / L42` -/

open scoped Classical in
/-- The index of the real embedding of `K21` below a real place of `L42`. -/
noncomputable def placeIdx (v : InfinitePlace L42) : Fin 3 :=
  if h : v.IsReal then
    Classical.choose (exists_eq_realEmb ((embedding_of_isReal h).comp (algebraMap K21 L42)))
  else 0

theorem placeIdx_spec (v : InfinitePlace L42) (h : v.IsReal) :
    (embedding_of_isReal h).comp (algebraMap K21 L42) = realEmb (placeIdx v) := by
  unfold placeIdx
  rw [dif_pos h]
  exact Classical.choose_spec (exists_eq_realEmb _)

theorem placeIdx_injOn :
    Set.InjOn placeIdx (FurioLombardo.M3b.ramifiedRealPlaces L42 N84) := by
  intro v₁ hv₁ v₂ hv₂ hk
  obtain ⟨h₁, hn₁⟩ := neg_of_mem_ramifiedRealPlaces (a := eN) v₁ hv₁
  obtain ⟨h₂, hn₂⟩ := neg_of_mem_ramifiedRealPlaces (a := eN) v₂ hv₂
  set σ₁ := embedding_of_isReal h₁
  set σ₂ := embedding_of_isReal h₂
  have hres : σ₁.comp (algebraMap K21 L42) = σ₂.comp (algebraMap K21 L42) := by
    rw [placeIdx_spec v₁ h₁, placeIdx_spec v₂ h₂, hk]
  have hsq : σ₁ ω * σ₁ ω = σ₂ ω * σ₂ ω := by
    rw [map_omega_mul_self, map_omega_mul_self, hres]
  have h0 : (σ₁ ω - σ₂ ω) * (σ₁ ω + σ₂ ω) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp h0 with h | h
  · exact eq_of_embedding_of_isReal_eq h₁ h₂ (quad_hom_ext hres (sub_eq_zero.mp h))
  · exfalso
    have hprod := mul_eq_norm_of_neg hres (eq_neg_of_add_eq_zero_left h) eN
    rw [norm_eN, placeIdx_spec v₂ h₂] at hprod
    have hm := realEmb_m_neg (placeIdx v₂)
    have hpos : 0 < σ₁ eN * σ₂ eN := mul_pos_of_neg_of_neg hn₁ hn₂
    rw [hprod] at hpos
    exact lt_asymm hpos hm

theorem ncard_ramifiedRealPlaces_N84 :
    (FurioLombardo.M3b.ramifiedRealPlaces L42 N84).ncard ≤ 3 := by
  calc (FurioLombardo.M3b.ramifiedRealPlaces L42 N84).ncard
      ≤ (Set.univ : Set (Fin 3)).ncard :=
        Set.ncard_le_ncard_of_injOn placeIdx (fun _ _ => Set.mem_univ _) placeIdx_injOn
          (Set.toFinite _)
    _ = 3 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **ramN**: at most four places of `L42` ramify in `N84`. -/
theorem ramBound_N84 : FurioLombardo.M3b.RamBound L42 N84 4 := by
  unfold FurioLombardo.M3b.RamBound FurioLombardo.M3b.ramifiedPlaceCount
  have h1 := ncard_ramifiedPrimes_N84
  have h2 := ncard_ramifiedRealPlaces_N84
  omega

end FurioLombardo.Discharge.M3b
