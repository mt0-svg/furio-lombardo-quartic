import FurioLombardo.M2.Zimmert.Defs
import FurioLombardo.Vendor.AINTLIB.CompletedZeta.MellinAgreement
import FurioLombardo.Vendor.AINTLIB.CompletedZeta.Existence

/-!
# The partial zeta functions of the ideal classes as Zimmert data (lane M2)

For an ideal class `C` of a number field `K`, the per class Hecke theta pair of AINTLIB
(`heckeGClass`, `heckeGClass_inversion`) gives a `WeakFEPair`; after the change of variable
`s ↦ s/2` and a positive normalisation it is a `ZData` whose `g` side is the Dirichlet series
`Σ_{J ∈ C} N(J)^{-s}` over the integral ideals of `C`, with `A = |d_K|^{1/2} π^{-n/2}`, Gamma
factor `Γ(s/2)^(r₁+r₂) Γ((s+1)/2)^r₂`, and whose `f` side is the class `[𝔡] C⁻¹`.
-/

universe u

namespace FurioLombardo.M2.Zimmert

open NumberField

open scoped nonZeroDivisors

/-- The nonzero integral ideals of the class `C`. -/
def classIdeals (K : Type*) [Field K] [NumberField K] (C : ClassGroup (𝓞 K)) : Type _ :=
  {J : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 J = C}

section ClassZeta

open FurioLombardo.Vendor.AINTLIB.DedekindResidue NumberField.InfinitePlace NumberField.Units MeasureTheory
open Filter Asymptotics Topology
open scoped Real ENNReal NNReal

/-! ### A generic strip bound and the half-argument algebra for weak FE-pairs -/

/-- Pointwise Mellin triangle inequality for `Λ₀` of any weak FE-pair (as AINTLIB
`norm_heckeΛ₀_le`). -/
theorem fePair_norm_Λ₀_le (Q : WeakFEPair ℂ) (s : ℂ) :
    ‖Q.Λ₀ s‖ ≤ ∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖Q.f_modif x‖ := by
  rw [WeakFEPair.Λ₀, mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- The norm integrals of `f_modif` converge at every real exponent. -/
theorem fePair_integrable_Λ₀_norm (Q : WeakFEPair ℂ) (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖Q.f_modif x‖) (Set.Ioi 0) := by
  have hconv : MellinConvergent (Q.f_modif) (a : ℂ) :=
    (Q.isStrongFEPair_toStrongFEPair.hasMellin (a : ℂ)).1
  have hnn : IntegrableOn
      (fun x : ℝ => ‖((x:ℂ) ^ ((a:ℂ) - 1) • Q.f_modif x)‖) (Set.Ioi 0) := hconv.norm
  refine hnn.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show ‖((x:ℂ) ^ ((a:ℂ) - 1) • Q.f_modif x)‖ = x ^ (a - 1) * ‖Q.f_modif x‖
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- `‖Λ₀‖` of any weak FE-pair is bounded on every vertical strip (as AINTLIB
`exists_heckeΛ₀_strip_bound`). -/
theorem fePair_exists_Λ₀_strip_bound (Q : WeakFEPair ℂ) (a b : ℝ) :
    ∃ B : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Q.Λ₀ s‖ ≤ B := by
  refine ⟨(∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖Q.f_modif x‖)
    + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖Q.f_modif x‖, ?_⟩
  intro s ha hb
  refine le_trans (fePair_norm_Λ₀_le Q s) ?_
  have hmono : ∀ x ∈ Set.Ioi (0:ℝ),
      x ^ (s.re - 1) * ‖Q.f_modif x‖
        ≤ x ^ (a - 1) * ‖Q.f_modif x‖ + x ^ (b - 1) * ‖Q.f_modif x‖ := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    rcases le_or_gt x 1 with hx1 | hx1
    · have h1 : x ^ (s.re - 1) ≤ x ^ (a - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (b - 1) * ‖Q.f_modif x‖ := by positivity
      nlinarith [norm_nonneg (Q.f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
    · have h1 : x ^ (s.re - 1) ≤ x ^ (b - 1) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (a - 1) * ‖Q.f_modif x‖ := by positivity
      nlinarith [norm_nonneg (Q.f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
  calc (∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖Q.f_modif x‖)
      ≤ ∫ x in Set.Ioi (0:ℝ),
          (x ^ (a - 1) * ‖Q.f_modif x‖ + x ^ (b - 1) * ‖Q.f_modif x‖) :=
        setIntegral_mono_on (fePair_integrable_Λ₀_norm Q s.re)
          ((fePair_integrable_Λ₀_norm Q a).add (fePair_integrable_Λ₀_norm Q b))
          measurableSet_Ioi hmono
    _ = (∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖Q.f_modif x‖)
          + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖Q.f_modif x‖ :=
        integral_add (fePair_integrable_Λ₀_norm Q a) (fePair_integrable_Λ₀_norm Q b)

/-- For a pair with `k = 1/2`, `ε = 1`, `f₀ = g₀ = c`: the normalised `Λ₀(s/2)` with the
polar terms `κ/s`, `κ/(s-1)`, `κ = 2c/K₀`, is the normalised `Λ(s/2)`. -/
theorem fePair_Λ₀_half_sub_polar (Q : WeakFEPair ℂ) {c K₀ : ℂ} (hK₀ : K₀ ≠ 0)
    (hf₀ : Q.f₀ = c) (hg₀ : Q.g₀ = c) (hε : Q.ε = 1) (hk : Q.k = 1 / 2) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    K₀⁻¹ * Q.Λ₀ (s / 2) - (2 * c / K₀) / s + (2 * c / K₀) / (s - 1)
      = K₀⁻¹ * Q.Λ (s / 2) := by
  have hΛ : Q.Λ (s / 2) = Q.Λ₀ (s / 2) - (1 / (s / 2)) • Q.f₀
      - ((Q.ε / (((Q.k : ℝ) : ℂ) - s / 2)) • Q.g₀) := rfl
  rw [hΛ, hf₀, hg₀, hε, hk, smul_eq_mul, smul_eq_mul]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hks : (((1 / 2 : ℝ)) : ℂ) - s / 2 ≠ 0 := by
    intro h
    apply hs1
    push_cast at h
    linear_combination (-2 : ℂ) * h
  have hks' : (((1 / 2 : ℝ)) : ℂ) - s / 2 = (1 - s) / 2 := by push_cast; ring
  rw [hks']
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- The functional equation of `Λ₀(s/2)` for a pair with `k = 1/2`, `ε = 1`. -/
theorem fePair_symm_Λ₀_half (Q : WeakFEPair ℂ) (hε : Q.ε = 1) (hk : Q.k = 1 / 2) (s : ℂ) :
    Q.symm.Λ₀ (s / 2) = Q.Λ₀ ((1 - s) / 2) := by
  have h := Q.functional_equation₀ (s / 2)
  rw [hε, one_smul, hk] at h
  rw [← h]
  congr 1
  push_cast
  ring


/-! ### The per class Hecke pair -/

variable (K : Type*) [Field K] [NumberField K]

/-- The constant term `w⁻¹ · vol` of every class theta. -/
noncomputable def classConst : ℝ := (torsionOrder K : ℝ)⁻¹ * unitBoxVol K

open scoped Classical in
/-- Rapid decay of a class theta to its constant term. -/
theorem heckeGClass_sub_const_isBigO (C : ClassGroup (𝓞 K)) (r : ℝ) :
    (fun x : ℝ => heckeGClass K C x - classConst K) =O[atTop] fun x : ℝ => x ^ r := by
  obtain ⟨Cb, c', x₀, hCb, hc', hx₀, hdev⟩ := exists_heckeGClass_dev_bound K C
  have hn : (0:ℝ) < (1 : ℝ) / (Module.finrank ℚ K) := div_pos one_pos (finrank_pos_real K)
  refine IsBigO.trans ?_ (isBigO_exp_neg_rpow hc' hn r)
  rw [isBigO_iff]
  refine ⟨Cb, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop x₀] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hdev hx

/-- The complex-valued version of `heckeGClass_sub_const_isBigO`. -/
theorem complex_heckeGClass_sub_const_isBigO (C : ClassGroup (𝓞 K)) (r : ℝ) :
    (fun x : ℝ => (heckeGClass K C x : ℂ) - (classConst K : ℂ)) =O[atTop]
      fun x : ℝ => x ^ r := by
  have hbase := heckeGClass_sub_const_isBigO K C r
  rw [isBigO_iff] at hbase ⊢
  obtain ⟨C', hC⟩ := hbase
  refine ⟨C', ?_⟩
  filter_upwards [hC] with x hx
  calc ‖(heckeGClass K C x : ℂ) - (classConst K : ℂ)‖
      = ‖((heckeGClass K C x - classConst K : ℝ) : ℂ)‖ := by push_cast; ring_nf
    _ = ‖heckeGClass K C x - classConst K‖ := Complex.norm_real _
    _ ≤ C' * ‖x ^ r‖ := hx

open scoped Classical in
/-- **The per class Hecke pair**: `f = Ĝ_C`, `g = Ĝ_{C^∨}`, `k = 1/2`, `ε = 1`,
`f₀ = g₀ = w⁻¹ · vol`. -/
noncomputable def classFEPair (C : ClassGroup (𝓞 K)) : WeakFEPair ℂ where
  f := fun x => (heckeGClass K C x : ℂ)
  g := fun x => (heckeGClass K (dualClass K C) x : ℂ)
  k := 1 / 2
  ε := 1
  f₀ := (classConst K : ℂ)
  g₀ := (classConst K : ℂ)
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_heckeGClass K C)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_heckeGClass K (dualClass K C))).locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq := fun x hx => by
    have h := heckeGClass_inversion K C (Set.mem_Ioi.mp hx)
    rw [Real.sqrt_eq_rpow] at h
    change ((heckeGClass K C (1 / x) : ℝ) : ℂ) = _
    rw [h, one_mul, smul_eq_mul]
    push_cast
    ring
  hf_top := complex_heckeGClass_sub_const_isBigO K C
  hg_top := complex_heckeGClass_sub_const_isBigO K (dualClass K C)


/-! ### The Mellin transform of a class theta at real points -/

/-- Summability of the norm sums over a set of nonzero ideals, for real `s > 1`. -/
theorem summable_subtype_ideal_norm_rpow (p : (Ideal (𝓞 K))⁰ → Prop) {s : ℝ} (hs : 1 < s) :
    Summable (fun b : Subtype p =>
      ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-s)) := by
  classical
  exact (summable_ideal_norm_rpow K hs).subtype p

open scoped Classical in
/-- Nonnegativity of the closed real form of the class Mellin transform. -/
theorem classClosedForm_nonneg (E : ClassGroup (𝓞 K)) {σ : ℝ} (hσ0 : 0 < σ) :
    (0:ℝ) ≤ (heckeBeta K) ^ (-σ)
      * ((((heckeJacobian K : ℝ≥0)) : ℝ)
        * ∏ w : InfinitePlace K,
          π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))
      * ∑' b : {b : (Ideal (𝓞 K))⁰ //
          ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
          ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-(2 * σ)) := by
  have hβ := heckeBeta_pos K
  have hΓ := prod_pi_rpow_mul_Gamma_nonneg K hσ0
  have hz : 0 ≤ ∑' b : {b : (Ideal (𝓞 K))⁰ //
          ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
      ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-(2 * σ)) :=
    tsum_nonneg (fun b => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hJ : (0:ℝ) ≤ (((heckeJacobian K : ℝ≥0)) : ℝ) := (heckeJacobian K).2
  positivity

open scoped Classical in
/-- The `ENNReal.ofReal` of the Mellin integral of a class theta deviation is the `ofReal` of
the closed form (per class version of AINTLIB `ennreal_ofReal_integral_heckeF_dev_eq`). -/
theorem ennreal_ofReal_integral_heckeGClass_dev_eq (E : ClassGroup (𝓞 K)) {σ : ℝ}
    (hσ0 : 0 < σ) (h2σ : 1 < 2 * σ)
    (hri : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * (heckeGClass K E t - classConst K))
      (Set.Ioi (0:ℝ)) volume)
    (hnnae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      (fun t : ℝ => t ^ (σ - 1) * (heckeGClass K E t - classConst K))) :
    ENNReal.ofReal (∫ t in Set.Ioi (0:ℝ), t ^ (σ - 1) * (heckeGClass K E t - classConst K))
      = ENNReal.ofReal ((heckeBeta K) ^ (-σ)
        * ((((heckeJacobian K : ℝ≥0)) : ℝ)
          * ∏ w : InfinitePlace K,
            π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))
        * ∑' b : {b : (Ideal (𝓞 K))⁰ //
            ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
            ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-(2 * σ))) := by
  rw [ofReal_integral_eq_lintegral_ofReal hri hnnae]
  have hsplit : ∀ t ∈ Set.Ioi (0:ℝ),
      ENNReal.ofReal (t ^ (σ - 1) * (heckeGClass K E t - classConst K))
      = ENNReal.ofReal (t ^ (σ - 1))
        * ENNReal.ofReal (heckeGClass K E t - (torsionOrder K : ℝ)⁻¹ * unitBoxVol K) :=
    fun t ht => ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt ht) _)
  rw [setLIntegral_congr_fun measurableSet_Ioi hsplit,
    lintegral_mellin_heckeGClass_dev K E hσ0]
  have hzsum : (∑' b : {b : (Ideal (𝓞 K))⁰ //
      ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
      ENNReal.ofReal ((((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2)
        ^ (-σ)))
      = ENNReal.ofReal (∑' b : {b : (Ideal (𝓞 K))⁰ //
          ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
          ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-(2 * σ))) := by
    have hb : ∀ b : {b : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
        (((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ 2) ^ (-σ)
          = ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-(2 * σ)) := by
      intro b
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    simp_rw [hb]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (summable_subtype_ideal_norm_rpow K _ h2σ)).symm
  rw [hzsum]
  rw [show ((heckeJacobian K : ℝ≥0) : ℝ≥0∞)
    = ENNReal.ofReal (((heckeJacobian K : ℝ≥0)) : ℝ) from
    (ENNReal.ofReal_coe_nnreal).symm]
  have hβ := heckeBeta_pos K
  have hJnn : (0:ℝ) ≤ ((heckeJacobian K : ℝ≥0) : ℝ) := (heckeJacobian K).2
  have hΓnn' := prod_pi_rpow_mul_Gamma_nonneg K hσ0
  rw [← ENNReal.ofReal_mul hJnn, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]

open scoped Classical in
/-- **Real values of `Λ` for a pair whose `f` is a class theta** (per class version of AINTLIB
`heckeFEPair_Λ_real`): the Dirichlet series runs over the class inverse to `E`. -/
theorem fePair_Λ_real_of_class (Q : WeakFEPair ℂ) (E : ClassGroup (𝓞 K))
    (hf : ∀ x, Q.f x = (heckeGClass K E x : ℂ)) (hf₀ : Q.f₀ = (classConst K : ℂ))
    (hk : Q.k = 1 / 2) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Q.Λ (σ : ℂ)
      = (((heckeBeta K) ^ (-σ)
          * ((((heckeJacobian K : ℝ≥0)) : ℝ)
            * ∏ w : InfinitePlace K,
              π ^ (-((mult w : ℝ) * σ)) * Real.Gamma ((mult w : ℝ) * σ))
          * ∑' b : {b : (Ideal (𝓞 K))⁰ //
              ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
              ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ))
                ^ (-(2 * σ)) : ℝ) : ℂ) := by
  have hσ' : Q.k < (σ : ℂ).re := by
    rw [hk]
    simpa using hσ
  have hM := Q.hasMellin hσ'
  rw [← hM.2]
  have hfshape : ∀ t : ℝ, Q.f t - Q.f₀ = (((heckeGClass K E t - classConst K : ℝ)) : ℂ) := by
    intro t
    rw [hf, hf₀]
    push_cast
    ring
  have hptwise : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ ((σ : ℂ) - 1) • (Q.f t - Q.f₀)
      = (((t ^ (σ - 1) * (heckeGClass K E t - classConst K) : ℝ)) : ℂ) := by
    intro t ht
    rw [hfshape, smul_eq_mul]
    rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_cpow (le_of_lt ht), ← Complex.ofReal_mul]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hptwise, integral_complex_ofReal]
  congr 1
  have hri : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * (heckeGClass K E t - classConst K))
      (Set.Ioi (0:ℝ)) volume := by
    have h1 := hM.1.re
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun t ht => ?_) measurableSet_Ioi
    show RCLike.re ((t : ℂ) ^ ((σ : ℂ) - 1) • (Q.f t - Q.f₀))
      = t ^ (σ - 1) * (heckeGClass K E t - classConst K)
    rw [hptwise t ht]
    exact Complex.ofReal_re _
  have hnnae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      (fun t : ℝ => t ^ (σ - 1) * (heckeGClass K E t - classConst K)) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun t ht => ?_))
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (heckeGClass_dev_nonneg K E ht)
  have hσ0 : (0:ℝ) < σ := lt_trans (by norm_num) hσ
  have h2σ : (1:ℝ) < 2 * σ := by linarith
  have hENN := ennreal_ofReal_integral_heckeGClass_dev_eq K E hσ0 h2σ hri hnnae
  have hlhs_nn : 0 ≤ ∫ t in Set.Ioi (0:ℝ), t ^ (σ - 1) * (heckeGClass K E t - classConst K) :=
    integral_nonneg_of_ae hnnae
  exact (ENNReal.ofReal_eq_ofReal_iff hlhs_nn (classClosedForm_nonneg K E hσ0)).mp hENN


/-! ### Constants, class bookkeeping and the real identity -/

open scoped Classical in
/-- The normalising constant `K₀ = Jac · (2 √π)^(-r₂) = Jac · 2^(-r₂) π^(-r₂/2)`. -/
noncomputable def classK0 : ℝ :=
  ((heckeJacobian K : ℝ≥0) : ℝ) * ((2 * Real.sqrt π)⁻¹) ^ nrComplexPlaces K

theorem classK0_pos : 0 < classK0 K := by
  classical
  have hJ : (0:ℝ) < ((heckeJacobian K : ℝ≥0) : ℝ) := by exact_mod_cast heckeJacobian_pos K
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  unfold classK0
  positivity

/-- Zimmert's conductor `A = |d_K|^{1/2} π^{-n/2}`. -/
noncomputable def classA : ℝ :=
  Real.sqrt |(discr K : ℝ)| * Real.pi ^ (-(Module.finrank ℚ K : ℝ) / 2)

theorem classA_pos : 0 < classA K := by
  have hd : (0:ℝ) < |(discr K : ℝ)| := by
    have := discr_ne_zero K
    positivity
  unfold classA
  have := Real.sqrt_pos.mpr hd
  positivity

/-- The absolute norm on the ideals of a class. -/
noncomputable def classNorm (F : ClassGroup (𝓞 K)) (J : classIdeals K F) : ℝ :=
  (Ideal.absNorm (J.1 : Ideal (𝓞 K)) : ℝ)

theorem one_le_classNorm (F : ClassGroup (𝓞 K)) (J : classIdeals K F) : 1 ≤ classNorm K F J := by
  unfold classNorm
  have hJ : (J.1 : Ideal (𝓞 K)) ≠ ⊥ := by
    intro h
    exact nonZeroDivisors.coe_ne_zero J.1 h
  have h0 : Ideal.absNorm (J.1 : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hJ
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0

theorem summable_classNorm (F : ClassGroup (𝓞 K)) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun J : classIdeals K F => classNorm K F J ^ (-σ) :=
  summable_subtype_ideal_norm_rpow K (fun J => ClassGroup.mk0 J = F) hσ

/-- The class bookkeeping: the AINTLIB sum over `{b // mk0 b = (mk0 J_E)⁻¹}` is the sum over the
ideals of the class `F = E⁻¹`. -/
theorem tsum_repInv_eq (E F : ClassGroup (𝓞 K)) (hF : E⁻¹ = F) (g : (Ideal (𝓞 K))⁰ → ℝ) :
    ∑' b : {b : (Ideal (𝓞 K))⁰ //
        ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹}, g b
      = ∑' J : classIdeals K F, g J.1 := by
  have hE : ClassGroup.mk0 (ClassGroup.mk0_surjective E).choose = E :=
    (ClassGroup.mk0_surjective E).choose_spec
  let e : {b : (Ideal (𝓞 K))⁰ //
      ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹}
      ≃ classIdeals K F :=
    Equiv.subtypeEquivRight (fun b => by rw [hE, hF])
  exact Equiv.tsum_eq e (fun J : classIdeals K F => g J.1)

open scoped Classical in
/-- **The constant check at real `s > 1`**: the AINTLIB closed form at `σ = s/2` is
`K₀ · A^s · Γ(s/2)^(r₁+r₂) Γ((s+1)/2)^r₂ · Σ_{J ∈ F} N(J)^{-s}`. -/
theorem classClosedForm_eq (E F : ClassGroup (𝓞 K)) (hF : E⁻¹ = F) {s : ℝ} (hs : 1 < s) :
    (heckeBeta K) ^ (-(s / 2))
      * ((((heckeJacobian K : ℝ≥0)) : ℝ)
        * ∏ w : InfinitePlace K,
          π ^ (-((mult w : ℝ) * (s / 2))) * Real.Gamma ((mult w : ℝ) * (s / 2)))
      * ∑' b : {b : (Ideal (𝓞 K))⁰ //
          ClassGroup.mk0 b = (ClassGroup.mk0 ((ClassGroup.mk0_surjective E).choose))⁻¹},
          ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-(2 * (s / 2)))
      = classK0 K * classA K ^ s
        * (Real.Gamma (s / 2) ^ (nrRealPlaces K + nrComplexPlaces K)
          * Real.Gamma ((s + 1) / 2) ^ nrComplexPlaces K)
        * ∑' J : classIdeals K F, classNorm K F J ^ (-s) := by
  have hs0 : 0 < s := lt_trans one_pos hs
  have h2s : 2 * (s / 2) = s := by ring
  rw [h2s, tsum_repInv_eq K E F hF
    (fun b => ((Ideal.absNorm ((b : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ)) ^ (-s)),
    prod_place_gamma K (s / 2), h2s]
  have hDpos := natAbs_discr_pos K
  -- β^{-s/2} = (2^{-s})^{r₂} |d|^{s/2}
  have hβsplit : (heckeBeta K) ^ (-(s/2))
      = ((2:ℝ) ^ (-s)) ^ (nrComplexPlaces K)
        * (((discr K).natAbs : ℕ) : ℝ) ^ ((s:ℝ)/2) := by
    rw [heckeBeta, Real.div_rpow (by positivity) hDpos.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg hDpos.le]
    congr 1
    · rw [← Real.rpow_natCast (4:ℝ) (nrComplexPlaces K), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((2:ℝ) ^ (-s)) (nrComplexPlaces K),
        ← Real.rpow_mul (by norm_num)]
      rw [show (4:ℝ) = (2:ℝ) ^ ((2:ℕ):ℝ) by
        rw [Real.rpow_natCast]
        norm_num]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    · ring_nf
  -- A^s = |d|^{s/2} (π^{-s/2})^n
  have hDD : |((discr K : ℤ) : ℝ)| = (((discr K).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hAs : classA K ^ s = (((discr K).natAbs : ℕ) : ℝ) ^ ((s:ℝ)/2)
      * (π ^ (-(s / 2))) ^ (nrRealPlaces K + 2 * nrComplexPlaces K) := by
    rw [classA, Real.mul_rpow (Real.sqrt_nonneg _) (Real.rpow_nonneg Real.pi_pos.le _), hDD,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_mul Real.pi_pos.le,
      card_add_two_mul_card_eq_rank, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 2
    · ring
    · ring
  -- π^{-(2·(s/2))}... is (π^{-s/2})^2
  have hπ2 : π ^ (-s) = (π ^ (-(s / 2))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    push_cast
    ring
  -- Legendre duplication: 2^{-s} Γ(s) = Γ(s/2) Γ((s+1)/2) / (2 √π)
  have hleg : (2:ℝ) ^ (-s) * Real.Gamma s
      = Real.Gamma (s / 2) * Real.Gamma ((s + 1) / 2) * (2 * Real.sqrt π)⁻¹ := by
    have h := Real.Gamma_mul_Gamma_add_half (s / 2)
    rw [h2s, show s / 2 + 1 / 2 = (s + 1) / 2 by ring] at h
    rw [h, show (1 : ℝ) - s = 1 + -s by ring, Real.rpow_add (by norm_num), Real.rpow_one]
    have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
  rw [hβsplit, hAs, hπ2, classK0]
  calc ((2:ℝ) ^ (-s)) ^ nrComplexPlaces K * (((discr K).natAbs : ℕ) : ℝ) ^ (s / 2)
        * (((heckeJacobian K : ℝ≥0) : ℝ)
          * ((π ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
            * ((π ^ (-(s / 2))) ^ 2 * Real.Gamma s) ^ nrComplexPlaces K))
        * ∑' J : classIdeals K F, classNorm K F J ^ (-s)
      = (((discr K).natAbs : ℕ) : ℝ) ^ (s / 2) * ((heckeJacobian K : ℝ≥0) : ℝ)
        * (π ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ nrRealPlaces K
        * ((π ^ (-(s / 2))) ^ 2 * ((2:ℝ) ^ (-s) * Real.Gamma s)) ^ nrComplexPlaces K
        * ∑' J : classIdeals K F, classNorm K F J ^ (-s) := by ring
    _ = _ := by
        rw [hleg]
        ring


/-! ### The identity on the half plane `Re s > 1` -/

/-- The right-hand side `K₀ A^s G(s) D_F(s)` of the class identity. -/
noncomputable def classRHS (F : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  (classK0 K : ℂ) * (classA K : ℂ) ^ s
    * Gz (nrRealPlaces K + nrComplexPlaces K) (nrComplexPlaces K) s * dser (classNorm K F) s

/-- The Dirichlet series of a class is differentiable on `Re s > 1`. -/
theorem differentiableAt_dser_classNorm (F : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (dser (classNorm K F)) s := by
  obtain ⟨σ₀, h1, h2⟩ := exists_between hs
  have hU : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (dser (classNorm K F)) {z : ℂ | σ₀ < z.re} := by
    show DifferentiableOn ℂ (fun w : ℂ => ∑' J, ((classNorm K F J : ℝ) : ℂ) ^ (-w)) _
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun J => classNorm K F J ^ (-σ₀))
      (summable_classNorm K F h1) (fun J => ?_) hU (fun J z hz => ?_)
    · have hN : ((classNorm K F J : ℝ) : ℂ) ≠ 0 := by
        have := one_le_classNorm K F J
        exact_mod_cast (show classNorm K F J ≠ 0 by linarith)
      exact fun z _ => (differentiableAt_id.neg.const_cpow (Or.inl hN)).differentiableWithinAt
    · have hN1 := one_le_classNorm K F J
      have hNpos : 0 < classNorm K F J := by linarith
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos, Complex.neg_re]
      have hz' : σ₀ < z.re := hz
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  exact hd.differentiableAt (hU.mem_nhds h2)

theorem differentiableAt_Gamma_half {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
  refine DifferentiableAt.comp (𝕜 := ℂ) (g := Complex.Gamma) (f := fun w : ℂ => w / 2) s ?_
    (by fun_prop)
  refine Complex.differentiableAt_Gamma _ (fun m h => ?_)
  have hz2 : s = (-(2 * (m : ℂ))) := by linear_combination (2:ℂ) * h
  rw [hz2] at hs
  rw [show (-(2 * (m : ℂ))).re = -(2 * (m : ℝ)) by simp] at hs
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem differentiableAt_Gz {a b : ℕ} {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Gz a b) s := by
  have h1 := differentiableAt_Gamma_half hs
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + 1) / 2)) s := by
    have hs1 : 0 < (s + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have := differentiableAt_Gamma_half hs1
    exact this.comp (𝕜 := ℂ) (g := fun z : ℂ => Complex.Gamma (z / 2))
      (f := fun z : ℂ => z + 1) s (by fun_prop)
  exact (h1.pow a).mul (h2.pow b)

theorem analyticOnNhd_classRHS (F : ClassGroup (𝓞 K)) :
    AnalyticOnNhd ℂ (classRHS K F) {z : ℂ | 1 < z.re} := by
  have hUopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hUopen
  intro z hz
  have hz' : 1 < z.re := hz
  have hA0 : (classA K : ℂ) ≠ 0 := by exact_mod_cast (classA_pos K).ne'
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (((differentiableAt_const _).mul ?_).mul ?_).mul ?_
  · exact differentiableAt_id.const_cpow (Or.inl hA0)
  · exact differentiableAt_Gz (by linarith)
  · exact differentiableAt_dser_classNorm K F hz'

theorem analyticOnNhd_fePair_Λ_half (Q : WeakFEPair ℂ) (hk : Q.k = 1 / 2) :
    AnalyticOnNhd ℂ (fun s : ℂ => Q.Λ (s / 2)) {z : ℂ | 1 < z.re} := by
  have hUopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hUopen
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hz' : 1 < z.re := hz
  have hz2 : z / 2 ≠ 0 := by
    intro h
    have : z = 0 := by linear_combination (2:ℂ) * h
    rw [this, Complex.zero_re] at hz'
    linarith
  have hzk : z / 2 ≠ ((Q.k : ℝ) : ℂ) := by
    intro h
    rw [hk] at h
    have : z = 1 := by
      push_cast at h
      linear_combination (2:ℂ) * h
    rw [this, Complex.one_re] at hz'
    linarith
  have hd := Q.differentiableAt_Λ (Or.inl hz2) (Or.inl hzk)
  exact DifferentiableAt.comp (𝕜 := ℂ) (g := Q.Λ) (f := fun w : ℂ => w / 2) z hd (by fun_prop)

/-- `classRHS` at a real point is real. -/
theorem classRHS_ofReal (F : ClassGroup (𝓞 K)) (x : ℝ) :
    classRHS K F (x : ℂ)
      = ((classK0 K * classA K ^ x
          * (Real.Gamma (x / 2) ^ (nrRealPlaces K + nrComplexPlaces K)
            * Real.Gamma ((x + 1) / 2) ^ nrComplexPlaces K)
          * ∑' J : classIdeals K F, classNorm K F J ^ (-x) : ℝ) : ℂ) := by
  have h1 : (classA K : ℂ) ^ (x : ℂ) = ((classA K ^ x : ℝ) : ℂ) :=
    (Complex.ofReal_cpow (classA_pos K).le x).symm
  have h2 : Complex.Gamma ((x : ℂ) / 2) = (Real.Gamma (x / 2) : ℂ) := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  have h3 : Complex.Gamma (((x : ℂ) + 1) / 2) = (Real.Gamma ((x + 1) / 2) : ℂ) := by
    rw [show ((x : ℂ) + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal]
  have h4 : dser (classNorm K F) (x : ℂ)
      = ((∑' J : classIdeals K F, classNorm K F J ^ (-x) : ℝ) : ℂ) := by
    unfold dser
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun J => ?_)
    rw [Complex.ofReal_cpow (le_trans zero_le_one (one_le_classNorm K F J))]
    push_cast
    rfl
  unfold classRHS Gz
  rw [h1, h2, h3, h4]
  push_cast
  ring

/-- Frequent agreement near `2` along the real points `2 + 1/(n+1)`. -/
theorem frequently_eq_of_real {f g : ℂ → ℂ} (h : ∀ x : ℝ, 1 < x → f x = g x) :
    ∃ᶠ z in nhdsWithin (2:ℂ) {(2:ℂ)}ᶜ, f z = g z := by
  have htend : Filter.Tendsto (fun n : ℕ => (((2 + (1:ℝ)/(n+1) : ℝ)) : ℂ))
      Filter.atTop (nhdsWithin (2:ℂ) {(2:ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hre : Filter.Tendsto (fun n : ℕ => (2 + (1:ℝ)/(n+1) : ℝ))
          Filter.atTop (𝓝 (2:ℝ)) := by
        have h0 : Filter.Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have := Filter.Tendsto.const_add (2:ℝ) h0
        simpa using this
      have hcomp := (Complex.continuous_ofReal.tendsto (2:ℝ)).comp hre
      refine hcomp.congr (fun n => rfl) |>.mono_right ?_
      rw [show ((2:ℝ) : ℂ) = (2:ℂ) by norm_cast]
    · refine Filter.Eventually.of_forall (fun n => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hreal : (2 + (1:ℝ)/(n+1) : ℝ) = 2 := by exact_mod_cast h
      have hpos : (0:ℝ) < (1:ℝ)/(n+1) := by positivity
      linarith
  refine htend.frequently (Filter.Frequently.of_forall (fun n => ?_))
  have hgt : (1:ℝ) < 2 + (1:ℝ)/(n+1) := by
    have hpos : (0:ℝ) < (1:ℝ)/(n+1) := by positivity
    linarith
  exact h _ hgt

open scoped Classical in
/-- **The class identity on the half plane**: for a pair whose `f` is the class theta `Ĝ_E`,
`Λ(s/2) = K₀ A^s G(s) Σ_{J ∈ E⁻¹} N(J)^{-s}` for `Re s > 1`. -/
theorem fePair_Λ_half_eq_classRHS (Q : WeakFEPair ℂ) (E F : ClassGroup (𝓞 K)) (hF : E⁻¹ = F)
    (hf : ∀ x, Q.f x = (heckeGClass K E x : ℂ)) (hf₀ : Q.f₀ = (classConst K : ℂ))
    (hk : Q.k = 1 / 2) {s : ℂ} (hs : 1 < s.re) :
    Q.Λ (s / 2) = classRHS K F s := by
  have hUconn : IsPreconnected {z : ℂ | 1 < z.re} :=
    (convex_halfSpace_re_gt 1).isPreconnected
  have h2mem : (2:ℂ) ∈ {z : ℂ | 1 < z.re} := by
    show (1:ℝ) < (2:ℂ).re
    norm_num
  have hfreq : ∃ᶠ z in nhdsWithin (2:ℂ) {(2:ℂ)}ᶜ,
      (fun s : ℂ => Q.Λ (s / 2)) z = classRHS K F z := by
    refine frequently_eq_of_real (fun x hx => ?_)
    show Q.Λ ((x : ℂ) / 2) = classRHS K F x
    have hσ : (1:ℝ) / 2 < x / 2 := by linarith
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      fePair_Λ_real_of_class K Q E hf hf₀ hk hσ, classClosedForm_eq K E F hF hx,
      classRHS_ofReal]
  have hEq := (analyticOnNhd_fePair_Λ_half Q hk).eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_classRHS K F) hUconn h2mem hfreq
  exact hEq hs

end ClassZeta

/-- Zimmert data for the class `C`: the `g` side is `Σ_{J ∈ C} N(J)^{-s}`. -/
theorem exists_zdata {K : Type u} [Field K] [NumberField K] (C : ClassGroup (𝓞 K)) :
    ∃ (ιf : Type u) (D : ZData (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K)
        (InfinitePlace.nrComplexPlaces K) ιf (classIdeals K C)),
      D.A = Real.sqrt |(discr K : ℝ)| * Real.pi ^ (-(Module.finrank ℚ K : ℝ) / 2) ∧
      ∀ J : classIdeals K C, D.μ J = (Ideal.absNorm (J.1 : Ideal (𝓞 K)) : ℝ) := by
  classical
  set P : WeakFEPair ℂ := classFEPair K C⁻¹ with hP
  have hK₀ : (classK0 K : ℂ) ≠ 0 := by exact_mod_cast (classK0_pos K).ne'
  have hPk : P.k = 1 / 2 := rfl
  have hPε : P.ε = 1 := rfl
  have hPf₀ : P.f₀ = (classConst K : ℂ) := rfl
  have hPg₀ : P.g₀ = (classConst K : ℂ) := rfl
  have hSk : P.symm.k = 1 / 2 := rfl
  have hSε : P.symm.ε = 1 := by
    show P.ε⁻¹ = 1
    rw [hPε, inv_one]
  have hSf₀ : P.symm.f₀ = (classConst K : ℂ) := rfl
  have hSg₀ : P.symm.g₀ = (classConst K : ℂ) := rfl
  have hne : ∀ s : ℂ, 1 < s.re → s ≠ 0 ∧ s ≠ 1 := by
    intro s hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, Complex.zero_re] at hs
      linarith
    · rw [h, Complex.one_re] at hs
      exact lt_irrefl _ hs
  have hcancel : ∀ X : ℂ, (classK0 K : ℂ)⁻¹ * ((classK0 K : ℂ) * X) = X := fun X =>
    inv_mul_cancel_left₀ hK₀ X
  refine ⟨classIdeals K (FurioLombardo.Vendor.AINTLIB.DedekindResidue.dualClass K C⁻¹)⁻¹,
    { A := classA K
      hA := classA_pos K
      ν := classNorm K (FurioLombardo.Vendor.AINTLIB.DedekindResidue.dualClass K C⁻¹)⁻¹
      μ := classNorm K C
      hν := one_le_classNorm K _
      hμ := one_le_classNorm K C
      hνs := fun σ hσ => summable_classNorm K _ hσ
      hμs := fun σ hσ => summable_classNorm K C hσ
      Lf := fun s => (classK0 K : ℂ)⁻¹ * P.symm.Λ₀ (s / 2)
      Lg := fun s => (classK0 K : ℂ)⁻¹ * P.Λ₀ (s / 2)
      κ := 2 * (classConst K : ℂ) / (classK0 K : ℂ)
      hLf := ?_
      hfe := ?_
      hstrip := ?_
      hdf := ?_
      hdg := ?_ }, rfl, fun J => rfl⟩
  · exact (P.symm.differentiable_Λ₀.comp (by fun_prop : Differentiable ℂ fun s : ℂ => s / 2)
      ).const_mul _
  · intro s
    show (classK0 K : ℂ)⁻¹ * P.symm.Λ₀ (s / 2) = (classK0 K : ℂ)⁻¹ * P.Λ₀ ((1 - s) / 2)
    rw [fePair_symm_Λ₀_half P hPε hPk s]
  · intro σ₁ σ₂
    obtain ⟨B, hB⟩ := fePair_exists_Λ₀_strip_bound P.symm (σ₁ / 2) (σ₂ / 2)
    refine ⟨‖(classK0 K : ℂ)⁻¹‖ * B, fun s h1 h2 => ?_⟩
    have hre : (s / 2).re = s.re / 2 := by simp
    show ‖(classK0 K : ℂ)⁻¹ * P.symm.Λ₀ (s / 2)‖ ≤ ‖(classK0 K : ℂ)⁻¹‖ * B
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB (s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith))
      (norm_nonneg _)
  · intro s hs
    obtain ⟨hs0, hs1⟩ := hne s hs
    show (classK0 K : ℂ)⁻¹ * P.symm.Λ₀ (s / 2) - 2 * (classConst K : ℂ) / (classK0 K : ℂ) / s
        + 2 * (classConst K : ℂ) / (classK0 K : ℂ) / (s - 1) = _
    rw [fePair_Λ₀_half_sub_polar P.symm hK₀ hSf₀ hSg₀ hSε hSk hs0 hs1,
      fePair_Λ_half_eq_classRHS K P.symm (FurioLombardo.Vendor.AINTLIB.DedekindResidue.dualClass K C⁻¹) _ rfl (fun x => rfl)
        hSf₀ hSk hs,
      classRHS, mul_assoc, mul_assoc, hcancel, ← mul_assoc]
  · intro s hs
    obtain ⟨hs0, hs1⟩ := hne s hs
    show (classK0 K : ℂ)⁻¹ * P.Λ₀ (s / 2) - 2 * (classConst K : ℂ) / (classK0 K : ℂ) / s
        + 2 * (classConst K : ℂ) / (classK0 K : ℂ) / (s - 1) = _
    rw [fePair_Λ₀_half_sub_polar P hK₀ hPf₀ hPg₀ hPε hPk hs0 hs1,
      fePair_Λ_half_eq_classRHS K P C⁻¹ C (inv_inv C) (fun x => rfl) hPf₀ hPk hs,
      classRHS, mul_assoc, mul_assoc, hcancel, ← mul_assoc]

end FurioLombardo.M2.Zimmert
