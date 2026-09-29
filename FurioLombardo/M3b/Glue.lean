import FurioLombardo.M3b.Abstract
import FurioLombardo.M3b.Chevalley

/-!
# Lane M3b: the Galois data of a quadratic extension of number fields

For `L/K` quadratic with nontrivial automorphism `σ`: `σ` on `Lˣ`, on `𝓞 L` and on the invertible
fractional ideals of `L`; Hilbert 90 for `Lˣ` (Mathlib's `groupCohomology.exists_div_of_norm_eq_one`)
and for ideals (`b = 1 + a`); the `InvData` instance `galData` and the identification of its pieces:
`E = (𝓞 L)ˣ`, `E⁺ = (𝓞 K)ˣ`, `E ∩ N(Lˣ) = normUnits K L`, `fix Lˣ = Kˣ`, `PK = ext(P_K)`.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.M3b

open NumberField
open scoped nonZeroDivisors

section NumberFieldGlue

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `σ` restricted to the ring of integers of `L`. -/
noncomputable def sigmaO (σ : L ≃ₐ[K] L) : 𝓞 L ≃+* 𝓞 L :=
  NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv

theorem sigmaO_apply (σ : L ≃ₐ[K] L) (x : 𝓞 L) : ((sigmaO σ x : 𝓞 L) : L) = σ (x : L) := rfl

/-- `σ` on `Lˣ`. -/
noncomputable def sigmaX (σ : L ≃ₐ[K] L) : Lˣ →* Lˣ := Units.map (σ : L →* L)

theorem coe_sigmaX (σ : L ≃ₐ[K] L) (x : Lˣ) : ((sigmaX σ x : Lˣ) : L) = σ (x : L) := rfl

/-- `σ` on the invertible fractional ideals of `L`. -/
noncomputable def sigmaI (σ : L ≃ₐ[K] L) :
    (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  Units.map (FractionalIdeal.ringEquivOfRingEquiv L L (sigmaO σ)).toMonoidHom

theorem coe_sigmaI (σ : L ≃ₐ[K] L) (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    ((sigmaI σ a : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      FractionalIdeal.ringEquivOfRingEquiv L L (sigmaO σ) (a : FractionalIdeal (𝓞 L)⁰ L) := rfl

variable (K L) in
/-- Extension of invertible fractional ideals from `K` to `L`. -/
noncomputable def extU : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  Units.map (FractionalIdeal.extendedHom L (𝓞 L)).toMonoidHom

theorem coe_extU (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((extU K L b : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      FractionalIdeal.extendedHom L (𝓞 L) (b : FractionalIdeal (𝓞 K)⁰ K) := rfl

variable (K L) in
/-- Units of `𝓞 K` inside `Lˣ`. -/
noncomputable def iotaK : (𝓞 K)ˣ →* Lˣ := Units.map (algebraMap (𝓞 K) L).toMonoidHom

theorem coe_iotaK (u : (𝓞 K)ˣ) : ((iotaK K L u : Lˣ) : L) = algebraMap (𝓞 K) L (u : 𝓞 K) := rfl




theorem ringEquivOfRingEquiv_sigmaO_apply (σ : L ≃ₐ[K] L) (x : L) :
    IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) (sigmaO σ) x = σ x := by
  have h : (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) (sigmaO σ)).toRingHom =
      (σ : L →+* L) := by
    refine IsLocalization.ringHom_ext (𝓞 L)⁰ (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rfl
  exact congrArg (fun f : L →+* L => f x) h

theorem toPrincipalIdeal_sigmaX (σ : L ≃ₐ[K] L) (x : Lˣ) :
    toPrincipalIdeal (𝓞 L) L (sigmaX σ x) = sigmaI σ (toPrincipalIdeal (𝓞 L) L x) := by
  apply Units.ext
  rw [coe_sigmaI, coe_toPrincipalIdeal, coe_toPrincipalIdeal,
    FractionalIdeal.ringEquivOfRingEquiv_spanSingleton, ringEquivOfRingEquiv_sigmaO_apply,
    coe_sigmaX]

theorem sigmaX_sigmaX (σ : L ≃ₐ[K] L) (hσ : ∀ x, σ (σ x) = x) (x : Lˣ) :
    sigmaX σ (sigmaX σ x) = x := by
  apply Units.ext
  rw [coe_sigmaX, coe_sigmaX, hσ]

theorem sigmaO_sigmaO (σ : L ≃ₐ[K] L) (hσ : ∀ x, σ (σ x) = x) (x : 𝓞 L) :
    sigmaO σ (sigmaO σ x) = x := by
  apply RingOfIntegers.ext
  rw [sigmaO_apply, sigmaO_apply, hσ]

theorem sigmaI_sigmaI (σ : L ≃ₐ[K] L) (hσ : ∀ x, σ (σ x) = x)
    (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : sigmaI σ (sigmaI σ a) = a := by
  apply Units.ext
  rw [coe_sigmaI, coe_sigmaI]
  have h : ((FractionalIdeal.ringEquivOfRingEquiv L L (sigmaO σ)).trans
      (FractionalIdeal.ringEquivOfRingEquiv L L (sigmaO σ))) = RingEquiv.refl _ := by
    rw [← FractionalIdeal.ringEquivOfRingEquiv_trans]
    have : (sigmaO σ).trans (sigmaO σ) = RingEquiv.refl (𝓞 L) :=
      RingEquiv.ext fun x => sigmaO_sigmaO σ hσ x
    rw [this, FractionalIdeal.ringEquivOfRingEquiv_refl]
  exact congrArg (fun f => f (a : FractionalIdeal (𝓞 L)⁰ L)) h

theorem h90I (σ : L ≃ₐ[K] L) (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ)
    (ha : a * sigmaI σ a = 1) : ∃ b, a = b / sigmaI σ b := by
  set f := FractionalIdeal.ringEquivOfRingEquiv L L (sigmaO σ)
  have ha' : (a : FractionalIdeal (𝓞 L)⁰ L) * f a = 1 := by
    have := congrArg Units.val ha
    rwa [Units.val_mul, coe_sigmaI, Units.val_one] at this
  set c : FractionalIdeal (𝓞 L)⁰ L := 1 + (a : FractionalIdeal (𝓞 L)⁰ L)
  have hc : c ≠ 0 := by
    intro h0
    have : (1 : FractionalIdeal (𝓞 L)⁰ L) ≤ c := le_sup_left
    rw [h0, le_zero_iff] at this
    exact one_ne_zero this
  refine ⟨Units.mk0 c hc, ?_⟩
  rw [eq_div_iff_mul_eq']
  apply Units.ext
  rw [Units.val_mul, coe_sigmaI, Units.val_mk0, map_add, map_one, mul_add, mul_one, ha', add_comm]

/-- In a quadratic extension, every automorphism is `1` or the nontrivial one. -/
theorem aut_eq_one_or (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1)
    (τ : L ≃ₐ[K] L) : τ = 1 ∨ τ = σ := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 hcard
  by_cases h : τ = 1
  · exact Or.inl h
  · exact Or.inr ((hy τ h).trans (hy σ hσ1).symm)

theorem sigma_sigma (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (x : L) :
    σ (σ x) = x := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  have := pow_card_eq_one' (G := L ≃ₐ[K] L) (x := σ)
  rw [hcard, sq] at this
  rw [← AlgEquiv.mul_apply, this, AlgEquiv.one_apply]

/-- The norm of a quadratic extension is `x σ(x)`. -/
theorem algebraMap_norm_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.norm K x) = x * σ x := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  rw [Algebra.norm_eq_prod_automorphisms, Fintype.prod_eq_mul 1 σ hσ1.symm]
  · rfl
  · intro τ hτ
    rcases aut_eq_one_or h2 σ hσ1 τ with h | h
    · exact absurd h hτ.1
    · exact absurd h hτ.2

theorem h90X (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hσ1 : σ ≠ 1) (x : Lˣ) (hx : x * sigmaX σ x = 1) : ∃ y, x = y / sigmaX σ y := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have hcyc : IsCyclic (L ≃ₐ[K] L) := by
    refine ⟨⟨σ, fun τ => ?_⟩⟩
    rcases aut_eq_one_or h2 σ hσ1 τ with h | h
    · exact ⟨0, by rw [h]; exact zpow_zero σ⟩
    · exact ⟨1, by rw [h]; exact zpow_one σ⟩
  have hn : Algebra.norm K (x : L) = 1 := by
    apply FaithfulSMul.algebraMap_injective K L
    rw [algebraMap_norm_eq h2 σ hσ1, map_one, ← coe_sigmaX, ← Units.val_mul, hx, Units.val_one]
  have hg : ∀ τ, τ ∈ Subgroup.zpowers σ := by
    intro τ
    rcases aut_eq_one_or h2 σ hσ1 τ with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers σ
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one hg hn
  refine ⟨y, Units.ext ?_⟩
  rw [← hy, Units.val_div_eq_div_val, coe_sigmaX]

/-! ### The kernel of the principal ideal map

Adapted from Michael Stoll, EllipticCurves (commit 1e47094, Apache 2.0),
`EllipticCurves/Mathlib/FractionalIdeal.lean`: `spanSingleton_eq_one_iff`,
`toPrincipalIdeal_eq_one_iff`. -/

theorem spanSingleton_eq_one_iff' {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] {x : F} (hx : x ≠ 0) :
    FractionalIdeal.spanSingleton R⁰ x = 1 ↔ ∃ a : Rˣ, algebraMap R F a = x := by
  constructor
  · intro h
    have hinv : FractionalIdeal.spanSingleton R⁰ x⁻¹ = 1 := by
      rw [← FractionalIdeal.spanSingleton_inv, h, inv_one]
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff R⁰).mp
      (h ▸ FractionalIdeal.mem_spanSingleton_self R⁰ x)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff R⁰).mp
      (hinv ▸ FractionalIdeal.mem_spanSingleton_self R⁰ x⁻¹)
    have hab : a * b = 1 := IsFractionRing.injective R F (by
      rw [map_mul, ha, hb, mul_inv_cancel₀ hx, map_one])
    exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr a.isUnit,
      FractionalIdeal.coeIdeal_top]

theorem toPrincipalIdeal_eq_one_iff' {R F : Type*} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (u : Fˣ) :
    toPrincipalIdeal R F u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R F : R →* F) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, spanSingleton_eq_one_iff' u.ne_zero]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩

/-- The units of `𝓞 L` inside `Lˣ`. -/
noncomputable def iotaL (L : Type) [Field L] [NumberField L] : (𝓞 L)ˣ →* Lˣ :=
  Units.map (algebraMap (𝓞 L) L).toMonoidHom

theorem iotaL_injective : Function.Injective (iotaL L) := by
  intro u v h
  apply Units.ext
  apply RingOfIntegers.ext
  exact congrArg Units.val h

theorem ker_toPrincipalIdeal : (toPrincipalIdeal (𝓞 L) L).ker = (iotaL L).range := by
  ext x
  rw [MonoidHom.mem_ker, toPrincipalIdeal_eq_one_iff']
  rfl

theorem iotaK_injective : Function.Injective (iotaK K L) := by
  intro u v h
  apply Units.ext
  apply RingOfIntegers.ext
  have := congrArg Units.val h
  simp only [coe_iotaK] at this
  have h' : algebraMap K L (u : 𝓞 K) = algebraMap K L (v : 𝓞 K) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]; exact this
  exact (algebraMap K L).injective h'

/-- The data of Chevalley's count for a quadratic extension `L/K`. -/
noncomputable def galData (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    InvData Lˣ (FractionalIdeal (𝓞 L)⁰ L)ˣ where
  sX := sigmaX σ
  sI := sigmaI σ
  φ := toPrincipalIdeal (𝓞 L) L
  sX_sX := sigmaX_sigmaX σ (sigma_sigma h2 σ)
  sI_sI := sigmaI_sigmaI σ (sigma_sigma h2 σ)
  φ_sX := toPrincipalIdeal_sigmaX σ

theorem galData_H90X (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    (galData h2 σ).H90X := fun x hx => h90X h2 σ hσ1 x hx

theorem galData_H90I (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    (galData h2 σ).H90I := fun a ha => h90I σ a ha

theorem galData_E (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    (galData h2 σ).E = (iotaL L).range := ker_toPrincipalIdeal

theorem sigma_iotaK (σ : L ≃ₐ[K] L) (u : (𝓞 K)ˣ) : sigmaX σ (iotaK K L u) = iotaK K L u := by
  apply Units.ext
  rw [coe_sigmaX, coe_iotaK, IsScalarTower.algebraMap_apply (𝓞 K) K L, AlgEquiv.commutes]

theorem iotaK_mem_E (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (u : (𝓞 K)ˣ) :
    iotaK K L u ∈ (galData h2 σ).E := by
  rw [galData_E]
  refine ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom u, Units.ext ?_⟩
  simp only [iotaL, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, coe_iotaK]
  rw [← IsScalarTower.algebraMap_apply]

theorem algebraMap_OK_L_injective : Function.Injective (algebraMap (𝓞 K) L) := by
  rw [IsScalarTower.algebraMap_eq (𝓞 K) K L]
  exact (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)

theorem exists_of_sigma_fixed (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1)
    (w : (𝓞 L)ˣ) (hw : sigmaX σ (iotaL L w) = iotaL L w) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) L a = ((w : 𝓞 L) : L) := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have hτ : ∀ τ : L ≃ₐ[K] L, τ ((w : 𝓞 L) : L) = ((w : 𝓞 L) : L) := by
    intro τ
    rcases aut_eq_one_or h2 σ hσ1 τ with rfl | rfl
    · rfl
    · exact congrArg Units.val hw
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed _).2 hτ)
  have hint : IsIntegral ℤ k := by
    have : IsIntegral ℤ (algebraMap K L k) := by
      rw [hk]; exact RingOfIntegers.isIntegral_coe _
    exact isIntegral_algebraMap_iff.1 this
  exact ⟨(⟨k, (mem_integralClosure_iff ℤ K).2 hint⟩ : 𝓞 K),
    (IsScalarTower.algebraMap_apply (𝓞 K) K L _).trans hk⟩

theorem galData_Eplus (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    (galData h2 σ).Eplus = (iotaK K L).range := by
  ext x
  constructor
  · rintro ⟨hxE, hxfix⟩
    rw [galData_E] at hxE
    obtain ⟨v, rfl⟩ := hxE
    have hv : sigmaX σ (iotaL L v) = iotaL L v := hxfix
    have hv' : sigmaX σ (iotaL L v⁻¹) = iotaL L v⁻¹ := by rw [map_inv, map_inv, hv]
    obtain ⟨a, ha⟩ := exists_of_sigma_fixed h2 σ hσ1 v hv
    obtain ⟨b, hb⟩ := exists_of_sigma_fixed h2 σ hσ1 v⁻¹ hv'
    have hab : a * b = 1 := by
      apply algebraMap_OK_L_injective (K := K) (L := L)
      rw [map_mul, ha, hb, map_one]
      show algebraMap (𝓞 L) L _ * algebraMap (𝓞 L) L _ = 1
      rw [← map_mul, Units.mul_inv, map_one]
    refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, Units.ext ?_⟩
    rw [coe_iotaK]
    exact ha
  · rintro ⟨u, rfl⟩
    exact ⟨iotaK_mem_E h2 σ u, sigma_iotaK σ u⟩

theorem galData_NXE (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    (galData h2 σ).NXE = (normUnits K L).map (iotaK K L) := by
  ext x
  constructor
  · intro hx
    have hplus := (galData h2 σ).NXE_le_Eplus hx
    rw [galData_Eplus h2 σ hσ1] at hplus
    obtain ⟨u, rfl⟩ := hplus
    obtain ⟨y, hy⟩ := hx.2
    refine ⟨u, ⟨(y : L), ?_⟩, rfl⟩
    apply (algebraMap K L).injective
    rw [algebraMap_norm_eq h2 σ hσ1, ← IsScalarTower.algebraMap_apply]
    have := congrArg Units.val hy
    rw [InvData.normX_apply, Units.val_mul] at this
    exact this.trans (coe_iotaK u)
  · rintro ⟨u, ⟨y, hy⟩, rfl⟩
    refine ⟨iotaK_mem_E h2 σ u, ?_⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hy
      exact u.ne_zero (RingOfIntegers.ext (by rw [← hy]; rfl))
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    change y * σ y = _
    rw [← algebraMap_norm_eq h2 σ hσ1, hy, coe_iotaK, ← IsScalarTower.algebraMap_apply]

theorem isFractionRing_map_eq (k : K) :
    IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) k = algebraMap K L k := by
  have h : (IsFractionRing.map (K := K) (L := L)
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) : K →+* L) = algebraMap K L := by
    refine IsLocalization.ringHom_ext (𝓞 K)⁰ (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, IsFractionRing.map, IsLocalization.map_eq]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact congrArg (fun f : K →+* L => f k) h

/-- `σ` on `Lˣ` fixes exactly `Kˣ`. -/
theorem fixX_eq_range (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    (galData h2 σ).fixX = (Units.map (algebraMap K L).toMonoidHom).range := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  ext x
  constructor
  · intro hx
    have hx' : sigmaX σ x = x := hx
    have hτ : ∀ τ : L ≃ₐ[K] L, τ (x : L) = x := by
      intro τ
      rcases aut_eq_one_or h2 σ hσ1 τ with rfl | rfl
      · rfl
      · exact congrArg Units.val hx'
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed _).2 hτ)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [map_zero] at hk
      exact x.ne_zero hk.symm
    exact ⟨Units.mk0 k hk0, Units.ext hk⟩
  · rintro ⟨k, rfl⟩
    show sigmaX σ _ = _
    apply Units.ext
    rw [coe_sigmaX]
    exact σ.commutes (k : K)

theorem extU_toPrincipalIdeal (k : Kˣ) :
    extU K L (toPrincipalIdeal (𝓞 K) K k) =
      toPrincipalIdeal (𝓞 L) L (Units.map (algebraMap K L).toMonoidHom k) := by
  apply Units.ext
  rw [coe_extU, coe_toPrincipalIdeal, coe_toPrincipalIdeal, FractionalIdeal.extendedHom_spanSingleton,
    isFractionRing_map_eq]
  rfl

theorem galData_PK (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    (galData h2 σ).PK = (toPrincipalIdeal (𝓞 K) K).range.map (extU K L) := by
  rw [InvData.PK, fixX_eq_range h2 σ hσ1, MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  exact MonoidHom.ext fun k => (extU_toPrincipalIdeal (L := L) k).symm

end NumberFieldGlue

end FurioLombardo.M3b
