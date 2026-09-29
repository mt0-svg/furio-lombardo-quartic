import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.M3a.SelmerK2

/-!
# The global span through `K[T]/(f) ≅ L × N` (generic part)

For `f = q · (c h)` with `q`, `h` monic irreducible and coprime, roots `x ∈ L` of `q` and `y ∈ N`
of `h`, and `[L : K] + [N : K] = deg f`:

* `crtHom_bijective`: `T ↦ (x, y)` is an isomorphism `K[T]/(f) ≅ L × N`;
* `mk_eq_prod_of_components`: a unit `z` of `K[T]/(f)` whose two components, times a product of
  the components of units `u s`, are `κ y₁²` and `κ y₂²` with the same `κ ∈ K^×`, has the class
  `∏ [u s]^(a s)` in `H f`;
* `CompCond`, `components_of_isSquare`: the component condition, from one S-unit square in each field, for a family
  `p` indexed by `Fin (m₁ + m₂)` whose first `m₁` members are `(g₁ i, 1)` and last `m₂` are
  `(1, g₂ j)`;
* `globalSpan_of_components`: `GlobalSpan f` from these component conditions, one point at a time.

Auxiliary lemmas: `dvd_of_aeval_eq_zero_pair`,
`isUnit_prod_iff_ne_zero`, `exists_units_sq_of_equiv`, `bijective_of_injective_finrank`,
`finrank_adjoinRoot`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.GlobalGen

open Polynomial FurioLombardo.M3a.Genus2

/-! ## Auxiliary lemmas -/

theorem dvd_of_aeval_eq_zero_pair {K L N : Type*} [Field K] [Field L] [Field N] [Algebra K L]
    [Algebra K N] {q h P : K[X]} (hq : q.Monic) (hh : h.Monic) (hqi : Irreducible q)
    (hhi : Irreducible h) (hqh : IsCoprime q h) {α : L} {β : N} (hα : aeval α q = 0)
    (hβ : aeval β h = 0) (hPα : aeval α P = 0) (hPβ : aeval β P = 0) : q * h ∣ P := by
  have hq_eq_minpoly : q = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hqi hα hq
  have hh_eq_minpoly : h = minpoly K β :=
    minpoly.eq_of_irreducible_of_monic hhi hβ hh
  have hq_dvd_P : q ∣ P := by
    rw [hq_eq_minpoly]
    exact minpoly.dvd K α hPα
  have hh_dvd_P : h ∣ P := by
    rw [hh_eq_minpoly]
    exact minpoly.dvd K β hPβ
  exact IsCoprime.mul_dvd hqh hq_dvd_P hh_dvd_P

theorem isUnit_prod_iff_ne_zero {L N : Type*} [Field L] [Field N] (x : L × N) :
    IsUnit x ↔ x.1 ≠ 0 ∧ x.2 ≠ 0 := by
  simp [Prod.isUnit_iff, isUnit_iff_ne_zero]

theorem exists_units_sq_of_equiv {A L N : Type*} [CommRing A] [Field L] [Field N]
    (e : A ≃+* L × N) (z : A) (y1 : L) (y2 : N) (h1 : y1 ≠ 0) (h2 : y2 ≠ 0)
    (hz : e z = (y1 ^ 2, y2 ^ 2)) : ∃ Y : Aˣ, z = (Y : A) ^ 2 := by
  have hy_unit : IsUnit (y1, y2) := by
    refine Prod.isUnit_iff.mpr ⟨?_, ?_⟩
    · exact (isUnit_iff_ne_zero.mpr h1)
    · exact (isUnit_iff_ne_zero.mpr h2)
  let Y0 := e.symm (y1, y2)
  have hY0_unit : IsUnit Y0 := IsUnit.map (e.symm : L × N →+* A) hy_unit
  set Y := hY0_unit.unit with hY_def
  have hY_eq : (Y : A) = Y0 := by
    rw [hY_def, IsUnit.unit_spec]
  have h_eq : e ((Y : A) ^ 2) = e z := by
    calc
      e ((Y : A) ^ 2) = (e (Y : A)) ^ 2 := by rw [map_pow]
      _ = (e Y0) ^ 2 := by rw [hY_eq]
      _ = ((y1, y2)) ^ 2 := by rw [RingEquiv.apply_symm_apply]
      _ = (y1 ^ 2, y2 ^ 2) := by rfl
      _ = e z := by rw [← hz]
  refine ⟨Y, e.injective h_eq.symm⟩

theorem bijective_of_injective_finrank {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A]
    [Algebra K B] [FiniteDimensional K A] [FiniteDimensional K B] (φ : A →ₐ[K] B)
    (hφ : Function.Injective φ) (hd : Module.finrank K A = Module.finrank K B) :
    Function.Bijective φ := by
  have h_surj : Function.Surjective φ :=
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd (f := φ.toLinearMap)).mp hφ)
  exact ⟨hφ, h_surj⟩

theorem finrank_adjoinRoot {K : Type*} [Field K] {f : K[X]} (hf : f ≠ 0) :
    Module.finrank K (AdjoinRoot f) = f.natDegree := by
  calc
    Module.finrank K (AdjoinRoot f) = (AdjoinRoot.powerBasis hf).dim := PowerBasis.finrank _
    _ = f.natDegree := AdjoinRoot.powerBasis_dim hf

/-! ## The isomorphism -/

variable {K L N : Type*} [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]

theorem aeval_prod_mk (x : L) (y : N) (p : K[X]) : aeval (x, y) p = (aeval x p, aeval y p) := by
  ext
  · exact (aeval_algHom_apply (AlgHom.fst K L N) (x, y) p).symm
  · exact (aeval_algHom_apply (AlgHom.snd K L N) (x, y) p).symm

/-- `T ↦ (x, y)`. -/
noncomputable def crtHom (f : K[X]) (x : L) (y : N) (h : aeval (x, y) f = 0) :
    AdjoinRoot f →ₐ[K] L × N :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId K (L × N)) (x, y) (by rw [← h, aeval_def]; rfl)

theorem crtHom_mk (f : K[X]) (x : L) (y : N) (h : aeval (x, y) f = 0) (P : K[X]) :
    crtHom f x y h (AdjoinRoot.mk f P) = (aeval x P, aeval y P) := by
  rw [← aeval_prod_mk, aeval_def]
  rfl

theorem aeval_pair_eq_zero {f q h : K[X]} {c : K} (hf : f = q * (C c * h)) {x : L} {y : N}
    (hx : aeval x q = 0) (hy : aeval y h = 0) : aeval (x, y) f = 0 := by
  rw [aeval_prod_mk, hf]
  simp [hx, hy]

theorem crtHom_bijective {f q h : K[X]} {c : K} (hc : c ≠ 0) (hf : f = q * (C c * h))
    (hq : q.Monic) (hh : h.Monic) (hqi : Irreducible q) (hhi : Irreducible h)
    (hqh : IsCoprime q h) {x : L} {y : N} (hx : aeval x q = 0) (hy : aeval y h = 0)
    [FiniteDimensional K L] [FiniteDimensional K N]
    (hdim : Module.finrank K L + Module.finrank K N = f.natDegree) :
    Function.Bijective (crtHom f x y (aeval_pair_eq_zero hf hx hy)) := by
  have hf0 : f ≠ 0 := by
    rw [hf]
    exact mul_ne_zero hq.ne_zero (mul_ne_zero (C_ne_zero.mpr hc) hh.ne_zero)
  have : FiniteDimensional K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  refine bijective_of_injective_finrank _ ?_ ?_
  · refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [crtHom_mk, Prod.mk_eq_zero] at ha
    have hdvd := dvd_of_aeval_eq_zero_pair hq hh hqi hhi hqh hx hy ha.1 ha.2
    rw [AdjoinRoot.mk_eq_zero]
    have hfqh : f = C c * (q * h) := by rw [hf]; ring
    rw [hfqh]
    exact (C_mul_dvd hc).mpr hdvd
  · rw [finrank_adjoinRoot hf0, Module.finrank_prod, hdim]

/-- The isomorphism `K[T]/(f) ≅ L × N`, `T ↦ (x, y)`. -/
noncomputable def crtEquiv {f q h : K[X]} {c : K} (hc : c ≠ 0) (hf : f = q * (C c * h))
    (hq : q.Monic) (hh : h.Monic) (hqi : Irreducible q) (hhi : Irreducible h)
    (hqh : IsCoprime q h) {x : L} {y : N} (hx : aeval x q = 0) (hy : aeval y h = 0)
    [FiniteDimensional K L] [FiniteDimensional K N]
    (hdim : Module.finrank K L + Module.finrank K N = f.natDegree) :
    AdjoinRoot f ≃ₐ[K] L × N :=
  AlgEquiv.ofBijective _ (crtHom_bijective hc hf hq hh hqi hhi hqh hx hy hdim)

theorem crtEquiv_mk {f q h : K[X]} {c : K} (hc : c ≠ 0) (hf : f = q * (C c * h))
    (hq : q.Monic) (hh : h.Monic) (hqi : Irreducible q) (hhi : Irreducible h)
    (hqh : IsCoprime q h) {x : L} {y : N} (hx : aeval x q = 0) (hy : aeval y h = 0)
    [FiniteDimensional K L] [FiniteDimensional K N]
    (hdim : Module.finrank K L + Module.finrank K N = f.natDegree) (P : K[X]) :
    crtEquiv hc hf hq hh hqi hhi hqh hx hy hdim (AdjoinRoot.mk f P) = (aeval x P, aeval y P) :=
  crtHom_mk f x y (aeval_pair_eq_zero hf hx hy) P

/-- `P (T)` is a unit when `P (x) ≠ 0` and `P (y) ≠ 0`. -/
theorem isUnit_mk_of_equiv {f : K[X]} (ψ : AdjoinRoot f ≃ₐ[K] L × N) (P : K[X])
    (h1 : (ψ (AdjoinRoot.mk f P)).1 ≠ 0) (h2 : (ψ (AdjoinRoot.mk f P)).2 ≠ 0) :
    IsUnit (AdjoinRoot.mk f P) := by
  have hu : IsUnit (ψ (AdjoinRoot.mk f P)) := (isUnit_prod_iff_ne_zero _).mpr ⟨h1, h2⟩
  have := hu.map ψ.symm
  rwa [AlgEquiv.symm_apply_apply] at this

/-! ## Classes in `H f` from the components -/

theorem mk_eq_prod_of_components {f : K[X]} (ψ : AdjoinRoot f ≃ₐ[K] L × N) {m : ℕ}
    (u : Fin m → (AdjoinRoot f)ˣ) (z : (AdjoinRoot f)ˣ) (κ : K) (hκ : κ ≠ 0) (a : Fin m → ℕ)
    (y1 : L) (y2 : N) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (h1 : (ψ z).1 * ∏ s, (ψ (u s)).1 ^ a s = algebraMap K L κ * y1 ^ 2)
    (h2 : (ψ z).2 * ∏ s, (ψ (u s)).2 ^ a s = algebraMap K N κ * y2 ^ 2) :
    (QuotientGroup.mk z : H f) = ∏ s, (QuotientGroup.mk (u s) : H f) ^ a s := by
  have hYu : IsUnit (ψ.symm (y1, y2)) :=
    ((isUnit_prod_iff_ne_zero (y1, y2)).mpr ⟨hy1, hy2⟩).map ψ.symm
  set Y : (AdjoinRoot f)ˣ := hYu.unit with hYdef
  have hYval : ψ (Y : AdjoinRoot f) = (y1, y2) := by
    rw [hYdef, IsUnit.unit_spec, AlgEquiv.apply_symm_apply]
  set W : (AdjoinRoot f)ˣ := z * ∏ s, u s ^ a s with hW
  have hWval : (W : AdjoinRoot f) = algebraMap K (AdjoinRoot f) κ * (Y : AdjoinRoot f) ^ 2 := by
    apply ψ.injective
    rw [map_mul, map_pow, AlgEquiv.commutes, hYval, hW, Units.val_mul, map_mul, Units.coe_prod,
      map_prod]
    ext
    · simp only [Prod.fst_mul, Prod.fst_prod, Units.val_pow_eq_pow_val, map_pow, Prod.pow_fst,
        Prod.algebraMap_apply]
      exact h1
    · simp only [Prod.snd_mul, Prod.snd_prod, Units.val_pow_eq_pow_val, map_pow, Prod.pow_snd,
        Prod.algebraMap_apply]
      exact h2
  have hWmem : W ∈ sqClass f := by
    have hWeq : W = Units.map (algebraMap K (AdjoinRoot f)).toMonoidHom (Units.mk0 κ hκ) * Y ^ 2 := by
      ext
      rw [hWval]
      simp
    rw [hWeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨Units.mk0 κ hκ, rfl⟩)
      (Subgroup.mem_sup_right ⟨Y, rfl⟩)
  have hW1 : (QuotientGroup.mk W : H f) = 1 := (QuotientGroup.eq_one_iff W).mpr hWmem
  have hsplit : (QuotientGroup.mk W : H f) =
      (QuotientGroup.mk z : H f) * ∏ s, (QuotientGroup.mk (u s) : H f) ^ a s := by
    rw [hW, QuotientGroup.mk_mul]
    congr 1
    exact map_prod (QuotientGroup.mk' (sqClass f)) (fun s => u s ^ a s) Finset.univ
  rw [hW1] at hsplit
  have hX : (∏ s, (QuotientGroup.mk (u s) : H f) ^ a s)⁻¹ = ∏ s, (QuotientGroup.mk (u s) : H f) ^ a s :=
    inv_eq_of_mul_eq_one_right (by
      rw [← sq]; exact FurioLombardo.Discharge.M3a.H_sq_eq_one f _)
  exact (eq_inv_of_mul_eq_one_left hsplit.symm).trans hX

/-- The component condition on `(x₁, x₂) ∈ L × N` for the family `(p₁ s, p₂ s)`: one `κ ∈ K^×` and one
exponent vector `a` with `x₁ ∏ p₁^a = κ y₁²` and `x₂ ∏ p₂^a = κ y₂²`. -/
def CompCond (K : Type*) {L N : Type*} [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
    {m : ℕ} (x1 : L) (x2 : N) (p1 : Fin m → L) (p2 : Fin m → N) : Prop :=
  ∃ κ : K, κ ≠ 0 ∧ ∃ a : Fin m → ℕ, ∃ y1 : L, ∃ y2 : N, y1 ≠ 0 ∧ y2 ≠ 0 ∧
    x1 * ∏ s, p1 s ^ a s = algebraMap K L κ * y1 ^ 2 ∧
    x2 * ∏ s, p2 s ^ a s = algebraMap K N κ * y2 ^ 2

/-- The two components from one square in each field. -/
theorem components_of_isSquare {m1 m2 : ℕ} (κ : K) (hκ : κ ≠ 0) (x1 : L) (x2 : N) (hx1 : x1 ≠ 0)
    (hx2 : x2 ≠ 0) (g1 : Fin m1 → L) (g2 : Fin m2 → N) (hg1 : ∀ i, g1 i ≠ 0) (hg2 : ∀ j, g2 j ≠ 0)
    (p1 : Fin (m1 + m2) → L) (p2 : Fin (m1 + m2) → N)
    (hp1l : ∀ i, p1 (Fin.castAdd m2 i) = g1 i) (hp1r : ∀ j, p1 (Fin.natAdd m1 j) = 1)
    (hp2l : ∀ i, p2 (Fin.castAdd m2 i) = 1) (hp2r : ∀ j, p2 (Fin.natAdd m1 j) = g2 j)
    (a1 : Fin m1 → ℕ) (a2 : Fin m2 → ℕ)
    (h1 : IsSquare (x1 / algebraMap K L κ * ∏ i, g1 i ^ a1 i))
    (h2 : IsSquare (x2 / algebraMap K N κ * ∏ j, g2 j ^ a2 j)) :
    CompCond K x1 x2 p1 p2 := by
  obtain ⟨r1, hr1⟩ := h1
  obtain ⟨r2, hr2⟩ := h2
  have hκL : algebraMap K L κ ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  have hκN : algebraMap K N κ ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  have hP1 : ∏ i, g1 i ^ a1 i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hg1 i)
  have hP2 : ∏ j, g2 j ^ a2 j ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hg2 j)
  have hr1' : r1 ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr1
    exact mul_ne_zero (div_ne_zero hx1 hκL) hP1 hr1
  have hr2' : r2 ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr2
    exact mul_ne_zero (div_ne_zero hx2 hκN) hP2 hr2
  refine ⟨κ, hκ, Fin.append a1 a2, r1, r2, hr1', hr2', ?_, ?_⟩
  · rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, hp1l, hp1r, one_pow, Finset.prod_const_one,
      mul_one]
    rw [sq, ← hr1]
    field_simp
  · rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, hp2l, hp2r, one_pow, Finset.prod_const_one,
      one_mul]
    rw [sq, ← hr2]
    field_simp

/-- **`GlobalSpan` from the component conditions.** -/
theorem globalSpan_of_components (f : K[X]) [GoodSextic f] (ψ : AdjoinRoot f ≃ₐ[K] L × N)
    {m : ℕ} (u : Fin m → (AdjoinRoot f)ˣ)
    (hμ : ∀ Q : Jac f, ∃ z : (AdjoinRoot f)ˣ, muJ f Q = QuotientGroup.mk z ∧
      CompCond K (ψ z).1 (ψ z).2 (fun s => (ψ (u s)).1) (fun s => (ψ (u s)).2)) :
    GlobalSpan f (fun s => (QuotientGroup.mk (u s) : H f)) := by
  intro Q
  obtain ⟨z, hz, κ, hκ, a, y1, y2, hy1, hy2, h1, h2⟩ := hμ Q
  exact ⟨a, hz.trans (mk_eq_prod_of_components ψ u z κ hκ a y1 y2 hy1 hy2 h1 h2)⟩

end FurioLombardo.Discharge.SelmerBasis.GlobalGen
