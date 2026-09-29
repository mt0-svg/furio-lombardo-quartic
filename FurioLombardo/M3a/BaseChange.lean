import Mathlib
import FurioLombardo.M3a.Pic

/-!
# Base change of the class group and of the Jacobian (lane M3a)

For a field homomorphism `φ : K →+* K'` (in the application `K21 → k_v`):

* `relNorm_map_baseChange`: the relative norm commutes with base change (sandwich argument: one
  inclusion from the norms of elements, equality from `I * I' = (a)`);
* `picMap φ f : Pic f →* Pic (f.map φ)` (Mathlib's `ClassGroup.extendedHom`), `picMap_mk0`;
* `parity_picMap`: base change preserves the parity; `jacMap φ f : Jac f →* Jac (f.map φ)`, the
  localisation `ι : A(k) → A(k_v)`.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

theorem FurioLombardo.M3a.eq_of_le_of_le_of_mul_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    {A A' B B' : Ideal R} (hA : A ≤ A') (hB : B ≤ B') (h : A * B = A' * B') (h0 : A * B ≠ ⊥) :
    A = A' := by
  have hA_dvd : A' ∣ A := Ideal.dvd_iff_le.mpr hA
  have hB_dvd : B' ∣ B := Ideal.dvd_iff_le.mpr hB
  rcases hA_dvd with ⟨C, hC⟩
  rcases hB_dvd with ⟨D, hD⟩
  have h_nonzero : A' * B' ≠ ⊥ := by rw [← h]; exact h0
  have h_mul : (A' * B') * (C * D) = A' * B' := by
    calc
      (A' * B') * (C * D) = (A' * C) * (B' * D) := by ring
      _ = A * B := by rw [hC, hD]
      _ = A' * B' := h
  have h_cancel : C * D = ⊤ := by
    apply mul_left_cancel₀ h_nonzero
    calc
      (A' * B') * (C * D) = A' * B' := h_mul
      _ = (A' * B') * ⊤ := by simp
  have hC_top : C = ⊤ := by
    have h_le : C * D ≤ C := Ideal.mul_le_left
    rw [h_cancel] at h_le
    exact top_le_iff.mp h_le
  rw [hC, hC_top, Ideal.mul_top]

theorem FurioLombardo.M3a.exists_mul_eq_span_singleton {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) : ∃ a : R, a ≠ 0 ∧ ∃ I' : Ideal R, I * I' = Ideal.span {a} := by
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hle : Ideal.span {a} ≤ I := (Ideal.span_singleton_le_iff_mem (I := I)).mpr haI
  have hdvd : I ∣ Ideal.span {a} := Ideal.dvd_iff_le.mpr hle
  rcases hdvd with ⟨I', hI'⟩
  exact ⟨a, ha0, I', hI'.symm⟩


theorem FurioLombardo.M3a.Genus2.map_relNorm_le_relNorm_map {K : Type*} [Field K] {K' : Type*}
    [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f] [GoodSextic (f.map φ)]
    (I : Ideal (CoordRing f)) :
    (Ideal.relNorm K[X] I).map (Polynomial.mapRingHom φ) ≤
      Ideal.relNorm K'[X] (I.map (baseChange φ f)) := by
  rw [Ideal.relNorm_apply, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [Algebra.intNorm_eq_norm, Polynomial.coe_mapRingHom, ← norm_baseChange]
  exact Ideal.norm_mem_relNorm _ _ (Ideal.mem_map_of_mem _ hx)

theorem FurioLombardo.M3a.Genus2.relNorm_map_baseChange {K : Type*} [Field K] {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f]
    [GoodSextic (f.map φ)] (I : Ideal (CoordRing f)) :
    Ideal.relNorm K'[X] (I.map (baseChange φ f)) =
      (Ideal.relNorm K[X] I).map (Polynomial.mapRingHom φ) := by
  by_cases hI : I = ⊥
  · subst hI
    rw [Ideal.map_bot, Ideal.relNorm_bot, Ideal.relNorm_bot, Ideal.map_bot]
  obtain ⟨a, ha, I', hI'⟩ := exists_mul_eq_span_singleton hI
  set ψ := Polynomial.mapRingHom φ
  set bc := baseChange φ f
  have hψa : ψ (Algebra.norm K[X] a) ≠ 0 := by
    rw [Polynomial.coe_mapRingHom, Ne, Polynomial.map_eq_zero_iff φ.injective]
    exact (norm_ne_zero_and_even ha).1
  have hprod : (Ideal.relNorm K[X] I).map ψ * (Ideal.relNorm K[X] I').map ψ =
      Ideal.relNorm K'[X] (I.map bc) * Ideal.relNorm K'[X] (I'.map bc) := by
    rw [← Ideal.map_mul, ← map_mul, hI', ← map_mul, ← Ideal.map_mul, hI', Ideal.map_span,
      Set.image_singleton, Ideal.relNorm_singleton, Ideal.relNorm_singleton, Ideal.map_span,
      Set.image_singleton, Algebra.intNorm_eq_norm, Algebra.intNorm_eq_norm, norm_baseChange]
    rfl
  have h0 : (Ideal.relNorm K[X] I).map ψ * (Ideal.relNorm K[X] I').map ψ ≠ ⊥ := by
    rw [← Ideal.map_mul, ← map_mul, hI', Ideal.relNorm_singleton, Ideal.map_span,
      Set.image_singleton, Algebra.intNorm_eq_norm, Ne, Ideal.span_singleton_eq_bot]
    exact hψa
  exact (eq_of_le_of_le_of_mul_eq (map_relNorm_le_relNorm_map φ f I)
    (map_relNorm_le_relNorm_map φ f I') hprod h0).symm

theorem FurioLombardo.M3a.Genus2.idealDeg_map {K : Type*} [Field K] {K' : Type*} [Field K'] (φ : K →+* K') (J : Ideal K[X]) :
    idealDeg (J.map (Polynomial.mapRingHom φ)) = idealDeg J := by
  unfold idealDeg
  let g := Submodule.IsPrincipal.generator J
  have hJspan : Ideal.span {g} = J := Ideal.span_singleton_generator J
  have hmap : J.map (Polynomial.mapRingHom φ) = Ideal.span {(Polynomial.mapRingHom φ) g} := by
    rw [← hJspan, Ideal.map_span, Set.image_singleton]
  rw [hmap]
  rw [FurioLombardo.M3a.Genus2.natDegree_generator_span_singleton]
  have hinj : Function.Injective φ := RingHom.injective φ
  have hnatDegree : ((Polynomial.mapRingHom φ) g).natDegree = g.natDegree := by
    simp [Polynomial.mapRingHom, Polynomial.natDegree_map_eq_of_injective hinj g]
  rw [hnatDegree]

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The class group map induced by the base change `φ : K → K'`. -/
noncomputable def picMap {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f]
    [GoodSextic (f.map φ)] : Pic f →* Pic (f.map φ) :=
  letI := (baseChange φ f).toAlgebra
  haveI : FaithfulSMul (CoordRing f) (CoordRing (f.map φ)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (baseChange_injective φ f)
  ClassGroup.extendedHom (CoordRing f) (CoordRing (f.map φ))

end FurioLombardo.M3a.Genus2


theorem FurioLombardo.M3a.Genus2.picMap_mk0 {K : Type*} [Field K] {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f]
    [GoodSextic (f.map φ)] (I : (Ideal (CoordRing f))⁰) (J : (Ideal (CoordRing (f.map φ)))⁰)
    (hJ : (J : Ideal (CoordRing (f.map φ))) = (I : Ideal (CoordRing f)).map (baseChange φ f)) :
    picMap φ f (ClassGroup.mk0 I) = ClassGroup.mk0 J := by
  unfold picMap
  rw [ClassGroup.extendedHom_mk0]
  congr 1
  exact Subtype.ext hJ.symm


theorem FurioLombardo.M3a.Genus2.parity_picMap {K : Type*} [Field K] {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f]
    [GoodSextic (f.map φ)] (c : Pic f) : parity (f.map φ) (picMap φ f c) = parity f c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hne : (I : Ideal (CoordRing f)).map (baseChange φ f) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (baseChange_injective φ f)).not.mpr
      (nonZeroDivisors.ne_zero I.2)
  rw [picMap_mk0 φ f I ⟨_, mem_nonZeroDivisors_of_ne_zero hne⟩ rfl, parity_mk0, parity_mk0]
  change Multiplicative.ofAdd ((normDeg (f.map φ) ((I : Ideal (CoordRing f)).map
    (baseChange φ f)) : ℕ) : ZMod 2) = Multiplicative.ofAdd ((normDeg f I : ℕ) : ZMod 2)
  unfold normDeg
  rw [relNorm_map_baseChange, idealDeg_map]

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The map `A(K) → A(K')` of Jacobians induced by `φ : K → K'`. -/
noncomputable def jacMap {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f]
    [GoodSextic (f.map φ)] : Jac f →* Jac (f.map φ) :=
  ((picMap φ f).comp (Jac f).subtype).codRestrict (Jac (f.map φ)) (fun c => by
    change parity (f.map φ) (picMap φ f c) = 1
    rw [parity_picMap]
    exact c.2)

end FurioLombardo.M3a.Genus2
