import Mathlib
import FurioLombardo.M3b.Chevalley

/-!
# Real places in a quadratic extension `K(√a) = QuadraticAlgebra K a 0`

Generic lemmas for the M3b discharge. `ω` is the class with `ω² = a`.

* `extendHom φ s hs`: the ring homomorphism `QuadraticAlgebra R a 0 → A` extending `φ : R → A` by
  `ω ↦ s` when `s * s = φ a`; every ring homomorphism is of this form (`eq_extendHom`).
* `isReal_of_comap_pos`: a place `w` of `L = K(√a)` above a real place `v` of `K` with `a > 0`
  at `v` is real (the image of `ω` is a real square root).
* `mem_ramifiedRealPlaces_of_neg`: a real place of `K` with `a < 0` is ramified in `L` (the
  embedding `ω ↦ i √(-a)` is not real).
* `neg_of_mem_ramifiedRealPlaces`: conversely a ramified real place has `a < 0`.
* `mul_eq_norm_of_neg`: two real embeddings of `L` with the same restriction to `K` and opposite
  values at `ω` multiply to the norm.
-/

namespace FurioLombardo.Discharge.M3b

open NumberField InfinitePlace QuadraticAlgebra ComplexConjugate

section Ext

variable {R : Type*} [CommRing R] {a : R} {A : Type*} [CommRing A]

/-- The decomposition `x = x.re + x.im ω`. -/
theorem quad_decomp (x : QuadraticAlgebra R a 0) :
    x = algebraMap R _ x.re + algebraMap R _ x.im * ω := by
  ext <;> simp [algebraMap_eq]

theorem omega_mul_omega_zero : (ω : QuadraticAlgebra R a 0) * ω = algebraMap R _ a := by
  rw [omega_mul_omega_eq_algebraMap]; simp

/-- The ring homomorphism `QuadraticAlgebra R a 0 → A` extending `φ` by `ω ↦ s`, `s * s = φ a`. -/
def extendHom (φ : R →+* A) (s : A) (hs : s * s = φ a) : QuadraticAlgebra R a 0 →+* A where
  toFun x := φ x.re + φ x.im * s
  map_one' := by simp [re_one, im_one]
  map_mul' x y := by
    simp only [re_mul, im_mul, map_add, map_mul, zero_mul, add_zero]
    linear_combination (-(φ x.im * φ y.im)) * hs
  map_zero' := by simp
  map_add' x y := by simp only [re_add, im_add, map_add]; ring

theorem extendHom_apply (φ : R →+* A) (s : A) (hs : s * s = φ a) (x : QuadraticAlgebra R a 0) :
    extendHom φ s hs x = φ x.re + φ x.im * s := rfl

@[simp] theorem extendHom_algebraMap (φ : R →+* A) (s : A) (hs : s * s = φ a) (k : R) :
    extendHom φ s hs (algebraMap R (QuadraticAlgebra R a 0) k) = φ k := by
  simp [extendHom_apply, algebraMap_eq]

@[simp] theorem extendHom_omega (φ : R →+* A) (s : A) (hs : s * s = φ a) :
    extendHom φ s hs (ω : QuadraticAlgebra R a 0) = s := by
  simp [extendHom_apply]

theorem extendHom_comp_algebraMap (φ : R →+* A) (s : A) (hs : s * s = φ a) :
    (extendHom φ s hs).comp (algebraMap R (QuadraticAlgebra R a 0)) = φ := by
  ext k; simp

theorem map_omega_mul_self (τ : QuadraticAlgebra R a 0 →+* A) :
    τ ω * τ ω = τ.comp (algebraMap R (QuadraticAlgebra R a 0)) a := by
  rw [← map_mul, omega_mul_omega_zero]; rfl

/-- Every ring homomorphism out of `QuadraticAlgebra R a 0` is an `extendHom`. -/
theorem eq_extendHom (τ : QuadraticAlgebra R a 0 →+* A) :
    τ = extendHom (τ.comp (algebraMap R _)) (τ ω) (map_omega_mul_self τ) := by
  ext x
  conv_lhs => rw [quad_decomp x]
  rw [map_add, map_mul, extendHom_apply]
  rfl

/-- Two ring homomorphisms agreeing on `R` and at `ω` are equal. -/
theorem quad_hom_ext {τ₁ τ₂ : QuadraticAlgebra R a 0 →+* A}
    (h : τ₁.comp (algebraMap R _) = τ₂.comp (algebraMap R _)) (hω : τ₁ ω = τ₂ ω) : τ₁ = τ₂ := by
  ext x
  rw [quad_decomp x, map_add, map_mul, map_add, map_mul, hω]
  have h1 := congrArg (fun f => f x.re) h
  have h2 := congrArg (fun f => f x.im) h
  simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
  rw [h1, h2]

/-- Two homomorphisms with the same restriction and opposite values at `ω` multiply to the norm. -/
theorem mul_eq_norm_of_neg {τ₁ τ₂ : QuadraticAlgebra R a 0 →+* A}
    (h : τ₁.comp (algebraMap R _) = τ₂.comp (algebraMap R _)) (hω : τ₁ ω = -τ₂ ω)
    (x : QuadraticAlgebra R a 0) :
    τ₁ x * τ₂ x = τ₂.comp (algebraMap R _) (norm x) := by
  have hs := map_omega_mul_self τ₂
  have h1 : τ₁ (algebraMap R _ x.re) = τ₂ (algebraMap R _ x.re) := RingHom.congr_fun h x.re
  have h2 : τ₁ (algebraMap R _ x.im) = τ₂ (algebraMap R _ x.im) := RingHom.congr_fun h x.im
  simp only [RingHom.coe_comp, Function.comp_apply] at hs ⊢
  conv_lhs => rw [quad_decomp x, map_add, map_mul, map_add, map_mul, hω, h1, h2]
  rw [norm_def]
  simp only [map_sub, map_add, map_mul, map_zero, zero_mul, add_zero]
  linear_combination (-(τ₂ (algebraMap R _ x.im) * τ₂ (algebraMap R _ x.im))) * hs

/-- The algebra norm of `QuadraticAlgebra R a b` over `R` is its norm. -/
theorem algebra_norm_eq {R : Type*} [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    Algebra.norm R z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  congr 1

end Ext

section Complex

/-- A complex number whose square is a positive real is real. -/
theorem conj_eq_of_mul_self_pos {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z * z = r) : conj z = z := by
  set t := Real.sqrt r
  have ht : (t : ℂ) * t = r := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le]
  have h0 : (z - t) * (z + t) = 0 := by linear_combination hz - ht
  rcases mul_eq_zero.mp h0 with h | h
  · rw [sub_eq_zero.mp h, Complex.conj_ofReal]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, Complex.conj_ofReal]

/-- `ofReal ∘ σ` is a real complex embedding. -/
theorem isReal_ofReal_comp {F : Type*} [Field F] (σ : F →+* ℝ) :
    ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

/-- A real place is the place of the real embedding it defines. -/
theorem mk_ofReal_embedding_of_isReal {F : Type*} [Field F] {v : InfinitePlace F} (hv : v.IsReal) :
    InfinitePlace.mk (Complex.ofRealHom.comp (embedding_of_isReal hv)) = v := by
  have : Complex.ofRealHom.comp (embedding_of_isReal hv) = v.embedding := by
    ext x; simp
  rw [this, mk_embedding]

theorem embedding_of_isReal_mk {F : Type*} [Field F] (σ : F →+* ℝ)
    (h : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal) : embedding_of_isReal h = σ := by
  ext x
  have := embedding_of_isReal_apply h x
  rw [embedding_mk_eq_of_isReal (isReal_ofReal_comp σ)] at this
  exact Complex.ofReal_injective this

/-- Two real places with the same real embedding are equal. -/
theorem eq_of_embedding_of_isReal_eq {F : Type*} [Field F] {v₁ v₂ : InfinitePlace F}
    (h₁ : v₁.IsReal) (h₂ : v₂.IsReal) (h : embedding_of_isReal h₁ = embedding_of_isReal h₂) :
    v₁ = v₂ := by
  rw [← mk_ofReal_embedding_of_isReal h₁, ← mk_ofReal_embedding_of_isReal h₂, h]

end Complex

section Real

variable {K : Type*} [Field K] [NumberField K] {a : K} [Fact (¬ IsSquare a)]
  [NumberField (QuadraticAlgebra K a 0)]

theorem ne_zero_of_not_isSquare : a ≠ 0 := by
  rintro rfl
  exact Fact.out (p := ¬ IsSquare (0 : K)) ⟨0, by simp⟩

/-- A place of `K(√a)` above a real place of `K` where `a > 0` is real. -/
theorem isReal_of_comap_pos (w : InfinitePlace (QuadraticAlgebra K a 0))
    (hv : (w.comap (algebraMap K (QuadraticAlgebra K a 0))).IsReal)
    (hpos : 0 < embedding_of_isReal hv a) : w.IsReal := by
  have hc := comap_embedding_of_isReal (algebraMap K (QuadraticAlgebra K a 0)) hv
  have hre : ∀ k : K, w.embedding (algebraMap K _ k) = (embedding_of_isReal hv k : ℂ) := by
    intro k
    rw [embedding_of_isReal_apply, hc]
    rfl
  have hz : conj (w.embedding ω) = w.embedding ω := by
    refine conj_eq_of_mul_self_pos hpos ?_
    rw [← map_mul, omega_mul_omega_zero, hre]
  rw [isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, quad_decomp x, map_add, map_mul, hre, hre, map_add,
    map_mul, Complex.conj_ofReal, Complex.conj_ofReal, hz]

/-- A real place of `K` where `a < 0` is ramified in `K(√a)`. -/
theorem mem_ramifiedRealPlaces_of_neg (v : InfinitePlace K) (hv : v.IsReal)
    (hneg : embedding_of_isReal hv a < 0) :
    v ∈ FurioLombardo.M3b.ramifiedRealPlaces K (QuadraticAlgebra K a 0) := by
  set σ := embedding_of_isReal hv
  set t := Real.sqrt (-σ a)
  have ht : t * t = -σ a := Real.mul_self_sqrt (by linarith)
  have htpos : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have hs : ((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I) = (Complex.ofRealHom.comp σ) a := by
    have : ((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I) = -((t * t : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [this, ht]; simp
  set Φ := extendHom (Complex.ofRealHom.comp σ) _ hs
  refine ⟨hv, InfinitePlace.mk Φ, ?_, ?_⟩
  · rw [comap_mk, extendHom_comp_algebraMap]
    exact mk_ofReal_embedding_of_isReal hv
  · rw [← not_isReal_iff_isComplex, isReal_mk_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h1 := congrArg (fun f => f (ω : QuadraticAlgebra K a 0)) h
    simp only [ComplexEmbedding.conjugate_coe_eq, Φ, extendHom_omega, map_mul,
      Complex.conj_ofReal, Complex.conj_I] at h1
    have h2 : (t : ℂ) * Complex.I = 0 := by linear_combination (-1 / 2 : ℂ) * h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact htpos.ne' (by exact_mod_cast h3)
    · exact Complex.I_ne_zero h3

/-- At a real place of `K` ramified in `K(√a)`, `a < 0`. -/
theorem neg_of_mem_ramifiedRealPlaces (v : InfinitePlace K)
    (hv : v ∈ FurioLombardo.M3b.ramifiedRealPlaces K (QuadraticAlgebra K a 0)) :
    ∃ h : v.IsReal, embedding_of_isReal h a < 0 := by
  obtain ⟨hvr, w, hw, hwc⟩ := hv
  refine ⟨hvr, ?_⟩
  subst hw
  by_contra hle
  rw [not_lt] at hle
  have hne : embedding_of_isReal hvr a ≠ 0 := by
    rw [map_ne_zero]; exact ne_zero_of_not_isSquare
  exact (not_isReal_iff_isComplex.mpr hwc)
    (isReal_of_comap_pos w hvr (lt_of_le_of_ne hle (Ne.symm hne)))

end Real

end FurioLombardo.Discharge.M3b
