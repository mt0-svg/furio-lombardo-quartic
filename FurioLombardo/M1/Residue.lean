import FurioLombardo.M1.ZKInt
import FurioLombardo.M1.DataBezout

/-!
# Residue homomorphisms of `𝓞 K21`

`f'(θ)` lies in the conductor of `ℤ[θ]` in `𝓞 K21` (Mathlib `conductor_mul_differentIdeal`), and the
Bezout identity `s f + t f' = DB` (DataBezout.lean, checked by the kernel) gives `DB · 𝓞 K21 ⊆ ℤ[θ]`.
Hence for every commutative ring `R`, root `r` of `f` in `R` and inverse `u` of `DB` in `R` there is
a unique ring homomorphism `𝓞 K21 → R` sending `θ` to `r` (`resHom`, `resHom_unique`): on
`b = g(θ) / DB` it is `u g(r)`.
-/

namespace FurioLombardo.M1

open Polynomial NumberField

/-- `θ` in `𝓞 K21`. -/
noncomputable def θO : 𝓞 K21 := ⟨θ, isIntegral_θ⟩

@[simp] theorem coe_θO : ((θO : 𝓞 K21) : K21) = θ := rfl

theorem aeval_θ_fZ : aeval θ fZ = 0 := by
  have h := evalL_θ_fL
  rw [← evalL_ofListL, ofListL_fL] at h
  rw [aeval_def]; convert h using 2; exact RingHom.ext_int _ _

theorem aeval_θO_fZ : aeval θO fZ = 0 := by
  apply RingOfIntegers.coe_injective
  rw [← aeval_algebraMap_apply]
  simpa using aeval_θ_fZ

theorem minpoly_θO : minpoly ℤ θO = fZ := by
  have hint : IsIntegral ℤ θO := RingOfIntegers.isIntegral θO
  obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hint aeval_θO_fZ
  rcases fZ_irreducible.isUnit_or_isUnit hg with h | h
  · exact absurd h (minpoly.not_isUnit ℤ θO)
  · exact eq_of_monic_of_associated (minpoly.monic hint) fZ_monic
      ⟨h.unit, by rw [IsUnit.unit_spec, ← hg]⟩

theorem adjoin_θ_eq_top : Algebra.adjoin ℚ {algebraMap (𝓞 K21) K21 θO} = ⊤ := by
  show Algebra.adjoin ℚ {AdjoinRoot.root fQ} = ⊤
  exact AdjoinRoot.adjoinRoot_eq_top

/-- `f'(θ)` lies in the conductor of `ℤ[θ]`. -/
theorem derivative_mem_conductor :
    aeval θO (derivative fZ) ∈ conductor ℤ θO := by
  have h := conductor_mul_differentIdeal (A := ℤ) (K := ℚ) (B := 𝓞 K21) K21 θO adjoin_θ_eq_top
  rw [minpoly_θO] at h
  have : Ideal.span {aeval θO (derivative fZ)} ≤ conductor ℤ θO := by
    rw [← h]; exact Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem aeval_ofListL {A : Type*} [CommRing A] (x : A) (l : List ℤ) :
    aeval x (ofListL l) = evalL x l := by
  rw [aeval_def, algebraMap_int_eq, evalL_ofListL]

theorem bezout_list : allZeroL (subL (addL (mulL sL fL) (mulL tL fdL)) [DB]) = true := by
  decide +kernel

theorem ofListL_fdL : ofListL fdL = derivative fZ := by
  simp only [ofListL, fdL, fZ, derivative_add, derivative_sub, derivative_mul, derivative_X_pow,
    derivative_ofNat, derivative_X, derivative_one, derivative_C]
  simp only [map_neg, map_ofNat, map_one, map_zero, eq_intCast, Int.cast_ofNat, C_neg]
  ring

/-- `t(θ) f'(θ) = DB` in `𝓞 K21`. -/
theorem bezout_θO : aeval θO (ofListL tL) * aeval θO (derivative fZ) = (DB : 𝓞 K21) := by
  have h := evalL_eq_of_allZeroL_subL θO _ _ bezout_list
  rw [evalL_addL, evalL_mulL, evalL_mulL] at h
  have hf : evalL θO fL = 0 := by
    rw [← aeval_ofListL, ofListL_fL]; exact aeval_θO_fZ
  rw [hf, mul_zero, zero_add] at h
  rw [← ofListL_fdL, aeval_ofListL, aeval_ofListL, h]
  simp

/-- `DB · 𝓞 K21 ⊆ ℤ[θ]`. -/
theorem exists_DB_mul (b : 𝓞 K21) : ∃ g : ℤ[X], (DB : 𝓞 K21) * b = aeval θO g := by
  have hb := (mem_conductor_iff.mp derivative_mem_conductor) b
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨h, hh⟩ := hb
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hh
  refine ⟨ofListL tL * h, ?_⟩
  rw [map_mul, ← bezout_θO, hh]; ring

section Res

variable {R : Type*} [CommRing R] (r : R) (hr : aeval r fZ = 0) (u : R) (hu : u * (DB : R) = 1)

include hr in
theorem aeval_eq_of_aeval_θO_eq {g g' : ℤ[X]} (h : aeval θO g = aeval θO g') :
    aeval r g = aeval r g' := by
  have h0 : aeval θO (g - g') = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd (RingOfIntegers.isIntegral θO) h0
  rw [minpoly_θO] at hq
  have : aeval r (g - g') = 0 := by rw [hq, map_mul, hr, zero_mul]
  rwa [map_sub, sub_eq_zero] at this

/-- The residue map on elements. -/
noncomputable def resFun (b : 𝓞 K21) : R := u * aeval r (Classical.choose (exists_DB_mul b))

include hr in
theorem resFun_spec (b : 𝓞 K21) (g : ℤ[X]) (hg : (DB : 𝓞 K21) * b = aeval θO g) :
    resFun r u b = u * aeval r g := by
  rw [resFun, aeval_eq_of_aeval_θO_eq r hr ((Classical.choose_spec (exists_DB_mul b)).symm.trans hg)]

/-- **The residue homomorphism** `𝓞 K21 → R` with `θ ↦ r`. -/
noncomputable def resHom : 𝓞 K21 →+* R where
  toFun := resFun r u
  map_one' := by
    rw [resFun_spec r hr u 1 (C DB) (by simp)]
    simp [hu]
  map_mul' b c := by
    obtain ⟨gb, hb⟩ := exists_DB_mul b
    obtain ⟨gc, hc⟩ := exists_DB_mul c
    obtain ⟨gbc, hbc⟩ := exists_DB_mul (b * c)
    rw [resFun_spec r hr u b gb hb, resFun_spec r hr u c gc hc, resFun_spec r hr u _ gbc hbc]
    have h1 : aeval θO (C DB * gbc) = aeval θO (gb * gc) := by
      rw [map_mul, map_mul, ← hbc, ← hb, ← hc, aeval_C]; simp; ring
    have h2 := aeval_eq_of_aeval_θO_eq r hr h1
    rw [map_mul, map_mul, aeval_C] at h2
    simp only [algebraMap_int_eq, eq_intCast] at h2
    calc u * aeval r gbc = u * u * ((DB : R) * aeval r gbc) := by
          rw [← mul_assoc, mul_assoc u u, hu]; ring
      _ = u * aeval r gb * (u * aeval r gc) := by rw [h2]; ring
  map_zero' := by
    rw [resFun_spec r hr u 0 0 (by simp)]
    simp
  map_add' b c := by
    obtain ⟨gb, hb⟩ := exists_DB_mul b
    obtain ⟨gc, hc⟩ := exists_DB_mul c
    rw [resFun_spec r hr u b gb hb, resFun_spec r hr u c gc hc,
      resFun_spec r hr u (b + c) (gb + gc) (by rw [mul_add, hb, hc, map_add])]
    rw [map_add, mul_add]

theorem resHom_apply (b : 𝓞 K21) (g : ℤ[X]) (hg : (DB : 𝓞 K21) * b = aeval θO g) :
    resHom r hr u hu b = u * aeval r g :=
  resFun_spec r hr u b g hg

theorem resHom_θO : resHom r hr u hu θO = r := by
  rw [resHom_apply r hr u hu θO (C DB * X) (by simp)]
  simp only [map_mul, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast, map_intCast]
  rw [← mul_assoc, hu, one_mul]

/-- **Uniqueness**: a ring homomorphism `𝓞 K21 → R` is determined by the image of `θ`. -/
theorem resHom_unique (ψ : 𝓞 K21 →+* R) (hψ : ψ θO = r) : ψ = resHom r hr u hu := by
  ext b
  obtain ⟨g, hg⟩ := exists_DB_mul b
  rw [resHom_apply r hr u hu b g hg]
  have : ψ ((DB : 𝓞 K21) * b) = aeval r g := by
    rw [hg, ← hψ]
    exact (Polynomial.hom_eval₂ g (algebraMap ℤ (𝓞 K21)) ψ θO).trans (by
      rw [aeval_def]; congr 1; exact RingHom.ext_int _ _)
  rw [map_mul, map_intCast] at this
  rw [← this, ← mul_assoc, hu, one_mul]

end Res

end FurioLombardo.M1
