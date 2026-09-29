import Mathlib

/-!
# Lane M3b: the group of fractional ideals is free abelian on the primes

For a Dedekind domain `R` with fraction field `F`: `unitOfPrime`, `toFinsupp`, `ofFinsupp`,
`count_ofFinsupp`, `count_injective` and the isomorphism `factorization :
(FractionalIdeal R⁰ F)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ)`, plus `countHom`, the count
at one prime as a homomorphism.

Adapted from Michael Stoll, EllipticCurves (https://github.com/MichaelStollBayreuth/EllipticCurves,
commit 1e4709496a2c0cb3da66b400efbb15939358d444, Apache License 2.0),
`EllipticCurves/Mathlib/FractionalIdeal.lean` (also in the workspace Toolbox as
`Toolbox.Stoll.Mathlib.FractionalIdeal`): declarations renamed into `FurioLombardo.M3b`, proofs
unchanged. `countHom` and `count_finsuppProd_units` are new.
-/

namespace FurioLombardo.M3b

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors Classical

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- A nonzero fractional ideal is the product `∏ v ^ (count v)` over the height one primes. -/
theorem prod_count {I : FractionalIdeal R⁰ F} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ F) ^ count F v I = I := by
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  simp_rw [fun v ↦ count_well_defined F v hI haJ]
  exact finprod_heightOneSpectrum_factorization hI haJ

variable (F) in
/-- The prime `v` as a unit of the group of fractional ideals. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ F)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ F) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] theorem coe_unitOfPrime (v : HeightOneSpectrum R) :
    ((unitOfPrime F v : (FractionalIdeal R⁰ F)ˣ) : FractionalIdeal R⁰ F) = v.asIdeal := rfl

/-- The finitely supported tuple of valuations of a unit fractional ideal. -/
noncomputable def toFinsupp (I : (FractionalIdeal R⁰ F)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v ↦ count F v (I : FractionalIdeal R⁰ F)) (by
    have := finite_factors (I : FractionalIdeal R⁰ F)
    simpa [Function.support, Filter.eventually_cofinite] using this)

@[simp] theorem toFinsupp_apply (I : (FractionalIdeal R⁰ F)ˣ) (v : HeightOneSpectrum R) :
    toFinsupp I v = count F v (I : FractionalIdeal R⁰ F) := rfl

variable (F) in
/-- The unit fractional ideal `∏ v ^ (g v)`. -/
noncomputable def ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) : (FractionalIdeal R⁰ F)ˣ :=
  g.prod (fun v e ↦ unitOfPrime F v ^ e)

theorem coe_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) :
    ((ofFinsupp F g : (FractionalIdeal R⁰ F)ˣ) : FractionalIdeal R⁰ F)
      = g.prod (fun v e ↦ (v.asIdeal : FractionalIdeal R⁰ F) ^ e) := by
  rw [ofFinsupp, ← Units.coeHom_apply, map_finsuppProd]
  simp [Units.coeHom]

theorem count_ofFinsupp (g : HeightOneSpectrum R →₀ ℤ) (v : HeightOneSpectrum R) :
    count F v ((ofFinsupp F g : (FractionalIdeal R⁰ F)ˣ) : FractionalIdeal R⁰ F) = g v := by
  rw [coe_ofFinsupp, count_finsuppProd]

/-- A unit fractional ideal is determined by its valuations. -/
theorem count_injective {I J : (FractionalIdeal R⁰ F)ˣ}
    (h : ∀ v, count F v (I : FractionalIdeal R⁰ F) = count F v (J : FractionalIdeal R⁰ F)) :
    I = J := by
  apply Units.ext
  rw [← prod_count (Units.ne_zero I), ← prod_count (Units.ne_zero J)]
  exact finprod_congr fun v ↦ by rw [h v]

theorem ofFinsupp_toFinsupp (I : (FractionalIdeal R⁰ F)ˣ) : ofFinsupp F (toFinsupp I) = I :=
  count_injective fun v ↦ by rw [count_ofFinsupp]; rfl

variable (R F) in
/-- **The group of nonzero fractional ideals of a Dedekind domain is free abelian on the height
one primes.** -/
noncomputable def factorization :
    (FractionalIdeal R⁰ F)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (toFinsupp I)
  invFun g := ofFinsupp F (Multiplicative.toAdd g)
  left_inv I := ofFinsupp_toFinsupp I
  right_inv g := by
    apply Multiplicative.toAdd.injective
    ext
    simp only [toAdd_ofAdd, toFinsupp_apply, count_ofFinsupp]
  map_mul' I J := by
    apply Multiplicative.toAdd.injective
    ext v
    simp only [toAdd_ofAdd, Finsupp.coe_add, Pi.add_apply, toFinsupp_apply, Units.val_mul,
      toAdd_mul]
    exact count_mul F v (Units.ne_zero I) (Units.ne_zero J)

@[simp] theorem factorization_apply (I : (FractionalIdeal R⁰ F)ˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (factorization R F I) v = count F v (I : FractionalIdeal R⁰ F) := rfl

variable (F) in
/-- The count at one prime, as a homomorphism on the unit fractional ideals. -/
noncomputable def countHom (v : HeightOneSpectrum R) :
    (FractionalIdeal R⁰ F)ˣ →* Multiplicative ℤ where
  toFun I := Multiplicative.ofAdd (count F v (I : FractionalIdeal R⁰ F))
  map_one' := by simp [count_one]
  map_mul' I J := by
    rw [Units.val_mul, count_mul F v (Units.ne_zero I) (Units.ne_zero J), ofAdd_add]

theorem countHom_apply (v : HeightOneSpectrum R) (I : (FractionalIdeal R⁰ F)ˣ) :
    Multiplicative.toAdd (countHom F v I) = count F v (I : FractionalIdeal R⁰ F) := rfl

theorem count_unitOfPrime (v w : HeightOneSpectrum R) :
    count F w ((unitOfPrime F v : (FractionalIdeal R⁰ F)ˣ) : FractionalIdeal R⁰ F) =
      if v = w then 1 else 0 := by
  rw [coe_unitOfPrime, count_maximal]

end FurioLombardo.M3b
