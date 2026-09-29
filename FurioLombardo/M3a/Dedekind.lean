import Mathlib
import FurioLombardo.M3a.CoordRing

/-!
# `K[X, Y]/(Y² - f)` is a Dedekind domain (lane M3a)

For `f` squarefree and not a square and `2 ≠ 0` in `K`, the coordinate ring `CoordRing f` is
integrally closed, hence a Dedekind domain. The argument is TauCeti's for Weierstrass curves
(`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean`, Apache 2.0, see
`THIRD_PARTY.md`): an integral element `(p + qY)/d` of the function field has integral trace `2p/d`
and norm `(p² - q² f)/d²`, so `d ∣ p` and `d² ∣ q² f`, hence `d ∣ q`.
-/

namespace FurioLombardo.M3a.Genus2

open Polynomial

variable {K : Type*} [Field K]

/-- In a GCD domain, `d² ∣ q² f` with `f` squarefree gives `d ∣ q`. -/
theorem dvd_of_sq_dvd_sq_mul {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R] {f d q : R}
    (hf : Squarefree f) (h : d ^ 2 ∣ q ^ 2 * f) : d ∣ q := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [zero_pow two_ne_zero, zero_dvd_iff] at h
    have hq : q ^ 2 = 0 := (mul_eq_zero.mp h).resolve_right hf.ne_zero
    rw [pow_eq_zero_iff two_ne_zero] at hq
    simp [hq]
  obtain ⟨d', q', hd', hq', hu⟩ := extract_gcd d q
  set g := gcd d q
  have hg : g ≠ 0 := by
    intro h0; apply hd; rw [hd', h0, zero_mul]
  rw [hd', hq', mul_pow, mul_pow, mul_assoc] at h
  have h' : d' ^ 2 ∣ q' ^ 2 * f := (mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).mp h
  have hrel : IsRelPrime (d' ^ 2) (q' ^ 2) :=
    (gcd_isUnit_iff_isRelPrime.mp hu).pow
  have hdf : d' * d' ∣ f := by
    rw [← sq]; exact hrel.dvd_of_dvd_mul_left h'
  have hunit : IsUnit d' := hf d' hdf
  rw [hd', hq']
  exact mul_dvd_mul_left g hunit.dvd

/-- The divisibility core: `d ∣ 2p` and `d² ∣ p² - q² f` give `d ∣ p` and `d ∣ q`, when `2` is a
unit and `f` is squarefree. -/
theorem dvd_and_dvd_of_trace_norm {f d p q : K[X]} (h2 : (2 : K) ≠ 0) (hf : Squarefree f)
    (htr : d ∣ 2 * p) (hn : d ^ 2 ∣ p ^ 2 - q ^ 2 * f) : d ∣ p ∧ d ∣ q := by
  classical
  have hu : IsUnit (2 : K[X]) := by
    rw [← map_ofNat C 2]; exact isUnit_C.mpr (IsUnit.mk0 _ h2)
  have hp : d ∣ p := (hu.dvd_mul_left).mp htr
  refine ⟨hp, ?_⟩
  obtain ⟨p', rfl⟩ := hp
  refine dvd_of_sq_dvd_sq_mul hf ?_
  have h1 : d ^ 2 ∣ (d * p') ^ 2 := ⟨p' ^ 2, by ring⟩
  have := dvd_sub h1 hn
  rwa [sub_sub_cancel] at this

variable {f : K[X]} [GoodSextic f]

/-- Every element of the function field that is integral over `K[X]` lies in `CoordRing f`. -/
theorem exists_algebraMap_eq {z : FunField f} (hz : IsIntegral K[X] z) :
    ∃ b : CoordRing f, algebraMap (CoordRing f) (FunField f) b = z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (CoordRing f) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  -- rewrite `a / b` as `(a * conj b) / N(b)`, with denominator in `K[X]`
  set n := Algebra.norm K[X] b with hn
  have hbn : b * conj f b = algebraMap K[X] (CoordRing f) n := mul_conj f b
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_eq_zero] at hbn
    rcases hbn with h | h
    · exact hb0 h
    · exact hb0 ((conj f).injective (by rw [h, map_zero]))
  have hinjK : Function.Injective (algebraMap K[X] (FunField f)) := by
    rw [IsScalarTower.algebraMap_eq K[X] (CoordRing f) (FunField f)]
    exact (IsFractionRing.injective (CoordRing f) (FunField f)).comp (algebraMap_injective f)
  have hnK : algebraMap K[X] (FunField f) n ≠ 0 := (map_ne_zero_iff _ hinjK).mpr hn0
  have hbK : algebraMap (CoordRing f) (FunField f) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (CoordRing f) (FunField f))).mpr hb0
  have hcK : algebraMap (CoordRing f) (FunField f) (conj f b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (CoordRing f) (FunField f))).mpr
      (fun h => hb0 ((conj f).injective (by rw [h, map_zero])))
  have hz' : algebraMap (CoordRing f) (FunField f) a / algebraMap (CoordRing f) (FunField f) b =
      algebraMap (CoordRing f) (FunField f) (a * conj f b) / algebraMap K[X] (FunField f) n := by
    rw [IsScalarTower.algebraMap_apply K[X] (CoordRing f) (FunField f), ← hbn, map_mul, map_mul,
      mul_div_mul_right _ _ hcK]
  rw [hz'] at hz ⊢
  obtain ⟨p, q, hpq⟩ := exists_smul_basis_eq f (a * conj f b)
  have htr := dvd_trace_of_isIntegral_div hn0 hpq hz
  have hnm := sq_dvd_norm_of_isIntegral_div hn0 hpq hz
  obtain ⟨⟨p', rfl⟩, ⟨q', rfl⟩⟩ :=
    dvd_and_dvd_of_trace_norm (GoodSextic.two_ne_zero (f := f)) (GoodSextic.squarefree) htr hnm
  refine ⟨p' • 1 + q' • Yc f, ?_⟩
  rw [eq_div_iff hnK, IsScalarTower.algebraMap_apply K[X] (CoordRing f) (FunField f), ← map_mul,
    ← hpq]
  congr 1
  simp only [smul_eq, map_mul, mul_one]
  ring

/-- `CoordRing f` is integrally closed. -/
instance isIntegrallyClosed : IsIntegrallyClosed (CoordRing f) := by
  have : Algebra.IsIntegral K[X] (CoordRing f) := Algebra.IsIntegral.of_finite _ _
  have : IsIntegrallyClosedIn (CoordRing f) (FunField f) :=
    isIntegrallyClosedIn_iff.mpr ⟨IsFractionRing.injective _ _,
      fun hx => exists_algebraMap_eq (isIntegral_trans _ hx)⟩
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn (CoordRing f) (FunField f)

/-- `CoordRing f` is a Dedekind domain. -/
instance isDedekindDomain : IsDedekindDomain (CoordRing f) := by
  have : Algebra.IsIntegral K[X] (CoordRing f) := Algebra.IsIntegral.of_finite _ _
  exact { __ := Ring.DimensionLEOne.of_isIntegral K[X] (CoordRing f) }

end FurioLombardo.M3a.Genus2
