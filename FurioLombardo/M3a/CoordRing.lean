import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The coordinate ring of `Y² = f(X)` (lane M3a)

For a field `K` and `f : K[X]`, `CoordRing f = K[X][Y]/(Y² - f)` is the affine coordinate ring of the
hyperelliptic curve `Y² = f(X)`. This file gives its `K[X]`-basis `{1, Y}`, the norm
`N(p + qY) = p² - q² f`, the conjugation `Y ↦ -Y`, and proves that it is a domain when `f` is not a
square, and a Dedekind domain when moreover `f` is squarefree and `2 ≠ 0` in `K`.

The proof of integral closedness follows the one of TauCeti for Weierstrass curves
(`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean`, Apache 2.0, see
`THIRD_PARTY.md`), in the simpler setting `Y² = f`: an element `(p + qY)/d` of the fraction field
that is integral over `K[X]` has integral trace `2p/d` and norm `(p² - q²f)/d²`, so `d ∣ p` (as `2`
is a unit) and `d² ∣ q² f`, hence `d ∣ q` since `f` is squarefree.
-/

namespace FurioLombardo.M3a.Genus2

open Polynomial

variable {K : Type*} [Field K]

/-- `Y² - f`, as a polynomial in `Y` over `K[X]`. -/
noncomputable def curvePoly (f : K[X]) : K[X][X] := X ^ 2 - C f

theorem curvePoly_monic (f : K[X]) : (curvePoly f).Monic :=
  monic_X_pow_sub_C _ two_ne_zero

theorem curvePoly_natDegree (f : K[X]) : (curvePoly f).natDegree = 2 :=
  natDegree_X_pow_sub_C

/-- The affine coordinate ring `K[X, Y]/(Y² - f)`. -/
abbrev CoordRing (f : K[X]) : Type _ := AdjoinRoot (curvePoly f)

/-- The quotient map `K[X][Y] → K[X, Y]/(Y² - f)`. -/
noncomputable abbrev mk (f : K[X]) : K[X][X] →+* CoordRing f := AdjoinRoot.mk (curvePoly f)

/-- The coordinate function `Y`. -/
noncomputable abbrev Yc (f : K[X]) : CoordRing f := AdjoinRoot.root (curvePoly f)

variable (f : K[X])

theorem Yc_sq : Yc f ^ 2 = algebraMap K[X] (CoordRing f) f := by
  have h : aeval (Yc f) (X ^ 2 - C f : K[X][X]) = 0 := by
    change aeval (Yc f) (curvePoly f) = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [map_sub, map_pow, aeval_X, aeval_C] at h
  exact sub_eq_zero.mp h

/-- The power basis `{1, Y}` of `CoordRing f` over `K[X]`. -/
noncomputable def basis : Module.Basis (Fin 2) K[X] (CoordRing f) :=
  (AdjoinRoot.powerBasis' (curvePoly_monic f)).basis.reindex (finCongr (curvePoly_natDegree f))

set_option backward.isDefEq.respectTransparency.types false in
theorem basis_apply (n : Fin 2) :
    basis f n = (AdjoinRoot.powerBasis' (curvePoly_monic f)).gen ^ (n : ℕ) := by
  rw [basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm_apply,
    Fin.val_cast]

@[simp] theorem basis_zero : basis f 0 = 1 := by
  rw [basis_apply]; simp

@[simp] theorem basis_one : basis f 1 = Yc f := by
  simp only [basis_apply, AdjoinRoot.powerBasis'_gen, Fin.val_one, pow_one]

instance : Module.Free K[X] (CoordRing f) := .of_basis (basis f)

instance : Module.Finite K[X] (CoordRing f) := .of_basis (basis f)

instance : Nontrivial (CoordRing f) := ⟨_, _, (basis f).ne_zero 0⟩

theorem smul_eq (x : K[X]) (y : CoordRing f) : x • y = algebraMap K[X] (CoordRing f) x * y :=
  Algebra.smul_def x y

theorem smul_basis_eq_zero {p q : K[X]} (hpq : p • (1 : CoordRing f) + q • Yc f = 0) :
    p = 0 ∧ q = 0 := by
  have h := Fintype.linearIndependent_iff.mp (basis f).linearIndependent ![p, q]
  rw [Fin.sum_univ_succ, basis_zero, Fin.sum_univ_one, Fin.succ_zero_eq_one, basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩

theorem exists_smul_basis_eq (x : CoordRing f) :
    ∃ p q : K[X], p • (1 : CoordRing f) + q • Yc f = x := by
  have h := (basis f).sum_equivFun x
  rw [Fin.sum_univ_succ, Fin.sum_univ_one, basis_zero, Fin.succ_zero_eq_one, basis_one] at h
  exact ⟨_, _, h⟩

theorem algebraMap_injective : Function.Injective (algebraMap K[X] (CoordRing f)) := by
  intro a b h
  have h' : (a - b) • (1 : CoordRing f) + (0 : K[X]) • Yc f = 0 := by
    rw [zero_smul, add_zero, smul_eq, mul_one, map_sub, h, sub_self]
  exact sub_eq_zero.mp (smul_basis_eq_zero f h').1

instance : FaithfulSMul K[X] (CoordRing f) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_injective f)

theorem smul_basis_mul_Y (p q : K[X]) :
    (p • (1 : CoordRing f) + q • Yc f) * Yc f = (q * f) • (1 : CoordRing f) + p • Yc f := by
  simp only [smul_eq, map_mul, mul_one, add_mul]
  rw [mul_assoc (algebraMap K[X] (CoordRing f) q), ← sq, Yc_sq]
  ring

/-- The norm of `p + qY` is `p² - q² f`. -/
theorem repr_smul_basis (p q : K[X]) :
    (basis f).repr (p • (1 : CoordRing f) + q • Yc f) 0 = p ∧
      (basis f).repr (p • (1 : CoordRing f) + q • Yc f) 1 = q := by
  rw [← basis_zero, ← basis_one]
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  simp

theorem norm_smul_basis (p q : K[X]) :
    Algebra.norm K[X] (p • (1 : CoordRing f) + q • Yc f) = p ^ 2 - q ^ 2 * f := by
  rw [Algebra.norm_eq_matrix_det (basis f), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, basis_zero, basis_one, mul_one,
    smul_basis_mul_Y, (repr_smul_basis f _ _).1, (repr_smul_basis f _ _).2]
  ring

/-! ## Conjugation `Y ↦ -Y` -/

/-- The conjugation `Y ↦ -Y` of `CoordRing f` over `K[X]`, as an algebra homomorphism. -/
noncomputable def conjHom : CoordRing f →ₐ[K[X]] CoordRing f :=
  AdjoinRoot.liftAlgHom (curvePoly f) (Algebra.ofId K[X] (CoordRing f)) (-Yc f) <| by
    simp only [curvePoly, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq, Yc_sq]
    exact sub_self _

@[simp] theorem conjHom_Yc : conjHom f (Yc f) = -Yc f :=
  AdjoinRoot.liftAlgHom_root ..

theorem conjHom_comp : (conjHom f).comp (conjHom f) = AlgHom.id K[X] (CoordRing f) := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply, conjHom_Yc, map_neg, conjHom_Yc, neg_neg]

theorem conjHom_conjHom (x : CoordRing f) : conjHom f (conjHom f x) = x :=
  congrArg (fun g : CoordRing f →ₐ[K[X]] CoordRing f => g x) (conjHom_comp f)

/-- The conjugation `Y ↦ -Y` of `CoordRing f` over `K[X]`. -/
noncomputable def conj : CoordRing f ≃ₐ[K[X]] CoordRing f :=
  AlgEquiv.ofAlgHom (conjHom f) (conjHom f) (conjHom_comp f) (conjHom_comp f)

@[simp] theorem conj_apply (x : CoordRing f) : conj f x = conjHom f x := rfl

@[simp] theorem conj_Yc : conj f (Yc f) = -Yc f := conjHom_Yc f

theorem conj_smul_basis (p q : K[X]) :
    conj f (p • (1 : CoordRing f) + q • Yc f) = p • (1 : CoordRing f) - q • Yc f := by
  rw [map_add, map_smul, map_smul, map_one, conj_Yc, smul_neg, sub_eq_add_neg]

/-- `x * conj x` is the norm of `x`. -/
theorem mul_conj (x : CoordRing f) :
    x * conj f x = algebraMap K[X] (CoordRing f) (Algebra.norm K[X] x) := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f x
  rw [conj_smul_basis, norm_smul_basis]
  simp only [smul_eq, mul_one, map_sub, map_pow, map_mul]
  rw [← Yc_sq]
  ring

/-- `x + conj x` is the trace `2p` of `x = p + qY`. -/
theorem add_conj_smul_basis (p q : K[X]) :
    (p • (1 : CoordRing f) + q • Yc f) + conj f (p • (1 : CoordRing f) + q • Yc f) =
      algebraMap K[X] (CoordRing f) (2 * p) := by
  rw [conj_smul_basis]
  simp only [smul_eq, mul_one, map_mul, map_ofNat]
  ring

/-! ## Domain -/

/-- If `f` is not a square in `K[X]`, then `Y² - f` is irreducible over `K[X]`. -/
theorem curvePoly_irreducible (hf : ¬ IsSquare f) : Irreducible (curvePoly f) := by
  rw [(curvePoly_monic f).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [curvePoly_natDegree]) (by rw [curvePoly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun g hg => hf ⟨g, ?_⟩
  have hg' := (mem_roots (curvePoly_monic f).ne_zero).mp hg
  rw [IsRoot, curvePoly, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hg'
  rw [← hg', sq]

theorem isDomain_of_not_isSquare (hf : ¬ IsSquare f) : IsDomain (CoordRing f) :=
  AdjoinRoot.isDomain_of_prime (curvePoly_irreducible f hf).prime

/-! ## The standing hypotheses on the sextic -/

/-- The standing hypotheses on `f` for the genus 2 layer: `f` is a squarefree sextic whose leading
coefficient is not a square, over a field in which `2 ≠ 0`. The last condition makes the place at
infinity of `Y² = f` a single place of degree 2, so that the parity kernel of the class group of
`CoordRing f` is `Pic⁰`. -/
class GoodSextic (f : K[X]) : Prop where
  squarefree : Squarefree f
  natDegree_eq : f.natDegree = 6
  not_isSquare_leadingCoeff : ¬ IsSquare f.leadingCoeff
  two_ne_zero : (2 : K) ≠ 0

variable {f}

theorem GoodSextic.not_isSquare [hf : GoodSextic f] : ¬ IsSquare f := by
  rintro ⟨g, hg⟩
  have hu : IsUnit g := hf.squarefree g (by rw [hg])
  have h0 : f.natDegree = 0 := by
    rw [hg, natDegree_mul' (by simpa using hu.ne_zero), natDegree_eq_zero_of_isUnit hu]
  rw [hf.natDegree_eq] at h0
  exact absurd h0 (by norm_num)

instance [GoodSextic f] : IsDomain (CoordRing f) :=
  isDomain_of_not_isSquare f GoodSextic.not_isSquare

/-! ## Integral closedness

Adapted from TauCeti, `TauCeti/AlgebraicGeometry/EllipticCurve/Affine/CoordinateRing.lean`
(sections "The divisibility core" and "Integral closedness", Apache 2.0, see `THIRD_PARTY.md`),
for the curve `Y² = f` in place of a Weierstrass curve. -/

section IntegrallyClosed

/-- An element of a field extension of `A` that is a quotient of elements of `A` and is integral
over `A` has its numerator divisible by its denominator, when `A` is integrally closed.
(TauCeti, `WeierstrassCurve.Affine.dvd_of_isIntegral_div`.) -/
theorem dvd_of_isIntegral_div {A L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field L] [Algebra A L] [FaithfulSMul A L] {a d : A} (hd : d ≠ 0)
    (h : IsIntegral A (algebraMap A L a / algebraMap A L d)) : d ∣ a := by
  have hinj : Function.Injective (algebraMap A L) := FaithfulSMul.algebraMap_injective A L
  let g : FractionRing A →ₐ[A] L := IsFractionRing.liftAlgHom (g := Algebra.ofId A L) hinj
  have hg : Function.Injective g := (g : FractionRing A →+* L).injective
  have hdF : algebraMap A (FractionRing A) d ≠ 0 := fun h' =>
    hd (IsFractionRing.injective A (FractionRing A) (by rw [h', map_zero]))
  have hw : g (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) d) =
      algebraMap A L a / algebraMap A L d := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes]
  obtain ⟨e, he⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algHom_iff g hg).mp (hw ▸ h))
  refine ⟨e, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, he, mul_div_cancel₀ _ hdF]

variable (f) [GoodSextic f]

/-- The function field of `Y² = f`. -/
abbrev FunField : Type _ := FractionRing (CoordRing f)

/-- The conjugation `Y ↦ -Y` of the function field over `K[X]`. -/
noncomputable def conjFrac : FunField f ≃ₐ[K[X]] FunField f :=
  IsFractionRing.algEquivOfAlgEquiv (conj f)

theorem conjFrac_apply_div (b : CoordRing f) (d : K[X]) :
    conjFrac f (algebraMap (CoordRing f) (FunField f) b / algebraMap K[X] (FunField f) d) =
      algebraMap (CoordRing f) (FunField f) (conj f b) / algebraMap K[X] (FunField f) d := by
  rw [map_div₀, conjFrac, IsFractionRing.algEquivOfAlgEquiv_algebraMap, AlgEquiv.commutes]

variable {f}

/-- The trace `2p/d` of an integral quotient `(p + qY)/d` lies in `K[X]`. -/
theorem dvd_trace_of_isIntegral_div {b : CoordRing f} {d p q : K[X]} (hd0 : d ≠ 0)
    (hpq : p • (1 : CoordRing f) + q • Yc f = b)
    (hz : IsIntegral K[X] (algebraMap (CoordRing f) (FunField f) b /
      algebraMap K[X] (FunField f) d)) :
    d ∣ 2 * p := by
  refine dvd_of_isIntegral_div (L := FunField f) hd0 ?_
  have hsum : algebraMap K[X] (FunField f) (2 * p) / algebraMap K[X] (FunField f) d =
      algebraMap (CoordRing f) (FunField f) b / algebraMap K[X] (FunField f) d +
        conjFrac f (algebraMap (CoordRing f) (FunField f) b / algebraMap K[X] (FunField f) d) := by
    rw [conjFrac_apply_div, ← add_div, ← map_add,
      IsScalarTower.algebraMap_apply K[X] (CoordRing f) (FunField f), ← hpq,
      add_conj_smul_basis]
  rw [hsum]
  exact hz.add (hz.map (conjFrac f : FunField f →ₐ[K[X]] FunField f))

/-- The norm `(p² - q² f)/d²` of an integral quotient `(p + qY)/d` lies in `K[X]`. -/
theorem sq_dvd_norm_of_isIntegral_div {b : CoordRing f} {d p q : K[X]} (hd0 : d ≠ 0)
    (hpq : p • (1 : CoordRing f) + q • Yc f = b)
    (hz : IsIntegral K[X] (algebraMap (CoordRing f) (FunField f) b /
      algebraMap K[X] (FunField f) d)) :
    d ^ 2 ∣ p ^ 2 - q ^ 2 * f := by
  refine dvd_of_isIntegral_div (L := FunField f) (pow_ne_zero 2 hd0) ?_
  have hnorm : Algebra.norm K[X] b = p ^ 2 - q ^ 2 * f := by
    rw [← hpq, norm_smul_basis]
  have hprod : algebraMap K[X] (FunField f) (p ^ 2 - q ^ 2 * f) /
      algebraMap K[X] (FunField f) (d ^ 2) =
      (algebraMap (CoordRing f) (FunField f) b / algebraMap K[X] (FunField f) d) *
        conjFrac f (algebraMap (CoordRing f) (FunField f) b / algebraMap K[X] (FunField f) d) := by
    rw [conjFrac_apply_div, div_mul_div_comm, ← map_mul, ← hnorm, mul_conj,
      ← IsScalarTower.algebraMap_apply K[X] (CoordRing f) (FunField f), map_pow, pow_two]
  rw [hprod]
  exact hz.mul (hz.map (conjFrac f : FunField f →ₐ[K[X]] FunField f))

end IntegrallyClosed

end FurioLombardo.M3a.Genus2
