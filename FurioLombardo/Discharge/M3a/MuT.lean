import Mathlib
import FurioLombardo.Discharge.M3a.LocalTwoTorsion

/-!
# The `x - T` image of the 2-torsion point `T` (discharge of M3a, WP1)

For a field `K`, `f : K[X]` with `GoodSextic f` and `f = q r` with `q` monic quadratic, the point
`T = [⟨q, Y⟩]` has `μ(T) = [(q - r)(T)]` in `H f = L^× / K^× (L^×)²`, `L = K[T]/(f)`
(`muJ_Tpt`). Proof: `(Y + q) = ⟨q, Y⟩ J` with `J = ⟨q - r, Y + q⟩` (`v = -q`, `v² - f = q (q - r)`),
so `T = [J]⁻¹`; `J` is coprime to `(Y)` since `(q, q - r) = 1`, its norm is `(q - r)`, and `H f`
has exponent 2.

Consequences for (L1), `LocalTwoTorsion` at `v`:

* `eq_of_monic_quadratic_dvd`: if `r` is irreducible of degree `> 2`, `q` is the only monic
  quadratic divisor of `f = q r`;
* `mk_ne_one_of_forall`: a unit `x` of `L` with `x ≠ c y²` for all `c ∈ K`, `y ∈ L` has a
  nontrivial class in `H f`;
* `localTwoTorsion_route_of_factors`: the field `localTwoTorsion` of M3a's `Inputs` from
  `r^σ` irreducible over `k_v` and `(q^σ - r^σ)(T) ∉ k_v (L_v)²`.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.M3a

variable {K : Type*} [Field K]

theorem isCoprime_of_squarefree_mul {q r : K[X]} (h : Squarefree (q * r)) : IsCoprime q r :=
  (IsRelPrime.of_squarefree_mul h).isCoprime

/-- `(q - r)(T)` is a unit of `K[T]/(f)` when `f = q r` is squarefree. -/
theorem isUnit_mk_sub {f q r : K[X]} (hqr : f = q * r) (hsq : Squarefree f) :
    IsUnit (AdjoinRoot.mk f (q - r)) := by
  obtain ⟨a, b, hab⟩ := isCoprime_of_squarefree_mul (hqr ▸ hsq)
  have h1 : IsCoprime (q - r) q := ⟨-b, a + b, by linear_combination hab⟩
  have h2 : IsCoprime (q - r) r := ⟨a, a + b, by linear_combination hab⟩
  obtain ⟨c, d, hcd⟩ := hqr ▸ h1.mul_right h2
  refine IsUnit.of_mul_eq_one_right (AdjoinRoot.mk f c) ?_
  have := congrArg (AdjoinRoot.mk f) hcd
  rwa [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] at this

/-- `μ(T) = [(q - r)(T)]` for `f = q r`, `q` monic quadratic. -/
theorem muJ_Tpt (f : K[X]) [GoodSextic f] {q r : K[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2) (hqr : f = q * r) :
    muJ f (Tpt f hq hqf hdeg) =
      (QuotientGroup.mk (isUnit_mk_sub hqr GoodSextic.squarefree).unit : H f) := by
  classical
  have hsq : Squarefree f := GoodSextic.squarefree
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  set φ := algebraMap K[X] (CoordRing f) with hφ
  have hw : (-q) ^ 2 - f = q * (q - r) := by rw [hqr]; ring
  have hqr0 : q - r ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have h6 : f.natDegree = 4 := by rw [hqr, ← h, natDegree_mul hq.ne_zero hq.ne_zero, hdeg]
    rw [GoodSextic.natDegree_eq] at h6
    exact absurd h6 (by norm_num)
  have hassoc : Associated (q - r) (normalize (q - r)) := (normalize_associated _).symm
  have hu1 : (normalize (q - r)).Monic := monic_normalize hqr0
  -- `(Y + q) = ⟨q, Y⟩ J`, so `T = [J]⁻¹`
  have hM0 : mumford f q (-q) = mumford f q 0 := by
    have h := mumford_add_mul f q 0 (-1)
    rwa [zero_add, mul_neg_one] at h
  have hprod := mumford_mul_mumford_eq_span (f := f) h2 hw (exists_coprime_of_squarefree hsq hw)
  rw [hM0, mumford_eq_of_associated f hassoc] at hprod
  have hT : ((Tpt f hq hqf hdeg : Jac f) : Pic f) =
      (ClassGroup.mk0 (mumford0 f hu1.ne_zero (-q)))⁻¹ := by
    rw [coe_Tpt]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨_, Yc_sub_ne_zero f (-q), hprod⟩
  -- `J` is coprime to `(Y)`
  have hJY : mumford f (normalize (q - r)) (-q) ⊔ Ideal.span {Yc f} = ⊤ := by
    rw [← mumford_eq_of_associated f hassoc, Ideal.eq_top_iff_one]
    obtain ⟨a, b, hab⟩ := isCoprime_of_squarefree_mul (hqr ▸ hsq)
    have hq_mem : φ q ∈ mumford f (q - r) (-q) ⊔ Ideal.span {Yc f} := by
      have e : φ q = (Yc f - φ (-q)) - Yc f := by rw [map_neg]; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
        (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hqr_mem : φ (q - r) ∈ mumford f (q - r) (-q) ⊔ Ideal.span {Yc f} :=
      Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
    have e1 : (1 : CoordRing f) = φ (a + b) * φ q + φ (-b) * φ (q - r) := by
      rw [← map_mul, ← map_mul, ← map_add, ← map_one φ]
      congr 1
      linear_combination -hab
    rw [e1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq_mem) (Ideal.mul_mem_left _ _ hqr_mem)
  -- `μ([J]) = [(q - r)(T)]`
  obtain ⟨w1, hw1⟩ : normalize (q - r) ∣ (-q) ^ 2 - f := by
    rw [hw]; exact hassoc.symm.dvd.trans (dvd_mul_left _ _)
  have hN : Ideal.relNorm K[X] (mumford f (normalize (q - r)) (-q)) =
      Ideal.span {normalize (q - r)} :=
    relNorm_mumford f hu1 hw1 (exists_coprime_of_squarefree hsq hw1)
  have hmuJ : mu f (ClassGroup.mk0 (mumford0 f hu1.ne_zero (-q))) =
      (QuotientGroup.mk (isUnit_mk_sub hqr hsq).unit : H f) := by
    rw [mu_mk0 f (mumford0 f hu1.ne_zero (-q)) hJY]
    have hu : IsUnit (AdjoinRoot.mk f (Submodule.IsPrincipal.generator (Ideal.relNorm K[X]
        ((mumford0 f hu1.ne_zero (-q) : (Ideal (CoordRing f))⁰) : Ideal (CoordRing f))))) :=
      isUnit_mk_generator f _ hJY
    unfold muIdeal
    rw [dite_eq_left_of_eq_true (eq_true hu), QuotientGroup.eq]
    set g := Submodule.IsPrincipal.generator (Ideal.relNorm K[X]
      ((mumford0 f hu1.ne_zero (-q) : (Ideal (CoordRing f))⁰) : Ideal (CoordRing f))) with hg
    have hassoc2 : Associated g (q - r) := by
      rw [← Ideal.span_singleton_eq_span_singleton, hg, Ideal.span_singleton_generator]
      change Ideal.relNorm K[X] (mumford f (normalize (q - r)) (-q)) = _
      rw [hN, Ideal.span_singleton_eq_span_singleton]
      exact hassoc.symm
    obtain ⟨w, hw⟩ := hassoc2
    obtain ⟨c, hc, hcw⟩ := Polynomial.isUnit_iff.mp w.isUnit
    have hkey : AdjoinRoot.mk f (q - r) = AdjoinRoot.mk f g * algebraMap K (AdjoinRoot f) c := by
      rw [← hw, map_mul, ← hcw, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    apply Subgroup.mem_sup_left
    refine ⟨hc.unit, ?_⟩
    ext
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_mul,
      IsUnit.unit_spec]
    rw [hkey, ← mul_assoc, Units.inv_mul_of_eq hu.unit_spec, one_mul]
  -- `H f` has exponent 2
  have hinv : ∀ x : (AdjoinRoot f)ˣ, (QuotientGroup.mk x : H f)⁻¹ = QuotientGroup.mk x := by
    intro x
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_sup_right ⟨x, by simp [sq]⟩
  change mu f ((Tpt f hq hqf hdeg : Jac f) : Pic f) = _
  rw [hT, map_inv, hmuJ, hinv]

/-- If `f = q r` with `r` irreducible of degree `> 2`, then `q` is the only monic quadratic divisor
of `f`. -/
theorem eq_of_monic_quadratic_dvd {f q r : K[X]} (hqr : f = q * r) (hq : q.Monic)
    (hdeg : q.natDegree = 2) (hr : Irreducible r) (hrdeg : 2 < r.natDegree) :
    ∀ u : K[X], u.Monic → u.natDegree = 2 → u ∣ f → u = q := by
  intro u hu hudeg huf
  have hru : ¬ r ∣ u := fun h => by
    have := natDegree_le_of_dvd h hu.ne_zero
    omega
  have hcop : IsCoprime u r := ((Irreducible.coprime_iff_not_dvd hr).mpr hru).symm
  have huq : u ∣ q := hcop.dvd_of_dvd_mul_right (hqr ▸ huf)
  exact (eq_of_monic_of_dvd_of_natDegree_le hu hq huq (by rw [hdeg, hudeg])).symm

/-- A unit of `L = K[T]/(f)` that is not of the form `c y²` (`c ∈ K`, `y ∈ L`) has a nontrivial
class in `H f = L^× / K^× (L^×)²`. -/
theorem mk_ne_one_of_forall (f : K[X]) {x : (AdjoinRoot f)ˣ}
    (h : ∀ (c : K) (y : AdjoinRoot f), (x : AdjoinRoot f) ≠ algebraMap K (AdjoinRoot f) c * y ^ 2) :
    (QuotientGroup.mk x : H f) ≠ 1 := by
  intro h1
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨a, ⟨c, rfl⟩, b, ⟨y, rfl⟩, hab⟩ := Subgroup.mem_sup.mp h1
  apply h c y
  rw [← hab]
  simp [sq]

/-- The field `localTwoTorsion` of M3a's `Inputs` from two concrete local facts at `v`, for
`f = q r`: `r^σ` is irreducible over `k_v`, and `(q^σ - r^σ)(T)` is not in `k_v (L_v)²`, where
`L_v = k_v[T]/(f^σ)`. -/
theorem localTwoTorsion_route_of_factors {k kv : Type*} [Field k] [Field kv] (σ : k →+* kv)
    (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)] {q r : k[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2) (hqr : f = q * r) (hr : Irreducible (r.map σ))
    (hsq : ∀ (c : kv) (y : AdjoinRoot (f.map σ)),
      AdjoinRoot.mk (f.map σ) (q.map σ - r.map σ) ≠ algebraMap kv (AdjoinRoot (f.map σ)) c * y ^ 2) :
    LocalTwoTorsion (f.map σ) (jacMap σ f (Tpt f hq hqf hdeg)) := by
  have hqr' : f.map σ = q.map σ * r.map σ := by rw [hqr, Polynomial.map_mul]
  have hdeg' : (q.map σ).natDegree = 2 := by rw [natDegree_map, hdeg]
  have hrdeg : 2 < (r.map σ).natDegree := by
    have h6 := GoodSextic.natDegree_eq (f := f.map σ)
    rw [hqr', natDegree_mul (hq.map σ).ne_zero hr.ne_zero, hdeg'] at h6
    omega
  refine localTwoTorsion_route σ f hq hqf hdeg
    (eq_of_monic_quadratic_dvd hqr' (hq.map σ) hdeg' hr hrdeg) ?_
  rw [jacMap_Tpt]
  refine not_sq_of_muJ_ne_one (f.map σ) ?_
  rw [muJ_Tpt (f.map σ) (hq.map σ) _ hdeg' hqr']
  exact mk_ne_one_of_forall (f.map σ) hsq

end FurioLombardo.Discharge.M3a
