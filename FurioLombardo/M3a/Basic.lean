import Mathlib
import FurioLombardo.M3a.Dedekind
import FurioLombardo.M3a.IdealDeg

/-!
# Mumford ideals, the evaluation `Y ↦ 0`, base change (lane M3a)

Definitions on `CoordRing f = K[X][Y]/(Y² - f)`:

* `mumford f u v = ⟨u(X), Y - v(X)⟩`, the ideal of a Mumford pair;
* `evT f : CoordRing f → K[X]/(f)`, `X ↦ T`, `Y ↦ 0` (the ring behind the `x - T` map);
* `baseChange φ f : CoordRing f → CoordRing (f.map φ)` for a field hom `φ : K → K'`.
-/

namespace FurioLombardo.M3a.Genus2

open Polynomial

variable {K : Type*} [Field K]

/-- The Mumford ideal `⟨u(X), Y - v(X)⟩` of `K[X, Y]/(Y² - f)`. -/
noncomputable def mumford (f u v : K[X]) : Ideal (CoordRing f) :=
  Ideal.span {algebraMap K[X] (CoordRing f) u, Yc f - algebraMap K[X] (CoordRing f) v}

/-- The map `K[X, Y]/(Y² - f) → K[X]/(f)`, `X ↦ T` (the class of `X`), `Y ↦ 0`. -/
noncomputable def evT (f : K[X]) : CoordRing f →+* AdjoinRoot f :=
  AdjoinRoot.lift (AdjoinRoot.mk f) 0 (by simp [curvePoly])

/-- Base change of the coordinate ring along a field homomorphism `φ : K → K'`. -/
noncomputable def baseChange {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) :
    CoordRing f →+* CoordRing (f.map φ) :=
  AdjoinRoot.map (Polynomial.mapRingHom φ) (curvePoly f) (curvePoly (f.map φ))
    (dvd_of_eq (by simp [curvePoly]))

@[simp] theorem evT_algebraMap (f p : K[X]) :
    evT f (algebraMap K[X] (CoordRing f) p) = AdjoinRoot.mk f p := by
  simp [evT, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]

@[simp] theorem evT_Yc (f : K[X]) : evT f (Yc f) = 0 := by
  simp [evT, AdjoinRoot.lift_root]

@[simp] theorem baseChange_algebraMap {K' : Type*} [Field K'] (φ : K →+* K') (f p : K[X]) :
    baseChange φ f (algebraMap K[X] (CoordRing f) p) =
      algebraMap K'[X] (CoordRing (f.map φ)) (p.map φ) := by
  simp [baseChange, AdjoinRoot.algebraMap_eq]

@[simp] theorem baseChange_Yc {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) :
    baseChange φ f (Yc f) = Yc (f.map φ) := by
  simp [baseChange]

end FurioLombardo.M3a.Genus2

open Polynomial

theorem FurioLombardo.M3a.Genus2.map_conj_mumford {K : Type*} [Field K] (f u v : K[X]) :
    (FurioLombardo.M3a.Genus2.mumford f u v).map (FurioLombardo.M3a.Genus2.conj f) =
      FurioLombardo.M3a.Genus2.mumford f u (-v) := by
  dsimp [mumford]
  rw [Ideal.map_span, Set.image_pair]
  have hgoal : Ideal.span {conj f (algebraMap K[X] (CoordRing f) u), conj f (Yc f - algebraMap K[X] (CoordRing f) v)} =
      Ideal.span {algebraMap K[X] (CoordRing f) u, Yc f - algebraMap K[X] (CoordRing f) (-v)} := by
    rw [AlgEquiv.commutes (conj f) u, map_sub, conj_Yc, AlgEquiv.commutes (conj f) v, map_neg, sub_neg_eq_add]
    -- Goal: Ideal.span {algebraMap ... u, -Yc f - algebraMap ... v} = Ideal.span {algebraMap ... u, Yc f + algebraMap ... v}
    have h : -(Yc f) - algebraMap K[X] (CoordRing f) v = -(Yc f + algebraMap K[X] (CoordRing f) v) := by ring
    rw [h]
    apply le_antisymm
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (hx | hx)
      · rw [hx]; exact Ideal.subset_span (by simp)
      · rw [hx]
        exact Submodule.neg_mem _ (Ideal.subset_span (by simp))
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (hx | hx)
      · rw [hx]; exact Ideal.subset_span (by simp)
      · rw [hx]
        -- Goal: Yc f + algebraMap ... v ∈ Ideal.span {algebraMap ... u, -(Yc f + algebraMap ... v)}
        have hmem : -(Yc f + algebraMap K[X] (CoordRing f) v) ∈
            Ideal.span {algebraMap K[X] (CoordRing f) u, -(Yc f + algebraMap K[X] (CoordRing f) v)} :=
          Ideal.subset_span (by simp)
        have hneg : Yc f + algebraMap K[X] (CoordRing f) v = -(-(Yc f + algebraMap K[X] (CoordRing f) v)) := by ring
        simpa [hneg] using Submodule.neg_mem _ hmem
  simpa using hgoal

theorem FurioLombardo.M3a.Genus2.baseChange_injective {K K' : Type*} [Field K] [Field K']
    (φ : K →+* K') (f : K[X]) : Function.Injective (FurioLombardo.M3a.Genus2.baseChange φ f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, q, rfl⟩ := FurioLombardo.M3a.Genus2.exists_smul_basis_eq f x
  have hcalc : (FurioLombardo.M3a.Genus2.baseChange φ f) (p • (1 : CoordRing f) + q • Yc f) =
      (p.map φ) • (1 : CoordRing (f.map φ)) + (q.map φ) • Yc (f.map φ) := by
    simp only [FurioLombardo.M3a.Genus2.smul_eq, map_add, map_mul, map_one,
      FurioLombardo.M3a.Genus2.baseChange_algebraMap, FurioLombardo.M3a.Genus2.baseChange_Yc]
  rw [hcalc] at hx
  have hpq := FurioLombardo.M3a.Genus2.smul_basis_eq_zero (f.map φ) hx
  rcases hpq with ⟨hp_map, hq_map⟩
  have hp : p = 0 :=
    Polynomial.map_injective φ (RingHom.injective φ) (by simpa using hp_map)
  have hq : q = 0 :=
    Polynomial.map_injective φ (RingHom.injective φ) (by simpa using hq_map)
  simp [hp, hq]

theorem FurioLombardo.M3a.Genus2.isUnit_of_isUnit_norm {K : Type*} [Field K] {f : K[X]}
    {g : FurioLombardo.M3a.Genus2.CoordRing f} (h : IsUnit (Algebra.norm K[X] g)) : IsUnit g := by
  have hnorm : IsUnit (algebraMap K[X] (FurioLombardo.M3a.Genus2.CoordRing f) (Algebra.norm K[X] g)) :=
    IsUnit.map (algebraMap K[X] (FurioLombardo.M3a.Genus2.CoordRing f)) h
  have hprod : IsUnit (g * FurioLombardo.M3a.Genus2.conj f g) := by
    rw [FurioLombardo.M3a.Genus2.mul_conj]
    exact hnorm
  exact isUnit_of_mul_isUnit_left hprod

theorem FurioLombardo.M3a.Genus2.mk_norm_eq_evT_sq {K : Type*} [Field K] {f : K[X]}
    (x : FurioLombardo.M3a.Genus2.CoordRing f) :
    AdjoinRoot.mk f (Algebra.norm K[X] x) = FurioLombardo.M3a.Genus2.evT f x ^ 2 := by
  obtain ⟨p, q, rfl⟩ := FurioLombardo.M3a.Genus2.exists_smul_basis_eq f x
  rw [FurioLombardo.M3a.Genus2.norm_smul_basis]
  have h_evT : FurioLombardo.M3a.Genus2.evT f (p • (1 : CoordRing f) + q • Yc f) = AdjoinRoot.mk f p := by
    simp [FurioLombardo.M3a.Genus2.evT, FurioLombardo.M3a.Genus2.Yc, smul_eq, mul_one, map_add, map_mul,
      AdjoinRoot.lift_of, AdjoinRoot.lift_root]
  rw [h_evT]
  simp [map_pow, AdjoinRoot.mk_self]


theorem FurioLombardo.M3a.Genus2.norm_baseChange {K K' : Type*} [Field K] [Field K']
    (φ : K →+* K') (f : K[X]) (x : FurioLombardo.M3a.Genus2.CoordRing f) :
    Algebra.norm K'[X] (FurioLombardo.M3a.Genus2.baseChange φ f x) =
      (Algebra.norm K[X] x).map φ := by
  obtain ⟨p, q, h⟩ := FurioLombardo.M3a.Genus2.exists_smul_basis_eq f x
  rw [← h]
  have hbase : FurioLombardo.M3a.Genus2.baseChange φ f (p • (1 : FurioLombardo.M3a.Genus2.CoordRing f) +
      q • FurioLombardo.M3a.Genus2.Yc f) =
      (p.map φ) • (1 : FurioLombardo.M3a.Genus2.CoordRing (f.map φ)) +
      (q.map φ) • FurioLombardo.M3a.Genus2.Yc (f.map φ) := by
    simp only [map_add, map_mul, map_one, FurioLombardo.M3a.Genus2.smul_eq,
      FurioLombardo.M3a.Genus2.baseChange_algebraMap, FurioLombardo.M3a.Genus2.baseChange_Yc]
  rw [hbase]
  simp only [FurioLombardo.M3a.Genus2.norm_smul_basis]
  simp

theorem FurioLombardo.M3a.Genus2.sq_sub_sq_mul_ne_zero_even {K : Type*} [Field K] {f p q : K[X]}
    (hlc : ¬ IsSquare f.leadingCoeff) (hf : Even f.natDegree) (hpq : p ≠ 0 ∨ q ≠ 0) :
    p ^ 2 - q ^ 2 * f ≠ 0 ∧ Even (p ^ 2 - q ^ 2 * f).natDegree := by
  have hf0 : f ≠ 0 := by rintro rfl; exact hlc ⟨0, by simp⟩
  by_cases hq : q = 0
  · subst hq
    have hp : p ≠ 0 := hpq.resolve_right (by simp)
    rw [zero_pow two_ne_zero, zero_mul, sub_zero, natDegree_pow]
    exact ⟨pow_ne_zero 2 hp, even_two_mul _⟩
  by_cases hp : p = 0
  · subst hp
    rw [zero_pow two_ne_zero, zero_sub, neg_ne_zero, natDegree_neg,
      natDegree_mul (pow_ne_zero 2 hq) hf0, natDegree_pow]
    exact ⟨mul_ne_zero (pow_ne_zero 2 hq) hf0, (even_two_mul _).add hf⟩
  have ha : (p ^ 2).natDegree = 2 * p.natDegree := natDegree_pow _ _
  have hb : (q ^ 2 * f).natDegree = 2 * q.natDegree + f.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hq) hf0, natDegree_pow]
  rcases lt_trichotomy (p ^ 2).natDegree (q ^ 2 * f).natDegree with h | h | h
  · refine ⟨fun h0 => ?_, ?_⟩
    · rw [sub_eq_zero] at h0; rw [h0] at h; exact lt_irrefl _ h
    · rw [natDegree_sub_eq_right_of_natDegree_lt h, hb]; exact (even_two_mul _).add hf
  · have hq' : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
    have hlc' : (p ^ 2).leadingCoeff ≠ (q ^ 2 * f).leadingCoeff := by
      rw [leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_pow]
      intro heq
      apply hlc
      refine ⟨p.leadingCoeff / q.leadingCoeff, ?_⟩
      rw [div_mul_div_comm, ← sq, ← sq, heq, mul_div_cancel_left₀ _ (pow_ne_zero 2 hq')]
    have hcoeff : (p ^ 2 - q ^ 2 * f).coeff (p ^ 2).natDegree ≠ 0 := by
      rw [coeff_sub]
      nth_rewrite 2 [h]
      rw [← leadingCoeff, ← leadingCoeff, sub_ne_zero]
      exact hlc'
    have hle : (p ^ 2 - q ^ 2 * f).natDegree ≤ (p ^ 2).natDegree :=
      (natDegree_sub_le _ _).trans (by rw [← h, max_self])
    have heq : (p ^ 2 - q ^ 2 * f).natDegree = (p ^ 2).natDegree :=
      le_antisymm hle (le_natDegree_of_ne_zero hcoeff)
    refine ⟨fun h0 => hcoeff (by rw [h0, coeff_zero]), ?_⟩
    rw [heq, ha]; exact even_two_mul _
  · refine ⟨fun h0 => ?_, ?_⟩
    · rw [sub_eq_zero] at h0; rw [h0] at h; exact lt_irrefl _ h
    · rw [natDegree_sub_eq_left_of_natDegree_lt h, ha]; exact even_two_mul _


theorem FurioLombardo.M3a.Genus2.mumford_zero_ne_top {K : Type*} [Field K] {f q : K[X]}
    (hq : q ∣ f) (hdeg : 0 < q.natDegree) : FurioLombardo.M3a.Genus2.mumford f q 0 ≠ ⊤ := by
  have hev : eval₂ (AdjoinRoot.mk q) (0 : AdjoinRoot q) (curvePoly f) = 0 := by
    simp [curvePoly, AdjoinRoot.mk_eq_zero.mpr hq]
  set ψ : CoordRing f →+* AdjoinRoot q := AdjoinRoot.lift (AdjoinRoot.mk q) 0 hev with hψ
  have hψa : ∀ p : K[X], ψ (algebraMap K[X] (CoordRing f) p) = AdjoinRoot.mk q p := by
    intro p; simp [hψ, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  have hψY : ψ (Yc f) = 0 := by simp [hψ, Yc, AdjoinRoot.lift_root]
  have hle : mumford f q 0 ≤ RingHom.ker ψ := by
    rw [mumford, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rcases hx with rfl | rfl
    · rw [hψa, AdjoinRoot.mk_self]
    · rw [map_sub, hψY, hψa, AdjoinRoot.mk_eq_zero.mpr (dvd_zero q), sub_zero]
  have : Nontrivial (AdjoinRoot q) := AdjoinRoot.nontrivial q (by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hdeg)]; exact_mod_cast hdeg.ne')
  intro htop
  rw [htop, top_le_iff] at hle
  exact RingHom.ker_ne_top ψ hle

theorem FurioLombardo.M3a.Genus2.norm_ne_zero_and_even {K : Type*} [Field K] {f : K[X]}
    [FurioLombardo.M3a.Genus2.GoodSextic f] {x : FurioLombardo.M3a.Genus2.CoordRing f}
    (hx : x ≠ 0) :
    Algebra.norm K[X] x ≠ 0 ∧ Even (Algebra.norm K[X] x).natDegree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f x
  rw [norm_smul_basis]
  refine sq_sub_sq_mul_ne_zero_even GoodSextic.not_isSquare_leadingCoeff
    (by rw [GoodSextic.natDegree_eq]; decide) ?_
  by_contra h
  push Not at h
  apply hx
  rw [h.1, h.2, zero_smul, zero_smul, add_zero]

theorem FurioLombardo.M3a.Genus2.mumford_mul_mumford_neg {K : Type*} [Field K] {f u v w : K[X]}
    (h2 : (2 : K) ≠ 0) (hw : v ^ 2 - f = u * w)
    (hc : ∃ a b c : K[X], a * u + b * v + c * w = 1) :
    mumford f u v * mumford f u (-v) = Ideal.span {algebraMap K[X] (CoordRing f) u} := by
  obtain ⟨a, b, c, habc⟩ := hc
  set φ := algebraMap K[X] (CoordRing f) with hφ
  have hY : Yc f ^ 2 = φ f := Yc_sq f
  have hvw : φ v ^ 2 - φ f = φ u * φ w := by rw [← map_pow, ← map_sub, hw, map_mul]
  have hprod : (Yc f - φ v) * (Yc f + φ v) = -(φ u * φ w) := by
    linear_combination hY - hvw
  have hI : mumford f u (-v) = Ideal.span {φ u, Yc f + φ v} := by
    simp only [mumford, map_neg, sub_neg_eq_add, hφ]
  rw [hI, mumford]
  apply le_antisymm
  · rw [Ideal.span_mul_span, Ideal.span_le]
    rintro x ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Dvd.intro _ rfl
    · exact Dvd.intro _ rfl
    · exact Dvd.intro_left _ rfl
    · dsimp only; rw [hprod]; exact (Dvd.intro _ rfl).neg_right
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h2R : algebraMap K (CoordRing f) 2⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap K (CoordRing f)) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
    have habc' : φ a * φ u + φ b * φ v + φ c * φ w = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, habc, map_one]
    have key : φ u = φ a * (φ u * φ u) + φ b * algebraMap K (CoordRing f) 2⁻¹ *
        (φ u * (Yc f + φ v) - (Yc f - φ v) * φ u) + φ c * (-((Yc f - φ v) * (Yc f + φ v))) := by
      rw [hprod]
      linear_combination (-φ u) * habc' + (-(φ b * φ u * φ v)) * h2R
    suffices hmem : φ a * (φ u * φ u) + φ b * algebraMap K (CoordRing f) 2⁻¹ *
        (φ u * (Yc f + φ v) - (Yc f - φ v) * φ u) + φ c * (-((Yc f - φ v) * (Yc f + φ v))) ∈
        Ideal.span {φ u, Yc f - φ v} * Ideal.span {φ u, Yc f + φ v} by rwa [← key] at hmem
    have hu1 : φ u ∈ Ideal.span {φ u, Yc f - φ v} := Ideal.subset_span (by simp)
    have hv1 : Yc f - φ v ∈ Ideal.span {φ u, Yc f - φ v} := Ideal.subset_span (by simp)
    have hu2 : φ u ∈ Ideal.span {φ u, Yc f + φ v} := Ideal.subset_span (by simp)
    have hv2 : Yc f + φ v ∈ Ideal.span {φ u, Yc f + φ v} := Ideal.subset_span (by simp)
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hu1 hu2)
    · exact Ideal.mul_mem_left _ _
        (Ideal.sub_mem _ (Ideal.mul_mem_mul hu1 hv2) (Ideal.mul_mem_mul hv1 hu2))
    · exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_mul hv1 hv2))

theorem FurioLombardo.M3a.eq_span_of_mul_self_eq_span_mul_self {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {J : Ideal R} {u : R} (h : J * J = Ideal.span {u * u}) :
    J = Ideal.span {u} := by
  obtain ⟨g, rfl⟩ : ∃ g, J = Ideal.span {g} :=
    ⟨Submodule.IsPrincipal.generator J, (Ideal.span_singleton_generator J).symm⟩
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton] at h
  rw [Ideal.span_singleton_eq_span_singleton]
  rw [← sq, ← sq] at h
  exact associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp h.dvd)
    ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp h.symm.dvd)
