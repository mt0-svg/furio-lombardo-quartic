import Mathlib
import FurioLombardo.Discharge.M3a.XTKernelK1
import FurioLombardo.Discharge.M3a.K1Half

/-!
# (K1) without a named input: the kernel of `x - T` is `2 A(k)` (lane K1)

The elementary proof of Cassels and Flynn (Prolegomena, chapter 6, sections 1, 2, 8), in M3a's ideal
class model.

**Theorem K1E** (`xtKernel_of_deltaTrivial`). Let `f` satisfy `GoodSextic f`. Assume

* (H1) `DeltaTrivial f`;
* (H3) `f` has no root in `K`;
* (H4) `μ(T) ≠ 1` for the class `T = [⟨q, Y⟩]` of every monic quadratic divisor `q` of `f`.

Then `XTKernel f`. So `PoonenSchaefer f` holds under (H3) and (H4) (`poonenSchaefer_of`), and no
literature input and no `A(k) = Pic⁰(C)(k)` is needed.

Proof: Step 0 (`jac_eq_one_or_reduced`), Step 1 (classes with Weierstrass support, by (H3) and
(H4)), Step 2 (`mu_mumford_of_coprime`, `exists_eq_const_mul_sq`: `u(Θ) = η ρ²`), Step 3 (the sign
`f₆ η³ N(ρ) = ±N_u(v)` from `lc_sq_mul_norm_eq_sq`, and the switch `(η, ρ) ↦ (η/d, ερ)` by (H1)),
Steps 4 to 8 (`exists_half_of_good_sign`, K1Half.lean).
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.M3a

open K1

variable {K : Type*} [Field K]

/-- **Step 2.** For `u` monic coprime to `f` with `v² - f = u w`, `μ([⟨u, Y - v⟩]) = [u(Θ)]`. -/
theorem mu_mumford_of_coprime (f : K[X]) [GoodSextic f] {u v w : K[X]} (hu : u.Monic)
    (hw : v ^ 2 - f = u * w) (huf : IsCoprime u f) :
    mu f (ClassGroup.mk0 (mumford0 f hu.ne_zero v)) =
      QuotientGroup.mk (isUnit_mk_of_isCoprime huf).unit := by
  have huv : IsCoprime u v := isCoprime_u_v hw huf
  set φ := algebraMap K[X] (CoordRing f) with hφ
  have hI : (mumford0 f hu.ne_zero v : Ideal (CoordRing f)) ⊔ Ideal.span {Yc f} = ⊤ := by
    obtain ⟨a, b, hab⟩ := huv
    rw [Ideal.eq_top_iff_one, Submodule.mem_sup]
    refine ⟨φ a * φ u - φ b * (Yc f - φ v), ?_, φ b * Yc f, ?_, ?_⟩
    · refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · have := congrArg φ hab
      rw [map_add, map_mul, map_mul, map_one] at this
      rw [← this]
      ring
  rw [mu_mk0 f _ hI]
  have hc := exists_coprime_of_squarefree GoodSextic.squarefree hw
  have hN : Ideal.relNorm K[X] (mumford0 f hu.ne_zero v : Ideal (CoordRing f)) =
      Ideal.span {u} := relNorm_mumford f hu hw hc
  set g := Submodule.IsPrincipal.generator
    (Ideal.relNorm K[X] (mumford0 f hu.ne_zero v : Ideal (CoordRing f))) with hg
  have hassoc : Associated g u := by
    rw [← Ideal.span_singleton_eq_span_singleton, hg, Ideal.span_singleton_generator, hN]
  obtain ⟨c, hc'⟩ := hassoc
  obtain ⟨r, hr, hrc⟩ := Polynomial.isUnit_iff.mp c.isUnit
  have hkey : AdjoinRoot.mk f g * algebraMap K (AdjoinRoot f) r = AdjoinRoot.mk f u := by
    rw [← hc', map_mul, ← hrc, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  have hgu : IsUnit (AdjoinRoot.mk f g) :=
    isUnit_of_mul_isUnit_left (hkey ▸ isUnit_mk_of_isCoprime huf)
  unfold muIdeal
  rw [dite_eq_left_of_eq_true (eq_true hgu), QuotientGroup.eq]
  apply Subgroup.mem_sup_left
  refine ⟨hr.unit, ?_⟩
  ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_mul,
    IsUnit.unit_spec]
  rw [← hkey, ← mul_assoc, Units.inv_mul_of_eq hgu.unit_spec.symm, one_mul]

/-- **Step 2.** A unit of `A = K[X]/(f)` with trivial class in `H f` is `η ρ²` with `η ∈ K^×`. -/
theorem exists_eq_const_mul_sq {f : K[X]} {x : (AdjoinRoot f)ˣ}
    (h : (QuotientGroup.mk x : H f) = 1) :
    ∃ η : K, η ≠ 0 ∧ ∃ ρ : AdjoinRoot f, (x : AdjoinRoot f) = algebraMap K (AdjoinRoot f) η * ρ ^ 2 := by
  rw [QuotientGroup.eq_one_iff] at h
  obtain ⟨a, ⟨c, rfl⟩, b, ⟨y, rfl⟩, hab⟩ := Subgroup.mem_sup.mp h
  refine ⟨c, c.ne_zero, y, ?_⟩
  rw [← hab]
  simp [sq]

/-- **Theorem K1E.** Under `DeltaTrivial f`, no root of `f` in `K` and `μ(T) ≠ 1` for the class `T` of
every monic quadratic divisor of `f`, the kernel of `μ = x - T` on `A(K) = Jac f` is `2 A(K)`. -/
theorem xtKernel_of_deltaTrivial (f : K[X]) [GoodSextic f] (hδ : DeltaTrivial f)
    (hroot : ∀ a : K, f.eval a ≠ 0)
    (hT : ∀ (q : K[X]) (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2),
      muJ f (Tpt f hq hqf hdeg) ≠ 1) :
    XTKernel f := by
  intro Q hQ
  have h6 : f.natDegree = 6 := GoodSextic.natDegree_eq
  have hf0 : f ≠ 0 := by rintro rfl; simp at h6
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  -- Step 0
  rcases jac_eq_one_or_reduced f Q with rfl | ⟨u, v, w₀, hu, h2, hv, hw₀, hQu⟩
  · exact ⟨1, by rw [one_pow]⟩
  -- Step 1
  have huf : IsCoprime u f := by
    by_contra hnc
    have hdvd := dvd_of_not_isCoprime hu h2 hroot hnc
    have hv0 := v_eq_zero_of_dvd h2 hdvd GoodSextic.squarefree hw₀ hv
    subst hv0
    apply hT u hu hdvd h2
    have hQT : Q = Tpt f hu hdvd h2 := Subtype.ext (by rw [hQu, coe_Tpt])
    rw [← hQT]
    exact hQ
  -- Step 2
  have hmu := mu_mumford_of_coprime f hu hw₀ huf
  have hmuQ : (QuotientGroup.mk (isUnit_mk_of_isCoprime huf).unit : H f) = 1 := by
    rw [← hmu, ← hQu]
    exact hQ
  obtain ⟨η, hη, ρ, hρ⟩ := exists_eq_const_mul_sq hmuQ
  rw [IsUnit.unit_spec] at hρ
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective ρ
  -- Step 3: the sign
  have hsq := lc_sq_mul_norm_eq_sq h6 hu h2 ⟨w₀, hw₀⟩
  have hNu : Algebra.norm K (AdjoinRoot.mk f u) =
      η ^ 6 * Algebra.norm K (AdjoinRoot.mk f r) ^ 2 := by
    rw [hρ, map_mul, map_pow, norm_algebraMap_adjoinRoot_of_ne_zero hf0, h6]
  have hsign : (f.leadingCoeff * η ^ 3 * Algebra.norm K (AdjoinRoot.mk f r)) ^ 2 =
      Algebra.norm K (AdjoinRoot.mk u v) ^ 2 := by
    rw [← hsq, hNu]
    ring
  suffices h : ∃ R : Jac f, ClassGroup.mk0 (mumford0 f hu.ne_zero v) = (R : Pic f) ^ 2 by
    obtain ⟨R, hR⟩ := h
    exact ⟨R, Subtype.ext (by rw [hQu, hR]; rfl)⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsign with hbad | hgood
  · -- the switch (η, ρ) ↦ (η/d, ερ)
    obtain ⟨d, hd, ε, hε, hNε⟩ := hδ
    obtain ⟨e, rfl⟩ := AdjoinRoot.mk_surjective ε
    refine exists_half_of_good_sign f hroot hu h2 hw₀ huf (η := η / d) (div_ne_zero hη hd)
      (r := e * r) ?_ ?_
    · rw [hρ, map_mul, mul_pow, hε, ← mul_assoc, ← map_mul, div_mul_cancel₀ η hd]
    · rw [map_mul, map_mul, hNε, ← hbad]
      field_simp
  · exact exists_half_of_good_sign f hroot hu h2 hw₀ huf hη hρ hgood

/-- **`PoonenSchaefer f` is a theorem** under the two concrete side facts (H3) and (H4). -/
theorem poonenSchaefer_of (f : K[X]) [GoodSextic f] (hroot : ∀ a : K, f.eval a ≠ 0)
    (hT : ∀ (q : K[X]) (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2),
      muJ f (Tpt f hq hqf hdeg) ≠ 1) :
    PoonenSchaefer f :=
  fun hδ => xtKernel_of_deltaTrivial f hδ hroot hT

end FurioLombardo.Discharge.M3a
