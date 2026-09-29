import Mathlib
import FurioLombardo.M3a.TwoTorsion

/-!
# Reduction theory of the ideal class model of `Y² = f` (discharge of M3a, WP1)

For a field `K` and `f : K[X]` with `GoodSextic f`, on `R = CoordRing f = K[X][Y]/(Y² - f)`:

* `exists_coprime_of_squarefree`: if `v² - f = u w` with `f` squarefree, then `(u, v, w) = 1`
  (the hypothesis `hc` of M3a's `relNorm_mumford`, `parity_mumford`, `mk0_mumford_neg`);
* `dvd_of_algebraMap_mem_mumford`: `⟨u, Y - v⟩ ∩ K[X] ⊆ (u)` when `u ∣ v² - f`;
* `exists_mumford_normal_form`: every nonzero ideal is `(z) ⟨u, Y - v⟩` with `z ≠ 0`, `u` monic,
  `u ∣ v² - f`;
* `mumford_mul_mumford_eq_span`: `⟨u, Y - v⟩ ⟨w, Y - v⟩ = (Y - v)` when `v² - f = u w` and
  `(u, v, w) = 1`;
* `mk0_mumford_eq_mk0_mumford_neg`: one Cantor step, `[⟨u, Y - v⟩] = [⟨w', Y + v⟩]` with `w'` the
  monic associate of `(v² - f)/u`;
* `exists_reduced_of_mumford`: every Mumford class is the class of a Mumford ideal `⟨u, Y - v⟩`
  with `deg u ≤ 3` and `deg v < deg u`;
* `jac_eq_one_or_reduced`: every point of `Jac f` is `1` or the class of a Mumford ideal
  `⟨u, Y - v⟩` with `u` monic of degree 2 and `deg v < 2`.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.M3a

variable {K : Type*} [Field K]

/-- Coprimality of a Mumford triple is automatic when `f` is squarefree: a common divisor `d` of
`u, v, w` has `d² ∣ v² - u w = f`. -/
theorem exists_coprime_of_squarefree {f u v w : K[X]} (hf : Squarefree f)
    (hw : v ^ 2 - f = u * w) : ∃ a b c : K[X], a * u + b * v + c * w = 1 := by
  set J : Ideal K[X] := Ideal.span {u, v, w}
  set d := Submodule.IsPrincipal.generator J
  have hJ : J = Ideal.span {d} := (Ideal.span_singleton_generator J).symm
  have hdvd : ∀ x ∈ ({u, v, w} : Set K[X]), d ∣ x := fun x hx =>
    Ideal.mem_span_singleton.mp (hJ ▸ Ideal.subset_span hx)
  have hdu := hdvd u (by simp)
  have hdv := hdvd v (by simp)
  have hdw := hdvd w (by simp)
  have hf' : f = v ^ 2 - u * w := by rw [← hw]; ring
  have hdd : d * d ∣ f := by
    rw [hf', sq]; exact dvd_sub (mul_dvd_mul hdv hdv) (mul_dvd_mul hdu hdw)
  have h1 : (1 : K[X]) ∈ J := by
    rw [hJ, Ideal.span_singleton_eq_top.mpr (hf d hdd)]; exact Submodule.mem_top
  obtain ⟨a, z, hz, hza⟩ := Ideal.mem_span_insert.mp h1
  obtain ⟨b, c, hbc⟩ := Ideal.mem_span_pair.mp hz
  exact ⟨a, b, c, by rw [hza, ← hbc]; ring⟩

/-- The Mumford ideal only depends on `u` up to a unit. -/
theorem mumford_eq_of_associated (f : K[X]) [GoodSextic f] {u u' : K[X]} (h : Associated u u')
    (v : K[X]) : mumford f u v = mumford f u' v := by
  unfold mumford
  rw [Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_eq_span_singleton.mpr (h.map (algebraMap K[X] (CoordRing f)))]

/-- The Mumford ideal only depends on `v` modulo `u`. -/
theorem mumford_add_mul (f u v k : K[X]) : mumford f u (v + u * k) = mumford f u v := by
  unfold mumford
  have h : Yc f - algebraMap K[X] (CoordRing f) (v + u * k) =
      (Yc f - algebraMap K[X] (CoordRing f) v) +
        (-algebraMap K[X] (CoordRing f) k) * algebraMap K[X] (CoordRing f) u := by
    rw [map_add, map_mul]; ring
  rw [h, Set.pair_comm, Ideal.span_pair_add_mul_right, Set.pair_comm]

/-- `⟨u, Y - v⟩ ∩ K[X] ⊆ (u)` when `u ∣ v² - f`: the map `X ↦ X`, `Y ↦ v` to `K[X]/(u)` kills
the ideal. -/
theorem dvd_of_algebraMap_mem_mumford {f u v g : K[X]} (hu : u ∣ v ^ 2 - f)
    (hg : algebraMap K[X] (CoordRing f) g ∈ mumford f u v) : u ∣ g := by
  have hev : eval₂ (AdjoinRoot.mk u) (AdjoinRoot.mk u v) (curvePoly f) = 0 := by
    simp only [curvePoly, eval₂_sub, eval₂_X_pow, eval₂_C]
    rw [← map_pow, ← map_sub]
    exact AdjoinRoot.mk_eq_zero.mpr hu
  set ψ : CoordRing f →+* AdjoinRoot u := AdjoinRoot.lift (AdjoinRoot.mk u) (AdjoinRoot.mk u v) hev
    with hψ
  have hψa : ∀ p : K[X], ψ (algebraMap K[X] (CoordRing f) p) = AdjoinRoot.mk u p := by
    intro p; simp [hψ, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  have hψY : ψ (Yc f) = AdjoinRoot.mk u v := by simp [hψ, Yc, AdjoinRoot.lift_root]
  have hle : mumford f u v ≤ RingHom.ker ψ := by
    rw [mumford, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rcases hx with rfl | rfl
    · rw [hψa, AdjoinRoot.mk_self]
    · rw [map_sub, hψY, hψa, sub_self]
  have := hle hg
  rw [RingHom.mem_ker, hψa] at this
  exact AdjoinRoot.mk_eq_zero.mp this

/-- The second coordinate (on `Y`) of an element of `CoordRing f`, as a `K[X]`-linear map. -/
noncomputable abbrev coordY (f : K[X]) : CoordRing f →ₗ[K[X]] K[X] := (basis f).coord 1

theorem coordY_smul_basis (f p q : K[X]) : coordY f (p • (1 : CoordRing f) + q • Yc f) = q := by
  rw [Module.Basis.coord_apply]; exact (repr_smul_basis f p q).2

/-- Mumford normal form: every nonzero ideal of `CoordRing f` is `(z) ⟨u, Y - v⟩` with `z ≠ 0`,
`u` monic and `u ∣ v² - f`. -/
theorem exists_mumford_normal_form (f : K[X]) [GoodSextic f] {I : Ideal (CoordRing f)}
    (hI : I ≠ ⊥) :
    ∃ z u v w : K[X], z ≠ 0 ∧ u.Monic ∧ v ^ 2 - f = u * w ∧
      I = Ideal.span {algebraMap K[X] (CoordRing f) z} * mumford f u v := by
  classical
  set φ := algebraMap K[X] (CoordRing f) with hφ
  have hsmul : ∀ (p : K[X]) (x : CoordRing f), p • x = φ p * x := fun p x => smul_eq f p x
  -- `I0 = I ∩ K[X]` and `I1`, the ideal of `Y`-coordinates of `I`
  set I0 : Ideal K[X] := I.comap φ with hI0
  set I1 : Ideal K[X] := Submodule.map (coordY f) (I.restrictScalars K[X]) with hI1
  have hmemI1 : ∀ p q : K[X], p • (1 : CoordRing f) + q • Yc f ∈ I → q ∈ I1 := by
    intro p q h
    exact ⟨_, h, coordY_smul_basis f p q⟩
  have hI1mem : ∀ q ∈ I1, ∃ p : K[X], p • (1 : CoordRing f) + q • Yc f ∈ I := by
    rintro q ⟨x, hx, rfl⟩
    obtain ⟨p, q', rfl⟩ := exists_smul_basis_eq f x
    exact ⟨p, by rw [coordY_smul_basis]; exact hx⟩
  set w0 := Submodule.IsPrincipal.generator I0
  set z := Submodule.IsPrincipal.generator I1
  have hw0I : φ w0 ∈ I := Submodule.IsPrincipal.generator_mem I0
  have hI0dvd : ∀ g : K[X], φ g ∈ I → w0 ∣ g := fun g hg =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd I0).mp hg
  -- `I0 ≠ 0`: it contains the norm of a nonzero element of `I`
  have hw0 : w0 ≠ 0 := by
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hN : φ (Algebra.norm K[X] x) ∈ I := by
      rw [← mul_conj]; exact I.mul_mem_right _ hxI
    obtain ⟨c, hc⟩ := hI0dvd _ hN
    intro h0
    rw [h0, zero_mul] at hc
    exact (norm_ne_zero_and_even hx0).1 hc
  -- `z ∣ w0`, from `w0 Y ∈ I`
  have hzw0 : z ∣ w0 := by
    refine (Submodule.IsPrincipal.mem_iff_generator_dvd I1).mp (hmemI1 0 w0 ?_)
    rw [zero_smul, zero_add, hsmul]
    exact I.mul_mem_right _ hw0I
  obtain ⟨e, he⟩ := hzw0
  have hz : z ≠ 0 := by rintro h0; rw [h0, zero_mul] at he; exact hw0 he
  have he0 : e ≠ 0 := by rintro h0; rw [h0, mul_zero] at he; exact hw0 he
  -- an element `t + zY` of `I`, and `z ∣ t` from `(t + zY) Y ∈ I`
  obtain ⟨t, ht⟩ := hI1mem z (Submodule.IsPrincipal.generator_mem I1)
  have hzt : z ∣ t := by
    refine (Submodule.IsPrincipal.mem_iff_generator_dvd I1).mp (hmemI1 (z * f) t ?_)
    rw [← smul_basis_mul_Y]
    exact I.mul_mem_right _ ht
  obtain ⟨t', rfl⟩ := hzt
  set g := (z * t') • (1 : CoordRing f) + z • Yc f with hg
  have hgφ : g = φ z * (Yc f + φ t') := by
    rw [hg, hsmul, hsmul, map_mul]; ring
  -- `e ∣ f - t'²`, from `Y g - t' g = z (f - t'²) ∈ I`
  have hef : e ∣ f - t' ^ 2 := by
    have hmem : φ (z * (f - t' ^ 2)) ∈ I := by
      have h1 : Yc f * g - φ t' * g ∈ I := I.sub_mem (I.mul_mem_left _ ht) (I.mul_mem_left _ ht)
      have h2 : Yc f * g - φ t' * g = φ (z * (f - t' ^ 2)) := by
        rw [hgφ, map_mul, map_sub, map_pow, ← Yc_sq]; ring
      rwa [h2] at h1
    have := hI0dvd _ hmem
    rw [he] at this
    exact (mul_dvd_mul_iff_left hz).mp this
  -- `I = (w0, g)`
  have hIeq : I = Ideal.span {φ w0, g} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f x
      obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd I1).mp (hmemI1 p q hx)
      replace hs : q = z * s := hs
      have hdiff : p • (1 : CoordRing f) + q • Yc f - φ s * g = φ (p - s * (z * t')) := by
        rw [hs, hg]; simp only [hsmul, map_sub, map_mul, mul_one]; ring
      have hmem : φ (p - s * (z * t')) ∈ I := by
        rw [← hdiff]; exact I.sub_mem hx (I.mul_mem_left _ ht)
      obtain ⟨r, hr⟩ := hI0dvd _ hmem
      have hx' : p • (1 : CoordRing f) + q • Yc f = φ r * φ w0 + φ s * g := by
        rw [← sub_eq_iff_eq_add, hdiff, hr, map_mul, mul_comm]
      rw [hx']
      exact Ideal.mem_span_pair.mpr ⟨φ r, φ s, rfl⟩
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hw0I
      · exact ht
  -- the Mumford data
  set u := normalize e with hu
  have hue : Associated u e := normalize_associated e
  have hmonic : u.Monic := monic_normalize he0
  have hudvd : u ∣ (-t') ^ 2 - f := by
    have : (-t') ^ 2 - f = -(f - t' ^ 2) := by ring
    rw [this]
    exact (hue.dvd.trans hef).neg_right
  obtain ⟨w, hw⟩ := hudvd
  refine ⟨z, u, -t', w, hz, hmonic, hw, ?_⟩
  rw [mumford_eq_of_associated f hue, hIeq, mumford, Ideal.span_mul_span, Set.singleton_mul,
    Set.image_pair, he, hgφ, map_neg, sub_neg_eq_add, map_mul]


/-- `⟨u, Y - v⟩ ⟨w, Y - v⟩ = (Y - v)` when `v² - f = u w` and `(u, v, w) = 1`: the product is
contained in `(Y - v)` since `u w = -(Y - v)(Y + v)`, and `Y - v` is in the product since
`v (Y - v) = -((Y - v)² + u w)/2`. -/
theorem mumford_mul_mumford_eq_span {f u v w : K[X]} (h2 : (2 : K) ≠ 0)
    (hw : v ^ 2 - f = u * w) (hc : ∃ a b c : K[X], a * u + b * v + c * w = 1) :
    mumford f u v * mumford f w v =
      Ideal.span {Yc f - algebraMap K[X] (CoordRing f) v} := by
  obtain ⟨a, b, c, habc⟩ := hc
  set φ := algebraMap K[X] (CoordRing f) with hφ
  have hY : Yc f ^ 2 = φ f := Yc_sq f
  have hvw : φ v ^ 2 - φ f = φ u * φ w := by rw [← map_pow, ← map_sub, hw, map_mul]
  have huw : φ u * φ w = -((Yc f - φ v) * (Yc f + φ v)) := by linear_combination hY - hvw
  apply le_antisymm
  · rw [mumford, mumford, Ideal.span_mul_span, Ideal.span_le]
    rintro x ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> dsimp only
    · rw [huw]; exact (Dvd.intro _ rfl).neg_right
    · exact Dvd.intro_left _ rfl
    · exact Dvd.intro _ rfl
    · exact Dvd.intro _ rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have h2R : algebraMap K (CoordRing f) 2⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap K (CoordRing f)) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
    have habc' : φ a * φ u + φ b * φ v + φ c * φ w = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, habc, map_one]
    have key : Yc f - φ v = φ a * (φ u * (Yc f - φ v)) -
        φ b * algebraMap K (CoordRing f) 2⁻¹ * ((Yc f - φ v) * (Yc f - φ v) + φ u * φ w) +
        φ c * ((Yc f - φ v) * φ w) := by
      linear_combination (-(Yc f - φ v)) * habc' + (-(φ b * φ v * (Yc f - φ v))) * h2R +
        (φ b * algebraMap K (CoordRing f) 2⁻¹) * hY -
        (φ b * algebraMap K (CoordRing f) 2⁻¹) * hvw
    rw [key]
    have hu1 : φ u ∈ mumford f u v := Ideal.subset_span (Set.mem_insert _ _)
    have hv1 : Yc f - φ v ∈ mumford f u v := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hw2 : φ w ∈ mumford f w v := Ideal.subset_span (Set.mem_insert _ _)
    have hv2 : Yc f - φ v ∈ mumford f w v := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hu1 hv2)
    · exact Ideal.mul_mem_left _ _
        (Ideal.add_mem _ (Ideal.mul_mem_mul hv1 hv2) (Ideal.mul_mem_mul hu1 hw2))
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hv1 hw2)

theorem Yc_sub_ne_zero (f v : K[X]) : Yc f - algebraMap K[X] (CoordRing f) v ≠ 0 := by
  intro h0
  have h : (-v) • (1 : CoordRing f) + (1 : K[X]) • Yc f = 0 := by
    rw [smul_eq, smul_eq, map_neg, map_one, mul_one, one_mul, ← h0]; ring
  exact one_ne_zero (smul_basis_eq_zero f h).2

/-- One Cantor step: for `v² - f = u w` with `w ≠ 0`, `[⟨u, Y - v⟩] = [⟨w₁, Y + v⟩]` where `w₁` is
the monic associate of `w`. -/
theorem mk0_mumford_eq_mk0_mumford_neg (f : K[X]) [GoodSextic f] {u v w : K[X]} (hu : u.Monic)
    (hw0 : w ≠ 0) (hw : v ^ 2 - f = u * w) :
    ∃ (w₁ w' : K[X]) (hw₁ : w₁.Monic), w₁.natDegree = w.natDegree ∧ (-v) ^ 2 - f = w₁ * w' ∧
      ClassGroup.mk0 (mumford0 f hu.ne_zero v) = ClassGroup.mk0 (mumford0 f hw₁.ne_zero (-v)) := by
  classical
  have hsq : Squarefree f := GoodSextic.squarefree
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have hassoc : Associated w (normalize w) := (normalize_associated w).symm
  have hw1 : (normalize w).Monic := monic_normalize hw0
  obtain ⟨w', hw'⟩ : normalize w ∣ v ^ 2 - f :=
    hassoc.symm.dvd.trans (Dvd.intro_left u hw.symm)
  have hprod := mumford_mul_mumford_eq_span (f := f) h2 hw (exists_coprime_of_squarefree hsq hw)
  rw [mumford_eq_of_associated f hassoc] at hprod
  have h1 : ClassGroup.mk0 (mumford0 f hu.ne_zero v) =
      (ClassGroup.mk0 (mumford0 f hw1.ne_zero v))⁻¹ :=
    ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨_, Yc_sub_ne_zero f v, hprod⟩
  refine ⟨normalize w, w', hw1,
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc.symm),
    by rw [neg_sq]; exact hw', ?_⟩
  rw [h1, mk0_mumford_neg f hw1 hw' (exists_coprime_of_squarefree hsq hw')]

/-- Cantor reduction: the class of a Mumford ideal `⟨u, Y - v⟩` (`u` monic, `u ∣ v² - f`) is the
class of a Mumford ideal `⟨u', Y - v'⟩` with `deg u' ≤ 3` and `deg v' < deg u'`. -/
theorem exists_reduced_of_mumford (f : K[X]) [GoodSextic f] (n : ℕ) :
    ∀ (u v w : K[X]) (hu : u.Monic), u.natDegree = n → v ^ 2 - f = u * w →
      ∃ (u' v' w' : K[X]) (hu' : u'.Monic), u'.natDegree ≤ 3 ∧ v'.degree < u'.degree ∧
        v' ^ 2 - f = u' * w' ∧
        ClassGroup.mk0 (mumford0 f hu.ne_zero v) =
          ClassGroup.mk0 (mumford0 f hu'.ne_zero v') := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v w hu hn hw
  -- reduce `v` modulo `u`
  set v1 := v %ₘ u with hv1def
  have hv : v1 + u * (v /ₘ u) = v := modByMonic_add_div v u
  have hdeg1 : v1.degree < u.degree := degree_modByMonic_lt v hu
  have hM : mumford f u v = mumford f u v1 := by rw [← hv, mumford_add_mul]
  set w1 := w - 2 * (v /ₘ u) * v1 - u * (v /ₘ u) ^ 2 with hw1def
  have hw1 : v1 ^ 2 - f = u * w1 := by
    have h := hw
    rw [← hv] at h
    linear_combination h
  have hcls : ClassGroup.mk0 (mumford0 f hu.ne_zero v) =
      ClassGroup.mk0 (mumford0 f hu.ne_zero v1) := by
    congr 1; exact Subtype.ext hM
  by_cases hn3 : n ≤ 3
  · exact ⟨u, v1, w1, hu, by omega, hdeg1, hw1, hcls⟩
  -- one Cantor step lowers the degree when `deg u ≥ 4`
  rw [not_le] at hn3
  have hw10 : w1 ≠ 0 := by
    rintro h0
    rw [h0, mul_zero, sub_eq_zero] at hw1
    exact GoodSextic.not_isSquare (f := f) ⟨v1, by rw [← hw1, sq]⟩
  have hv1n : v1.natDegree < n := by
    by_cases hv10 : v1 = 0
    · rw [hv10, natDegree_zero]; omega
    · rw [← hn]; exact natDegree_lt_natDegree hv10 hdeg1
  have hdegw1 : w1.natDegree < n := by
    have h1 : (u * w1).natDegree = n + w1.natDegree := by
      rw [natDegree_mul hu.ne_zero hw10, hn]
    have h2 : (v1 ^ 2 - f).natDegree ≤ max (2 * v1.natDegree) 6 := by
      refine (natDegree_sub_le _ _).trans ?_
      rw [natDegree_pow, GoodSextic.natDegree_eq (f := f), mul_comm]
    rw [hw1, h1] at h2
    rcases le_max_iff.mp h2 with h | h <;> omega
  obtain ⟨u2, w2, hu2, hu2deg, hw2, hcls2⟩ := mk0_mumford_eq_mk0_mumford_neg f hu hw10 hw1
  obtain ⟨u', v', w', hu', h3, hdeg', hw', hcls'⟩ :=
    ih _ (hu2deg ▸ hdegw1) u2 (-v1) w2 hu2 rfl hw2
  exact ⟨u', v', w', hu', h3, hdeg', hw', hcls.trans (hcls2.trans hcls')⟩

/-- Reduced representatives: every point of `A(K) = Jac f` is `1` or the class of a Mumford ideal
`⟨u, Y - v⟩` with `u` monic of degree 2, `deg v < 2` and `u ∣ v² - f`. -/
theorem jac_eq_one_or_reduced (f : K[X]) [GoodSextic f] (c : Jac f) :
    c = 1 ∨ ∃ (u v w : K[X]) (hu : u.Monic), u.natDegree = 2 ∧ v.degree < 2 ∧
      v ^ 2 - f = u * w ∧ (c : Pic f) = ClassGroup.mk0 (mumford0 f hu.ne_zero v) := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective (c : Pic f)
  obtain ⟨z, u, v, w, hz, hu, hw, hIeq⟩ :=
    exists_mumford_normal_form f (nonZeroDivisors.ne_zero I.2)
  have hz' : algebraMap K[X] (CoordRing f) z ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective f)).mpr hz
  have hZmem : Ideal.span {algebraMap K[X] (CoordRing f) z} ∈ (Ideal (CoordRing f))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot])
  have hIZ : I = ⟨_, hZmem⟩ * mumford0 f hu.ne_zero v := Subtype.ext hIeq
  have hZ : ClassGroup.mk0 ⟨_, hZmem⟩ = 1 := (ClassGroup.mk0_eq_one_iff hZmem).mpr ⟨_, rfl⟩
  have hcM : (c : Pic f) = ClassGroup.mk0 (mumford0 f hu.ne_zero v) := by
    rw [← hI, hIZ, map_mul, hZ, one_mul]
  obtain ⟨u', v', w', hu', h3, hdeg', hw', hcls⟩ := exists_reduced_of_mumford f _ u v w hu rfl hw
  rw [hcls] at hcM
  have hpar : parity f (c : Pic f) = 1 := MonoidHom.mem_ker.mp c.2
  rw [hcM, parity_mumford f hu' hw' (exists_coprime_of_squarefree GoodSextic.squarefree hw'),
    ofAdd_eq_one] at hpar
  have hev : 2 ∣ u'.natDegree := (ZMod.natCast_eq_zero_iff _ _).mp hpar
  rcases (by omega : u'.natDegree = 0 ∨ u'.natDegree = 2) with h0 | h2
  · left
    have h1 : u' = 1 := eq_one_of_monic_natDegree_zero hu' h0
    subst h1
    apply Subtype.ext
    rw [hcM, OneMemClass.coe_one]
    apply (ClassGroup.mk0_eq_one_iff _).mpr
    have htop : mumford f 1 v' = ⊤ := by
      rw [Ideal.eq_top_iff_one, mumford, map_one]; exact Ideal.subset_span (by simp)
    change (mumford f 1 v').IsPrincipal
    rw [htop]
    exact ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩
  · right
    refine ⟨u', v', w', hu', h2, ?_, hw', hcM⟩
    rwa [degree_eq_natDegree hu'.ne_zero, h2] at hdeg'

end FurioLombardo.Discharge.M3a
