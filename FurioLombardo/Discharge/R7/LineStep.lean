import Mathlib
import FurioLombardo.Discharge.M3a.Reduction

/-!
# Line steps in the ideal class model of `Y² = f` (item R7)

On `CoordRing f = K[X][Y]/(Y² - f)` with `GoodSextic f` (M3a's model of the Jacobian):

* `mumford_mul_mumford_of_dvd`: `⟨g, Y - V⟩ ⟨h, Y - V⟩ = ⟨g h, Y - V⟩` when `g h ∣ V² - f`
  (inclusion, plus equality of the products with the conjugates, in the Dedekind domain);
* `mk0_mumford_congr`, `mk0_mumford_of_associated`, `mk0_mumford_neg_of_dvd`: the class of
  `⟨u, Y - v⟩` depends on `v` modulo `u` and on `u` up to a unit, and `⟨u, Y + v⟩` is the inverse;
* `mk0_mumford_eq_of_sq_sub`: if `V² - f = c g h` with `c` a nonzero constant then
  `[⟨g, Y - V⟩] = [⟨h, Y + V⟩]` (one line step);
* `mk0_add_law`: the group law by two line steps, `Q(u) Q(u') = E0 Q(u'')`, from the polynomial
  identities `V² - f = c1 u u' w`, `W² - f = c2 w X2 u''` and the divisibilities
  `u ∣ V - v`, `u' ∣ V - v'`, `w ∣ W + V`, `X2 ∣ W + v0`, `u'' ∣ v'' + W`;
* `eq_of_mk0_mumford_eq`: uniqueness of reduced representatives of degree 2 (the leading
  coefficient of `f` is not a square), the injectivity of the chart.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a

namespace FurioLombardo.Discharge.R7

variable {K : Type*} [Field K]

theorem sq_sub_ne_zero (f : K[X]) [GoodSextic f] (V : K[X]) : V ^ 2 - f ≠ 0 := by
  intro h0
  rw [sub_eq_zero] at h0
  exact GoodSextic.not_isSquare (f := f) ⟨V, by rw [← h0, sq]⟩

/-- The product of two Mumford ideals with the same `V` lies in the Mumford ideal of the
product. -/
theorem mumford_mul_le (f g h V : K[X]) :
    mumford f g V * mumford f h V ≤ mumford f (g * h) V := by
  rw [mumford, mumford, Ideal.span_mul_span, Ideal.span_le]
  rintro x ⟨s, hs, t, ht, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rw [SetLike.mem_coe]
  have hA : algebraMap K[X] (CoordRing f) (g * h) ∈ mumford f (g * h) V :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hB : Yc f - algebraMap K[X] (CoordRing f) V ∈ mumford f (g * h) V :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simpa only [map_mul] using hA
  · exact Ideal.mul_mem_left _ _ hB
  · exact Ideal.mul_mem_right _ _ hB
  · exact Ideal.mul_mem_left _ _ hB

/-- `⟨g, Y - V⟩ ⟨h, Y - V⟩ = ⟨g h, Y - V⟩` when `g h ∣ V² - f`. -/
theorem mumford_mul_mumford_of_dvd (f : K[X]) [GoodSextic f] {g h V r : K[X]}
    (hr : V ^ 2 - f = g * h * r) :
    mumford f g V * mumford f h V = mumford f (g * h) V := by
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have hsq : Squarefree f := GoodSextic.squarefree
  have hne := sq_sub_ne_zero f V
  have hg : g ≠ 0 := by rintro rfl; apply hne; rw [hr]; ring
  have hh : h ≠ 0 := by rintro rfl; apply hne; rw [hr]; ring
  have hwg : V ^ 2 - f = g * (h * r) := by rw [hr]; ring
  have hwh : V ^ 2 - f = h * (g * r) := by rw [hr]; ring
  have hIg := mumford_mul_mumford_neg h2 hwg (exists_coprime_of_squarefree hsq hwg)
  have hIh := mumford_mul_mumford_neg h2 hwh (exists_coprime_of_squarefree hsq hwh)
  have hIgh := mumford_mul_mumford_neg h2 hr (exists_coprime_of_squarefree hsq hr)
  have hprod : mumford f g V * mumford f h V * (mumford f g (-V) * mumford f h (-V)) =
      Ideal.span {algebraMap K[X] (CoordRing f) (g * h)} := by
    calc mumford f g V * mumford f h V * (mumford f g (-V) * mumford f h (-V))
        = (mumford f g V * mumford f g (-V)) * (mumford f h V * mumford f h (-V)) := by ring
      _ = Ideal.span {algebraMap K[X] (CoordRing f) g} *
          Ideal.span {algebraMap K[X] (CoordRing f) h} := by rw [hIg, hIh]
      _ = Ideal.span {algebraMap K[X] (CoordRing f) (g * h)} := by
          rw [Ideal.span_singleton_mul_span_singleton, map_mul]
  refine eq_of_le_of_le_of_mul_eq (mumford_mul_le f g h V) (mumford_mul_le f g h (-V)) ?_ ?_
  · rw [hprod, hIgh]
  · rw [hprod, Ne, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (algebraMap_injective f)).mpr (mul_ne_zero hg hh)

/-- The class of `⟨u, Y - v⟩` only depends on `v` modulo `u`. -/
theorem mk0_mumford_congr (f : K[X]) [GoodSextic f] {u v v' : K[X]} (hu : u ≠ 0)
    (h : u ∣ v' - v) :
    ClassGroup.mk0 (mumford0 f hu v') = ClassGroup.mk0 (mumford0 f hu v) := by
  obtain ⟨k, hk⟩ := h
  have hv : v' = v + u * k := by linear_combination hk
  congr 1
  exact Subtype.ext (by
    change mumford f u v' = mumford f u v
    rw [hv, mumford_add_mul])

/-- The class of `⟨u, Y - v⟩` only depends on `u` up to a unit. -/
theorem mk0_mumford_of_associated (f : K[X]) [GoodSextic f] {u u' : K[X]} (hu : u ≠ 0)
    (hu' : u' ≠ 0) (h : Associated u u') (v : K[X]) :
    ClassGroup.mk0 (mumford0 f hu v) = ClassGroup.mk0 (mumford0 f hu' v) := by
  congr 1
  exact Subtype.ext (mumford_eq_of_associated f h v)

/-- `[⟨u, Y + v⟩] = [⟨u, Y - v⟩]⁻¹` when `u ∣ v² - f`. -/
theorem mk0_mumford_neg_of_dvd (f : K[X]) [GoodSextic f] {u v : K[X]} (hu : u ≠ 0)
    (hdvd : u ∣ v ^ 2 - f) :
    ClassGroup.mk0 (mumford0 f hu (-v)) = (ClassGroup.mk0 (mumford0 f hu v))⁻¹ := by
  obtain ⟨w, hw⟩ := hdvd
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have hm := mumford_mul_mumford_neg h2 hw (exists_coprime_of_squarefree GoodSextic.squarefree hw)
  refine ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨algebraMap K[X] (CoordRing f) u,
    (map_ne_zero_iff _ (algebraMap_injective f)).mpr hu, ?_⟩
  change mumford f u (-v) * mumford f u v = _
  rw [mul_comm]; exact hm

/-- The product of the classes of `⟨g, Y - V⟩` and `⟨h, Y - V⟩` when `g h ∣ V² - f`. -/
theorem mk0_mumford_mul (f : K[X]) [GoodSextic f] {g h V r : K[X]} (hg : g ≠ 0) (hh : h ≠ 0)
    (hr : V ^ 2 - f = g * h * r) :
    ClassGroup.mk0 (mumford0 f hg V) * ClassGroup.mk0 (mumford0 f hh V) =
      ClassGroup.mk0 (mumford0 f (mul_ne_zero hg hh) V) := by
  rw [← map_mul]
  congr 1
  exact Subtype.ext (mumford_mul_mumford_of_dvd f hr)

/-- One line step: if `V² - f = c g h` with `c` a nonzero constant, then
`[⟨g, Y - V⟩] = [⟨h, Y + V⟩]`. -/
theorem mk0_mumford_eq_of_sq_sub (f : K[X]) [GoodSextic f] {g h V : K[X]} {c : K} (hc : c ≠ 0)
    (hg : g ≠ 0) (hh : h ≠ 0) (hV : V ^ 2 - f = C c * (g * h)) :
    ClassGroup.mk0 (mumford0 f hg V) = ClassGroup.mk0 (mumford0 f hh (-V)) := by
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have hw : V ^ 2 - f = g * (C c * h) := by rw [hV]; ring
  have hcu : IsUnit (C c) := Polynomial.isUnit_C.mpr (Ne.isUnit hc)
  have hprod := mumford_mul_mumford_eq_span (f := f) h2 hw
    (exists_coprime_of_squarefree GoodSextic.squarefree hw)
  rw [mumford_eq_of_associated f (associated_unit_mul_left h (C c) hcu)] at hprod
  have hinv : ClassGroup.mk0 (mumford0 f hg V) = (ClassGroup.mk0 (mumford0 f hh V))⁻¹ :=
    ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨_, Yc_sub_ne_zero f V, hprod⟩
  have hdh : h ∣ V ^ 2 - f := ⟨C c * g, by rw [hV]; ring⟩
  rw [hinv, mk0_mumford_neg_of_dvd f hh hdh]

/-- The group law by two line steps. With `E0 = [⟨X2, Y - v0⟩]`:
`[⟨u, Y - v⟩] [⟨u', Y - v'⟩] = E0 [⟨u'', Y - v''⟩]`. -/
theorem mk0_add_law (f : K[X]) [GoodSextic f] {u u' w X2 u'' v v' v0 v'' V W : K[X]} {c1 c2 : K}
    (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0) (hu : u ≠ 0) (hu' : u' ≠ 0) (hX2 : X2 ≠ 0) (hu'' : u'' ≠ 0)
    (hVu : u ∣ V - v) (hVu' : u' ∣ V - v') (hV : V ^ 2 - f = C c1 * (u * u' * w))
    (hWw : w ∣ W + V) (hWX : X2 ∣ W + v0) (hW : W ^ 2 - f = C c2 * (w * X2 * u''))
    (hWu : u'' ∣ v'' + W) :
    ClassGroup.mk0 (mumford0 f hu v) * ClassGroup.mk0 (mumford0 f hu' v') =
      ClassGroup.mk0 (mumford0 f hX2 v0) * ClassGroup.mk0 (mumford0 f hu'' v'') := by
  have hw : w ≠ 0 := by
    rintro rfl; apply sq_sub_ne_zero f V; rw [hV]; ring
  have huu' : u * u' ≠ 0 := mul_ne_zero hu hu'
  have hwX : w * X2 ≠ 0 := mul_ne_zero hw hX2
  have e1 := mk0_mumford_congr f hu hVu
  have e2 := mk0_mumford_congr f hu' hVu'
  have e3 := mk0_mumford_mul f hu hu' (r := C c1 * w) (by rw [hV]; ring)
  have e4 := mk0_mumford_eq_of_sq_sub f hc1 huu' hw hV
  have e5 : ClassGroup.mk0 (mumford0 f hw (-V)) = ClassGroup.mk0 (mumford0 f hw W) := by
    obtain ⟨k, hk⟩ := hWw
    exact mk0_mumford_congr f hw (v := W) (v' := -V) ⟨-k, by linear_combination -hk⟩
  have e6 := mk0_mumford_mul f hw hX2 (V := W) (r := C c2 * u'') (by rw [hW]; ring)
  have e7 : ClassGroup.mk0 (mumford0 f hX2 W) = ClassGroup.mk0 (mumford0 f hX2 (-v0)) :=
    mk0_mumford_congr f hX2 (by simpa [sub_neg_eq_add] using hWX)
  have hX2d : X2 ∣ v0 ^ 2 - f := by
    have h1 : X2 ∣ W ^ 2 - f := ⟨C c2 * w * u'', by rw [hW]; ring⟩
    have h3 : v0 ^ 2 - f = (v0 - W) * (W + v0) + (W ^ 2 - f) := by ring
    rw [h3]; exact dvd_add (dvd_mul_of_dvd_right hWX _) h1
  have e8 := mk0_mumford_neg_of_dvd f hX2 hX2d
  have e9 := mk0_mumford_eq_of_sq_sub f hc2 hwX hu'' hW
  have e10 : ClassGroup.mk0 (mumford0 f hu'' (-W)) = ClassGroup.mk0 (mumford0 f hu'' v'') :=
    (mk0_mumford_congr f hu'' (by rw [sub_neg_eq_add]; exact hWu)).symm
  rw [← e1, ← e2, e3, e4, e5]
  have key : ClassGroup.mk0 (mumford0 f hw W) * (ClassGroup.mk0 (mumford0 f hX2 v0))⁻¹ =
      ClassGroup.mk0 (mumford0 f hu'' v'') := by
    rw [← e8, ← e7, e6, e9, e10]
  have key2 : ClassGroup.mk0 (mumford0 f hw W) =
      ClassGroup.mk0 (mumford0 f hu'' v'') * ClassGroup.mk0 (mumford0 f hX2 v0) := by
    rw [← key, inv_mul_cancel_right]
  rw [key2, mul_comm]

/-- Uniqueness of reduced representatives of degree 2: `[⟨u1, Y - v1⟩] = [⟨u2, Y - v2⟩]` with
`u1, u2` monic quadratic, `u_i ∣ v_i² - f`, forces `u1 = u2` and `v1 ≡ v2 mod u1`. -/
theorem eq_of_mk0_mumford_eq (f : K[X]) [GoodSextic f] {u1 u2 v1 v2 : K[X]} (hu1 : u1.Monic)
    (hu2 : u2.Monic) (hd1 : u1.natDegree = 2) (hd2 : u2.natDegree = 2) (h1 : u1 ∣ v1 ^ 2 - f)
    (h2 : u2 ∣ v2 ^ 2 - f)
    (h : ClassGroup.mk0 (mumford0 f hu1.ne_zero v1) = ClassGroup.mk0 (mumford0 f hu2.ne_zero v2)) :
    u1 = u2 ∧ u1 ∣ v1 - v2 := by
  have hk2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have hsq : Squarefree f := GoodSextic.squarefree
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  have hw2' : (-v2) ^ 2 - f = u2 * w2 := by rw [neg_sq]; exact hw2
  have hd1' : u1 ∣ v1 ^ 2 - f := Dvd.intro w1 hw1.symm
  have hd2' : u2 ∣ (-v2) ^ 2 - f := Dvd.intro w2 hw2'.symm
  have hinv := mk0_mumford_neg_of_dvd f hu2.ne_zero ⟨w2, hw2⟩
  rw [← inv_inv (ClassGroup.mk0 (mumford0 f hu2.ne_zero v2)), ← hinv] at h
  obtain ⟨α, hα0, hα⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp h
  change mumford f u1 v1 * mumford f u2 (-v2) = Ideal.span {α} at hα
  -- norms
  have hN : Ideal.span {Algebra.norm K[X] α} = Ideal.span {u1 * u2} := by
    rw [← relNorm_span_singleton, ← hα, map_mul,
      relNorm_mumford f hu1 hw1 (exists_coprime_of_squarefree hsq hw1),
      relNorm_mumford f hu2 hw2' (exists_coprime_of_squarefree hsq hw2'),
      Ideal.span_singleton_mul_span_singleton]
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f α
  rw [norm_smul_basis, Ideal.span_singleton_eq_span_singleton] at hN
  have hdeg12 : (u1 * u2).natDegree = 4 := by
    rw [natDegree_mul hu1.ne_zero hu2.ne_zero, hd1, hd2]
  have hdN : (p ^ 2 - q ^ 2 * f).natDegree = 4 :=
    (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hN)).trans hdeg12
  have hq : q = 0 := by
    by_contra hq
    have := six_le_natDegree_sq_sub_sq_mul (p := p) GoodSextic.not_isSquare_leadingCoeff
      (GoodSextic.natDegree_eq (f := f)) hq
    omega
  subst hq
  have hαp : p • (1 : CoordRing f) + (0 : K[X]) • Yc f = algebraMap K[X] (CoordRing f) p := by
    rw [zero_smul, add_zero, smul_eq, mul_one]
  rw [hαp] at hα
  rw [zero_pow two_ne_zero, zero_mul, sub_zero] at hN hdN
  have hp0 : p ≠ 0 := by rintro rfl; simp at hdN
  have hpdeg : p.natDegree = 2 := by rw [natDegree_pow] at hdN; omega
  have hmem : algebraMap K[X] (CoordRing f) p ∈ mumford f u1 v1 * mumford f u2 (-v2) := by
    rw [hα]; exact Ideal.mem_span_singleton_self _
  have hdp1 : u1 ∣ p :=
    dvd_of_algebraMap_mem_mumford hd1' (Ideal.mul_le_left hmem)
  have hdp2 : u2 ∣ p :=
    dvd_of_algebraMap_mem_mumford hd2' (Ideal.mul_le_right hmem)
  have hassoc : ∀ {u : K[X]}, u.natDegree = 2 → u ∣ p → Associated u p := by
    intro u hud hup
    obtain ⟨c, hc⟩ := hup
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hp0 hc
    have hu0 : u ≠ 0 := by rintro rfl; simp at hud
    have hcd : c.natDegree = 0 := by
      have := congrArg natDegree hc
      rw [natDegree_mul hu0 hc0, hud, hpdeg] at this; omega
    rw [natDegree_eq_zero] at hcd
    obtain ⟨c', rfl⟩ := hcd
    have hc' : c' ≠ 0 := by rintro rfl; simp at hc0
    rw [hc, mul_comm]
    exact (associated_unit_mul_left u (C c') (Polynomial.isUnit_C.mpr (Ne.isUnit hc'))).symm
  have hu12 : u1 = u2 :=
    eq_of_monic_of_associated hu1 hu2 ((hassoc hd1 hdp1).trans (hassoc hd2 hdp2).symm)
  subst hu12
  refine ⟨rfl, ?_⟩
  -- cancel `⟨u1, Y - v1⟩`
  have hm1 := mumford_mul_mumford_neg hk2 hw1 (exists_coprime_of_squarefree hsq hw1)
  have hspan : Ideal.span {algebraMap K[X] (CoordRing f) p} =
      Ideal.span {algebraMap K[X] (CoordRing f) u1} :=
    Ideal.span_singleton_eq_span_singleton.mpr ((hassoc hd1 hdp1).symm.map _)
  have hcanc : mumford f u1 (-v2) = mumford f u1 (-v1) := by
    apply mul_left_cancel₀ (mumford_ne_bot f hu1.ne_zero v1)
    rw [hα, hspan, hm1]
  have hY1 : Yc f - algebraMap K[X] (CoordRing f) (-v1) ∈ mumford f u1 (-v2) := by
    rw [hcanc]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hY2 : Yc f - algebraMap K[X] (CoordRing f) (-v2) ∈ mumford f u1 (-v2) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hdiff : algebraMap K[X] (CoordRing f) (v1 - v2) ∈ mumford f u1 (-v2) := by
    have := Ideal.sub_mem _ hY1 hY2
    convert this using 1
    rw [map_sub, map_neg, map_neg]; ring
  exact dvd_of_algebraMap_mem_mumford hd2' hdiff

end FurioLombardo.Discharge.R7
