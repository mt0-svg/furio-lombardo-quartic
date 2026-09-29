import Mathlib
import FurioLombardo.M3a.Basic
import FurioLombardo.M3a.ClassGroupLift

/-!
# The class group of `Y² = f`, its parity and the Jacobian (lane M3a)

For `f` with `GoodSextic f` (squarefree sextic, leading coefficient not a square, `2 ≠ 0`):

* `Pic f = ClassGroup (CoordRing f)`, that is `Pic(F)/⟨∞⟩` for the degree 2 place `∞` above
  `X = ∞`;
* `normDeg f I`: the degree of the relative norm `N(I) ⊆ K[X]`; it is additive, and even on
  principal ideals (norms `p² - q² f` of nonzero elements have even degree);
* `parity f : Pic f →* Multiplicative (ZMod 2)` and `Jac f`, its kernel: the classes of even degree,
  which is `Pic⁰(F)(K) = A(K)` (every even degree class is `D + m ∞` with `D` of degree 0, and
  `Pic⁰ ∩ ℤ∞ = 0` since `∞` has degree 2);
* Mumford ideals `⟨u, Y - v⟩` as nonzero ideals (`mumford0`), their relative norm `(u)`
  (`relNorm_mumford`), their parity `deg u` (`parity_mumford`), the class of `⟨u, Y + v⟩` as the
  inverse (`mk0_mumford_neg`), and `mumfordJac` for `deg u` even;
* `mumford_zero_not_isPrincipal`: for a monic quadratic factor `q` of `f`, `⟨q, Y⟩` is not
  principal.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The ideal class group of `CoordRing f`, that is `Pic(F)/⟨∞⟩`. -/
abbrev Pic (f : K[X]) [GoodSextic f] : Type _ := ClassGroup (CoordRing f)

/-- The degree of the relative norm `N(I) ⊆ K[X]` of an ideal `I` of `CoordRing f`. -/
noncomputable def normDeg (f : K[X]) [GoodSextic f] (I : Ideal (CoordRing f)) : ℕ :=
  idealDeg (Ideal.relNorm K[X] I)

end FurioLombardo.M3a.Genus2

theorem FurioLombardo.M3a.Genus2.normDeg_top {K : Type*} [Field K] (f : K[X]) [GoodSextic f] : normDeg f ⊤ = 0 := by
  unfold normDeg idealDeg
  rw [Ideal.relNorm_top, ← Ideal.span_singleton_one, natDegree_generator_span_singleton, natDegree_one]

theorem FurioLombardo.M3a.Genus2.normDeg_mul {K : Type*} [Field K] (f : K[X]) [GoodSextic f] {I J : Ideal (CoordRing f)} (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) : normDeg f (I * J) = normDeg f I + normDeg f J := by
  dsimp [normDeg, idealDeg]
  rw [map_mul (Ideal.relNorm K[X]) I J]
  have hrelI : Ideal.relNorm K[X] I ≠ ⊥ :=
    mt (Ideal.relNorm_eq_bot_iff (R := K[X]) (S := CoordRing f)).mp hI
  have hrelJ : Ideal.relNorm K[X] J ≠ ⊥ :=
    mt (Ideal.relNorm_eq_bot_iff (R := K[X]) (S := CoordRing f)).mp hJ
  rw [FurioLombardo.M3a.Genus2.natDegree_generator_mul hrelI hrelJ]

theorem FurioLombardo.M3a.Genus2.relNorm_span_singleton {K : Type*} [Field K] (f : K[X]) [GoodSextic f] (x : CoordRing f) :
    Ideal.relNorm K[X] (Ideal.span {x}) = Ideal.span {Algebra.norm K[X] x} := by
  simp [Algebra.intNorm_eq_norm K[X] (CoordRing f), Ideal.relNorm_singleton K[X] x]

theorem FurioLombardo.M3a.Genus2.even_normDeg_of_isPrincipal {K : Type*} [Field K] (f : K[X]) [GoodSextic f] {I : Ideal (CoordRing f)}
    (hI : I ≠ ⊥) (h : I.IsPrincipal) : Even (normDeg f I) := by
  set x := Submodule.IsPrincipal.generator I with hx_def
  have hx_ne_zero : x ≠ 0 := by
    intro hx0
    apply hI
    have hgen0 : Submodule.IsPrincipal.generator I = 0 := by
      rw [← hx_def, hx0]
    calc
      I = CoordRing f ∙ Submodule.IsPrincipal.generator I := by
        rw [Submodule.IsPrincipal.span_singleton_generator I]
      _ = CoordRing f ∙ (0 : CoordRing f) := by rw [hgen0]
      _ = ⊥ := by simp
  have hI_eq : I = Ideal.span {x} := by
    rw [← Submodule.IsPrincipal.span_singleton_generator I, hx_def]
  have h_relNorm : Ideal.relNorm K[X] I = Ideal.span {Algebra.intNorm K[X] (CoordRing f) x} := by
    rw [hI_eq, Ideal.relNorm_singleton]
  have h_intNorm_eq_norm : Algebra.intNorm K[X] (CoordRing f) x = Algebra.norm K[X] x := by
    rw [Algebra.intNorm_eq_norm K[X] (CoordRing f)]
  have h_normDeg : normDeg f I = (Algebra.norm K[X] x).natDegree := by
    rw [normDeg, idealDeg, h_relNorm, h_intNorm_eq_norm]
    exact FurioLombardo.M3a.Genus2.natDegree_generator_span_singleton (Algebra.norm K[X] x)
  rw [h_normDeg]
  exact (FurioLombardo.M3a.Genus2.norm_ne_zero_and_even hx_ne_zero).2

theorem FurioLombardo.M3a.Genus2.mumford_ne_bot {K : Type*} [Field K] (f : K[X]) {u : K[X]} (hu : u ≠ 0) (v : K[X]) : mumford f u v ≠ ⊥ := by
  have hmem : algebraMap K[X] (CoordRing f) u ∈ mumford f u v := by
    rw [mumford]
    apply Ideal.subset_span
    simp
  have hne : algebraMap K[X] (CoordRing f) u ≠ 0 := by
    simpa using (algebraMap_injective f).ne hu
  intro h
  apply hne
  rw [h] at hmem
  simpa using hmem

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The parity of the norm degree, on nonzero ideals. -/
noncomputable def parity0 (f : K[X]) [GoodSextic f] :
    (Ideal (CoordRing f))⁰ →* Multiplicative (ZMod 2) where
  toFun I := Multiplicative.ofAdd ((normDeg f I : ℕ) : ZMod 2)
  map_one' := by
    change Multiplicative.ofAdd ((normDeg f ((1 : (Ideal (CoordRing f))⁰) : Ideal (CoordRing f)) : ℕ) : ZMod 2) = 1
    rw [OneMemClass.coe_one, Ideal.one_eq_top, normDeg_top]; rfl
  map_mul' I J := by
    have hI : (I : Ideal (CoordRing f)) ≠ ⊥ := nonZeroDivisors.ne_zero I.2
    have hJ : (J : Ideal (CoordRing f)) ≠ ⊥ := nonZeroDivisors.ne_zero J.2
    change Multiplicative.ofAdd ((normDeg f ((I : Ideal (CoordRing f)) * (J : Ideal (CoordRing f))) : ℕ) : ZMod 2) = _
    rw [normDeg_mul f hI hJ, Nat.cast_add, ofAdd_add]

theorem parity0_of_isPrincipal (f : K[X]) [GoodSextic f] (I : (Ideal (CoordRing f))⁰)
    (h : (I : Ideal (CoordRing f)).IsPrincipal) : parity0 f I = 1 := by
  obtain ⟨m, hm⟩ := even_normDeg_of_isPrincipal f (nonZeroDivisors.ne_zero I.2) h
  change Multiplicative.ofAdd ((normDeg f I : ℕ) : ZMod 2) = 1
  rw [hm, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  rfl

/-- The parity of the degree, on the class group. -/
noncomputable def parity (f : K[X]) [GoodSextic f] : Pic f →* Multiplicative (ZMod 2) :=
  Classical.choose (exists_classGroup_lift (parity0 f) (parity0_of_isPrincipal f))

theorem parity_mk0 (f : K[X]) [GoodSextic f] (I : (Ideal (CoordRing f))⁰) :
    parity f (ClassGroup.mk0 I) = parity0 f I :=
  Classical.choose_spec (exists_classGroup_lift (parity0 f) (parity0_of_isPrincipal f)) I

/-- The Jacobian `A(K) = Pic⁰(F)(K)`: the classes of even degree. -/
noncomputable def Jac (f : K[X]) [GoodSextic f] : Subgroup (Pic f) := (parity f).ker

/-- The Mumford ideal as a nonzero ideal. -/
noncomputable def mumford0 (f : K[X]) [GoodSextic f] {u : K[X]} (hu : u ≠ 0) (v : K[X]) :
    (Ideal (CoordRing f))⁰ :=
  ⟨mumford f u v, mem_nonZeroDivisors_of_ne_zero (mumford_ne_bot f hu v)⟩

end FurioLombardo.M3a.Genus2

theorem FurioLombardo.M3a.Genus2.mumford_data_of_dvd {K : Type*} [Field K] (f : K[X]) [GoodSextic f] {q : K[X]} (hqf : q ∣ f) :
    ∃ w : K[X], (0 : K[X]) ^ 2 - f = q * w ∧ ∃ a b c : K[X], a * q + b * 0 + c * w = 1 := by
  rcases hqf with ⟨r, hr⟩
  refine ⟨-r, ?_, ?_⟩
  · calc
      (0 : K[X]) ^ 2 - f = -f := by simp
      _ = -(q * r) := by rw [hr]
      _ = q * (-r) := by ring
  · have hsqfree : Squarefree f := GoodSextic.squarefree
    have hsqfree_mul : Squarefree (q * r) := by rwa [hr] at hsqfree
    have hrel : IsRelPrime q r := IsRelPrime.of_squarefree_mul hsqfree_mul
    have hcop : IsCoprime q r := hrel.isCoprime
    rcases hcop with ⟨a, c, h⟩
    refine ⟨a, 0, -c, ?_⟩
    calc
      a * q + (0 : K[X]) * 0 + (-c) * (-r) = a * q + c * r := by ring
      _ = 1 := h


theorem FurioLombardo.M3a.Genus2.relNorm_mumford {K : Type*} [Field K] (f : K[X]) [GoodSextic f] {u v w : K[X]} (hu : u.Monic)
    (hw : v ^ 2 - f = u * w) (hc : ∃ a b c : K[X], a * u + b * v + c * w = 1) :
    Ideal.relNorm K[X] (mumford f u v) = Ideal.span {u} := by
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have hprod := mumford_mul_mumford_neg (f := f) h2 hw hc
  have hconj : Ideal.relNorm K[X] (mumford f u (-v)) = Ideal.relNorm K[X] (mumford f u v) := by
    rw [← map_conj_mumford f u v]
    exact Ideal.relNorm_map_algEquiv (conj f) _
  have hrank : Module.finrank K[X] (CoordRing f) = 2 := by
    rw [Module.finrank_eq_card_basis (basis f), Fintype.card_fin]
  apply eq_span_of_mul_self_eq_span_mul_self
  calc Ideal.relNorm K[X] (mumford f u v) * Ideal.relNorm K[X] (mumford f u v)
      = Ideal.relNorm K[X] (mumford f u v) * Ideal.relNorm K[X] (mumford f u (-v)) := by
        rw [hconj]
    _ = Ideal.relNorm K[X] (mumford f u v * mumford f u (-v)) := (map_mul _ _ _).symm
    _ = Ideal.span {u * u} := by
        rw [hprod, Ideal.relNorm_singleton, Algebra.intNorm_eq_norm, Algebra.norm_algebraMap,
          hrank, sq]

theorem FurioLombardo.M3a.Genus2.parity_mumford {K : Type*} [Field K] (f : K[X]) [GoodSextic f] {u v w : K[X]} (hu : u.Monic)
    (hw : v ^ 2 - f = u * w) (hc : ∃ a b c : K[X], a * u + b * v + c * w = 1) :
    parity f (ClassGroup.mk0 (mumford0 f hu.ne_zero v)) =
      Multiplicative.ofAdd (u.natDegree : ZMod 2) := by
  rw [parity_mk0 f (mumford0 f hu.ne_zero v)]
  have hnorm : normDeg f (mumford0 f hu.ne_zero v) = u.natDegree := by
    dsimp [normDeg, idealDeg]
    have hcoeff : (mumford0 f hu.ne_zero v : Ideal (CoordRing f)) = mumford f u v := rfl
    rw [hcoeff]
    rw [relNorm_mumford f hu hw hc]
    rw [natDegree_generator_span_singleton u]
  dsimp [parity0]
  rw [hnorm]

theorem FurioLombardo.M3a.Genus2.mk0_mumford_neg {K : Type*} [Field K] (f : K[X]) [GoodSextic f] {u v w : K[X]} (hu : u.Monic)
    (hw : v ^ 2 - f = u * w) (hc : ∃ a b c : K[X], a * u + b * v + c * w = 1) :
    ClassGroup.mk0 (mumford0 f hu.ne_zero (-v)) = (ClassGroup.mk0 (mumford0 f hu.ne_zero v))⁻¹ := by
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have h_coprime_neg : ∃ a b c : K[X], a * u + b * (-v) + c * w = 1 := by
    rcases hc with ⟨a, b, c, h⟩
    refine ⟨a, -b, c, ?_⟩
    rw [neg_mul_neg, h]
  have h_mul := mumford_mul_mumford_neg h2 hw hc
  have hu_map_ne_zero : algebraMap K[X] (CoordRing f) u ≠ 0 := by
    intro hzero
    apply hu.ne_zero
    apply algebraMap_injective f
    rw [hzero, map_zero]
  refine ((ClassGroup.mk0_eq_mk0_inv_iff).mpr
    ⟨algebraMap K[X] (CoordRing f) u, hu_map_ne_zero, ?_⟩)
  simpa [Submonoid.coe_mul, mul_comm, mumford0] using h_mul

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The class of the Mumford ideal `⟨u, Y - v⟩` with `deg u` even, as a point of `A(K)`. -/
noncomputable def mumfordJac (f : K[X]) [GoodSextic f] {u v w : K[X]} (hu : u.Monic)
    (hdeg : Even u.natDegree) (hw : v ^ 2 - f = u * w)
    (hc : ∃ a b c : K[X], a * u + b * v + c * w = 1) : Jac f :=
  ⟨ClassGroup.mk0 (mumford0 f hu.ne_zero v), by
    change parity f _ = 1
    rw [parity_mumford f hu hw hc]
    obtain ⟨m, hm⟩ := hdeg
    rw [hm, Nat.cast_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
    rfl⟩

end FurioLombardo.M3a.Genus2


theorem FurioLombardo.M3a.Genus2.six_le_natDegree_sq_sub_sq_mul {K : Type*} [Field K]
    {f p r : K[X]} (hlc : ¬ IsSquare f.leadingCoeff) (hf : f.natDegree = 6) (hr : r ≠ 0) :
    6 ≤ (p ^ 2 - r ^ 2 * f).natDegree := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hrf : r ^ 2 * f ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr) hf0
  have hD : (r ^ 2 * f).natDegree = 2 * r.natDegree + 6 := by
    rw [natDegree_mul (pow_ne_zero 2 hr) hf0, natDegree_pow, hf]
  rcases lt_or_ge (r ^ 2 * f).natDegree (p ^ 2).natDegree with h | h
  · rw [natDegree_sub_eq_left_of_natDegree_lt h]; omega
  · have hcoeff : (p ^ 2 - r ^ 2 * f).coeff (r ^ 2 * f).natDegree ≠ 0 := by
      rw [coeff_sub]
      rcases h.lt_or_eq with h' | h'
      · rw [coeff_eq_zero_of_natDegree_lt h', zero_sub, neg_ne_zero]
        exact leadingCoeff_ne_zero.mpr hrf
      · by_cases hp : p = 0
        · subst hp
          rw [zero_pow two_ne_zero, coeff_zero, zero_sub, neg_ne_zero]
          exact leadingCoeff_ne_zero.mpr hrf
        have hr' : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hr
        nth_rewrite 1 [← h']
        rw [← leadingCoeff, ← leadingCoeff, leadingCoeff_pow, leadingCoeff_mul, leadingCoeff_pow,
          sub_ne_zero]
        intro heq
        apply hlc
        refine ⟨p.leadingCoeff / r.leadingCoeff, ?_⟩
        rw [div_mul_div_comm, ← sq, ← sq, heq, mul_div_cancel_left₀ _ (pow_ne_zero 2 hr')]
    have := le_natDegree_of_ne_zero hcoeff
    omega

theorem FurioLombardo.M3a.Genus2.mumford_zero_not_isPrincipal {K : Type*} [Field K] (f : K[X]) [GoodSextic f] {q : K[X]} (hq : q.Monic)
    (hqf : q ∣ f) (hdeg : q.natDegree = 2) : ¬ (mumford f q 0).IsPrincipal := by
  rintro ⟨g, hg⟩
  obtain ⟨w, hw, hc⟩ := mumford_data_of_dvd f hqf
  have hN := relNorm_mumford f hq hw hc
  rw [hg] at hN
  change Ideal.relNorm K[X] (Ideal.span {g}) = _ at hN
  rw [relNorm_span_singleton, Ideal.span_singleton_eq_span_singleton] at hN
  obtain ⟨p, r, rfl⟩ := exists_smul_basis_eq f g
  rw [norm_smul_basis] at hN
  have hdN : (p ^ 2 - r ^ 2 * f).natDegree = 2 := by
    exact (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hN)).trans hdeg
  by_cases hr : r = 0
  · subst hr
    rw [zero_pow two_ne_zero, zero_mul, sub_zero] at hN hdN
    have hp1 : p.natDegree = 1 := by rw [natDegree_pow] at hdN; omega
    have hsq : Squarefree q := Squarefree.squarefree_of_dvd hqf GoodSextic.squarefree
    have hu : IsUnit p := hsq p (by rw [← sq]; exact hN.dvd)
    rw [natDegree_eq_zero_of_isUnit hu] at hp1
    exact absurd hp1 (by norm_num)
  · have := six_le_natDegree_sq_sub_sq_mul (p := p) GoodSextic.not_isSquare_leadingCoeff
      (GoodSextic.natDegree_eq (f := f)) hr
    omega
