import Mathlib

/-!
# Squares in quadratic algebras (lane SelmerSpan)

Generic facts for the independence certificates (Indep.lean), over a field `F`:

* `qa_not_isSquare_of_trace`: in `QuadraticAlgebra F a b`, `z` is not a square if `n² = N(z)` and
  neither `Tr z + 2n` nor `Tr z - 2n` is a square (if `z = w²` then `N(w) = ±n` and
  `(Tr w)² = Tr z + 2 N(w)`); `qa_not_isSquare_of_trace_dom`, the same over a commutative ring without
  zero divisors, and `qa0_mul_eq_zero` for `F(√δ)` (these two avoid the field instance of `F(√δ)`,
  whose unification with the ring instance over `K_v` is slow);
* `qa0_sq_mk`: a square root `⟨s/2, y/s⟩` of `⟨x, y⟩` in `F(√δ)` from `m² = x² - δ y²`,
  `s² = 2 (x + m)`; `qa0_scale_add`, `qa0_scale_sub`: `s² (T ± 2 ⟨s/2, y/s⟩)` without division;
* `qa0_tau_quad`, `qa0_tau_root`, `qa_root_quad`, `normForm_root_of`: values of quadratics at
  `⟨-h, 1⟩ ∈ F(√δ)` and at `⟨0, 1⟩ ∈ QuadraticAlgebra R (-P0) (-P1)`;
* `qa_isSquare_norm_mul`: the norm of `c w²` (`c` in the base) is a square;
* `isSquare_prod_sq_mul`: scaling the factors of a product by squares keeps it a square.
-/

namespace FurioLombardo.Discharge.SelmerSpan

theorem qa_not_isSquare_of_trace {F : Type*} [Field F] {a b : F} (z : QuadraticAlgebra F a b) (n : F)
    (hn : n ^ 2 = QuadraticAlgebra.norm z) (hp : ¬ IsSquare (QuadraticAlgebra.trace z + 2 * n))
    (hm : ¬ IsSquare (QuadraticAlgebra.trace z - 2 * n)) : ¬ IsSquare z := by
  intro hsq
  rcases hsq with ⟨w, hw⟩
  have hnorm : n ^ 2 = (QuadraticAlgebra.norm w) ^ 2 := by
    rw [hn, hw, map_mul, pow_two]
  have htrace_eq : (QuadraticAlgebra.trace w) ^ 2 =
      QuadraticAlgebra.trace (w * w) + 2 * QuadraticAlgebra.norm w := by
    simp [QuadraticAlgebra.trace_def, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul]
    ring
  have htrace : (QuadraticAlgebra.trace w) ^ 2 = QuadraticAlgebra.trace z + 2 * QuadraticAlgebra.norm w := by
    rw [hw, htrace_eq]
  have hfactor : (n - QuadraticAlgebra.norm w) * (n + QuadraticAlgebra.norm w) = 0 := by
    calc
      (n - QuadraticAlgebra.norm w) * (n + QuadraticAlgebra.norm w) = n ^ 2 - (QuadraticAlgebra.norm w) ^ 2 := by
        ring
      _ = 0 := by rw [hnorm, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hfactor with (hsub | hadd)
  · have hn_eq : n = QuadraticAlgebra.norm w := sub_eq_zero.mp hsub
    apply hp
    rw [hn_eq]
    have hsq' : QuadraticAlgebra.trace z + 2 * QuadraticAlgebra.norm w =
        (QuadraticAlgebra.trace w) * (QuadraticAlgebra.trace w) := by
      calc
        QuadraticAlgebra.trace z + 2 * QuadraticAlgebra.norm w = (QuadraticAlgebra.trace w) ^ 2 := by
          rw [← htrace]
        _ = (QuadraticAlgebra.trace w) * (QuadraticAlgebra.trace w) := by ring
    rw [hsq']
    exact ⟨QuadraticAlgebra.trace w, rfl⟩
  · have hn_eq : n = -QuadraticAlgebra.norm w := by
      apply eq_neg_of_add_eq_zero_left hadd
    apply hm
    rw [hn_eq]
    have hsq' : QuadraticAlgebra.trace z - 2 * (-QuadraticAlgebra.norm w) =
        (QuadraticAlgebra.trace w) * (QuadraticAlgebra.trace w) := by
      calc
        QuadraticAlgebra.trace z - 2 * (-QuadraticAlgebra.norm w) =
            QuadraticAlgebra.trace z + 2 * QuadraticAlgebra.norm w := by ring
        _ = (QuadraticAlgebra.trace w) ^ 2 := by rw [← htrace]
        _ = (QuadraticAlgebra.trace w) * (QuadraticAlgebra.trace w) := by ring
    rw [hsq']
    exact ⟨QuadraticAlgebra.trace w, rfl⟩

/-- `qa_not_isSquare_of_trace` over a commutative ring without zero divisors (given as `hdom`). -/
theorem qa_not_isSquare_of_trace_dom {F : Type*} [CommRing F] {a b : F}
    (hdom : ∀ u v : F, u * v = 0 → u = 0 ∨ v = 0) (z : QuadraticAlgebra F a b) (n : F)
    (hn : n ^ 2 = QuadraticAlgebra.norm z) (hp : ¬ IsSquare (QuadraticAlgebra.trace z + 2 * n))
    (hm : ¬ IsSquare (QuadraticAlgebra.trace z - 2 * n)) : ¬ IsSquare z := by
  rintro ⟨w, hw⟩
  have htr : (QuadraticAlgebra.trace w) ^ 2 = QuadraticAlgebra.trace z + 2 * QuadraticAlgebra.norm w := by
    rw [hw]
    simp [QuadraticAlgebra.trace_def, QuadraticAlgebra.norm_def, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul]
    ring
  have hfactor : (n - QuadraticAlgebra.norm w) * (n + QuadraticAlgebra.norm w) = 0 := by
    have hnorm : n ^ 2 = (QuadraticAlgebra.norm w) ^ 2 := by rw [hn, hw, map_mul, pow_two]
    linear_combination hnorm
  rcases hdom _ _ hfactor with hsub | hadd
  · apply hp
    rw [show n = QuadraticAlgebra.norm w by linear_combination hsub, ← htr]
    exact ⟨_, pow_two _⟩
  · apply hm
    rw [show n = -QuadraticAlgebra.norm w by linear_combination hadd,
      show QuadraticAlgebra.trace z - 2 * -QuadraticAlgebra.norm w =
        QuadraticAlgebra.trace z + 2 * QuadraticAlgebra.norm w by ring, ← htr]
    exact ⟨_, pow_two _⟩

/-- `F(√δ)` has no zero divisors when `δ` is not a square. -/
theorem qa0_mul_eq_zero {F : Type*} [Field F] {δ : F} (hδ : ¬ IsSquare δ) {u v : QuadraticAlgebra F δ 0}
    (h : u * v = 0) : u = 0 ∨ v = 0 := by
  have : Fact (¬ IsSquare δ) := ⟨hδ⟩
  exact mul_eq_zero.mp h

theorem qa0_sq_mk {F : Type*} [Field F] {δ x y m s : F} (h2 : (2 : F) ≠ 0) (hm : m ^ 2 = x ^ 2 - δ * y ^ 2)
    (hs : s ^ 2 = 2 * (x + m)) (hs0 : s ≠ 0) :
    (⟨s / 2, y / s⟩ : QuadraticAlgebra F δ 0) ^ 2 = ⟨x, y⟩ := by
  apply QuadraticAlgebra.ext
  · simp [pow_two]
    field_simp [hs0, h2]
    have hs4 : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [hs4, hs]
    ring_nf
    rw [hm]
    ring_nf
  · simp [pow_two]
    field_simp [hs0]
    ring

theorem qa0_scale_add {F : Type*} [Field F] {δ x y m s : F} (h2 : (2 : F) ≠ 0) (hs : s ^ 2 = 2 * (x + m))
    (hs0 : s ≠ 0) (T : QuadraticAlgebra F δ 0) :
    algebraMap F (QuadraticAlgebra F δ 0) (s ^ 2) * (T + 2 * ⟨s / 2, y / s⟩) =
      algebraMap F _ (2 * (x + m)) * T + algebraMap F _ (2 * s) * ⟨x + m, y⟩ := by
  open QuadraticAlgebra in
  ext <;> simp [algebraMap_eq, re_mul, im_mul, re_add, im_add, hs]
  · field_simp [hs0]
  · field_simp [hs0]
    ring_nf
    rw [hs]
    ring

theorem qa0_scale_sub {F : Type*} [Field F] {δ x y m s : F} (h2 : (2 : F) ≠ 0) (hs : s ^ 2 = 2 * (x + m))
    (hs0 : s ≠ 0) (T : QuadraticAlgebra F δ 0) :
    algebraMap F (QuadraticAlgebra F δ 0) (s ^ 2) * (T - 2 * ⟨s / 2, y / s⟩) =
      algebraMap F _ (2 * (x + m)) * T - algebraMap F _ (2 * s) * ⟨x + m, y⟩ := by
  have hsq : algebraMap F (QuadraticAlgebra F δ 0) (s ^ 2) = algebraMap F _ (2 * (x + m)) := by
    rw [hs]
  rw [hsq]
  ext
  · simp [QuadraticAlgebra.algebraMap_eq, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    field_simp [h2]
  · simp [QuadraticAlgebra.algebraMap_eq, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    field_simp [hs0]
    ring_nf
    rw [hs]
    ring

theorem qa0_tau_quad {F : Type*} [Field F] (δ h p r : F) :
    (⟨-h, 1⟩ : QuadraticAlgebra F δ 0) ^ 2 + algebraMap F (QuadraticAlgebra F δ 0) p * ⟨-h, 1⟩ +
        algebraMap F _ r = ⟨h ^ 2 + δ - p * h + r, p - 2 * h⟩ := by
  ext <;> simp [pow_two, QuadraticAlgebra.algebraMap_eq] <;> ring

theorem qa0_tau_root {F : Type*} [Field F] {δ h q0 : F} (hδ : δ = h ^ 2 - q0) :
    (⟨-h, 1⟩ : QuadraticAlgebra F δ 0) ^ 2 + algebraMap F (QuadraticAlgebra F δ 0) (2 * h) * ⟨-h, 1⟩ +
        algebraMap F _ q0 = 0 := by
  ext
  · simp [pow_two, QuadraticAlgebra.algebraMap_eq]
    linear_combination hδ
  · simp [pow_two, QuadraticAlgebra.algebraMap_eq]
    ring

theorem qa_root_quad {R : Type*} [CommRing R] (P0 P1 p r : R) :
    (⟨0, 1⟩ : QuadraticAlgebra R (-P0) (-P1)) ^ 2 +
        algebraMap R (QuadraticAlgebra R (-P0) (-P1)) p * ⟨0, 1⟩ + algebraMap R _ r =
      ⟨r - P0, p - P1⟩ := by
  ext <;> simp [pow_two, QuadraticAlgebra.algebraMap_eq] <;> ring

/-- `x0` is a root of `A² - δ B²` when `x0² + P1 x0 + P0 = 0` with `P_i = a_i + B_i w`, `w² = δ`. -/
theorem normForm_root_of {F M : Type*} [Field F] [CommRing M] (ι : F →+* M) {δ a0 a1 B0 B1 : F}
    {w x0 : M} (hw : w * w = ι δ) (hx : x0 * x0 = -(ι a0 + ι B0 * w) - (ι a1 + ι B1 * w) * x0) :
    (x0 ^ 2 + ι a1 * x0 + ι a0) ^ 2 - ι δ * (ι B1 * x0 + ι B0) ^ 2 = 0 := by
  have key : x0 ^ 2 + ι a1 * x0 + ι a0 = -(w * (ι B1 * x0 + ι B0)) := by
    rw [pow_two, hx]; ring
  rw [key]
  linear_combination (ι B1 * x0 + ι B0) ^ 2 * hw

theorem qa_isSquare_norm_mul {R : Type*} [CommRing R] {a b : R} (c : R) (w : QuadraticAlgebra R a b) :
    IsSquare (QuadraticAlgebra.norm (algebraMap R (QuadraticAlgebra R a b) c * w ^ 2)) := by
  have h : QuadraticAlgebra.norm (algebraMap R (QuadraticAlgebra R a b) c * w ^ 2) =
      (c * QuadraticAlgebra.norm w) ^ 2 := by
    rw [map_mul, map_pow, QuadraticAlgebra.norm_algebraMap]; ring
  rw [h]
  exact ⟨c * QuadraticAlgebra.norm w, pow_two _⟩

/-- Scaling the factors of a product by squares keeps it a square. -/
theorem isSquare_prod_sq_mul {R : Type*} [CommMonoid R] {ι : Type*} (s : Finset ι) (x c : ι → R)
    (e : ι → ℕ) (h : IsSquare (∏ i ∈ s, x i ^ e i)) : IsSquare (∏ i ∈ s, (c i ^ 2 * x i) ^ e i) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨(∏ i ∈ s, c i ^ e i) * r, ?_⟩
  have e1 : ∏ i ∈ s, (c i ^ 2 * x i) ^ e i = (∏ i ∈ s, c i ^ e i) ^ 2 * ∏ i ∈ s, x i ^ e i := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (e i)]
  rw [e1, hr, sq]; ac_rfl

end FurioLombardo.Discharge.SelmerSpan
