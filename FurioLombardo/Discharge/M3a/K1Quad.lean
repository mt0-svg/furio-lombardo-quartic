import Mathlib
import FurioLombardo.Discharge.M3a.K1Res

/-!
# The quadratic algebra `K[X]/(u)` (lane K1, brick E5)

For a monic quadratic `u = X² + u₁ X + u₀` over a field `K` with `2 ≠ 0`: every element of
`B_u = K[X]/(u)` is `a + b θ`; its norm is `a² - a b u₁ + b² u₀`; and an element `t` with `t² = c`
and `N(t) = c` for some `c ≠ 0` lies in `K` (`exists_const_of_sq_eq_norm`; this replaces Cayley and
Hamilton in `B_u`).
-/

open Polynomial

namespace FurioLombardo.Discharge.M3a.K1

variable {K : Type*} [Field K]

/-- A monic quadratic is `X² + C u₁ X + C u₀`. -/
theorem monic_quadratic_eq {u : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2) :
    u = X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0) := by
  ext n
  have hcoeff2 : u.coeff 2 = 1 := by
    rw [← h2]
    exact hu.leadingCoeff
  have hzero (m : ℕ) (hm : 2 < m) : u.coeff m = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [h2]; exact hm)
  by_cases h0 : n = 0
  · subst h0; simp [coeff_add, coeff_X_pow, coeff_C]
  · by_cases h1 : n = 1
    · subst h1; simp [coeff_add, coeff_X_pow, coeff_C]
    · by_cases h2' : n = 2
      · subst h2'; simp [coeff_add, coeff_X_pow, hcoeff2]
      · have h_lt : 2 < n := by omega
        have hcoeff_rhs : coeff (X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0)) n = 0 := by
          rw [coeff_add, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
          simp [h0, h1, h2']
        rw [hzero n h_lt, hcoeff_rhs]

/-- Every element of `K[X]/(u)`, `u` monic quadratic, is the class of a polynomial `a + b X`. -/
theorem exists_linear_rep {u : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2) (x : AdjoinRoot u) :
    ∃ a b : K, x = AdjoinRoot.mk u (C a + C b * X) := by
  have hu_ne_one : u ≠ 1 := by
    intro h
    have : u.natDegree = 0 := by simp [h]
    linarith
  obtain ⟨p, hp⟩ := (AdjoinRoot.mk_surjective (g := u)) x
  have h_eq : AdjoinRoot.mk u p = AdjoinRoot.mk u (p %ₘ u) := by
    rw [AdjoinRoot.mk_eq_mk]
    have : p - p %ₘ u = u * (p /ₘ u) := by
      rw [Polynomial.modByMonic_eq_sub_mul_div p u, sub_sub_cancel]
    rw [this]
    exact ⟨p /ₘ u, rfl⟩
  rw [← hp, h_eq]
  have h_lt : (p %ₘ u).natDegree ≤ 1 := by
    have : (p %ₘ u).natDegree < u.natDegree := by
      apply Polynomial.natDegree_modByMonic_lt p hu hu_ne_one
    linarith
  obtain ⟨a, b, h⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one h_lt
  refine ⟨b, a, ?_⟩
  rw [h]
  congr 1
  ring

/-- A quadratic divides `a + b X` only if `a = b = 0`. -/
theorem linear_eq_zero_of_dvd {u : K[X]} (h2 : u.natDegree = 2) {a b : K}
    (h : u ∣ C a + C b * X) : a = 0 ∧ b = 0 := by
  set p := C a + C b * X with hp
  by_cases hp0 : p = 0
  · have ha : a = 0 := by
      have h0 := congrArg (fun q => coeff q 0) hp0
      simpa [p, coeff_add, coeff_C, coeff_C_mul_X] using h0
    have hb : b = 0 := by
      have h1 := congrArg (fun q => coeff q 1) hp0
      simpa [p, coeff_add, coeff_C, coeff_C_mul_X] using h1
    exact And.intro ha hb
  · have h_deg_le : u.natDegree ≤ p.natDegree :=
      Polynomial.natDegree_le_of_dvd h hp0
    have hp_natDegree_le_one : p.natDegree ≤ 1 := by
      dsimp [p]
      calc
        (C a + C b * X).natDegree ≤ max (C a).natDegree (C b * X).natDegree := natDegree_add_le _ _
        _ = max 0 (C b * X).natDegree := by rw [natDegree_C]
        _ ≤ max 0 1 := by
          refine max_le_max (le_refl 0) ?_
          have h_mul : (C b * X).natDegree ≤ (C b).natDegree + X.natDegree :=
            natDegree_mul_le (p := C b) (q := X)
          rw [natDegree_C, natDegree_X] at h_mul
          simpa using h_mul
        _ = 1 := by simp
    have h_contra : (2 : ℕ) ≤ 1 := by
      rw [← h2]
      exact le_trans h_deg_le hp_natDegree_le_one
    omega

/-- The norm of `a + b θ` in `K[X]/(u)`, `u = X² + u₁ X + u₀`. -/
theorem norm_mk_linear {u : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2) (a b : K) :
    Algebra.norm K (AdjoinRoot.mk u (C a + C b * X)) =
      a ^ 2 - a * b * u.coeff 1 + b ^ 2 * u.coeff 0 := by
  have hu2 := monic_quadratic_eq hu h2
  have hdeg : (C a + C b * X).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_C]; omega
    · exact (natDegree_C_mul_le b X).trans (by rw [natDegree_X])
  rw [norm_mk_eq_resultant_of_le hu hdeg, h2]
  by_cases hb : b = 0
  · subst hb
    rw [C_0, zero_mul, add_zero, resultant_C_right, ← h2, hu.coeff_natDegree, h2]
    ring
  · have hfac : C a + C b * X = C b * (X + C (a / b)) := by
      rw [mul_add, ← C_mul, mul_div_cancel₀ _ hb, add_comm]
    rw [hfac, resultant_C_mul_right, resultant_X_add_C_right _ _ _ (by rw [h2])]
    conv_lhs => rw [hu2]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
    field_simp
    ring

/-- The square of `a + b θ` in `K[X]/(u)`, `u = X² + u₁ X + u₀`. -/
theorem mk_linear_sq {u : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2) (a b : K) :
    AdjoinRoot.mk u ((C a + C b * X) ^ 2) =
      AdjoinRoot.mk u (C (a ^ 2 - b ^ 2 * u.coeff 0) + C (2 * a * b - b ^ 2 * u.coeff 1) * X) := by
  rw [AdjoinRoot.mk_eq_mk]
  refine ⟨C (b ^ 2), ?_⟩
  conv_rhs => rw [monic_quadratic_eq hu h2]
  simp only [C_sub, C_mul, C_pow, map_ofNat]
  ring

/-- The field identity behind `exists_const_of_sq_eq_norm`: if `a² - b² u₀ = c`,
`2 a b = b² u₁` and `a² - a b u₁ + b² u₀ = c` with `c ≠ 0` and `2 ≠ 0`, then `b = 0`. -/
theorem quad_coeff_eq_zero (h2K : (2 : K) ≠ 0) {a b c u₀ u₁ : K} (hc : c ≠ 0)
    (h1 : a ^ 2 - b ^ 2 * u₀ = c) (h2 : 2 * a * b = b ^ 2 * u₁)
    (h3 : a ^ 2 - a * b * u₁ + b ^ 2 * u₀ = c) : b = 0 := by
  by_contra! hb
  have h_sub : -a * b * u₁ + 2 * b ^ 2 * u₀ = 0 := by
    calc
      -a * b * u₁ + 2 * b ^ 2 * u₀ = (a ^ 2 - a * b * u₁ + b ^ 2 * u₀) - (a ^ 2 - b ^ 2 * u₀) := by ring
      _ = c - c := by rw [h3, h1]
      _ = 0 := by ring
  have h_factor : b * (-a * u₁ + 2 * b * u₀) = 0 := by
    calc
      b * (-a * u₁ + 2 * b * u₀) = b * (-a * u₁) + b * (2 * b * u₀) := by ring
      _ = -(a * b * u₁) + 2 * b ^ 2 * u₀ := by ring
      _ = -a * b * u₁ + 2 * b ^ 2 * u₀ := by ring
      _ = 0 := h_sub
  have h_zero : -a * u₁ + 2 * b * u₀ = 0 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero h_factor with hb' | hrest
    · exact absurd hb' hb
    · exact hrest
  have h_u1 : u₁ = 2 * a * b⁻¹ := by
    have h2' : 2 * a = b * u₁ := by
      apply mul_right_cancel₀ hb
      calc
        (2 * a) * b = 2 * a * b := by ring
        _ = b ^ 2 * u₁ := h2
        _ = (b * u₁) * b := by ring
    calc
      u₁ = (b * u₁) * b⁻¹ := by field_simp [hb]
      _ = (2 * a) * b⁻¹ := by rw [h2']
      _ = 2 * a * b⁻¹ := by ring
  have h_a_u1 : a * u₁ = 2 * b * u₀ := by
    calc
      a * u₁ = (a * u₁) + 0 := by ring
      _ = (a * u₁) + (-a * u₁ + 2 * b * u₀) := by rw [h_zero]
      _ = 2 * b * u₀ := by ring
  rw [h_u1] at h_a_u1
  field_simp [hb] at h_a_u1
  have h_a2_eq_b2_u0 : a ^ 2 = b ^ 2 * u₀ := h_a_u1
  have hc_eq_zero : c = 0 := by
    rw [h_a2_eq_b2_u0] at h1
    have htemp : b ^ 2 * u₀ - b ^ 2 * u₀ = (0 : K) := by ring
    rw [htemp] at h1
    exact h1.symm
  exact hc hc_eq_zero

/-- **Step 7.** In `K[X]/(u)`, `u` monic quadratic and `2 ≠ 0`, an element `t` with `t² = c` and
`N(t) = c` for some `c ≠ 0` is a constant. -/
theorem exists_const_of_sq_eq_norm (h2K : (2 : K) ≠ 0) {u : K[X]} (hu : u.Monic)
    (h2 : u.natDegree = 2) {c : K} (hc : c ≠ 0) {t : AdjoinRoot u}
    (hsq : t ^ 2 = algebraMap K (AdjoinRoot u) c) (hN : Algebra.norm K t = c) :
    ∃ s : K, t = algebraMap K (AdjoinRoot u) s := by
  obtain ⟨a, b, rfl⟩ := exists_linear_rep hu h2 t
  rw [norm_mk_linear hu h2] at hN
  rw [← map_pow, mk_linear_sq hu h2, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← sub_eq_zero, ← map_sub,
    AdjoinRoot.mk_eq_zero] at hsq
  have hsq' : u ∣ C (a ^ 2 - b ^ 2 * u.coeff 0 - c) + C (2 * a * b - b ^ 2 * u.coeff 1) * X := by
    convert hsq using 1
    simp only [C_sub]
    ring
  obtain ⟨h1, h2'⟩ := linear_eq_zero_of_dvd h2 hsq'
  have hb : b = 0 :=
    quad_coeff_eq_zero h2K hc (by linear_combination h1) (by linear_combination h2') hN
  exact ⟨a, by rw [hb, C_0, zero_mul, add_zero, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]⟩

end FurioLombardo.Discharge.M3a.K1
