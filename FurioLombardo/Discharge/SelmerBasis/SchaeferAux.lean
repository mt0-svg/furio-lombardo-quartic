import Mathlib

/-!
# Leaves of Schaefer's lemma

Valuation facts on polynomials over a valued field `M` (content through the valuation, no
uniformizer), the lifts to the valuation ring and the residue field, and the two polynomial
identities used by the proof: identity B (`identityB`) and the nonvanishing of the reduced
resultant when the reduction of `U` is linear at the reduced root (`resultant_ne_zero_of_sq`).
-/

open Polynomial

namespace FurioLombardo.Discharge.SelmerBasis.Schaefer

/-! ### Integral and primitive polynomials over a valued field -/

theorem integral_mul {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P Q : M[X]} (hP : ∀ i, v (P.coeff i) ≤ 1)
    (hQ : ∀ i, v (Q.coeff i) ≤ 1) : ∀ i, v ((P * Q).coeff i) ≤ 1 := by
  intro i
  rw [Polynomial.coeff_mul]
  refine Valuation.map_sum_le v (fun x hx => ?_)
  rw [Valuation.map_mul]
  have hx1 : v (P.coeff x.1) ≤ 1 := hP x.1
  have hx2 : v (Q.coeff x.2) ≤ 1 := hQ x.2
  exact mul_le_one' hx1 hx2

theorem primitive_mul {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P Q : M[X]} (hP : ∀ i, v (P.coeff i) ≤ 1)
    (hQ : ∀ i, v (Q.coeff i) ≤ 1) (hP1 : ∃ i, v (P.coeff i) = 1) (hQ1 : ∃ i, v (Q.coeff i) = 1) :
    ∃ i, v ((P * Q).coeff i) = 1 := by
  classical
  set i0 := Nat.find hP1 with hi0
  set j0 := Nat.find hQ1 with hj0
  use i0 + j0
  rw [coeff_mul]
  set s := Finset.HasAntidiagonal.antidiagonal (A := ℕ) (i0 + j0) with hs
  set a := (i0, j0) with ha
  have ha_mem : a ∈ s := by
    rw [hs, ha]
    simp
  have hsum := Finset.add_sum_erase s (λ x => P.coeff x.1 * Q.coeff x.2) ha_mem
  rw [← hsum]
  have hval_ij : v (P.coeff i0 * Q.coeff j0) = 1 := by
    rw [Valuation.map_mul]
    have hPi0 : v (P.coeff i0) = 1 := Nat.find_spec hP1
    have hQj0 : v (Q.coeff j0) = 1 := Nat.find_spec hQ1
    rw [hPi0, hQj0]
    simp
  have h_rest_lt_one : v (∑ x ∈ s.erase a, (P.coeff x.1 * Q.coeff x.2)) < 1 := by
    have h_one_ne_zero : (1 : Γ₀) ≠ 0 := one_ne_zero
    refine Valuation.map_sum_lt v h_one_ne_zero ?_
    intro x hx
    have hx_mem : x ∈ s := Finset.mem_of_mem_erase hx
    have hx_ne_a : x ≠ a := Finset.ne_of_mem_erase hx
    rw [hs] at hx_mem
    simp at hx_mem
    have h_cases : x.1 < i0 ∨ x.2 < j0 := by
      by_cases hx1_lt_i0 : x.1 < i0
      · exact Or.inl hx1_lt_i0
      · have hx1_ge_i0 : i0 ≤ x.1 := Nat.le_of_not_gt hx1_lt_i0
        by_cases hx2_lt_j0 : x.2 < j0
        · exact Or.inr hx2_lt_j0
        · have hx2_ge_j0 : j0 ≤ x.2 := Nat.le_of_not_gt hx2_lt_j0
          have hsum_le : i0 + j0 ≤ x.1 + x.2 := Nat.add_le_add hx1_ge_i0 hx2_ge_j0
          have hsum_eq : x.1 + x.2 = i0 + j0 := hx_mem
          have hi0_eq_x1 : i0 = x.1 := by
            by_contra! hne
            have hx1_gt_i0 : i0 < x.1 := Nat.lt_of_le_of_ne hx1_ge_i0 hne
            have hsum_lt : i0 + j0 < x.1 + x.2 := by
              calc
                i0 + j0 < x.1 + j0 := Nat.add_lt_add_right hx1_gt_i0 j0
                _ ≤ x.1 + x.2 := Nat.add_le_add_left hx2_ge_j0 x.1
            omega
          have hj0_eq_x2 : j0 = x.2 := by
            by_contra! hne
            have hx2_gt_j0 : j0 < x.2 := Nat.lt_of_le_of_ne hx2_ge_j0 hne
            have hsum_lt : i0 + j0 < x.1 + x.2 := by
              calc
                i0 + j0 < i0 + x.2 := Nat.add_lt_add_left hx2_gt_j0 i0
                _ ≤ x.1 + x.2 := Nat.add_le_add_right hx1_ge_i0 x.2
            omega
          have hpair : x = a := by
            rw [ha, hi0_eq_x1, hj0_eq_x2]
          exact absurd hpair hx_ne_a
    rcases h_cases with (hx1_lt_i0 | hx2_lt_j0)
    · have h_not_one : v (P.coeff x.1) ≠ 1 := by
        intro heq
        have hle := Nat.find_min' hP1 heq
        omega
      have h_lt_one : v (P.coeff x.1) < 1 :=
        lt_of_le_of_ne (hP x.1) h_not_one
      rw [Valuation.map_mul]
      calc
        v (P.coeff x.1) * v (Q.coeff x.2) ≤ v (P.coeff x.1) * 1 :=
          mul_le_mul_of_nonneg_left (hQ x.2) (zero_le (a := v (P.coeff x.1)))
        _ = v (P.coeff x.1) := by simp
        _ < 1 := h_lt_one
    · have h_not_one : v (Q.coeff x.2) ≠ 1 := by
        intro heq
        have hle := Nat.find_min' hQ1 heq
        omega
      have h_lt_one : v (Q.coeff x.2) < 1 :=
        lt_of_le_of_ne (hQ x.2) h_not_one
      rw [Valuation.map_mul]
      calc
        v (P.coeff x.1) * v (Q.coeff x.2) ≤ 1 * v (Q.coeff x.2) :=
          mul_le_mul_of_nonneg_right (hP x.1) (zero_le (a := v (Q.coeff x.2)))
        _ = v (Q.coeff x.2) := by simp
        _ < 1 := h_lt_one
  have h_lt : v (∑ x ∈ s.erase a, (P.coeff x.1 * Q.coeff x.2)) < v (P.coeff a.1 * Q.coeff a.2) := by
    rw [ha]
    simpa [ha, hval_ij] using h_rest_lt_one
  have h_add := Valuation.map_add_eq_of_lt_left v h_lt
  -- h_add : v (P.coeff a.1 * Q.coeff a.2 + ∑ x ∈ s.erase a, ...) = v (P.coeff a.1 * Q.coeff a.2)
  simpa [ha, hval_ij] using h_add

theorem exists_primitive {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P : M[X]} (hP : P ≠ 0) :
    ∃ a : M, a ≠ 0 ∧ ∃ P' : M[X], P = C a * P' ∧ (∀ i, v (P'.coeff i) ≤ 1) ∧
      ∃ i, v (P'.coeff i) = 1 := by
  have h_support_nonempty : P.support.Nonempty := by
    rwa [Polynomial.support_nonempty]
  obtain ⟨i0, hi0_mem, hi0_max⟩ :=
    Finset.exists_max_image P.support (fun i => v (P.coeff i)) h_support_nonempty
  have ha_ne_zero : P.coeff i0 ≠ 0 := by
    rwa [Polynomial.mem_support_iff] at hi0_mem
  set a := P.coeff i0 with ha_def
  have ha_val_ne_zero : v a ≠ 0 := by
    rwa [Valuation.ne_zero_iff]
  set P' := C (a⁻¹) * P with hP'_def
  have h_eq : P = C a * P' := by
    dsimp [P']
    calc
      P = C 1 * P := by simp
      _ = C (a * a⁻¹) * P := by
        rw [mul_inv_cancel₀ ha_ne_zero, C_1]
      _ = C a * C (a⁻¹) * P := by rw [C_mul]
      _ = C a * (C (a⁻¹) * P) := by ring
  have h_coeff_val_le_one : ∀ i, v (P'.coeff i) ≤ 1 := by
    intro i
    dsimp [P']
    rw [Polynomial.coeff_C_mul]
    by_cases hi : i ∈ P.support
    · have h_val_le : v (P.coeff i) ≤ v a := hi0_max i hi
      calc
        v (a⁻¹ * P.coeff i) = v a⁻¹ * v (P.coeff i) := Valuation.map_mul _ _ _
        _ = (v a)⁻¹ * v (P.coeff i) := by rw [Valuation.map_inv]
        _ ≤ (v a)⁻¹ * v a := by
          -- need: mul_le_mul_left (v a)⁻¹ h_val_le
          -- but (v a)⁻¹ might be zero? No, v a ≠ 0 so (v a)⁻¹ ≠ 0
          -- In LinearOrderedCommGroupWithZero, we have mul_le_mul_of_nonneg_left
          -- Actually we need positivity. Let's use: (v a)⁻¹ > 0
          have hpos : 0 ≤ (v a)⁻¹ := by
            apply zero_le
          exact mul_le_mul_of_nonneg_left h_val_le hpos
        _ = 1 := by
          rw [inv_mul_cancel₀ ha_val_ne_zero]
    · have h_coeff_zero : P.coeff i = 0 := by
        rwa [Polynomial.mem_support_iff, not_ne_iff] at hi
      simp [h_coeff_zero, Valuation.map_zero]
  have h_coeff_val_eq_one : ∃ i, v (P'.coeff i) = 1 := by
    refine ⟨i0, ?_⟩
    dsimp [P']
    rw [Polynomial.coeff_C_mul]
    calc
      v (a⁻¹ * P.coeff i0) = v a⁻¹ * v (P.coeff i0) := Valuation.map_mul _ _ _
      _ = (v a)⁻¹ * v a := by rw [Valuation.map_inv, ha_def]
      _ = 1 := inv_mul_cancel₀ ha_val_ne_zero
  refine ⟨a, ha_ne_zero, P', h_eq, h_coeff_val_le_one, h_coeff_val_eq_one⟩

theorem val_eq_one_of_primitive {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {P : M[X]} {z : M}
    (hP : ∀ i, v (P.coeff i) ≤ 1) (hP1 : ∃ i, v (P.coeff i) = 1)
    (hzP : ∀ i, v ((C z * P).coeff i) ≤ 1) (hzP1 : ∃ i, v ((C z * P).coeff i) = 1) :
    v z = 1 := by
  rcases hP1 with ⟨i, hi⟩
  have h1 : v z ≤ 1 := by
    calc
      v z = v z * 1 := by simp
      _ = v z * v (P.coeff i) := by rw [hi]
      _ = v (z * P.coeff i) := by rw [v.map_mul]
      _ = v ((C z * P).coeff i) := by rw [coeff_C_mul]
      _ ≤ 1 := hzP i
  rcases hzP1 with ⟨j, hj⟩
  have h2 : 1 ≤ v z := by
    calc
      1 = v ((C z * P).coeff j) := by rw [hj]
      _ = v (z * P.coeff j) := by rw [coeff_C_mul]
      _ = v z * v (P.coeff j) := by rw [v.map_mul]
      _ ≤ v z * 1 := by
        have hzero : 0 ≤ v z := zero_le (a := v z)
        exact mul_le_mul_of_nonneg_left (hP j) hzero
      _ = v z := by simp
  exact le_antisymm h1 h2

theorem eval_le_one {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P : M[X]} {x : M} (hP : ∀ i, v (P.coeff i) ≤ 1) (hx : v x ≤ 1) :
    v (P.eval x) ≤ 1 := by
  rw [Polynomial.eval_eq_sum_range]
  refine Valuation.map_sum_le v (fun i hi => ?_)
  rw [Valuation.map_mul, Valuation.map_pow]
  exact Right.mul_le_one (hP i) (pow_le_one' hx i)

lemma valuation_natCast_le_one {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) : ∀ n : ℕ, v ((n : M)) ≤ 1 := by
  intro n
  induction' n with k ih
  · rw [Nat.cast_zero, v.map_zero]
    exact zero_le_one' _
  · rw [Nat.cast_succ]
    apply le_trans (v.map_add (k : M) 1)
    rw [v.map_one]
    exact max_le ih (le_refl _)


theorem derivative_le_one {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {P : M[X]}
    (hP : ∀ i, v (P.coeff i) ≤ 1) : ∀ i, v (P.derivative.coeff i) ≤ 1 := by
  intro i
  rw [Polynomial.coeff_derivative]
  rw [v.map_mul]
  apply mul_le_one'
  · exact hP (i + 1)
  · -- v (↑i + 1) ≤ 1
    simpa [Nat.cast_succ] using valuation_natCast_le_one v (i + 1)

theorem root_le_one {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {f : M[X]} {θ : M} (hf : ∀ i, v (f.coeff i) ≤ 1)
    (hl : v f.leadingCoeff = 1) (hd : 0 < f.natDegree) (hθ : f.eval θ = 0) : v θ ≤ 1 := by
  by_contra! h
  have hvθ1 : 1 < v θ := h
  set n := f.natDegree with hn
  have hnpos : 0 < n := hd
  have hcoeff_n : f.coeff n = f.leadingCoeff := by
    rw [hn, coeff_natDegree]
  have hv_coeff_n : v (f.coeff n) = 1 := by
    rw [hcoeff_n, hl]
  have hval_top : v (f.coeff n * θ ^ n) = (v θ) ^ n := by
    rw [Valuation.map_mul, hv_coeff_n, Valuation.map_pow, one_mul]
  have hvθ0 : v θ ≠ 0 := by
    have h0lt1 : (0 : Γ₀) < 1 := zero_lt_one
    exact ne_of_gt (lt_trans h0lt1 hvθ1)
  have hpow_ne_zero : (v θ) ^ n ≠ 0 := pow_ne_zero n hvθ0
  have hval_lower : ∀ i ∈ Finset.range n, v (f.coeff i * θ ^ i) < (v θ) ^ n := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_lt_n : i < n := hi
    have hval_prod_i : v (f.coeff i * θ ^ i) = v (f.coeff i) * v (θ ^ i) := Valuation.map_mul v _ _
    have hval_pow_i : v (θ ^ i) = (v θ) ^ i := Valuation.map_pow v θ i
    rw [hval_prod_i, hval_pow_i]
    have h_pow_lt : (v θ) ^ i < (v θ) ^ n :=
      pow_lt_pow_right₀ hvθ1 hi_lt_n
    have h_nonneg_pow : 0 ≤ (v θ) ^ i := by
      have hpos : 0 < v θ := lt_trans zero_lt_one hvθ1
      exact pow_nonneg (by exact le_of_lt hpos) i
    calc
      v (f.coeff i) * (v θ) ^ i ≤ 1 * (v θ) ^ i :=
        mul_le_mul_of_nonneg_right (hf i) h_nonneg_pow
      _ = (v θ) ^ i := by simp
      _ < (v θ) ^ n := h_pow_lt
  have hval_sum_lower : v (∑ i ∈ Finset.range n, f.coeff i * θ ^ i) < (v θ) ^ n := by
    apply Valuation.map_sum_lt v hpow_ne_zero hval_lower
  have hval_eval : v (f.eval θ) = (v θ) ^ n := by
    calc
      v (f.eval θ) = v (∑ i ∈ Finset.range (n + 1), f.coeff i * θ ^ i) := by
        rw [eval_eq_sum_range]
      _ = v ((∑ i ∈ Finset.range n, f.coeff i * θ ^ i) + f.coeff n * θ ^ n) := by
        rw [Finset.sum_range_succ]
      _ = v (f.coeff n * θ ^ n) := by
        apply Valuation.map_add_eq_of_lt_right v
        rw [hval_top]
        exact hval_sum_lower
      _ = (v θ) ^ n := hval_top
  rw [hθ] at hval_eval
  have hval_zero : v (0 : M) = 0 := Valuation.map_zero v
  rw [hval_zero] at hval_eval
  have hpow_eq_zero : (v θ) ^ n = 0 := hval_eval.symm
  exact hpow_ne_zero hpow_eq_zero

theorem primitive_sub {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P E : M[X]} (hP : ∀ i, v (P.coeff i) ≤ 1)
    (hP1 : ∃ i, v (P.coeff i) = 1) (hE : ∀ i, v (E.coeff i) < 1) :
    (∀ i, v ((P - E).coeff i) ≤ 1) ∧ ∃ i, v ((P - E).coeff i) = 1 := by
  constructor
  · intro i
    rw [Polynomial.coeff_sub]
    calc
      v (P.coeff i - E.coeff i) ≤ max (v (P.coeff i)) (v (E.coeff i)) := Valuation.map_sub v _ _
      _ ≤ max 1 (v (E.coeff i)) := max_le_max (hP i) (le_refl _)
      _ = 1 := max_eq_left (hE i).le
  · rcases hP1 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [Polynomial.coeff_sub]
    have hlt : v (E.coeff i) < v (P.coeff i) := by
      rw [hi]
      exact hE i
    rw [Valuation.map_sub_eq_of_lt_left v hlt, hi]

theorem sq_sub_primitive {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {V f : M[X]}
    (hV : ∀ i, v (V.coeff i) ≤ 1) (hV1 : V.natDegree ≤ 1) (hf : ∀ i, v (f.coeff i) ≤ 1)
    (hdeg : f.natDegree = 6) (hl : v f.leadingCoeff = 1) :
    (∀ i, v ((V ^ 2 - f).coeff i) ≤ 1) ∧ ∃ i, v ((V ^ 2 - f).coeff i) = 1 := by
  have hV2_natDegree : (V ^ 2).natDegree ≤ 2 := by
    calc
      (V ^ 2).natDegree ≤ 2 * V.natDegree := Polynomial.natDegree_pow_le
      _ ≤ 2 * 1 := by
        nlinarith
      _ = 2 := by norm_num
  have hV2_coeff_zero : ∀ i, 2 < i → (V ^ 2).coeff i = 0 := by
    intro i hi
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt hV2_natDegree hi
  have hcoeff_sub : ∀ i, (V ^ 2 - f).coeff i = (V ^ 2).coeff i - f.coeff i :=
    Polynomial.coeff_sub (V ^ 2) f
  have hval_sub : ∀ i, v ((V ^ 2 - f).coeff i) ≤ 1 := by
    intro i
    rw [hcoeff_sub i]
    calc
      v ((V ^ 2).coeff i - f.coeff i) ≤ max (v ((V ^ 2).coeff i)) (v (f.coeff i)) :=
        Valuation.map_sub v ((V ^ 2).coeff i) (f.coeff i)
      _ ≤ max 1 1 := by
        apply max_le_max ?_ (hf i)
        -- need to show v ((V ^ 2).coeff i) ≤ 1
        rw [pow_two, Polynomial.coeff_mul V V i]
        apply Valuation.map_sum_le v
        intro x hx
        have hx_mem : x ∈ Finset.HasAntidiagonal.antidiagonal i := hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx_mem
        rw [Valuation.map_mul v (V.coeff x.1) (V.coeff x.2)]
        have h1 : v (V.coeff x.1) ≤ 1 := hV x.1
        have h2 : v (V.coeff x.2) ≤ 1 := hV x.2
        calc
          v (V.coeff x.1) * v (V.coeff x.2) ≤ 1 * 1 := mul_le_mul' h1 h2
          _ = 1 := by norm_num
      _ = 1 := by norm_num
  have hval_eq_one : ∃ i, v ((V ^ 2 - f).coeff i) = 1 := by
    use 6
    have hzero : (V ^ 2).coeff 6 = 0 := hV2_coeff_zero 6 (by omega)
    rw [hcoeff_sub 6, hzero, zero_sub, Valuation.map_neg v (f.coeff 6)]
    have hcoeff6 : f.coeff 6 = f.leadingCoeff := by
      rw [← Polynomial.coeff_natDegree, hdeg]
    rw [hcoeff6, hl]
  exact And.intro hval_sub hval_eq_one

theorem one_lt_of_not_integral {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {V V' : M[X]} {b : M}
    (hV : V = C b * V') (hV' : ∀ i, v (V'.coeff i) ≤ 1) (hni : ¬ ∀ i, v (V.coeff i) ≤ 1) :
    1 < v b := by
  push_neg at hni
  obtain ⟨i, hi⟩ := hni
  have hcoeff : V.coeff i = b * V'.coeff i := by
    calc
      V.coeff i = (C b * V').coeff i := by rw [hV]
      _ = b * V'.coeff i := by rw [Polynomial.coeff_C_mul]
  rw [hcoeff] at hi
  rw [Valuation.map_mul] at hi
  have hpos : 0 ≤ v b := zero_le (a := v b)
  calc
    1 < v b * v (V'.coeff i) := hi
    _ ≤ v b * 1 := mul_le_mul_of_nonneg_left (hV' i) hpos
    _ = v b := by rw [mul_one]

theorem coeff_C_mul_lt_one {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {f : M[X]} {e : M}
    (hf : ∀ i, v (f.coeff i) ≤ 1) (he : v e < 1) : ∀ i, v ((C e * f).coeff i) < 1 := by
  intro i
  rw [Polynomial.coeff_C_mul]
  rw [Valuation.map_mul]
  have h := hf i
  calc
    v e * v (f.coeff i) ≤ v e * 1 := mul_le_mul_right h (v e)
    _ = v e := mul_one (v e)
    _ < 1 := he

/-- The contradiction of the integral case (derivative at `θ`). -/
theorem derivative_eval_lt_one {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {U W V f : M[X]} {θ a : M}
    (hU : ∀ i, v (U.coeff i) ≤ 1) (hW : ∀ i, v (W.coeff i) ≤ 1) (hV : ∀ i, v (V.coeff i) ≤ 1)
    (hθ : v θ ≤ 1) (ha : v a ≤ 1) (h : C a * (U * W) = V ^ 2 - f) (hfθ : f.eval θ = 0)
    (hUθ : v (U.eval θ) < 1) (hWθ : v (W.eval θ) < 1) : v (f.derivative.eval θ) < 1 := by
  -- from h : C a * (U * W) = V ^ 2 - f, we get f = V ^ 2 - C a * (U * W)
  have hf : f = V ^ 2 - C a * (U * W) := by
    calc
      f = (V ^ 2) - (V ^ 2 - f) := by ring
      _ = V ^ 2 - C a * (U * W) := by rw [h]
  -- evaluate h at θ to get a * (U.eval θ * W.eval θ) = (V.eval θ)^2
  have h_eval : a * (U.eval θ * W.eval θ) = (V.eval θ) ^ 2 := by
    calc
      a * (U.eval θ * W.eval θ) = (C a * (U * W)).eval θ := by simp [eval_mul, eval_C]
      _ = (V ^ 2 - f).eval θ := by rw [h]
      _ = (V.eval θ) ^ 2 - f.eval θ := by simp [eval_sub, eval_pow]
      _ = (V.eval θ) ^ 2 := by rw [hfθ, sub_zero]
  -- take valuation: v a * v (U.eval θ) * v (W.eval θ) = (v (V.eval θ))^2
  have h_val_eq : v a * v (U.eval θ) * v (W.eval θ) = (v (V.eval θ)) ^ 2 := by
    calc
      v a * v (U.eval θ) * v (W.eval θ) = v (a * (U.eval θ * W.eval θ)) := by
        simp [Valuation.map_mul, mul_assoc]
      _ = v ((V.eval θ) ^ 2) := by rw [h_eval]
      _ = (v (V.eval θ)) ^ 2 := by rw [Valuation.map_pow]
  -- show v a * v (U.eval θ) * v (W.eval θ) < 1
  have h_prod_lt_one : v a * v (U.eval θ) * v (W.eval θ) < 1 := by
    have hWθ_le_one : v (W.eval θ) ≤ 1 := eval_le_one v hW hθ
    have hUθ_nonneg : 0 ≤ v (U.eval θ) := zero_le
    have ha_nonneg : 0 ≤ v a := zero_le
    have hUθ_mul_na : 0 ≤ v a * v (U.eval θ) := mul_nonneg ha_nonneg hUθ_nonneg
    -- step 1: v a * v (U.eval θ) ≤ v (U.eval θ)
    have h_step1 : v a * v (U.eval θ) ≤ v (U.eval θ) := by
      calc
        v a * v (U.eval θ) ≤ 1 * v (U.eval θ) :=
          mul_le_mul ha (le_refl _) (zero_le) (zero_le (a := 1))
        _ = v (U.eval θ) := by simp
    -- step 2: (v a * v (U.eval θ)) * v (W.eval θ) ≤ v (U.eval θ) * v (W.eval θ)
    have h_step2 : v a * v (U.eval θ) * v (W.eval θ) ≤ v (U.eval θ) * v (W.eval θ) :=
      mul_le_mul h_step1 (le_refl _) (zero_le) hUθ_nonneg
    -- step 3: v (U.eval θ) * v (W.eval θ) ≤ v (U.eval θ)
    have h_step3 : v (U.eval θ) * v (W.eval θ) ≤ v (U.eval θ) := by
      calc
        v (U.eval θ) * v (W.eval θ) ≤ v (U.eval θ) * 1 :=
          mul_le_mul (le_refl _) hWθ_le_one (zero_le) hUθ_nonneg
        _ = v (U.eval θ) := by simp
    -- combine
    calc
      v a * v (U.eval θ) * v (W.eval θ) ≤ v (U.eval θ) * v (W.eval θ) := h_step2
      _ ≤ v (U.eval θ) := h_step3
      _ < 1 := hUθ
  -- hence (v (V.eval θ))^2 < 1, so v (V.eval θ) < 1
  have hVθ_lt_one : v (V.eval θ) < 1 := by
    have h_sq_lt_one : (v (V.eval θ)) ^ 2 < 1 := by
      -- from h_val_eq and h_prod_lt_one
      rw [← h_val_eq]
      exact h_prod_lt_one
    -- if x^2 < 1 and x ≥ 0, then x < 1
    by_contra! hge
    have hge' : 1 ≤ v (V.eval θ) := hge
    have h_sq_ge_one : 1 ≤ (v (V.eval θ)) ^ 2 := one_le_pow₀ hge'
    exact not_lt.mpr h_sq_ge_one h_sq_lt_one
  -- derivative identity evaluated at θ
  have h_deriv : f.derivative.eval θ = (2 : M) * V.eval θ * V.derivative.eval θ - a * (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) := by
    rw [hf]
    simp [derivative_sub, derivative_pow, derivative_mul, eval_sub, eval_add, eval_mul, eval_C]
  -- now show v (f.derivative.eval θ) < 1
  rw [h_deriv]
  -- v (A - B) < 1 where A = 2 * V.eval θ * V.derivative.eval θ, B = a * (...)
  apply Valuation.map_sub_lt v
  · -- v (2 * V.eval θ * V.derivative.eval θ) < 1
    have hv2_le_one : v (2 : M) ≤ 1 := by
      calc
        v (2 : M) = v ((1 : M) + (1 : M)) := by norm_num
        _ ≤ max (v (1 : M)) (v (1 : M)) := Valuation.map_add v (1 : M) (1 : M)
        _ = max (1 : Γ₀) (1 : Γ₀) := by rw [Valuation.map_one]
        _ = 1 := max_self _
    have hVderiv_eval_le_one : v (V.derivative.eval θ) ≤ 1 :=
      eval_le_one v (derivative_le_one v hV) hθ
    have hA : v ((2 : M) * V.eval θ * V.derivative.eval θ) = v (2 : M) * v (V.eval θ) * v (V.derivative.eval θ) := by
      simp [Valuation.map_mul, mul_assoc]
    rw [hA]
    -- need: v 2 * v (V.eval θ) * v (V.derivative.eval θ) < 1
    -- We know: v 2 ≤ 1, v (V.eval θ) < 1, v (V.derivative.eval θ) ≤ 1
    have hVderiv_nonneg : 0 ≤ v (V.derivative.eval θ) := zero_le
    have hV_nonneg : 0 ≤ v (V.eval θ) := zero_le
    have h2_nonneg : 0 ≤ v (2 : M) := zero_le
    -- chain: v 2 * v (V.eval θ) * v (V.derivative.eval θ) ≤ 1 * v (V.eval θ) * 1 = v (V.eval θ) < 1
    have h1 : v (2 : M) * v (V.eval θ) ≤ 1 * v (V.eval θ) :=
      mul_le_mul hv2_le_one (le_refl _) (zero_le) (zero_le (a := 1))
    have h2 : (v (2 : M) * v (V.eval θ)) * v (V.derivative.eval θ) ≤ (1 * v (V.eval θ)) * 1 :=
      mul_le_mul h1 hVderiv_eval_le_one (zero_le) (mul_nonneg (zero_le (a := 1)) hV_nonneg)
    have h3 : (1 * v (V.eval θ)) * 1 = v (V.eval θ) := by simp
    have h4 : v (V.eval θ) < 1 := hVθ_lt_one
    -- now combine
    calc
      v (2 : M) * v (V.eval θ) * v (V.derivative.eval θ) ≤ (1 * v (V.eval θ)) * 1 := h2
      _ = v (V.eval θ) := by simp
      _ < 1 := hVθ_lt_one
  · -- v (a * (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ)) < 1
    have hUderiv_eval_le_one : v (U.derivative.eval θ) ≤ 1 :=
      eval_le_one v (derivative_le_one v hU) hθ
    have hWderiv_eval_le_one : v (W.derivative.eval θ) ≤ 1 :=
      eval_le_one v (derivative_le_one v hW) hθ
    have h_sum_lt_one : v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) < 1 := by
      apply Valuation.map_add_lt v
      · -- v (U.derivative.eval θ * W.eval θ) < 1
        have hprod : v (U.derivative.eval θ * W.eval θ) = v (U.derivative.eval θ) * v (W.eval θ) :=
          Valuation.map_mul v _ _
        rw [hprod]
        -- v (U.derivative.eval θ) ≤ 1, v (W.eval θ) < 1
        have h1 : v (U.derivative.eval θ) * v (W.eval θ) ≤ 1 * v (W.eval θ) :=
          mul_le_mul hUderiv_eval_le_one (le_refl _) (zero_le) (zero_le)
        have h2 : 1 * v (W.eval θ) = v (W.eval θ) := by simp
        have h3 : v (W.eval θ) < 1 := hWθ
        calc
          v (U.derivative.eval θ) * v (W.eval θ) ≤ 1 * v (W.eval θ) := h1
          _ = v (W.eval θ) := by simp
          _ < 1 := hWθ
      · -- v (U.eval θ * W.derivative.eval θ) < 1
        have hprod : v (U.eval θ * W.derivative.eval θ) = v (U.eval θ) * v (W.derivative.eval θ) :=
          Valuation.map_mul v _ _
        rw [hprod]
        have h1 : v (U.eval θ) * v (W.derivative.eval θ) ≤ v (U.eval θ) * 1 :=
          mul_le_mul (le_refl _) hWderiv_eval_le_one (zero_le) (zero_le)
        have h2 : v (U.eval θ) * 1 = v (U.eval θ) := by simp
        have h3 : v (U.eval θ) < 1 := hUθ
        calc
          v (U.eval θ) * v (W.derivative.eval θ) ≤ v (U.eval θ) * 1 := h1
          _ = v (U.eval θ) := by simp
          _ < 1 := hUθ
    -- now multiply by v a ≤ 1
    have hprod_total : v (a * (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ)) =
        v a * v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) :=
      Valuation.map_mul v _ _
    rw [hprod_total]
    have h1 : v a * v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) ≤
        1 * v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) :=
      mul_le_mul ha (le_refl _) (zero_le) (zero_le)
    have h2 : 1 * v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) =
        v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) := by simp
    calc
      v a * v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) ≤
          1 * v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) := h1
      _ = v (U.derivative.eval θ * W.eval θ + U.eval θ * W.derivative.eval θ) := by simp
      _ < 1 := h_sum_lt_one

/-! ### Degrees and the root factor -/

theorem natDegree_eq_four {M : Type*} [Field M] {U W V f : M[X]} (hU : U.natDegree = 2)
    (hV : V.natDegree ≤ 1) (hf : f.natDegree = 6) (h : V ^ 2 - f = U * W) :
    W.natDegree = 4 := by
  have hVpow : (V ^ 2).natDegree ≤ 2 := by
    calc
      (V ^ 2).natDegree ≤ 2 * V.natDegree := natDegree_pow_le
      _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 hV
      _ = 2 := by norm_num
  have h_lt : (V ^ 2).natDegree < f.natDegree := by
    rw [hf]
    omega
  have h_sub_deg : (V ^ 2 - f).natDegree = 6 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt h_lt, hf]
  have hU_ne_zero : U ≠ 0 := by
    intro hUzero
    rw [hUzero, natDegree_zero] at hU
    norm_num at hU
  have hW_ne_zero : W ≠ 0 := by
    intro hWzero
    rw [hWzero, mul_zero] at h
    have hzero : (V ^ 2 - f).natDegree = 0 := by rw [h, natDegree_zero]
    rw [h_sub_deg] at hzero
    norm_num at hzero
  have h_mul_deg : (U * W).natDegree = U.natDegree + W.natDegree :=
    natDegree_mul hU_ne_zero hW_ne_zero
  rw [h] at h_sub_deg
  rw [h_mul_deg, hU] at h_sub_deg
  omega

theorem eval_eq_derivative_eval {R : Type*} [CommRing R] {f g : R[X]} {θ : R}
    (h : f = (X - C θ) * g) : g.eval θ = f.derivative.eval θ := by
  subst h
  simp [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

/-! ### Identity B and the reduced resultant -/

/-- Identity B: `U(θ) Res_{2,5}(U, g)` is a square when `V² - (X - θ) g = U W`. -/
theorem identityB {K : Type*} [Field K] {U V W g : K[X]} {θ : K} (hU : U.natDegree ≤ 2)
    (hV : V.natDegree ≤ 1) (hW : W.natDegree ≤ 4) (hg : g.natDegree = 5)
    (h : V ^ 2 - (X - C θ) * g = U * W) : ∃ y : K, U.eval θ * resultant U g 2 5 = y ^ 2 := by
  set d := V.natDegree with hd
  have hd_le_one : d ≤ 1 := hV
  have h_eq : (X - C θ) * g = V ^ 2 + U * (-W) := by
    have h' : V ^ 2 = (X - C θ) * g + U * W := by
      rw [eq_add_of_sub_eq' h]
    calc
      (X - C θ) * g = ((X - C θ) * g + U * W) - U * W := by ring
      _ = V ^ 2 - U * W := by rw [← h']
      _ = V ^ 2 + U * (-W) := by ring
  have hp : (-W).natDegree + 2 ≤ 6 := by
    have h_negW : (-W).natDegree ≤ 4 := by
      simpa [natDegree_neg] using hW
    omega
  -- Step 1: resultant U ((X - C θ) * g) 2 6 = U.eval θ * resultant U g 2 5
  have h_step1 : resultant U ((X - C θ) * g) 2 6 = U.eval θ * resultant U g 2 5 := by
    calc
      resultant U ((X - C θ) * g) 2 6 = resultant U ((X - C θ) * g) 2 ((X - C θ).natDegree + g.natDegree) := by
        simp [natDegree_X_sub_C θ, hg]
      _ = resultant U (X - C θ) 2 * resultant U g 2 := by
        rw [resultant_mul_right U (X - C θ) g 2 hU]
      _ = (U.eval θ) * resultant U g 2 5 := by
        have h1 : resultant U (X - C θ) 2 = U.eval θ := by
          simpa using resultant_X_sub_C_right U 2 θ hU
        have h2 : resultant U g 2 = resultant U g 2 5 := by rw [hg]
        rw [h1, h2]
  -- Step 2: resultant U (V ^ 2 + U * (-W)) 2 6 = resultant U (V ^ 2) 2 6
  have h_step2 : resultant U (V ^ 2 + U * (-W)) 2 6 = resultant U (V ^ 2) 2 6 := by
    rw [resultant_add_mul_right U (V ^ 2) (-W) 2 6 hp hU]
  -- Step 3: resultant U (V ^ 2) 2 6 = (U.coeff 2 ^ (3 - d) * resultant U V 2) ^ 2
  have h_pow_natDegree : (V ^ 2).natDegree ≤ 2 * d := by
    have h := natDegree_pow_le (p := V) (n := 2)
    -- h : (V ^ 2).natDegree ≤ 2 * V.natDegree
    simpa [hd, mul_comm] using h
  have h_step3 : resultant U (V ^ 2) 2 6 = (U.coeff 2 ^ (3 - d) * resultant U V 2) ^ 2 := by
    have h_pow_eq : resultant U (V ^ 2) 2 (2 * d) = (resultant U V 2) ^ 2 := by
      calc
        resultant U (V ^ 2) 2 (2 * d) = resultant U (V * V) 2 (V.natDegree + V.natDegree) := by
          rw [pow_two, hd, two_mul]
        _ = resultant U V 2 * resultant U V 2 := by rw [resultant_mul_right U V V 2 hU]
        _ = (resultant U V 2) ^ 2 := by ring
    calc
      resultant U (V ^ 2) 2 6 = resultant U (V ^ 2) 2 ((2 * d) + (6 - 2 * d)) := by
        rw [Nat.add_sub_cancel' (by omega : 2 * d ≤ 6)]
      _ = U.coeff 2 ^ (6 - 2 * d) * resultant U (V ^ 2) 2 (2 * d) := by
        rw [resultant_add_right_deg U (V ^ 2) 2 (2 * d) (6 - 2 * d) h_pow_natDegree]
      _ = U.coeff 2 ^ (6 - 2 * d) * ((resultant U V 2) ^ 2) := by rw [h_pow_eq]
      _ = (U.coeff 2 ^ (3 - d)) ^ 2 * (resultant U V 2) ^ 2 := by
        have : 6 - 2 * d = 2 * (3 - d) := by omega
        rw [this]
        rw [pow_mul, ← pow_mul (U.coeff 2) (3 - d) 2, mul_comm (3 - d) 2, pow_mul]
      _ = (U.coeff 2 ^ (3 - d) * resultant U V 2) ^ 2 := by ring
  -- Combine everything
  have h_main : U.eval θ * resultant U g 2 5 = (U.coeff 2 ^ (3 - d) * resultant U V 2) ^ 2 := by
    calc
      U.eval θ * resultant U g 2 5 = resultant U ((X - C θ) * g) 2 6 := by symm; exact h_step1
      _ = resultant U (V ^ 2 + U * (-W)) 2 6 := by rw [h_eq]
      _ = resultant U (V ^ 2) 2 6 := h_step2
      _ = (U.coeff 2 ^ (3 - d) * resultant U V 2) ^ 2 := h_step3
  exact ⟨U.coeff 2 ^ (3 - d) * resultant U V 2, h_main⟩

/-- Over the residue field: if `P Q = z S²` with `S` linear and `P`, `Q` both vanish at `t`,
then `P` is linear with root `t`, so it is coprime to `g` when `g(t) ≠ 0`. -/
theorem resultant_ne_zero_of_sq {k : Type*} [Field k] {P Q S g : k[X]} {t z : k} (hP : P ≠ 0)
    (hQ : Q ≠ 0) (hS : S.natDegree ≤ 1) (hPQ : P * Q = C z * S ^ 2) (hPt : P.eval t = 0)
    (hQt : Q.eval t = 0) (hP2 : P.natDegree ≤ 2) (hg : g.natDegree = 5) (hgt : g.eval t ≠ 0) :
    resultant P g 2 5 ≠ 0 := by
  -- Step 1: P.natDegree ≥ 1 because P ≠ 0 and P has a root
  have hP_deg_pos : 0 < P.natDegree := by
    by_contra! h
    have h0 : P.natDegree = 0 := by omega
    have hP_eq_const : P = C (coeff P 0) := eq_C_of_natDegree_eq_zero h0
    have hcoeff_ne_zero : coeff P 0 ≠ 0 := by
      intro hzero
      apply hP
      rw [hP_eq_const, hzero, map_zero]
    have hval : (C (coeff P 0)).eval t = coeff P 0 := by simp
    rw [hP_eq_const, hval] at hPt
    exact hcoeff_ne_zero hPt
  -- Step 2: Q.natDegree ≥ 1 because Q ≠ 0 and Q has a root
  have hQ_deg_pos : 0 < Q.natDegree := by
    by_contra! h
    have h0 : Q.natDegree = 0 := by omega
    have hQ_eq_const : Q = C (coeff Q 0) := eq_C_of_natDegree_eq_zero h0
    have hcoeff_ne_zero : coeff Q 0 ≠ 0 := by
      intro hzero
      apply hQ
      rw [hQ_eq_const, hzero, map_zero]
    have hval : (C (coeff Q 0)).eval t = coeff Q 0 := by simp
    rw [hQ_eq_const, hval] at hQt
    exact hcoeff_ne_zero hQt
  -- Step 3: (P * Q).natDegree ≤ 2 from hPQ and hS
  have hPQ_deg : (P * Q).natDegree ≤ 2 := by
    rw [hPQ]
    calc
      (C z * S ^ 2).natDegree ≤ (S ^ 2).natDegree := natDegree_C_mul_le _ _
      _ ≤ 2 * S.natDegree := natDegree_pow_le
      _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 hS
      _ = 2 := by norm_num
  -- Step 4: P.natDegree + Q.natDegree = (P * Q).natDegree ≤ 2
  have h_deg_sum : P.natDegree + Q.natDegree ≤ 2 := by
    rw [← natDegree_mul hP hQ]
    exact hPQ_deg
  -- Step 5: P.natDegree = 1 and Q.natDegree = 1
  have hP_deg : P.natDegree = 1 := by
    have : P.natDegree ≤ 2 := hP2
    have hsum := h_deg_sum
    have hQge1 : 1 ≤ Q.natDegree := by omega
    omega
  have hQ_deg : Q.natDegree = 1 := by
    have hsum := h_deg_sum
    rw [hP_deg] at hsum
    have hQge1 : 1 ≤ Q.natDegree := by omega
    omega
  -- Step 6: Factor P = C b * (X - C t) with b ≠ 0
  have h_factor : ∃ b : k, b ≠ 0 ∧ P = C b * (X - C t) := by
    have h_dvd : (X - C t) ∣ P := (dvd_iff_isRoot (a := t)).mpr hPt
    rcases h_dvd with ⟨Q', hP_eq⟩
    have hQ'_ne : Q' ≠ 0 := by
      intro hzero
      apply hP
      rw [hP_eq, hzero, mul_zero]
    have h_natDegree_X_sub_C : (X - C t).natDegree = 1 := natDegree_X_sub_C t
    have hX_sub_C_ne_zero : X - C t ≠ 0 := by
      intro hzero
      have : (X - C t).natDegree = 0 := by simpa [hzero] using natDegree_zero
      rw [h_natDegree_X_sub_C] at this
      omega
    have hQ'_deg : Q'.natDegree = 0 := by
      have h_mul_deg : (X - C t).natDegree + Q'.natDegree = P.natDegree := by
        rw [hP_eq, natDegree_mul hX_sub_C_ne_zero hQ'_ne]
      rw [hP_deg, h_natDegree_X_sub_C] at h_mul_deg
      omega
    have hQ'_eq : Q' = C (coeff Q' 0) := eq_C_of_natDegree_eq_zero hQ'_deg
    set b := coeff Q' 0 with hb_def
    have hb_ne : b ≠ 0 := by
      intro hb0
      apply hP
      rw [hP_eq, hQ'_eq, hb0, C_0, mul_zero]
    have hP_eq' : P = C b * (X - C t) := by
      rw [hP_eq, hQ'_eq, hb_def, mul_comm]
    exact ⟨b, hb_ne, hP_eq'⟩
  rcases h_factor with ⟨b, hb_ne, hP_eq⟩
  -- Step 7: Compute resultant P g 2 5
  have hg_le : g.natDegree ≤ 5 := by rw [hg]
  have hP_deg_le_one : P.natDegree ≤ 1 := by rw [hP_deg]
  have h_deg_bound : (C b * (X - C t)).natDegree ≤ 1 := by
    rw [← hP_eq]
    exact hP_deg_le_one
  have h_resultant : resultant P g 2 5 = (-1) ^ 5 * g.coeff 5 * (b ^ 5) * g.eval t := by
    rw [hP_eq]
    rw [resultant_succ_left_deg (f := C b * (X - C t)) (g := g) (m := 1) (n := 5) h_deg_bound]
    rw [resultant_C_mul_left (f := X - C t) (g := g) (m := 1) (n := 5) b]
    rw [resultant_X_sub_C_left (r := t) (g := g) (n := 5) hg_le]
    ring
  -- Step 8: Show the result is nonzero
  rw [h_resultant]
  have h_neg_one_pow : (-1 : k) ^ 5 ≠ 0 := by
    norm_num
  have h_coeff_ne_zero : g.coeff 5 ≠ 0 := by
    rw [← hg, coeff_natDegree]
    have hg_ne_zero : g ≠ 0 := by
      intro hzero
      rw [hzero] at hg
      simp at hg
    exact ((leadingCoeff_ne_zero (p := g)).mpr hg_ne_zero)
  have hb_pow_ne_zero : b ^ 5 ≠ 0 := pow_ne_zero 5 hb_ne
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h_neg_one_pow h_coeff_ne_zero) hb_pow_ne_zero) hgt

/-! ### The valuation ring and its residue field -/

theorem exists_lift {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P : M[X]} (hP : ∀ i, v (P.coeff i) ≤ 1) :
    ∃ P₀ : v.valuationSubring[X], P₀.map (algebraMap v.valuationSubring M) = P := by
  have hcoeff (n : ℕ) : P.coeff n ∈ Set.range (algebraMap v.valuationSubring M) := by
    have hmem : P.coeff n ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]
      exact hP n
    refine ⟨⟨P.coeff n, hmem⟩, ?_⟩
    rfl
  have hP_lifts : P ∈ lifts (algebraMap v.valuationSubring M) := by
    rw [lifts_iff_coeff_lifts]
    exact hcoeff
  rcases (mem_lifts _).mp hP_lifts with ⟨P₀, hP₀⟩
  exact ⟨P₀, hP₀⟩

theorem residue_eq_zero_iff {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) (x : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring x = 0 ↔ v (x : M) < 1 := by
  have hle : v (x : M) ≤ 1 :=
    (Valuation.mem_valuationSubring_iff v (x : M)).mp x.2
  have h_iff := (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one (x := x)
  have h_iff' : IsUnit x ↔ v (x : M) = 1 := by
    simpa using h_iff
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  -- Goal: ¬ IsUnit x ↔ v (x : M) < 1
  have h_ne_iff_lt : v (x : M) ≠ 1 ↔ v (x : M) < 1 := by
    refine ⟨?_, ne_of_lt⟩
    intro hne
    exact lt_of_le_of_ne hle hne
  constructor
  · intro h
    -- h : ¬ IsUnit x
    -- Goal: v (x : M) < 1
    have hne : v (x : M) ≠ 1 := mt h_iff'.mpr h
    exact h_ne_iff_lt.mp hne
  · intro h
    -- h : v (x : M) < 1
    -- Goal: ¬ IsUnit x
    intro hx
    have h_eq_one : v (x : M) = 1 := h_iff'.mp hx
    exact ne_of_lt h h_eq_one

theorem map_residue_ne_zero {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {P₀ : v.valuationSubring[X]}
    (h : ∃ i, v ((P₀.coeff i : v.valuationSubring) : M) = 1) :
    P₀.map (IsLocalRing.residue v.valuationSubring) ≠ 0 := by
  rcases h with ⟨i, hi⟩
  intro hzero
  have hcoeff : (P₀.map (IsLocalRing.residue v.valuationSubring)).coeff i = 0 := by
    rw [hzero]
    simp
  have hcoeff_map : (P₀.map (IsLocalRing.residue v.valuationSubring)).coeff i =
      IsLocalRing.residue v.valuationSubring (P₀.coeff i) := by
    rw [Polynomial.coeff_map]
  rw [hcoeff_map] at hcoeff
  have h_lt_one : v ((P₀.coeff i : v.valuationSubring) : M) < 1 :=
    (residue_eq_zero_iff v (P₀.coeff i)).mp hcoeff
  rw [hi] at h_lt_one
  exact lt_irrefl 1 h_lt_one

/-! ### Parity in `ℤᵐ⁰` -/

theorem exists_two_mul {x y : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) (h : x = y ^ 2) :
    ∃ n : ℤ, x = WithZero.coe (Multiplicative.ofAdd (2 * n)) := by
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    rw [hy0] at h
    simp at h
    exact h
  rcases (WithZero.ne_zero_iff_exists.mp hy) with ⟨a, ha⟩
  refine ⟨Multiplicative.toAdd a, ?_⟩
  rw [h, ← ha]
  have h1 : ((a : WithZero (Multiplicative ℤ)) ^ 2) = ((a ^ 2 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simp [WithZero.coe_pow]
  rw [h1]
  have h2 : a ^ 2 = Multiplicative.ofAdd (2 • Multiplicative.toAdd a) := by
    calc
      a ^ 2 = (Multiplicative.ofAdd (Multiplicative.toAdd a)) ^ 2 := by
        rw [ofAdd_toAdd]
      _ = Multiplicative.ofAdd (2 • Multiplicative.toAdd a) := by
        rw [← ofAdd_nsmul 2 (Multiplicative.toAdd a)]
  rw [h2]
  rw [Int.nsmul_eq_mul]
  rfl

end FurioLombardo.Discharge.SelmerBasis.Schaefer
