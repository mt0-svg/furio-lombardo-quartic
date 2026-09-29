import Mathlib

/-!
# Square lemmas in ultrametric normed fields with a norm uniformizer

Everything is stated with norms only, for a normed field `F` with an ultrametric norm and a norm
uniformizer `π` (`NormUnif π`: `π ≠ 0`, `‖π‖ < 1`, every nonzero norm is an integer power of `‖π‖`),
with `‖2‖ = ‖π‖ ^ e`. No completeness is used: these are the independence side of the echelon
certificates.

Per component tests, for a finite set `S` of elements whose product is a square:

* `sb_test_val`: the valuation exponents sum to an even number;
* `sb_test_odd`: at an odd depth `t < 2e`, the digit vectors (on residue lifts `w`) sum to `0`;
* `sb_test_four`: at depth `2e` (the form `1 + 4 m`), the trace bits sum to `0`;
* `sb_test_chr`: in odd residue characteristic, the quadratic characters sum to `0`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

/-- A norm uniformizer: `π ≠ 0`, `‖π‖ < 1`, and every nonzero norm is an integer power of `‖π‖`. -/
structure NormUnif {F : Type*} [NormedField F] (π : F) : Prop where
  ne_zero : π ≠ 0
  norm_lt_one : ‖π‖ < 1
  disc : ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n

/-! ## Leaves -/

/-- If every nonzero norm squared is an even power of `‖ϖ‖`, every nonzero norm is a power of `‖ϖ‖`. -/
theorem sb_disc_of_sq {F : Type*} [NormedField F] {ϖ : F} (hϖ0 : ϖ ≠ 0)
    (hsq : ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ ^ 2 = ‖ϖ‖ ^ (2 * n)) :
    ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n := by
  intro x hx0
  rcases hsq x hx0 with ⟨n, h⟩
  refine ⟨n, ?_⟩
  have h_nonneg_x : 0 ≤ ‖x‖ := norm_nonneg _
  have h_nonneg_ϖ : 0 ≤ ‖ϖ‖ := norm_nonneg _
  have h_nonneg_ϖn : 0 ≤ ‖ϖ‖ ^ n := zpow_nonneg h_nonneg_ϖ n
  have h_sq_eq : ‖x‖ ^ 2 = (‖ϖ‖ ^ n) ^ 2 := by
    rw [h, zpow_mul' ‖ϖ‖ 2 n]; rfl
  exact ((sq_eq_sq₀ h_nonneg_x h_nonneg_ϖn).mp h_sq_eq)

/-- In a discretely normed field, an element of norm `‖π‖ ^ k` with `k` odd is not a square. -/
theorem sb_not_isSquare_of_norm_odd {F : Type*} [NormedField F] {π : F} (hπ0 : π ≠ 0)
    (hπ1 : ‖π‖ < 1) (hdisc : ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n) {z : F} {k : ℤ}
    (hz : ‖z‖ = ‖π‖ ^ k) (hk : Odd k) : ¬ IsSquare z := by
  rintro ⟨ξ, hξ⟩
  have hπ_norm_pos : 0 < ‖π‖ := (norm_pos_iff.mpr hπ0)
  have hπ_norm_ne_one : ‖π‖ ≠ 1 := by
    intro h
    linarith
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hz
    have hpos : 0 < ‖π‖ ^ k := zpow_pos hπ_norm_pos k
    linarith
  have hξ0 : ξ ≠ 0 := by
    intro hξ0
    apply hz0
    rw [hξ, hξ0, mul_zero]
  obtain ⟨n, hn⟩ := hdisc ξ hξ0
  have h_norm_eq : ‖π‖ ^ k = ‖π‖ ^ (2 * n) := by
    calc
      ‖π‖ ^ k = ‖z‖ := by rw [← hz]
      _ = ‖ξ * ξ‖ := by rw [hξ]
      _ = ‖ξ‖ * ‖ξ‖ := by rw [norm_mul]
      _ = (‖π‖ ^ n) * (‖π‖ ^ n) := by rw [hn]
      _ = ‖π‖ ^ (n + n) := by rw [← zpow_add₀ (show ‖π‖ ≠ 0 from by linarith) n n]
      _ = ‖π‖ ^ (2 * n) := by rw [two_mul]
  have hk_eq_2n : k = 2 * n := by
    have := (zpow_right_inj₀ hπ_norm_pos hπ_norm_ne_one).mp h_norm_eq
    exact this
  rcases hk with ⟨m, hm⟩
  rw [hk_eq_2n] at hm
  have : (2 : ℤ) * (n - m) = 1 := by
    linarith
  have h_parity : (2 : ℤ) ∣ (1 : ℤ) := by
    rw [← this]
    exact ⟨n - m, rfl⟩
  have : ¬ (2 : ℤ) ∣ (1 : ℤ) := by
    norm_num
  exact this h_parity

/-- In a discretely normed ultrametric field with `‖2‖ = ‖π‖ ^ e`, an element `z` with
`‖z - 1‖ = ‖π‖ ^ t`, `t` odd and `t < 2 e`, is not a square. -/
theorem sb_not_isSquare_of_norm_sub_one {F : Type*} [NormedField F] [IsUltrametricDist F]
    {π : F} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (hdisc : ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n)
    {e t : ℕ} (h2 : ‖(2 : F)‖ = ‖π‖ ^ e) (ht : Odd t) (hte : t < 2 * e) {z : F}
    (hz : ‖z - 1‖ = ‖π‖ ^ t) : ¬ IsSquare z := by
  rintro ⟨ξ, hξ⟩
  set a := ξ - 1 with ha
  have hr0 : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have hr_ne_one : ‖π‖ ≠ 1 := by linarith
  have haz : a ≠ 0 := by
    intro haz
    have hξ1 : ξ = 1 := by
      rw [ha, sub_eq_zero] at haz
      exact haz
    have hz1 : z = 1 := by
      rw [hξ, hξ1]
      simp
    have hz_sub_one : z - 1 = 0 := by rw [hz1, sub_self]
    have hnorm0 : ‖z - 1‖ = 0 := by rw [hz_sub_one, norm_zero]
    rw [hz] at hnorm0
    have hpos : 0 < ‖π‖ ^ t := pow_pos hr0 t
    linarith
  have hprod : a * (a + 2) = z - 1 := by
    dsimp [a]
    rw [hξ]
    ring
  have hnorm_prod : ‖a‖ * ‖a + 2‖ = ‖π‖ ^ t := by
    rw [← norm_mul, hprod, hz]
  rcases hdisc a haz with ⟨n, hn⟩
  have hnorm_2 : ‖(2 : F)‖ = ‖π‖ ^ (e : ℤ) := by
    simpa [zpow_natCast] using h2
  by_cases hlt : ‖a‖ < ‖(2 : F)‖
  · -- Case 1: ‖a‖ < ‖2‖
    have hne : ‖a‖ ≠ ‖(2 : F)‖ := by linarith
    have hnorm_a2 : ‖a + 2‖ = ‖(2 : F)‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_right hlt.le]
    rw [hnorm_a2] at hnorm_prod
    rw [hnorm_2] at hnorm_prod
    rw [hn] at hnorm_prod
    rw [← zpow_add₀ hr0.ne' n (e : ℤ)] at hnorm_prod
    have h_exp_eq : n + (e : ℤ) = (t : ℤ) :=
      (zpow_right_injective₀ hr0 hr_ne_one) hnorm_prod
    rw [hn, hnorm_2] at hlt
    have h_lt_exp : (e : ℤ) < n :=
      ((zpow_lt_zpow_iff_right_of_lt_one₀ hr0 hπ1).mp hlt)
    have h_contra : (t : ℤ) < (2 * e : ℤ) := by exact mod_cast hte
    have h_sum : (2 * e : ℤ) < n + (e : ℤ) := by
      linarith
    rw [h_exp_eq] at h_sum
    linarith
  · -- ‖a‖ ≥ ‖2‖
    push Not at hlt
    by_cases heq : ‖a‖ = ‖(2 : F)‖
    · -- Case 2: ‖a‖ = ‖2‖
      have hnorm_a2_le : ‖a + 2‖ ≤ ‖(2 : F)‖ := by
        have hmax := IsUltrametricDist.norm_add_le_max a (2 : F)
        rw [heq, max_self] at hmax
        exact hmax
      rw [hnorm_2] at hnorm_a2_le heq
      rw [hn] at hnorm_prod heq
      have h_exp_eq : n = (e : ℤ) :=
        (zpow_right_injective₀ hr0 hr_ne_one) heq
      rw [h_exp_eq] at hnorm_prod
      have hprod_le' : (‖π‖ ^ (e : ℤ)) * ‖a + 2‖ ≤ (‖π‖ ^ (e : ℤ)) * (‖π‖ ^ (e : ℤ)) :=
        mul_le_mul_of_nonneg_left hnorm_a2_le (by positivity)
      rw [hnorm_prod] at hprod_le'
      rw [← zpow_add₀ hr0.ne' (e : ℤ) (e : ℤ)] at hprod_le'
      have h_ineq : ((2 * e : ℕ) : ℤ) ≤ (t : ℤ) := by
        have htemp : ‖π‖ ^ (t : ℤ) ≤ ‖π‖ ^ ((2 * e : ℕ) : ℤ) := by
          simpa [zpow_natCast, two_mul, add_comm] using hprod_le'
        exact ((zpow_le_zpow_iff_right_of_lt_one₀ hr0 hπ1).mp htemp)
      have h_contra : (t : ℤ) < ((2 * e : ℕ) : ℤ) := by exact mod_cast hte
      linarith
    · -- Case 3: ‖a‖ > ‖2‖
      have hne : ‖a‖ ≠ ‖(2 : F)‖ := heq
      have hnorm_a2 : ‖a + 2‖ = ‖a‖ := by
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left (by linarith)]
      rw [hnorm_a2] at hnorm_prod
      rw [hn] at hnorm_prod
      rw [← zpow_add₀ hr0.ne' n n] at hnorm_prod
      have h_exp_eq : n + n = (t : ℤ) :=
        (zpow_right_injective₀ hr0 hr_ne_one) hnorm_prod
      rcases ht with ⟨k, hk⟩
      have h_even : (t : ℤ) = 2 * (k : ℤ) + 1 := by exact mod_cast hk
      rw [h_even] at h_exp_eq
      have h_sum : n + n = 2 * n := by ring
      rw [h_sum] at h_exp_eq
      omega

/-- If `1 + 4 m` is a square, with `m` integral, then `m = y ^ 2 + y` with `y` integral. -/
theorem sb_eq_sq_add_self_of_sq {F : Type*} [NormedField F] [IsUltrametricDist F]
    (h2 : (2 : F) ≠ 0) {m ξ : F} (hm : ‖m‖ ≤ 1) (hξ : ξ ^ 2 = 1 + 4 * m) :
    ∃ y : F, ‖y‖ ≤ 1 ∧ m = y ^ 2 + y := by
  set a := ξ - 1 with ha
  have ha_eq : a * (a + 2) = 4 * m := by
    dsimp [a]
    calc
      (ξ - 1) * ((ξ - 1) + 2) = (ξ - 1) * (ξ + 1) := by ring
      _ = ξ ^ 2 - 1 := by ring
      _ = (1 + 4 * m) - 1 := by rw [hξ]
      _ = 4 * m := by ring
  have h_norm_a_le_norm_two : ‖a‖ ≤ ‖(2 : F)‖ := by
    by_contra! h
    -- h : ‖(2 : F)‖ < ‖a‖
    have h_ne : ‖a‖ ≠ ‖(2 : F)‖ := by linarith
    have h_add : ‖a + (2 : F)‖ = max ‖a‖ ‖(2 : F)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
    have h_max_eq : max ‖a‖ ‖(2 : F)‖ = ‖a‖ :=
      max_eq_left (by linarith)
    have h_norm_add : ‖a + (2 : F)‖ = ‖a‖ := by
      rw [h_add, h_max_eq]
    have h_norm_4m : ‖(4 : F) * m‖ = ‖a‖ * ‖a‖ := by
      calc
        ‖(4 : F) * m‖ = ‖a * (a + (2 : F))‖ := by rw [ha_eq]
        _ = ‖a‖ * ‖a + (2 : F)‖ := by rw [norm_mul]
        _ = ‖a‖ * ‖a‖ := by rw [h_norm_add]
    have h_norm_two_nonneg : 0 ≤ ‖(2 : F)‖ := norm_nonneg _
    have h_sq_lt : ‖(2 : F)‖ ^ 2 < ‖a‖ ^ 2 := by
      exact pow_lt_pow_left₀ h h_norm_two_nonneg (by norm_num : 2 ≠ 0)
    have h_norm_four : ‖(4 : F)‖ = ‖(2 : F)‖ * ‖(2 : F)‖ := by
      calc
        ‖(4 : F)‖ = ‖(2 : F) * (2 : F)‖ := by norm_num
        _ = ‖(2 : F)‖ * ‖(2 : F)‖ := by rw [norm_mul]
    have h_norm_4m_le : ‖(4 : F) * m‖ ≤ ‖(4 : F)‖ := by
      calc
        ‖(4 : F) * m‖ = ‖(4 : F)‖ * ‖m‖ := by rw [norm_mul]
        _ ≤ ‖(4 : F)‖ * 1 := mul_le_mul_of_nonneg_left hm (norm_nonneg _)
        _ = ‖(4 : F)‖ := by simp
    have h_contra : ‖(4 : F) * m‖ < ‖(4 : F) * m‖ := by
      calc
        ‖(4 : F) * m‖ = ‖a‖ * ‖a‖ := h_norm_4m
        _ = ‖a‖ ^ 2 := by ring
        _ > ‖(2 : F)‖ ^ 2 := h_sq_lt
        _ = ‖(2 : F)‖ * ‖(2 : F)‖ := by ring
        _ = ‖(4 : F)‖ := by rw [← h_norm_four]
        _ ≥ ‖(4 : F) * m‖ := h_norm_4m_le
    exact lt_irrefl _ h_contra
  set y := a / (2 : F) with hy
  have h_norm_two_ne_zero : ‖(2 : F)‖ ≠ 0 := by
    intro hzero
    apply h2
    exact norm_eq_zero.mp hzero
  have h_norm_two_pos : 0 < ‖(2 : F)‖ := by
    have h_nonneg := norm_nonneg (2 : F)
    exact lt_of_le_of_ne h_nonneg h_norm_two_ne_zero.symm
  refine ⟨y, ?_, ?_⟩
  · -- ‖y‖ ≤ 1
    calc
      ‖y‖ = ‖a / (2 : F)‖ := rfl
      _ = ‖a‖ / ‖(2 : F)‖ := by rw [norm_div]
      _ ≤ ‖(2 : F)‖ / ‖(2 : F)‖ := by
        exact (div_le_div_iff_of_pos_right h_norm_two_pos).mpr h_norm_a_le_norm_two
      _ = 1 := by field_simp [h_norm_two_ne_zero]
  · -- m = y ^ 2 + y
    have h4_ne_zero : (4 : F) ≠ 0 := by
      intro hzero
      have h2sq_zero : (2 : F) * (2 : F) = 0 := by
        calc
          (2 : F) * (2 : F) = (4 : F) := by norm_num
          _ = 0 := hzero
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h2sq_zero with (h | h)
      · exact h2 h
      · exact h2 h
    have h_ay : a = (2 : F) * y := by
      dsimp [y]
      field_simp
    calc
      m = ((4 : F) * m) / (4 : F) := by field_simp [h4_ne_zero]
      _ = (a * (a + (2 : F))) / (4 : F) := by rw [ha_eq]
      _ = (((2 : F) * y) * (((2 : F) * y) + (2 : F))) / (4 : F) := by rw [h_ay]
      _ = ((2 : F) * y * ((2 : F) * (y + 1))) / (4 : F) := by ring
      _ = ((2 : F) * y * (2 : F) * (y + 1)) / (4 : F) := by ring
      _ = ((4 : F) * (y * (y + 1))) / (4 : F) := by ring
      _ = y * (y + 1) := by field_simp [h4_ne_zero]
      _ = y ^ 2 + y := by ring

/-- A finite product of elements `1 + a y_i`, with `‖a‖ < 1` and `y_i` within norm `< 1` of an
integral `u_i`, is `1 + a (∑ u_i + ρ)` with `‖ρ‖ < 1`. -/
theorem sb_prod_one_add_mul {F : Type*} [NormedField F] [IsUltrametricDist F] {α : Type*}
    (S : Finset α) {a : F} (ha : ‖a‖ < 1) (u y : α → F) (hu : ∀ i ∈ S, ‖u i‖ ≤ 1)
    (hy : ∀ i ∈ S, ‖y i - u i‖ < 1) :
    ∃ ρ : F, ‖ρ‖ < 1 ∧ ∏ i ∈ S, (1 + a * y i) = 1 + a * (∑ i ∈ S, u i + ρ) := by
  classical
  -- Helper: in an ultrametric normed additive group, the sum of elements each with norm ≤ 1
  -- also has norm ≤ 1
  have hsum_norm_le_one (t : Finset α) (f : α → F) (hf : ∀ i ∈ t, ‖f i‖ ≤ 1) :
      ‖∑ i ∈ t, f i‖ ≤ 1 := by
    induction' t using Finset.induction_on with k t hk IH
    · simp
    · simp only [Finset.sum_insert hk]
      have hk_norm : ‖f k‖ ≤ 1 := hf k (Finset.mem_insert_self k t)
      have hsum_norm : ‖∑ i ∈ t, f i‖ ≤ 1 := IH fun i hi => hf i (Finset.mem_insert_of_mem hi)
      calc
        ‖f k + ∑ i ∈ t, f i‖ ≤ max ‖f k‖ ‖∑ i ∈ t, f i‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max 1 1 := max_le_max hk_norm hsum_norm
        _ = 1 := by norm_num

  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, by simp, ?_⟩
      simp
  | insert j S hjS IH =>
      have hmem_insert : ∀ i ∈ insert j S, ‖u i‖ ≤ 1 := hu
      have hmem_insert_y : ∀ i ∈ insert j S, ‖y i - u i‖ < 1 := hy
      have hu_S : ∀ i ∈ S, ‖u i‖ ≤ 1 := fun i hi => hmem_insert i (Finset.mem_insert_of_mem hi)
      have hy_S : ∀ i ∈ S, ‖y i - u i‖ < 1 := fun i hi => hmem_insert_y i (Finset.mem_insert_of_mem hi)
      rcases IH hu_S hy_S with ⟨ρ, hρ, hprod⟩
      set U := ∑ i ∈ S, u i with hU
      set ρ' := ρ + (y j - u j) + a * (U + ρ) * y j with hρ'
      have hU_le_one : ‖U‖ ≤ 1 := by
        simpa [hU] using hsum_norm_le_one S u (fun i hi => hmem_insert i (Finset.mem_insert_of_mem hi))
      have hyj_norm_le_one : ‖y j‖ ≤ 1 := by
        have h1 : ‖u j‖ ≤ 1 := hmem_insert j (Finset.mem_insert_self j S)
        have h2 : ‖y j - u j‖ < 1 := hmem_insert_y j (Finset.mem_insert_self j S)
        calc
          ‖y j‖ = ‖(y j - u j) + u j‖ := by simp
          _ ≤ max ‖y j - u j‖ ‖u j‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ max 1 1 := by
            exact max_le_max (by linarith) h1
          _ = 1 := by simp
      have hUprho_norm_le_one : ‖U + ρ‖ ≤ 1 := by
        calc
          ‖U + ρ‖ ≤ max ‖U‖ ‖ρ‖ := IsUltrametricDist.norm_add_le_max _ _
          _ ≤ max 1 1 := max_le_max hU_le_one (by linarith)
          _ = 1 := by simp
      have h_termp_norm_lt_one : ‖a * (U + ρ) * y j‖ < 1 := by
        calc
          ‖a * (U + ρ) * y j‖ = ‖a‖ * ‖U + ρ‖ * ‖y j‖ := by
            simp [norm_mul]
          _ = ‖a‖ * (‖U + ρ‖ * ‖y j‖) := by ring
          _ ≤ ‖a‖ * (1 * 1) := by
            have h_nonneg_a : 0 ≤ ‖a‖ := norm_nonneg _
            have h_nonneg_yj : 0 ≤ ‖y j‖ := norm_nonneg _
            have h_inner : ‖U + ρ‖ * ‖y j‖ ≤ 1 * 1 :=
              mul_le_mul hUprho_norm_le_one hyj_norm_le_one h_nonneg_yj (by norm_num)
            exact mul_le_mul_of_nonneg_left h_inner h_nonneg_a
          _ = ‖a‖ := by ring
          _ < 1 := ha
      have h_rho'_lt_one : ‖ρ'‖ < 1 := by
        have hsum1 : max ‖ρ‖ ‖y j - u j‖ < 1 := by
          refine max_lt hρ (hmem_insert_y j (Finset.mem_insert_self j S))
        have hsum2 : max ‖ρ‖ ‖y j - u j‖ < max (max 1 1) 1 := by
          simpa [show max (max (1 : ℝ) 1) 1 = 1 by norm_num] using hsum1
        have hterm : ‖a * (U + ρ) * y j‖ < max (max 1 1) 1 := by
          simpa [show max (max (1 : ℝ) 1) 1 = 1 by norm_num] using h_termp_norm_lt_one
        calc
          ‖ρ'‖ = ‖(ρ + (y j - u j)) + a * (U + ρ) * y j‖ := by
            simp [hρ', add_assoc]
          _ ≤ max ‖ρ + (y j - u j)‖ ‖a * (U + ρ) * y j‖ :=
            IsUltrametricDist.norm_add_le_max _ _
          _ ≤ max (max ‖ρ‖ ‖y j - u j‖) ‖a * (U + ρ) * y j‖ := by
            gcongr
            exact IsUltrametricDist.norm_add_le_max _ _
          _ < max (max 1 1) 1 := max_lt hsum2 hterm
          _ = 1 := by norm_num
      have h_prod : ∏ i ∈ insert j S, (1 + a * y i) = 1 + a * (∑ i ∈ insert j S, u i + ρ') := by
        calc
          ∏ i ∈ insert j S, (1 + a * y i) = (1 + a * y j) * ∏ i ∈ S, (1 + a * y i) := by
            rw [Finset.prod_insert hjS]
          _ = (1 + a * y j) * (1 + a * (U + ρ)) := by
            rw [hprod, hU]
          _ = (1 + a * (U + ρ)) + (a * y j) * (1 + a * (U + ρ)) := by ring
          _ = 1 + a * (U + ρ) + a * y j + a * (U + ρ) * (a * y j) := by ring
          _ = 1 + a * (U + ρ + y j) + a ^ 2 * (U + ρ) * y j := by ring
          _ = 1 + a * (U + u j + (ρ + (y j - u j) + a * (U + ρ) * y j)) := by
            ring
          _ = 1 + a * ((u j + ∑ i ∈ S, u i) + ρ') := by
            simp [hU, hρ', add_comm, add_assoc]
          _ = 1 + a * (∑ i ∈ insert j S, u i + ρ') := by
            simp [Finset.sum_insert hjS, add_comm, add_assoc]
      exact ⟨ρ', h_rho'_lt_one, h_prod⟩

/-- Summing digit vectors lifted with integral weights `w`: the sum of the lifts is the lift of
the `ZMod 2` sum plus `2 m` with `m` integral. -/
theorem sb_sum_liftV {F : Type*} [NormedField F] [IsUltrametricDist F] {α : Type*} {f : ℕ}
    (S : Finset α) (w : Fin f → F) (hw : ∀ l, ‖w l‖ ≤ 1) (V : α → Fin f → ZMod 2) :
    ∃ m : F, ‖m‖ ≤ 1 ∧
      ∑ i ∈ S, ∑ l, ((V i l).val : F) * w l = ∑ l, ((∑ i ∈ S, V i l).val : F) * w l + 2 * m := by
  -- Swap the double sum so that the outer sum is over l
  rw [Finset.sum_comm]
  -- Factor w l out of each inner sum: ∑_i (a_i * w l) = (∑_i a_i) * w l
  simp_rw [← Finset.sum_mul]
  -- Move the Nat.cast inside the inner sum: ∑_i ((V i l).val : F) = (∑_i (V i l).val : F)
  simp_rw [← Nat.cast_sum]
  -- Define N_l = ∑_i (V i l).val (in ℕ)
  set N := fun (l : Fin f) => ∑ i ∈ S, (V i l).val with hN
  -- Key identity: (∑ V i l).val = N l % 2 (in ℕ), then cast to F
  have hN_val : ∀ l : Fin f, ((∑ i ∈ S, V i l).val : F) = ((N l % 2 : ℕ) : F) := by
    intro l
    have h_eq : (N l : ZMod 2) = ∑ i ∈ S, V i l := by
      dsimp [N]
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ZMod.natCast_zmod_val]
    calc
      ((∑ i ∈ S, V i l).val : F) = (((∑ i ∈ S, V i l).val : ℕ) : F) := by norm_num
      _ = (((N l : ZMod 2).val : ℕ) : F) := by rw [h_eq]
      _ = (((N l) % 2 : ℕ) : F) := by rw [ZMod.val_natCast]
  -- Decompose N l = N l % 2 + 2 * (N l / 2) and cast to F
  have h_decomp : ∀ l : Fin f, (N l : F) = ((N l % 2 : ℕ) : F) + 2 * ((N l / 2 : ℕ) : F) := by
    intro l
    have h_mod_div := Nat.mod_add_div (N l) 2
    calc
      (N l : F) = ((N l % 2 + 2 * (N l / 2) : ℕ) : F) := by rw [h_mod_div]
      _ = ((N l % 2 : ℕ) : F) + ((2 * (N l / 2) : ℕ) : F) := by rw [Nat.cast_add]
      _ = ((N l % 2 : ℕ) : F) + ((2 : ℕ) : F) * ((N l / 2 : ℕ) : F) := by rw [Nat.cast_mul]
      _ = ((N l % 2 : ℕ) : F) + 2 * ((N l / 2 : ℕ) : F) := by norm_num
  -- Define m = ∑_l ((N l / 2 : ℕ) : F) * w l
  set m := ∑ l : Fin f, ((N l / 2 : ℕ) : F) * w l with hm
  refine ⟨m, ?_, ?_⟩
  · -- Show ‖m‖ ≤ 1 using the ultrametric inequality
    have hterm : ∀ l : Fin f, ‖((N l / 2 : ℕ) : F) * w l‖ ≤ 1 := by
      intro l
      rw [norm_mul]
      have h_cast : ‖((N l / 2 : ℕ) : F)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (R := F) (N l / 2)
      have h_nonneg_w : 0 ≤ ‖w l‖ := norm_nonneg _
      have h_nonneg_one : 0 ≤ (1 : ℝ) := by norm_num
      have h_mul : ‖((N l / 2 : ℕ) : F)‖ * ‖w l‖ ≤ 1 * 1 :=
        mul_le_mul h_cast (hw l) h_nonneg_w h_nonneg_one
      simpa [mul_one] using h_mul
    have hterm' : ∀ l ∈ (Finset.univ : Finset (Fin f)), ‖((N l / 2 : ℕ) : F) * w l‖ ≤ 1 := by
      intro l hl
      exact hterm l
    dsimp [m]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) hterm'
  · -- Show the equality
    calc
      ∑ l : Fin f, (N l : F) * w l = ∑ l : Fin f, (((N l % 2 : ℕ) : F) + 2 * ((N l / 2 : ℕ) : F)) * w l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [h_decomp l]
      _ = ∑ l : Fin f, (((N l % 2 : ℕ) : F) * w l + (2 * ((N l / 2 : ℕ) : F)) * w l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [add_mul]
      _ = (∑ l : Fin f, ((N l % 2 : ℕ) : F) * w l) + (∑ l : Fin f, (2 * ((N l / 2 : ℕ) : F)) * w l) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ l : Fin f, ((N l % 2 : ℕ) : F) * w l) + (∑ l : Fin f, 2 * (((N l / 2 : ℕ) : F) * w l)) := by
        refine congrArg (fun t => (∑ l : Fin f, ((N l % 2 : ℕ) : F) * w l) + t) ?_
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
      _ = (∑ l : Fin f, ((N l % 2 : ℕ) : F) * w l) + 2 * (∑ l : Fin f, ((N l / 2 : ℕ) : F) * w l) := by
        rw [Finset.mul_sum]
      _ = (∑ l : Fin f, ((∑ i ∈ S, V i l).val : F) * w l) + 2 * m := by
        simp_rw [hN_val]
        rw [hm]
      _ = ∑ l, ((∑ i ∈ S, V i l).val : F) * w l + 2 * m := rfl

/-- A deeper datum is a datum of digit `0` at a smaller depth. -/
theorem sb_depth_mono {F : Type*} [NormedField F] [IsUltrametricDist F] {π : F}
    (hπ1 : ‖π‖ < 1) {t t' : ℕ} (htt : t < t') {z W : F} (hW : ‖W‖ ≤ 1)
    (hz : ‖z - 1 - π ^ t' * W‖ < ‖π‖ ^ t') : ‖z - 1‖ < ‖π‖ ^ t := by
  have hπ_nonneg : 0 ≤ ‖π‖ := norm_nonneg _
  have ht'_pos : 0 < t' := Nat.pos_of_ne_zero (by
    intro hzero
    have : t < 0 := by simpa [hzero] using htt
    exact Nat.not_lt_zero _ this)
  have hπ_pos : 0 < ‖π‖ := by
    by_contra! h
    have hzero : ‖π‖ = 0 := by linarith
    have hzero_pow : ‖π‖ ^ t' = 0 := by
      rw [hzero]
      exact zero_pow ht'_pos.ne.symm
    have h_neg : ‖z - 1 - π ^ t' * W‖ < 0 := by
      simpa [hzero_pow] using hz
    have h_nonneg : 0 ≤ ‖z - 1 - π ^ t' * W‖ := norm_nonneg _
    linarith
  have h_pow_lt : ‖π‖ ^ t' < ‖π‖ ^ t :=
    pow_lt_pow_right_of_lt_one₀ hπ_pos hπ1 htt
  have h_norm_pow : ‖π ^ t' * W‖ ≤ ‖π‖ ^ t' := by
    calc
      ‖π ^ t' * W‖ = ‖π ^ t'‖ * ‖W‖ := NormedField.norm_mul _ _
      _ = ‖π‖ ^ t' * ‖W‖ := by rw [norm_pow]
      _ ≤ ‖π‖ ^ t' * 1 := mul_le_mul_of_nonneg_left hW (pow_nonneg hπ_nonneg _)
      _ = ‖π‖ ^ t' := by simp
  have h_first_bound : ‖z - 1 - π ^ t' * W‖ ≤ ‖π‖ ^ t' := by linarith
  have h_max_bound : max ‖z - 1 - π ^ t' * W‖ ‖π ^ t' * W‖ ≤ ‖π‖ ^ t' :=
    max_le h_first_bound h_norm_pow
  have h_eq : (z - 1 - π ^ t' * W) + (π ^ t' * W) = z - 1 := by ring
  calc
    ‖z - 1‖ = ‖(z - 1 - π ^ t' * W) + (π ^ t' * W)‖ := by rw [h_eq]
    _ ≤ max ‖z - 1 - π ^ t' * W‖ ‖π ^ t' * W‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ ‖π‖ ^ t' := h_max_bound
    _ < ‖π‖ ^ t := h_pow_lt

/-- A datum of the form `1 + 4 m` is a datum of digit `0` at every depth `t` with `‖4‖ < ‖π‖ ^ t`. -/
theorem sb_depth_four {F : Type*} [NormedField F] [IsUltrametricDist F] {π : F} {t : ℕ}
    (h4 : ‖(4 : F)‖ < ‖π‖ ^ t) {z W : F} (hW : ‖W‖ ≤ 1)
    (hz : ‖z - 1 - 4 * W‖ < ‖(4 : F)‖) : ‖z - 1‖ < ‖π‖ ^ t := by
  have h_eq : z - 1 = (z - 1 - 4 * W) + 4 * W := by ring
  rw [h_eq]
  have h_le : ‖(z - 1 - 4 * W) + 4 * W‖ ≤ max (‖z - 1 - 4 * W‖) (‖4 * W‖) :=
    IsUltrametricDist.norm_add_le_max _ _
  have h_norm_mul : ‖4 * W‖ ≤ ‖(4 : F)‖ := by
    calc
      ‖4 * W‖ ≤ ‖(4 : F)‖ * ‖W‖ := norm_mul_le _ _
      _ ≤ ‖(4 : F)‖ * 1 := mul_le_mul_of_nonneg_left hW (norm_nonneg _)
      _ = ‖(4 : F)‖ := mul_one _
  have h_max_le : max (‖z - 1 - 4 * W‖) (‖4 * W‖) ≤ ‖(4 : F)‖ :=
    max_le hz.le h_norm_mul
  have h_total : ‖(z - 1 - 4 * W) + 4 * W‖ ≤ ‖(4 : F)‖ :=
    le_trans h_le h_max_le
  linarith

/-- In a normed field, if each factor has norm ≤ 1, then the product has norm ≤ 1. -/
lemma norm_prod_le_one {F : Type*} [NormedField F] {α : Type*} (S : Finset α) (f : α → F)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) : ‖∏ i ∈ S, f i‖ ≤ 1 := by
  classical
    induction' S using Finset.induction with j S hj ih
    · simp
    · rw [Finset.prod_insert hj, norm_mul]
      have hjf : ‖f j‖ ≤ 1 := hf j (Finset.mem_insert_self j S)
      have hSf : ‖∏ i ∈ S, f i‖ ≤ 1 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      have h_nonneg_j : 0 ≤ ‖f j‖ := norm_nonneg _
      have h_nonneg_S : 0 ≤ ‖∏ i ∈ S, f i‖ := norm_nonneg _
      nlinarith


/-- Products of close integral elements are close. -/
theorem sb_prod_sub_lt {F : Type*} [NormedField F] [IsUltrametricDist F] {α : Type*}
    (S : Finset α) (a b : α → F) (ha : ∀ i ∈ S, ‖a i‖ ≤ 1) (hb : ∀ i ∈ S, ‖b i‖ ≤ 1)
    (hab : ∀ i ∈ S, ‖a i - b i‖ < 1) : ‖∏ i ∈ S, a i - ∏ i ∈ S, b i‖ < 1 := by
  classical
    induction' S using Finset.induction with j S hj ih
    · simp
    · rw [Finset.prod_insert hj, Finset.prod_insert hj]
      have haj : ‖a j‖ ≤ 1 := ha j (Finset.mem_insert_self j S)
      have hbj : ‖b j‖ ≤ 1 := hb j (Finset.mem_insert_self j S)
      have hajb : ‖a j - b j‖ < 1 := hab j (Finset.mem_insert_self j S)
      have hA : ‖∏ i ∈ S, a i‖ ≤ 1 :=
        norm_prod_le_one S a (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      have hB : ‖∏ i ∈ S, b i‖ ≤ 1 :=
        norm_prod_le_one S b (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      have hAB : ‖∏ i ∈ S, a i - ∏ i ∈ S, b i‖ < 1 := ih
        (fun i hi => ha i (Finset.mem_insert_of_mem hi))
        (fun i hi => hb i (Finset.mem_insert_of_mem hi))
        (fun i hi => hab i (Finset.mem_insert_of_mem hi))
      have h_eq : a j * (∏ i ∈ S, a i) - b j * (∏ i ∈ S, b i) =
          a j * ((∏ i ∈ S, a i) - (∏ i ∈ S, b i)) + (a j - b j) * (∏ i ∈ S, b i) := by
        ring
      rw [h_eq]
      apply lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
      apply max_lt ?_ ?_
      · rw [norm_mul]
        have h_nonneg_aj : 0 ≤ ‖a j‖ := norm_nonneg _
        have h_nonneg_diff : 0 ≤ ‖(∏ i ∈ S, a i) - (∏ i ∈ S, b i)‖ := norm_nonneg _
        have h1 : ‖a j‖ * ‖(∏ i ∈ S, a i) - (∏ i ∈ S, b i)‖ ≤
            1 * ‖(∏ i ∈ S, a i) - (∏ i ∈ S, b i)‖ :=
          mul_le_mul_of_nonneg_right haj h_nonneg_diff
        have h2 : 1 * ‖(∏ i ∈ S, a i) - (∏ i ∈ S, b i)‖ < 1 := by
          nlinarith
        nlinarith
      · rw [norm_mul]
        have h_nonneg_diff : 0 ≤ ‖a j - b j‖ := norm_nonneg _
        have h_nonneg_B : 0 ≤ ‖∏ i ∈ S, b i‖ := norm_nonneg _
        by_cases hBzero : ‖∏ i ∈ S, b i‖ = 0
        · rw [hBzero, mul_zero]
          norm_num
        · have hBpos : 0 < ‖∏ i ∈ S, b i‖ := lt_of_le_of_ne h_nonneg_B (Ne.symm hBzero)
          have h1 : ‖a j - b j‖ * ‖∏ i ∈ S, b i‖ < 1 * 1 :=
            mul_lt_mul hajb hB hBpos (by norm_num)
          nlinarith

/-- Valuation parity test: if `∏ x i` is a square and `‖x i‖ = ‖π‖ ^ k i`, then `∑ k i` is even. -/
theorem sb_test_val {F : Type*} [NormedField F] {π : F} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hdisc : ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n) {α : Type*} (S : Finset α) (x : α → F)
    (k : α → ℤ) (hx : ∀ i ∈ S, ‖x i‖ = ‖π‖ ^ k i) (hsq : IsSquare (∏ i ∈ S, x i)) :
    (∑ i ∈ S, (k i : ZMod 2)) = 0 := by
  classical

  have hpos : 0 < ‖π‖ := by
    have h := norm_ne_zero_iff.mpr hπ0
    have h' : 0 ≤ ‖π‖ := norm_nonneg _
    exact h'.lt_of_ne h.symm

  have h_ne_one : ‖π‖ ≠ 1 := by linarith

  have hnorm_prod : ‖∏ i ∈ S, x i‖ = ∏ i ∈ S, ‖x i‖ := norm_prod _ _

  have hnorm_prod' : ‖∏ i ∈ S, x i‖ = ∏ i ∈ S, (‖π‖ ^ k i) := by
    rw [hnorm_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hx i hi]

  have h_prod_zpow_eq : ∏ i ∈ S, (‖π‖ ^ k i) = ‖π‖ ^ (∑ i ∈ S, k i) := by
    refine Finset.induction_on S ?_ ?_
    · simp
    · intro a S' haS' ih
      simp [Finset.sum_insert haS', Finset.prod_insert haS', ih, zpow_add₀ hpos.ne.symm]

  rcases hsq with ⟨ξ, hξ⟩

  have hξ0 : ξ ≠ 0 := by
    intro hzero
    have hprod_zero : ∏ i ∈ S, x i = 0 := by
      rw [hξ, hzero, zero_mul]
    have hnorm_zero : ‖∏ i ∈ S, x i‖ = 0 := by rw [hprod_zero, norm_zero]
    have hnorm_pow_ne_zero : ‖∏ i ∈ S, x i‖ ≠ 0 := by
      rw [hnorm_prod', h_prod_zpow_eq]
      exact zpow_ne_zero (∑ i ∈ S, k i) hpos.ne.symm
    exact hnorm_pow_ne_zero hnorm_zero

  rcases hdisc ξ hξ0 with ⟨n, hn⟩

  have h_eq_pow : ‖π‖ ^ (∑ i ∈ S, k i) = ‖π‖ ^ (2 * n) := by
    calc
      ‖π‖ ^ (∑ i ∈ S, k i) = ∏ i ∈ S, (‖π‖ ^ k i) := by rw [h_prod_zpow_eq]
      _ = ‖∏ i ∈ S, x i‖ := by rw [← hnorm_prod']
      _ = ‖ξ * ξ‖ := by rw [hξ]
      _ = ‖ξ‖ * ‖ξ‖ := norm_mul ξ ξ
      _ = (‖π‖ ^ n) * (‖π‖ ^ n) := by rw [hn]
      _ = ‖π‖ ^ (n + n) := by rw [zpow_add₀ hpos.ne.symm n n]
      _ = ‖π‖ ^ (2 * n) := by ring_nf

  have h_sum_eq : (∑ i ∈ S, k i) = 2 * n :=
    (zpow_right_injective₀ hpos h_ne_one) h_eq_pow

  calc
    (∑ i ∈ S, (k i : ZMod 2)) = ((∑ i ∈ S, k i : ℤ) : ZMod 2) := by simp
    _ = ((2 * n : ℤ) : ZMod 2) := by rw [h_sum_eq]
    _ = (0 : ZMod 2) := by
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]

/-! ## The unit tests -/

/-- Odd depth test. If `∏ x i` is a square and `x i / s i ^ 2 = 1 + π ^ t (∑ V i l w l) + O(π ^ (t+1))`
with `t` odd, `t < 2 e`, and lifts `w` independent modulo `𝔪`, then `∑ V i = 0`. -/
theorem sb_test_odd {F : Type*} [NormedField F] [IsUltrametricDist F] {π : F} (hπ0 : π ≠ 0)
    (hπ1 : ‖π‖ < 1) (hdisc : ∀ x : F, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n) {e t : ℕ}
    (h2 : ‖(2 : F)‖ = ‖π‖ ^ e) (ht : Odd t) (hte : t < 2 * e) {f : ℕ} (w : Fin f → F)
    (hw : ∀ l, ‖w l‖ ≤ 1)
    (hwind : ∀ C : Fin f → ZMod 2, C ≠ 0 → ‖∑ l, ((C l).val : F) * w l‖ = 1)
    {α : Type*} (S : Finset α) (x s : α → F) (V : α → Fin f → ZMod 2)
    (hx : ∀ i ∈ S, ‖x i / s i ^ 2 - 1 - π ^ t * ∑ l, ((V i l).val : F) * w l‖ < ‖π‖ ^ t)
    (hsq : IsSquare (∏ i ∈ S, x i)) : ∑ i ∈ S, V i = 0 := by
  open IsUltrametricDist in
  · by_contra! hsum
    -- hsum : ∑ i ∈ S, V i ≠ 0
    -- t is odd, so t ≥ 1
    have ht_pos : 1 ≤ t := by
      rcases ht with ⟨k, h⟩
      omega
    -- t < 2*e implies e ≥ 1
    have he_pos : 1 ≤ e := by
      by_contra! h
      have he0 : e = 0 := by omega
      subst he0
      have : t < 0 := by omega
      exact Nat.not_lt_zero _ this
    -- ‖π‖^t < 1
    have hπt_norm_lt_one : ‖π‖ ^ t < 1 := by
      have hπ_nonneg : 0 ≤ ‖π‖ := norm_nonneg _
      have hπ_le_one : ‖π‖ ≤ 1 := by linarith
      have hpow : ‖π‖ ^ t ≤ ‖π‖ ^ 1 :=
        pow_le_pow_of_le_one hπ_nonneg hπ_le_one ht_pos
      have hπ_one_lt_one : ‖π‖ ^ 1 < 1 := by simpa [pow_one] using hπ1
      exact lt_of_le_of_lt hpow hπ_one_lt_one
    -- ‖π^t‖ < 1
    have hnorm_πt_lt_one : ‖π ^ t‖ < 1 := by
      rw [norm_pow]
      exact hπt_norm_lt_one
    -- ‖π^t‖ > 0 (needed for division)
    have hnorm_πt_pos : 0 < ‖π ^ t‖ := by
      by_contra! hle
      -- hle : ‖π ^ t‖ ≤ 0
      have h_nonneg_πt : 0 ≤ ‖π ^ t‖ := norm_nonneg _
      have hzero : ‖π ^ t‖ = 0 := by linarith
      -- S must be nonempty, otherwise ∑ V i = 0 contradicting hsum
      have hS_nonempty : S.Nonempty := by
        by_contra! hS_empty
        -- hS_empty : S = ∅ (by_contra! pushes the negation)
        have hsum_zero : ∑ i ∈ S, V i = 0 := by
          rw [hS_empty]
          simp
        exact hsum hsum_zero
      obtain ⟨i, hi⟩ := hS_nonempty
      have hx_i := hx i hi
      rw [norm_pow] at hzero
      -- hzero : ‖π‖ ^ t = 0
      rw [hzero] at hx_i
      -- hx_i : ‖...‖ < 0
      have h_nonneg : 0 ≤ ‖x i / s i ^ 2 - 1 - π ^ t * ∑ l, ((V i l).val : F) * w l‖ := norm_nonneg _
      linarith
    -- ‖2‖ < 1
    have hnorm_two_lt_one : ‖(2 : F)‖ < 1 := by
      rw [h2]
      have hπ_nonneg : 0 ≤ ‖π‖ := norm_nonneg _
      have hπ_le_one : ‖π‖ ≤ 1 := by linarith
      have hpow : ‖π‖ ^ e ≤ ‖π‖ ^ 1 :=
        pow_le_pow_of_le_one hπ_nonneg hπ_le_one he_pos
      have hπ_one_lt_one : ‖π‖ ^ 1 < 1 := by simpa [pow_one] using hπ1
      have htemp : ‖π‖ ^ e < 1 := lt_of_le_of_lt hpow hπ_one_lt_one
      exact htemp
    -- Define u i = ∑ l, ((V i l).val : F) * w l
    set u := λ i => ∑ l, ((V i l).val : F) * w l with hu_def
    -- Define y i = (x i / s i ^ 2 - 1) / π ^ t
    set y := λ i => (x i / s i ^ 2 - 1) / π ^ t with hy_def
    -- Basic norm properties of u
    have hu_norm : ∀ i, ‖u i‖ ≤ 1 := by
      intro i
      dsimp [u]
      -- Each term has norm ≤ 1
      have h_each : ∀ l, ‖((V i l).val : F) * w l‖ ≤ 1 := by
        intro l
        have hval_norm : ‖((V i l).val : F)‖ ≤ 1 := by
          have hval_lt_two : (V i l).val < 2 := ZMod.val_lt _
          have hval_le_one : (V i l).val ≤ 1 := by omega
          -- Now (V i l).val is 0 or 1
          have h_cases : (V i l).val = 0 ∨ (V i l).val = 1 := by omega
          rcases h_cases with (h | h)
          · -- val = 0
            have : ((V i l).val : F) = (0 : F) := by simpa [h]
            rw [this]
            simp
          · -- val = 1
            have : ((V i l).val : F) = (1 : F) := by simpa [h]
            rw [this]
            simp
        calc
          ‖((V i l).val : F) * w l‖ = ‖((V i l).val : F)‖ * ‖w l‖ := norm_mul _ _
          _ ≤ 1 * 1 := mul_le_mul hval_norm (hw l) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      -- Use the ultrametric sum lemma
      refine norm_sum_le_of_forall_le_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) ?_
      intro l hl
      -- hl : l ∈ Finset.univ (since we're summing over all Fin f)
      -- But h_each expects l : Fin f, and h_each l gives the bound
      -- Actually, the sum is over all l : Fin f, so we need to provide the bound for each l
      -- The Finset is Finset.univ
      -- h_each l works
      exact h_each l
    -- x i / s i ^ 2 = 1 + π^t * y i
    have hy_eq : ∀ i, x i / s i ^ 2 = 1 + π ^ t * y i := by
      intro i
      dsimp [y]
      field_simp [hπ0, pow_ne_zero t hπ0]
      ring
    -- ‖y i - u i‖ < 1 for i ∈ S
    have hy_norm : ∀ i ∈ S, ‖y i - u i‖ < 1 := by
      intro i hi
      dsimp [y, u]
      -- y i - u i = ((x i / s i ^ 2 - 1) - π^t * (∑ l, ((V i l).val : F) * w l)) / π^t
      have h_num : (x i / s i ^ 2 - 1) / π ^ t - ∑ l, ((V i l).val : F) * w l =
          ((x i / s i ^ 2 - 1) - π ^ t * (∑ l, ((V i l).val : F) * w l)) / π ^ t := by
        field_simp [pow_ne_zero t hπ0]
      rw [h_num]
      rw [norm_div]
      -- Now we have: ‖...‖ / ‖π^t‖ < 1
      -- From hx i hi: ‖x i / s i ^ 2 - 1 - π^t * (∑ l, ...)‖ < ‖π‖^t
      have hx_i := hx i hi
      -- hx_i : ‖x i / s i ^ 2 - 1 - π ^ t * ∑ l, ((V i l).val : F) * w l‖ < ‖π‖ ^ t
      -- We need: ‖...‖ / ‖π^t‖ < 1
      -- Since ‖π^t‖ = ‖π‖^t (by norm_pow), we can rewrite
      rw [norm_pow]
      -- Now goal: ‖...‖ / (‖π‖ ^ t) < 1
      -- And hx_i: ‖...‖ < ‖π‖ ^ t
      -- Using div_lt_one: a / b < 1 ↔ a < b when b > 0
      -- But we need 0 < ‖π‖ ^ t, which follows from hnorm_πt_pos and norm_pow
      have hpos : 0 < ‖π‖ ^ t := by
        rw [← norm_pow]
        exact hnorm_πt_pos
      exact (div_lt_one hpos).mpr hx_i
    -- Z = ∏ (x i / s i ^ 2) is a square
    have hZ_sq : IsSquare (∏ i ∈ S, (x i / s i ^ 2)) := by
      rcases hsq with ⟨r, hr⟩
      -- hr : ∏ i ∈ S, x i = r * r
      refine ⟨r / ∏ i ∈ S, s i, ?_⟩
      calc
        ∏ i ∈ S, (x i / s i ^ 2) = (∏ i ∈ S, x i) / (∏ i ∈ S, s i ^ 2) := by
          rw [Finset.prod_div_distrib]
        _ = (∏ i ∈ S, x i) / ((∏ i ∈ S, s i) ^ 2) := by
          rw [Finset.prod_pow]
        _ = (r * r) / ((∏ i ∈ S, s i) ^ 2) := by rw [hr]
        _ = (r / ∏ i ∈ S, s i) * (r / ∏ i ∈ S, s i) := by ring
    -- Apply sb_prod_one_add_mul
    obtain ⟨ρ, hρ_norm, hZ_eq⟩ := sb_prod_one_add_mul S hnorm_πt_lt_one u y
      (by intro i hi; exact hu_norm i) (by intro i hi; exact hy_norm i hi)
    -- hZ_eq : ∏ i ∈ S, (1 + π ^ t * y i) = 1 + π ^ t * (∑ i ∈ S, u i + ρ)
    -- But we also have x i / s i ^ 2 = 1 + π^t * y i
    -- So ∏ (x i / s i ^ 2) = ∏ (1 + π^t * y i) = 1 + π^t * (∑ u i + ρ)
    have hZ_eq' : ∏ i ∈ S, (x i / s i ^ 2) = 1 + π ^ t * (∑ i ∈ S, u i + ρ) := by
      calc
        ∏ i ∈ S, (x i / s i ^ 2) = ∏ i ∈ S, (1 + π ^ t * y i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hy_eq i]
        _ = 1 + π ^ t * (∑ i ∈ S, u i + ρ) := hZ_eq
    -- Apply sb_sum_liftV
    obtain ⟨m, hm_norm, hsum_eq⟩ := sb_sum_liftV S w hw V
    -- hsum_eq : ∑ i ∈ S, u i = ∑ l, ((∑ i ∈ S, V i l).val : F) * w l + 2 * m
    -- Let T = ∑ l, ((∑ i ∈ S, V i l).val : F) * w l
    set T := ∑ l, (((∑ i ∈ S, V i) l).val : F) * w l with hT_def
    have hT_norm : ‖T‖ = 1 := by
      dsimp [T]
      -- (∑ i ∈ S, V i) l = ∑ i ∈ S, V i l  by Finset.sum_apply
      -- So we can rewrite the inner expression
      have := hwind (∑ i ∈ S, V i) hsum
      -- this : ‖∑ l, (((∑ i ∈ S, V i) l).val : F) * w l‖ = 1
      -- But hwind expects the sum to be exactly of the form ∑ l, (C l).val * w l
      -- Our T has ((∑ i ∈ S, V i) l).val, which is (C l).val where C = ∑ V i
      -- So we can just use hwind directly
      simpa [Finset.sum_apply] using hwind (∑ i ∈ S, V i) hsum
    -- Now ∑ u i + ρ = T + (2*m + ρ)
    have hsum_u_ρ_eq : ∑ i ∈ S, u i + ρ = T + (2 * m + ρ) := by
      rw [hsum_eq]
      dsimp [T]
      -- Goal: (∑ l, ((∑ i ∈ S, V i l).val : F) * w l + 2 * m) + ρ = (∑ l, (((∑ i ∈ S, V i) l).val : F) * w l) + (2 * m + ρ)
      -- The two sums are equal by Finset.sum_apply
      have hsum_eq_inner : (∑ l, ((∑ i ∈ S, V i l).val : F) * w l) = (∑ l, (((∑ i ∈ S, V i) l).val : F) * w l) := by
        refine Finset.sum_congr rfl (λ l hl => ?_)
        simp [Finset.sum_apply]
      rw [hsum_eq_inner]
      ring
    -- ‖2*m + ρ‖ < 1
    have h_norm_2m_ρ : ‖2 * m + ρ‖ < 1 := by
      have h2m : ‖2 * m‖ < 1 := by
        calc
          ‖2 * m‖ = ‖(2 : F)‖ * ‖m‖ := norm_mul _ _
          _ ≤ ‖(2 : F)‖ * 1 := mul_le_mul_of_nonneg_left hm_norm (norm_nonneg _)
          _ = ‖(2 : F)‖ := by simp
          _ < 1 := hnorm_two_lt_one
      have hmax : ‖2 * m + ρ‖ ≤ max (‖2 * m‖) (‖ρ‖) := norm_add_le_max _ _
      have hmax_lt_one : max (‖2 * m‖) (‖ρ‖) < 1 := max_lt h2m hρ_norm
      linarith
    -- Now ‖∑ u i + ρ‖ = 1
    have h_norm_sum_u_ρ : ‖∑ i ∈ S, u i + ρ‖ = 1 := by
      rw [hsum_u_ρ_eq]
      -- T + (2*m + ρ)
      -- ‖T‖ = 1, ‖2*m + ρ‖ < 1
      -- Since ‖T‖ ≠ ‖2*m + ρ‖, we have ‖T + (2*m + ρ)‖ = max(‖T‖, ‖2*m + ρ‖) = 1
      have h_ne : ‖T‖ ≠ ‖2 * m + ρ‖ := by
        rw [hT_norm]
        linarith
      rw [norm_add_eq_max_of_norm_ne_norm h_ne]
      rw [hT_norm]
      have h_max : max (1 : ℝ) (‖2 * m + ρ‖) = 1 :=
        max_eq_left (by linarith)
      rw [h_max]
    -- Now ‖Z - 1‖ = ‖π‖^t
    have hZ_sub_one_norm : ‖(∏ i ∈ S, (x i / s i ^ 2)) - 1‖ = ‖π‖ ^ t := by
      rw [hZ_eq']
      calc
        ‖(1 + π ^ t * (∑ i ∈ S, u i + ρ)) - 1‖ = ‖π ^ t * (∑ i ∈ S, u i + ρ)‖ := by
          rw [add_sub_cancel_left]
        _ = ‖π ^ t‖ * ‖∑ i ∈ S, u i + ρ‖ := norm_mul _ _
        _ = ‖π‖ ^ t * 1 := by rw [norm_pow, h_norm_sum_u_ρ]
        _ = ‖π‖ ^ t := by simp
    -- Contradiction with sb_not_isSquare_of_norm_sub_one
    have h_contra := sb_not_isSquare_of_norm_sub_one hπ0 hπ1 hdisc h2 ht hte hZ_sub_one_norm
    -- h_contra : ¬ IsSquare (∏ i ∈ S, (x i / s i ^ 2))
    exact h_contra hZ_sq

/-- Depth `2e` test. If `∏ x i` is a square and `x i / s i ^ 2 = 1 + 4 (∑ V i l w l) + O(4 π)`, and
the trace vector `τ` kills every `∑ C l w l` congruent to some `y ^ 2 + y`, then the trace bits
`∑ l, V i l * τ l` sum to `0`. -/
theorem sb_test_four {F : Type*} [NormedField F] [IsUltrametricDist F] (h20 : (2 : F) ≠ 0)
    (h21 : ‖(2 : F)‖ < 1) {f : ℕ} (w : Fin f → F) (hw : ∀ l, ‖w l‖ ≤ 1) (τ : Fin f → ZMod 2)
    (htr : ∀ (y : F) (C : Fin f → ZMod 2), ‖y‖ ≤ 1 →
      ‖y ^ 2 + y - ∑ l, ((C l).val : F) * w l‖ < 1 → ∑ l, C l * τ l = 0)
    {α : Type*} (S : Finset α) (x s : α → F) (V : α → Fin f → ZMod 2)
    (hx : ∀ i ∈ S, ‖x i / s i ^ 2 - 1 - 4 * ∑ l, ((V i l).val : F) * w l‖ < ‖(4 : F)‖)
    (hsq : IsSquare (∏ i ∈ S, x i)) : ∑ i ∈ S, ∑ l, V i l * τ l = 0 := by
  have h4ne : (4 : F) ≠ 0 := by
    intro h4z
    have h4eq : (4 : F) = (2 : F) * (2 : F) := by norm_num
    rw [h4eq] at h4z
    rcases mul_eq_zero.mp h4z with (h2z | h2z)
    · exact h20 h2z
    · exact h20 h2z
  have h4lt1 : ‖(4 : F)‖ < 1 := by
    have h4eq : (4 : F) = (2 : F) * (2 : F) := by norm_num
    rw [h4eq, norm_mul]
    have hpos : 0 ≤ ‖(2 : F)‖ := norm_nonneg _
    nlinarith
  have h4pos : ‖(4 : F)‖ > 0 :=
    norm_pos_iff.mpr h4ne
  -- For each i ∈ S, s i ≠ 0
  have hs_ne_zero : ∀ i ∈ S, s i ≠ 0 := by
    intro i hi
    by_contra hsi
    have hzero : x i / s i ^ 2 = 0 := by simp [hsi]
    have hx_i := hx i hi
    rw [hzero] at hx_i
    have hsimp : (0 : F) - 1 - 4 * ∑ l, ((V i l).val : F) * w l = -1 - 4 * ∑ l, ((V i l).val : F) * w l := by
      simp
    rw [hsimp] at hx_i
    set W := ∑ l, ((V i l).val : F) * w l with hW
    have hWnorm : ‖W‖ ≤ 1 := by
      have h_nonneg : 0 ≤ (1 : ℝ) := by norm_num
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg ?_
      intro l hl
      have hval : ((V i l).val : F) = 0 ∨ ((V i l).val : F) = 1 := by
        have hval_lt : (V i l).val < 2 := ZMod.val_lt (V i l)
        interval_cases (V i l).val
        · left; norm_num
        · right; norm_num
      rcases hval with (hval | hval)
      · simp [hval, hw l]
      · simp [hval, hw l]
    have h4Wnorm : ‖(4 : F) * W‖ < 1 := by
      calc
        ‖(4 : F) * W‖ = ‖(4 : F)‖ * ‖W‖ := norm_mul _ _
        _ ≤ ‖(4 : F)‖ * 1 := mul_le_mul_of_nonneg_left hWnorm (norm_nonneg _)
        _ < 1 * 1 := mul_lt_mul_of_pos_right h4lt1 (by norm_num : (0 : ℝ) < 1)
        _ = 1 := by norm_num
    have hnorm_neg_one : ‖(-1 : F)‖ = 1 := by
      simpa using norm_one (F := F)
    have h_ultr : ‖(-1 : F) - (4 : F) * W‖ = 1 := by
      have h_add : (-1 : F) - (4 : F) * W = (-1 : F) + (-((4 : F) * W)) := by ring
      rw [h_add]
      have h_ne : ‖(-1 : F)‖ ≠ ‖(-((4 : F) * W))‖ := by
        rw [hnorm_neg_one, norm_neg]
        exact Ne.symm (ne_of_lt h4Wnorm)
      have h_max := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
      rw [h_max, hnorm_neg_one, norm_neg]
      exact max_eq_left (le_of_lt h4Wnorm)
    rw [h_ultr] at hx_i
    linarith
  -- Define u i and y i
  set u : α → F := fun i => ∑ l, ((V i l).val : F) * w l with hu_def
  have hu_eq : ∀ i, u i = ∑ l, ((V i l).val : F) * w l := fun i => by rw [hu_def]
  set y : α → F := fun i => (x i / s i ^ 2 - 1) / 4 with hy_def
  have hy_eq : ∀ i, x i / s i ^ 2 = 1 + 4 * y i := by
    intro i
    dsimp [y]
    field_simp [h4ne]
    ring
  have hu_norm : ∀ i ∈ S, ‖u i‖ ≤ 1 := by
    intro i hi
    rw [hu_eq i]
    have h_nonneg : 0 ≤ (1 : ℝ) := by norm_num
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg ?_
    intro l hl
    have hval : ((V i l).val : F) = 0 ∨ ((V i l).val : F) = 1 := by
      have hval_lt : (V i l).val < 2 := ZMod.val_lt (V i l)
      interval_cases (V i l).val
      · left; norm_num
      · right; norm_num
    rcases hval with (hval | hval)
    · simp [hval, hw l]
    · simp [hval, hw l]
  have hy_diff : ∀ i ∈ S, ‖y i - u i‖ < 1 := by
    intro i hi
    have hx_i := hx i hi
    rw [← hu_eq i] at hx_i
    have htemp : x i / s i ^ 2 - 1 - 4 * u i = 4 * (y i - u i) := by
      rw [hu_eq i]
      dsimp [y]
      field_simp [h4ne]
    rw [htemp] at hx_i
    have hineq : ‖(4 : F)‖ * ‖y i - u i‖ < ‖(4 : F)‖ * 1 := by
      calc
        ‖(4 : F)‖ * ‖y i - u i‖ = ‖(4 : F) * (y i - u i)‖ := by rw [norm_mul]
        _ < ‖(4 : F)‖ := hx_i
        _ = ‖(4 : F)‖ * 1 := by ring
    nlinarith
  -- Prove that ∏ (x i / s i ^ 2) is a square
  have h_prod_sq : IsSquare (∏ i ∈ S, (x i / s i ^ 2)) := by
    rcases hsq with ⟨ξ, hξ⟩
    by_cases hSempty : S.Nonempty
    · have hprod_s_ne_zero : ∏ i ∈ S, s i ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        exact hs_ne_zero i hi
      refine ⟨ξ / ∏ i ∈ S, s i, ?_⟩
      have hξ_sq : ξ ^ 2 = ∏ i ∈ S, x i := by
        rw [pow_two, ← hξ]
      calc
        ∏ i ∈ S, (x i / s i ^ 2) = (∏ i ∈ S, x i) / (∏ i ∈ S, s i ^ 2) := by rw [Finset.prod_div_distrib]
        _ = (∏ i ∈ S, x i) / (∏ i ∈ S, s i) ^ 2 := by rw [Finset.prod_pow]
        _ = ξ ^ 2 / (∏ i ∈ S, s i) ^ 2 := by rw [hξ_sq]
        _ = (ξ / ∏ i ∈ S, s i) * (ξ / ∏ i ∈ S, s i) := by ring
    · have hSempty' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSempty
      simp [hSempty']
  rcases h_prod_sq with ⟨ξ, hξ⟩
  -- Apply sb_prod_one_add_mul to get ρ
  rcases sb_prod_one_add_mul S h4lt1 u y (fun i hi => hu_norm i hi) (fun i hi => hy_diff i hi) with ⟨ρ, hρ_norm, hρ_eq⟩
  -- hρ_eq : ∏ i ∈ S, (1 + (4 : F) * y i) = 1 + (4 : F) * (∑ i ∈ S, u i + ρ)
  -- But 1 + 4*y i = x i / s i ^ 2
  have hprod_eq' : ∏ i ∈ S, (x i / s i ^ 2) = 1 + (4 : F) * (∑ i ∈ S, u i + ρ) := by
    calc
      ∏ i ∈ S, (x i / s i ^ 2) = ∏ i ∈ S, (1 + (4 : F) * y i) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [hy_eq i]
      _ = 1 + (4 : F) * (∑ i ∈ S, u i + ρ) := hρ_eq
  -- From hξ, we have ξ^2 = ∏ (x i / s i ^ 2) = 1 + 4*(∑ u i + ρ)
  have h_sq_eq : ξ ^ 2 = 1 + (4 : F) * (∑ i ∈ S, u i + ρ) := by
    rw [pow_two, ← hξ, hprod_eq']
  -- Prove ‖∑ u i + ρ‖ ≤ 1
  have hsum_norm : ‖∑ i ∈ S, u i‖ ≤ 1 := by
    by_cases hSempty : S.Nonempty
    · have h_nonneg : 0 ≤ (1 : ℝ) := by norm_num
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg ?_
      intro i hi
      exact hu_norm i hi
    · have hSempty' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSempty
      simp [hSempty']
  have hM_norm : ‖∑ i ∈ S, u i + ρ‖ ≤ 1 := by
    calc
      ‖∑ i ∈ S, u i + ρ‖ ≤ max ‖∑ i ∈ S, u i‖ ‖ρ‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max 1 ‖ρ‖ := max_le_max hsum_norm (le_refl ‖ρ‖)
      _ = 1 := max_eq_left (a := 1) (b := ‖ρ‖) (le_of_lt hρ_norm)
  -- Apply sb_eq_sq_add_self_of_sq to get y'
  rcases sb_eq_sq_add_self_of_sq h20 hM_norm h_sq_eq with ⟨y', hy'_norm, hM_eq⟩
  -- hM_eq : ∑ i ∈ S, u i + ρ = y' ^ 2 + y'
  -- Apply sb_sum_liftV
  rcases sb_sum_liftV S w hw V with ⟨m', hm'_norm, hsum_eq⟩
  -- hsum_eq : ∑ i ∈ S, ∑ l, ((V i l).val : F) * w l = ∑ l, ((∑ i ∈ S, V i l).val : F) * w l + 2 * m'
  -- Define C l = ∑ i ∈ S, V i l
  set C : Fin f → ZMod 2 := fun l => ∑ i ∈ S, V i l with hC_def
  have hsum_u_eq : ∑ i ∈ S, u i = ∑ l, ((C l).val : F) * w l + 2 * m' := by
    calc
      ∑ i ∈ S, u i = ∑ i ∈ S, ∑ l, ((V i l).val : F) * w l := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hu_eq i]
      _ = ∑ l, ((∑ i ∈ S, V i l).val : F) * w l + 2 * m' := hsum_eq
      _ = ∑ l, ((C l).val : F) * w l + 2 * m' := by rw [hC_def]
  -- Now relate y'^2 + y' to the sum
  have h_diff : y' ^ 2 + y' - ∑ l, ((C l).val : F) * w l = 2 * m' + ρ := by
    calc
      y' ^ 2 + y' - ∑ l, ((C l).val : F) * w l = (∑ i ∈ S, u i + ρ) - ∑ l, ((C l).val : F) * w l := by rw [hM_eq]
      _ = (∑ l, ((C l).val : F) * w l + 2 * m' + ρ) - ∑ l, ((C l).val : F) * w l := by rw [hsum_u_eq]
      _ = 2 * m' + ρ := by ring
  -- Prove ‖2*m' + ρ‖ < 1
  have h2m'_norm : ‖(2 : F) * m'‖ < 1 := by
    calc
      ‖(2 : F) * m'‖ = ‖(2 : F)‖ * ‖m'‖ := norm_mul _ _
      _ ≤ ‖(2 : F)‖ * 1 := mul_le_mul_of_nonneg_left hm'_norm (norm_nonneg _)
      _ < 1 * 1 := mul_lt_mul_of_pos_right h21 (by norm_num : (0 : ℝ) < 1)
      _ = 1 := by norm_num
  have h_norm_diff : ‖y' ^ 2 + y' - ∑ l, ((C l).val : F) * w l‖ < 1 := by
    rw [h_diff]
    calc
      ‖2 * m' + ρ‖ ≤ max ‖(2 : F) * m'‖ ‖ρ‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt h2m'_norm hρ_norm
  -- Apply htr
  have hC_sum_zero : ∑ l, C l * τ l = 0 :=
    htr y' C hy'_norm h_norm_diff
  -- Final rearrangement
  calc
    ∑ i ∈ S, ∑ l, V i l * τ l = ∑ l, ∑ i ∈ S, V i l * τ l := by rw [Finset.sum_comm]
    _ = ∑ l, (∑ i ∈ S, V i l) * τ l := by simp [Finset.sum_mul]
    _ = ∑ l, C l * τ l := by rw [hC_def]
    _ = 0 := hC_sum_zero

/-- Odd residue characteristic test. With the Fermat congruence `ξ ^ (2N) ≡ 1` for units, if
`∏ x i` is a square and `(x i / s i ^ 2) ^ N ≡ (-1) ^ c i`, then `∑ c i = 0`. -/
theorem sb_test_chr {F : Type*} [NormedField F] [IsUltrametricDist F] (h2 : ‖(2 : F)‖ = 1)
    {N : ℕ} (hferm : ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ (2 * N) - 1‖ < 1)
    {α : Type*} (S : Finset α) (x s : α → F) (c : α → ZMod 2)
    (hx1 : ∀ i ∈ S, ‖x i / s i ^ 2‖ = 1)
    (hx : ∀ i ∈ S, ‖(x i / s i ^ 2) ^ N - (-1) ^ (c i).val‖ < 1)
    (hsq : IsSquare (∏ i ∈ S, x i)) : ∑ i ∈ S, c i = 0 := by
  -- Define z i = x i / s i ^ 2
  set z := fun i : α => x i / s i ^ 2 with hz_def
  have hz_norm : ∀ i ∈ S, ‖z i‖ = 1 := hx1
  have hs_ne_zero : ∀ i ∈ S, s i ≠ 0 := by
    intro i hi
    have hnorm := hz_norm i hi
    have hpos : ‖z i‖ ≠ 0 := by linarith
    have hzero : z i ≠ 0 := norm_ne_zero_iff.mp hpos
    dsimp [z] at hzero
    have h_div_ne_zero := div_ne_zero_iff.mp hzero
    have h_s_sq_ne_zero : s i ^ 2 ≠ 0 := h_div_ne_zero.2
    intro hsi
    apply h_s_sq_ne_zero
    rw [hsi]
    simp
  -- The product of z i is a square
  have hz_sq : IsSquare (∏ i ∈ S, z i) := by
    have hprod_eq : (∏ i ∈ S, x i) = (∏ i ∈ S, z i) * (∏ i ∈ S, s i) ^ 2 := by
      calc
        (∏ i ∈ S, x i) = (∏ i ∈ S, (z i * s i ^ 2)) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          dsimp [z]
          field_simp [hs_ne_zero i hi]
        _ = (∏ i ∈ S, z i) * (∏ i ∈ S, s i ^ 2) := Finset.prod_mul_distrib
        _ = (∏ i ∈ S, z i) * (∏ i ∈ S, s i) ^ 2 := by rw [Finset.prod_pow]
    have h_sq_denom : IsSquare ((∏ i ∈ S, s i) ^ 2) := by
      refine ⟨∏ i ∈ S, s i, ?_⟩
      ring
    have h_div_eq : (∏ i ∈ S, z i) = (∏ i ∈ S, x i) / (∏ i ∈ S, s i) ^ 2 := by
      rw [hprod_eq]
      have h_prod_s_ne_zero : (∏ i ∈ S, s i) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => hs_ne_zero i hi
      have h_denom_ne_zero : (∏ i ∈ S, s i) ^ 2 ≠ 0 := pow_ne_zero 2 h_prod_s_ne_zero
      have h_denom_ne_zero' : (∏ i ∈ S, s i) ≠ 0 := h_prod_s_ne_zero
      field_simp [h_denom_ne_zero, h_denom_ne_zero']
    rw [h_div_eq]
    exact IsSquare.div hsq h_sq_denom
  -- Get ξ such that ξ^2 = ∏ z i
  obtain ⟨ξ, hξ_sq⟩ := hz_sq
  -- Show ‖ξ‖ = 1
  have hξ_norm : ‖ξ‖ = 1 := by
    have h_norm_prod : ‖∏ i ∈ S, z i‖ = 1 := by
      rw [norm_prod]
      calc
        ∏ i ∈ S, ‖z i‖ = ∏ i ∈ S, (1 : ℝ) :=
          Finset.prod_congr rfl fun i hi => by rw [hz_norm i hi]
        _ = 1 := by simp
    have h_norm_ξ_sq : ‖ξ ^ 2‖ = 1 := by
      rw [pow_two, ← hξ_sq, h_norm_prod]
    have h_norm_sq : ‖ξ ^ 2‖ = ‖ξ‖ ^ 2 := by
      rw [norm_pow, pow_two]
    rw [h_norm_sq] at h_norm_ξ_sq
    have h_nonneg : 0 ≤ ‖ξ‖ := norm_nonneg _
    nlinarith
  -- Apply hferm to ξ
  have h_ferm : ‖(ξ ^ 2) ^ N - 1‖ < 1 := by
    have h_pow_eq : (ξ ^ 2) ^ N = ξ ^ (2 * N) := by
      rw [← pow_mul, mul_comm]
    rw [h_pow_eq]
    exact hferm ξ hξ_norm
  -- Set up a i = z i ^ N and b i = (-1)^(c i).val
  set a := fun i : α => z i ^ N with ha_def
  set b := fun i : α => (-1 : F) ^ (c i).val with hb_def
  have ha_norm : ∀ i ∈ S, ‖a i‖ ≤ 1 := by
    intro i hi
    rw [ha_def, norm_pow, hz_norm i hi, one_pow]
  have hb_norm : ∀ i ∈ S, ‖b i‖ ≤ 1 := by
    intro i hi
    rw [hb_def, norm_pow, norm_neg, norm_one, one_pow]
  have hab : ∀ i ∈ S, ‖a i - b i‖ < 1 := by
    intro i hi
    rw [ha_def, hb_def]
    exact hx i hi
  -- Apply sb_prod_sub_lt
  have h_prod_sub : ‖(∏ i ∈ S, a i) - (∏ i ∈ S, b i)‖ < 1 :=
    sb_prod_sub_lt S a b ha_norm hb_norm hab
  -- Compute ∏ a i = (∏ z i)^N
  have h_prod_a : (∏ i ∈ S, a i) = (∏ i ∈ S, z i) ^ N := by
    rw [ha_def, Finset.prod_pow]
  -- Compute ∏ b i = (-1)^(∑ (c i).val)
  have h_prod_b : (∏ i ∈ S, b i) = (-1 : F) ^ (∑ i ∈ S, (c i).val) := by
    rw [hb_def, Finset.prod_pow_eq_pow_sum]
  -- Rewrite h_prod_sub using these
  rw [h_prod_a, h_prod_b] at h_prod_sub
  -- Let Z := (∏ z i)^N
  set Z := (∏ i ∈ S, z i) ^ N with hZ_def
  -- We also have ‖Z - 1‖ < 1 from h_ferm (since Z = (ξ^2)^N = ξ^(2N))
  have hZ_sub_one : ‖Z - 1‖ < 1 := by
    rw [hZ_def, hξ_sq, ← pow_two]
    exact h_ferm
  -- Now the key: if ∑ c i ≠ 0, then (-1)^(∑ (c i).val) = -1
  by_contra h_sum_ne
  have h_sum_ne_zero : (∑ i ∈ S, c i) ≠ 0 := h_sum_ne
  -- Relate ∑ c i to ∑ (c i).val via ZMod.natCast_val
  have h_sum_val : (∑ i ∈ S, c i) = ((∑ i ∈ S, (c i).val : ℕ) : ZMod 2) := by
    simp [ZMod.natCast_val]
  rw [h_sum_val] at h_sum_ne_zero
  -- So ((∑ (c i).val : ℕ) : ZMod 2) ≠ 0, which means ∑ (c i).val is odd
  have h_odd : Odd (∑ i ∈ S, (c i).val) :=
    (ZMod.natCast_ne_zero_iff_odd (n := ∑ i ∈ S, (c i).val)).mp h_sum_ne_zero
  have h_neg_one : (-1 : F) ^ (∑ i ∈ S, (c i).val) = -1 :=
    h_odd.neg_one_pow
  rw [h_neg_one] at h_prod_sub
  -- Now h_prod_sub says ‖Z - (-1)‖ < 1, i.e., ‖Z + 1‖ < 1
  have hZ_add_one : ‖Z + 1‖ < 1 := by
    -- Z - (-1) = Z + 1
    have : Z - (-1 : F) = Z + 1 := by ring
    rw [this] at h_prod_sub
    exact h_prod_sub
  -- Now we have both ‖Z - 1‖ < 1 and ‖Z + 1‖ < 1
  -- In an ultrametric field, ‖(Z+1) - (Z-1)‖ ≤ max(‖Z+1‖, ‖Z-1‖) < 1
  -- But (Z+1) - (Z-1) = 2, contradicting h2
  have h_two_lt_one : ‖(2 : F)‖ < 1 := by
    have h_diff : (Z + 1) - (Z - 1) = (2 : F) := by ring
    rw [← h_diff]
    calc
      ‖(Z + 1) - (Z - 1)‖ = ‖(Z + 1) + (-(Z - 1))‖ := by ring
      _ ≤ max ‖Z + 1‖ ‖-(Z - 1)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖Z + 1‖ ‖Z - 1‖ := by rw [norm_neg]
      _ < 1 := max_lt hZ_add_one hZ_sub_one
  rw [h2] at h_two_lt_one
  linarith

end FurioLombardo.Discharge.SelmerBasis
