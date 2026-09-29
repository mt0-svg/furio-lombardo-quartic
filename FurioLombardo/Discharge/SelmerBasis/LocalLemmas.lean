import FurioLombardo.Discharge.SelmerBasis.Echelon

/-!
# Leaves of the per place certificates

* evaluation and perturbation bounds for data known up to a small error (`norm_eval_sub_le`,
  `sq_cert_perturb`), for the local roots `τ_j` approximated by global elements;
* the lifts of bitsets (`liftW_zero`, `liftW_two_pow`);
* the exact data of the standard basis of `F^× / F^×²` at a component (`dfact_one_four`,
  `dfact_one_chr`, `dfact_pi`, `dfact_odd_std`, `dfact_four_std`);
* residue field `𝔽₂` facts for the quadratic components (`norm_sq_add_mul_add_sq`,
  `no_root_unram`, `no_root_ram`).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial

section Approx

/-- An integral polynomial is `1`-Lipschitz on the unit ball. -/
theorem norm_eval_sub_le {F : Type*} [NormedField F] [IsUltrametricDist F]
    (P : F[X]) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) {x y : F} (hx : ‖x‖ ≤ 1)
    (hy : ‖y‖ ≤ 1) : ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  have hxy : ‖x - y‖ ≤ 1 := by
    have h := dist_triangle_max x (0 : F) y
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
    have h' : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by simpa [sub_zero, zero_sub, norm_neg] using h
    exact le_trans h' (max_le hx hy)
  -- Express P.eval x - P.eval y as a finite sum
  have h_eval_sub : P.eval x - P.eval y =
      ∑ i ∈ Finset.range (natDegree P + 1),
        (P.coeff i) * (x ^ i - y ^ i) := by
    simp [Polynomial.eval_eq_sum_range, Finset.sum_sub_distrib, mul_sub]
  rw [h_eval_sub]
  -- Use ultrametric sum property: norm of sum ≤ max of norms
  refine le_trans
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_) (le_refl _)
  intro i hi
  have hterm : ‖(P.coeff i) * (x ^ i - y ^ i)‖ ≤ ‖x - y‖ := by
    calc
      ‖(P.coeff i) * (x ^ i - y ^ i)‖ ≤ ‖P.coeff i‖ * ‖x ^ i - y ^ i‖ := norm_mul_le _ _
      _ ≤ 1 * ‖x ^ i - y ^ i‖ := mul_le_mul_of_nonneg_right (hP i) (norm_nonneg _)
      _ = ‖x ^ i - y ^ i‖ := by simp
      _ = ‖(∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j)) * (x - y)‖ := by
        rw [geom_sum₂_mul x y i]
      _ = ‖(x - y) * (∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j))‖ := by rw [mul_comm]
      _ ≤ ‖x - y‖ * ‖∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j)‖ := norm_mul_le _ _
      _ ≤ ‖x - y‖ * 1 := by
        have hsum : ‖∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j)‖ ≤ 1 := by
          refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) ?_
          intro j hj
          calc
            ‖x ^ j * y ^ (i - 1 - j)‖ ≤ ‖x ^ j‖ * ‖y ^ (i - 1 - j)‖ := norm_mul_le _ _
            _ ≤ (‖x‖ ^ j) * (‖y‖ ^ (i - 1 - j)) := by
              refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
              · exact norm_pow_le x j
              · exact norm_pow_le y (i - 1 - j)
            _ ≤ 1 * 1 := by
              refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
              · exact pow_le_pow_of_le_one (norm_nonneg _) hx (Nat.zero_le _)
              · exact pow_le_pow_of_le_one (norm_nonneg _) hy (Nat.zero_le _)
            _ = 1 := by simp
        exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      _ = ‖x - y‖ := by simp
  exact hterm

/-- A square certificate survives a perturbation of the element below `‖4‖ ‖s‖²`. -/
theorem sq_cert_perturb {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x x' s : F} (hs : s ≠ 0) (hx : ‖x / s ^ 2 - 1‖ < ‖(4 : F)‖)
    (hxx : ‖x' - x‖ < ‖(4 : F)‖ * ‖s‖ ^ 2) : ‖x' / s ^ 2 - 1‖ < ‖(4 : F)‖ := by
  have hpos_sq : 0 < ‖s‖ ^ 2 := pow_pos (by
    rw [norm_pos_iff]
    exact hs) 2
  have h_inv_pos : 0 < (‖s‖ ^ 2)⁻¹ := inv_pos.mpr hpos_sq
  have hx' : ‖(x' - x) / s ^ 2‖ < ‖(4 : F)‖ := by
    calc
      ‖(x' - x) / s ^ 2‖ = ‖(x' - x) * (s ^ 2)⁻¹‖ := by rw [div_eq_mul_inv]
      _ = ‖x' - x‖ * ‖(s ^ 2)⁻¹‖ := by rw [norm_mul]
      _ = ‖x' - x‖ * (‖s ^ 2‖⁻¹) := by rw [norm_inv]
      _ = ‖x' - x‖ * ((‖s‖ ^ 2)⁻¹) := by rw [norm_pow]
      _ < (‖(4 : F)‖ * ‖s‖ ^ 2) * ((‖s‖ ^ 2)⁻¹) := by
        exact mul_lt_mul_of_pos_right hxx h_inv_pos
      _ = ‖(4 : F)‖ := by
        field_simp [hpos_sq.ne.symm]
  have h_eq : x' / s ^ 2 - 1 = ((x' - x) / s ^ 2) + (x / s ^ 2 - 1) := by
    field_simp [hs]
    ring
  rw [h_eq]
  apply lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
  exact max_lt hx' hx

end Approx

section Lifts

theorem liftW_zero {F : Type*} [NormedField F] [IsUltrametricDist F]
    {f : ℕ} (w : Fin f → F) : liftW w 0 = 0 := by
  unfold liftW
  simp [bitv, Nat.zero_testBit, ZMod.val_zero]

theorem liftW_two_pow {F : Type*} [NormedField F] [IsUltrametricDist F]
    {f : ℕ} (w : Fin f → F) (l : Fin f) : liftW w (2 ^ (l : ℕ)) = w l := by
  unfold liftW
  have h_term : ∀ x ∈ (Finset.univ : Finset (Fin f)), ((bitv f (2 ^ (l : ℕ)) x).val : F) * w x = if x = l then w x else (0 : F) := by
    intro x hx
    by_cases h_eq : x = l
    · rw [h_eq]
      have h_val : ((bitv f (2 ^ (l : ℕ)) l).val : F) = (1 : F) := by
        unfold bitv
        simp [ZMod.val_one]
      rw [h_val]
      simp
    · have h_ne : (l : ℕ) ≠ (x : ℕ) := by
        intro h; apply h_eq; exact Fin.ext h.symm
      have h_val : ((bitv f (2 ^ (l : ℕ)) x).val : F) = (0 : F) := by
        unfold bitv
        simp [h_ne, ZMod.val_zero]
      rw [h_val]
      simp [h_eq]
  rw [Finset.sum_congr rfl h_term]
  simp

end Lifts

section Std

/-- The value `1` at a dyadic component: a datum of the form `1 + 4 · 0`. -/
theorem dfact_one_four {F : Type*} [NormedField F] [IsUltrametricDist F]
    (Q : CShape) (π : F) (w : Fin Q.f → F) (h4 : (4 : F) ≠ 0) :
    DFact Q π w 1 1 0 (.four 0) := by
  refine ⟨by simp, ?_⟩
  have h_lift : liftW w 0 = 0 := by
    unfold liftW
    simp [bitv, Nat.zero_testBit]
  have h_norm_pos : 0 < ‖(4 : F)‖ := norm_pos_iff.mpr h4
  calc
    ‖(1 : F) / ((1 : F) ^ 2) - 1 - (4 : F) * liftW w 0‖ = ‖(0 : F)‖ := by
      simp [h_lift]
    _ = 0 := by simp
    _ < ‖(4 : F)‖ := h_norm_pos

/-- The value `1` at a component of odd residue characteristic. -/
theorem dfact_one_chr {F : Type*} [NormedField F] [IsUltrametricDist F]
    (Q : CShape) (π : F) (w : Fin Q.f → F) :
    DFact Q π w 1 1 0 (.chr false) := by
  unfold DFact
  simp

/-- The uniformizer: valuation `1`, no unit datum. -/
theorem dfact_pi {F : Type*} [NormedField F] [IsUltrametricDist F]
    (Q : CShape) (π : F) (w : Fin Q.f → F) : DFact Q π w π 1 1 .none := by
  unfold DFact
  simp

/-- The standard unit `1 + π ^ t w_l`, exact at depth `t` with digit bitset `2 ^ l`. -/
theorem dfact_odd_std {F : Type*} [NormedField F] [IsUltrametricDist F]
    (Q : CShape) {π : F} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (w : Fin Q.f → F)
    (hw : ∀ l, ‖w l‖ ≤ 1) (t : ℕ) (ht : 0 < t) (l : Fin Q.f) :
    DFact Q π w (1 + π ^ t * w l) 1 0 (.odd t (2 ^ (l : ℕ))) := by
  simp [DFact]
  -- Goal: (UDatum.odd t (2 ^ ↑l)).1 ∧ (UDatum.odd t (2 ^ ↑l)).2
  -- which expands to:
  -- ‖1 + π ^ t * w l‖ = ‖π‖ ^ 0 ∧ ‖(1 + π ^ t * w l) / 1 ^ 2 - 1 - π ^ t * liftW w (2 ^ ↑l)‖ < ‖π‖ ^ t
  have h_norm_pi_pos : 0 < ‖π‖ := by
    rwa [norm_pos_iff]
  have h_norm_pi_pow_lt_one : ‖π‖ ^ t < 1 := by
    rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt ht) with (rfl | ht')
    · -- t = 1
      simp [hπ1]
    · -- t > 1
      have h := pow_lt_self_of_lt_one₀ h_norm_pi_pos hπ1 ht'
      linarith
  have h_norm_wl_le_one : ‖w l‖ ≤ 1 := hw l
  have h_norm_term_lt_one : ‖π ^ t * w l‖ < 1 := by
    calc
      ‖π ^ t * w l‖ ≤ ‖π ^ t‖ * ‖w l‖ := norm_mul_le _ _
      _ = ‖π‖ ^ t * ‖w l‖ := by rw [norm_pow]
      _ ≤ ‖π‖ ^ t * 1 := mul_le_mul_of_nonneg_left h_norm_wl_le_one (by positivity)
      _ = ‖π‖ ^ t := mul_one _
      _ < 1 := h_norm_pi_pow_lt_one
  have h_norm_one : ‖(1 : F)‖ = 1 := norm_one
  have h_norm_one_ne : ‖(1 : F)‖ ≠ ‖π ^ t * w l‖ := by
    rw [h_norm_one]
    exact (ne_of_lt h_norm_term_lt_one).symm
  have h_add_norm : ‖(1 : F) + π ^ t * w l‖ = max ‖(1 : F)‖ ‖π ^ t * w l‖ :=
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_norm_one_ne
  have h_max_eq_one : max ‖(1 : F)‖ ‖π ^ t * w l‖ = 1 := by
    rw [h_norm_one]
    exact max_eq_left (by linarith)
  have h_norm_sum : ‖(1 : F) + π ^ t * w l‖ = 1 := by
    rw [h_add_norm, h_max_eq_one]
  have h_norm_pow_zero : ‖π‖ ^ (0 : ℤ) = 1 := by
    simp
  constructor
  · -- ‖1 + π ^ t * w l‖ = ‖π‖ ^ 0
    simpa [h_norm_pow_zero] using h_norm_sum
  · -- ‖(1 + π ^ t * w l) / 1 ^ 2 - 1 - π ^ t * liftW w (2 ^ (l : ℕ))‖ < ‖π‖ ^ t
    have h_lift : liftW w (2 ^ (l : ℕ)) = w l := liftW_two_pow w l
    calc
      ‖π ^ t * w l - π ^ t * liftW w (2 ^ (l : ℕ))‖
          = ‖π ^ t * (w l - liftW w (2 ^ (l : ℕ)))‖ := by
        congr 1; ring
      _ = ‖π ^ t * (w l - w l)‖ := by rw [h_lift]
      _ = ‖π ^ t * 0‖ := by ring_nf
      _ = ‖(0 : F)‖ := by rw [mul_zero]
      _ = 0 := by simp
      _ < ‖π‖ ^ t := by
        have : 0 < ‖π‖ ^ t := pow_pos h_norm_pi_pos t
        exact this

/-- The standard unit `1 + 4 · (lift of c)`, exact of the form `four c`. -/
theorem dfact_four_std {F : Type*} [NormedField F] [IsUltrametricDist F]
    (Q : CShape) (π : F) (w : Fin Q.f → F) (hw : ∀ l, ‖w l‖ ≤ 1)
    (h40 : (4 : F) ≠ 0) (h41 : ‖(4 : F)‖ < 1) (c : ℕ) :
    DFact Q π w (1 + 4 * liftW w c) 1 0 (.four c) := by
  have h_norm_one : ‖(1 : F)‖ = 1 := by simp
  have h_norm_pi_pow_zero : ‖π‖ ^ (0 : ℤ) = 1 := by simp
  have h_bitv_val_le_one (l : Fin Q.f) : ‖((bitv Q.f c l).val : F)‖ ≤ 1 := by
    have h_val_lt_two : (bitv Q.f c l).val < 2 := ZMod.val_lt _
    have h_cases : (bitv Q.f c l).val = 0 ∨ (bitv Q.f c l).val = 1 := by omega
    have h_val : ((bitv Q.f c l).val : F) = 0 ∨ ((bitv Q.f c l).val : F) = 1 := by
      rcases h_cases with (h | h) <;> simp [h]
    rcases h_val with (h | h) <;> simp [h]
  have h_norm_liftW_le_one : ‖liftW w c‖ ≤ 1 := by
    have h_nonneg : 0 ≤ (1 : ℝ) := by norm_num
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h_nonneg (fun l hl => ?_)
    calc
      ‖((bitv Q.f c l).val : F) * w l‖ = ‖((bitv Q.f c l).val : F)‖ * ‖w l‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (h_bitv_val_le_one l) (hw l) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have h_norm_four_mul_liftW_lt_one : ‖(4 : F) * liftW w c‖ < 1 := by
    calc
      ‖(4 : F) * liftW w c‖ = ‖(4 : F)‖ * ‖liftW w c‖ := norm_mul _ _
      _ ≤ ‖(4 : F)‖ * 1 := mul_le_mul_of_nonneg_left h_norm_liftW_le_one (norm_nonneg _)
      _ = ‖(4 : F)‖ := by simp
      _ < 1 := h41
  have h_norm_sum_eq_one : ‖(1 : F) + (4 : F) * liftW w c‖ = 1 := by
    have h_ne : ‖(1 : F)‖ ≠ ‖(4 : F) * liftW w c‖ := by
      rw [h_norm_one]
      exact (ne_of_lt h_norm_four_mul_liftW_lt_one).symm
    have h_eq_max := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
    rw [h_eq_max, h_norm_one]
    exact max_eq_left h_norm_four_mul_liftW_lt_one.le
  have h_norm_zero_lt_four : ‖(0 : F)‖ < ‖(4 : F)‖ := by
    rw [norm_zero]
    exact norm_pos_iff.mpr h40
  refine And.intro ?_ ?_
  · rw [h_norm_sum_eq_one, h_norm_pi_pow_zero]
  · have h_expr_eq_zero : (1 + 4 * liftW w c) / (1 : F) ^ 2 - 1 - 4 * liftW w c = 0 := by ring
    rw [h_expr_eq_zero, norm_zero]
    exact norm_pos_iff.mpr h40

end Std

section Residue

lemma norm_add_eq_of_norm_lt {F : Type*} [SeminormedAddCommGroup F] [IsUltrametricDist F] {x y : F} (h : ‖x‖ < ‖y‖) : ‖x + y‖ = ‖y‖ := by
  have hle : ‖x + y‖ ≤ ‖y‖ := by
    calc
      ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = ‖y‖ := max_eq_right h.le
  have hge : ‖y‖ ≤ ‖x + y‖ := by
    have htmp : ‖y‖ ≤ max ‖x + y‖ ‖x‖ := by
      calc
        ‖y‖ = ‖(x + y) + (-x)‖ := by simp
        _ ≤ max ‖x + y‖ ‖-x‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖x + y‖ ‖x‖ := by simp
    rcases le_max_iff.mp htmp with (hcase | hcase)
    · exact hcase
    · exfalso
      linarith
  exact le_antisymm hle hge

-- Key lemma: under the hres condition, ‖1 + t + t^2‖ = 1 when ‖t‖ ≤ 1
lemma norm_one_add_t_add_t_sq_eq_one {F : Type*} [NormedField F] [IsUltrametricDist F]
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) {t : F} (ht_norm_le_one : ‖t‖ ≤ 1) :
    ‖(1 : F) + t + t ^ 2‖ = 1 := by
  have ht_nonneg : 0 ≤ ‖t‖ := norm_nonneg _
  have h2_lt_one : ‖(2 : F)‖ < 1 := by
    have h2_le_one : ‖(2 : F)‖ ≤ 1 := by
      calc
        ‖(2 : F)‖ = ‖(1 : F) + (1 : F)‖ := by norm_num
        _ ≤ max ‖(1 : F)‖ ‖(1 : F)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = ‖(1 : F)‖ := max_eq_left (le_refl _)
        _ = 1 := by norm_num
    rcases hres 2 h2_le_one with (h | h)
    · exact h
    · -- h : ‖2 - 1‖ < 1, i.e., ‖1‖ < 1, contradiction
      have : ‖(2 : F) - 1‖ = 1 := by norm_num
      rw [this] at h
      linarith
  have h3_norm : ‖(3 : F)‖ = 1 := by
    calc
      ‖(3 : F)‖ = ‖(2 : F) + (1 : F)‖ := by norm_num
      _ = ‖(1 : F)‖ := by
        have : ‖(2 : F)‖ < ‖(1 : F)‖ := by simpa [norm_one] using h2_lt_one
        exact norm_add_eq_of_norm_lt this
      _ = 1 := by norm_num
  by_cases ht_lt_one : ‖t‖ < 1
  · -- Case ‖t‖ < 1
    have ht_sq_lt_one : ‖t ^ 2‖ < 1 := by
      calc
        ‖t ^ 2‖ = ‖t‖ ^ 2 := norm_pow _ 2
        _ < 1 ^ 2 := by nlinarith
        _ = 1 := by norm_num
    have h_sum_lt_one : ‖t + t ^ 2‖ < 1 := by
      calc
        ‖t + t ^ 2‖ ≤ max ‖t‖ ‖t ^ 2‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt ht_lt_one ht_sq_lt_one
    calc
      ‖(1 : F) + t + t ^ 2‖ = ‖(t + t ^ 2) + (1 : F)‖ := by ring_nf
      _ = ‖(1 : F)‖ := by
        have : ‖t + t ^ 2‖ < ‖(1 : F)‖ := by simpa [norm_one] using h_sum_lt_one
        exact norm_add_eq_of_norm_lt this
      _ = 1 := by norm_num
  · -- Case ‖t‖ = 1
    have ht_eq_one : ‖t‖ = 1 := by linarith
    rcases hres t ht_norm_le_one with (h_lt | h_sub_lt)
    · linarith
    · -- h_sub_lt : ‖t - 1‖ < 1
      have h_expr : (1 : F) + t + t ^ 2 = (3 : F) + (3 : F) * (t - 1) + (t - 1) ^ 2 := by
        ring_nf
      rw [h_expr]
      have h_t1_lt_one : ‖t - 1‖ < 1 := h_sub_lt
      have h_3t1_lt_one : ‖(3 : F) * (t - 1)‖ < 1 := by
        calc
          ‖(3 : F) * (t - 1)‖ = ‖(3 : F)‖ * ‖t - 1‖ := norm_mul _ _
          _ = 1 * ‖t - 1‖ := by rw [h3_norm]
          _ = ‖t - 1‖ := by simp
          _ < 1 := h_t1_lt_one
      have h_t1_sq_lt_one : ‖(t - 1) ^ 2‖ < 1 := by
        have ht1_nonneg : 0 ≤ ‖t - 1‖ := norm_nonneg _
        calc
          ‖(t - 1) ^ 2‖ = ‖t - 1‖ ^ 2 := norm_pow _ 2
          _ < 1 ^ 2 := by nlinarith
          _ = 1 := by norm_num
      have h_tail_lt_one : ‖(3 : F) * (t - 1) + (t - 1) ^ 2‖ < 1 := by
        calc
          ‖(3 : F) * (t - 1) + (t - 1) ^ 2‖ ≤ max ‖(3 : F) * (t - 1)‖ ‖(t - 1) ^ 2‖ :=
            IsUltrametricDist.norm_add_le_max _ _
          _ < 1 := max_lt h_3t1_lt_one h_t1_sq_lt_one
      have h_tail_lt_norm_three : ‖(3 : F) * (t - 1) + (t - 1) ^ 2‖ < ‖(3 : F)‖ := by
        simpa [h3_norm] using h_tail_lt_one
      calc
        ‖(3 : F) + (3 : F) * (t - 1) + (t - 1) ^ 2‖ = ‖((3 : F) * (t - 1) + (t - 1) ^ 2) + (3 : F)‖ := by ring_nf
        _ = ‖(3 : F)‖ := norm_add_eq_of_norm_lt h_tail_lt_norm_three
        _ = 1 := h3_norm


/-- With residue field `𝔽₂`, the form `x² + x y + y²` is anisotropic: its norm is `max(‖x‖, ‖y‖)²`. -/
theorem norm_sq_add_mul_add_sq {F : Type*} [NormedField F] [IsUltrametricDist F]
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (x y : F) :
    ‖x ^ 2 + x * y + y ^ 2‖ = max ‖x‖ ‖y‖ ^ 2 := by
  by_cases hx0 : x = 0
  · subst x; simp
  by_cases hy0 : y = 0
  · subst y; simp
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  by_cases hxy : ‖x‖ < ‖y‖
  · -- Case ‖x‖ < ‖y‖: use symmetry
    have h_symm : x ^ 2 + x * y + y ^ 2 = y ^ 2 + y * x + x ^ 2 := by ring
    rw [h_symm]
    have hle' : ‖x‖ ≤ ‖y‖ := by linarith
    set t := x / y with ht_def
    have ht_norm_le_one : ‖t‖ ≤ 1 := by
      rw [ht_def, norm_div, div_le_one hy_norm_pos]
      exact hle'
    have h_expr : y ^ 2 + y * x + x ^ 2 = y ^ 2 * (1 + t + t ^ 2) := by
      rw [ht_def]
      field_simp [hy0]
    rw [h_expr, norm_mul, norm_pow]
    have h_norm_one_add : ‖(1 : F) + t + t ^ 2‖ = 1 :=
      norm_one_add_t_add_t_sq_eq_one hres ht_norm_le_one
    rw [h_norm_one_add, mul_one]
    rw [max_eq_right hle']
  · -- Case ‖y‖ ≤ ‖x‖
    have hle : ‖y‖ ≤ ‖x‖ := by linarith
    set t := y / x with ht_def
    have ht_norm_le_one : ‖t‖ ≤ 1 := by
      rw [ht_def, norm_div, div_le_one hx_norm_pos]
      exact hle
    have h_expr : x ^ 2 + x * y + y ^ 2 = x ^ 2 * (1 + t + t ^ 2) := by
      rw [ht_def]
      field_simp [hx0]
    rw [h_expr, norm_mul, norm_pow]
    have h_norm_one_add : ‖(1 : F) + t + t ^ 2‖ = 1 :=
      norm_one_add_t_add_t_sq_eq_one hres ht_norm_le_one
    rw [h_norm_one_add]
    simp [max_eq_left hle]

/-- With residue field `𝔽₂`, `X² - X + 1` has no root: `QuadraticAlgebra F (-1) 1` is a field. -/
theorem no_root_unram {F : Type*} [NormedField F] [IsUltrametricDist F]
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) :
    ∀ r : F, r ^ 2 ≠ -1 + 1 * r := by
  intro r
  intro h
  have h_sq_eq : r ^ 2 = r - 1 := by
    simpa [sub_eq_add_neg, add_comm] using h
  by_cases h_lt : ‖r‖ < 1
  · -- Case ‖r‖ < 1
    have h_norm_sq_lt_one : ‖r ^ 2‖ < 1 := by
      calc
        ‖r ^ 2‖ = ‖r‖ ^ 2 := norm_pow r 2
        _ < 1 ^ 2 := by
          have : 0 ≤ ‖r‖ := norm_nonneg _
          nlinarith
        _ = 1 := by norm_num
    have h_norm_r_sub_one_lt_one : ‖r - 1‖ < 1 := by
      rw [← h_sq_eq]
      exact h_norm_sq_lt_one
    have h_norm_r_sub_one_eq_one : ‖r - 1‖ = 1 := by
      have h_ne : ‖r‖ ≠ ‖(-1 : F)‖ := by
        simpa [norm_neg, norm_one] using ne_of_lt h_lt
      rw [sub_eq_add_neg]
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne]
      simp [h_lt.le, norm_neg, norm_one]
    linarith
  · -- Case ‖r‖ ≥ 1
    have h_ge : 1 ≤ ‖r‖ := by linarith
    by_cases h_gt : 1 < ‖r‖
    · -- Case ‖r‖ > 1
      have h_norm_sq_gt : ‖r‖ < ‖r ^ 2‖ := by
        calc
          ‖r‖ = ‖r‖ * 1 := by simp
          _ < ‖r‖ * ‖r‖ := by
            have : 0 < ‖r‖ := by linarith
            nlinarith
          _ = ‖r ^ 2‖ := by rw [norm_pow r 2, pow_two]
      have h_norm_sq_le : ‖r ^ 2‖ ≤ ‖r‖ := by
        rw [h_sq_eq]
        have h_ne : ‖r‖ ≠ ‖(-1 : F)‖ := by
          simpa [norm_neg, norm_one] using ne_of_gt h_gt
        rw [sub_eq_add_neg]
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne]
        simp [h_gt.le, norm_neg, norm_one]
      linarith
    · -- Case ‖r‖ = 1
      have h_eq_one : ‖r‖ = 1 := by linarith
      rcases hres r (by rw [h_eq_one]) with (h_lt' | h_sub_lt)
      · -- ‖r‖ < 1 contradicts h_eq_one
        linarith
      · -- ‖r - 1‖ < 1
        set y := r - 1 with hy_def
        have hy_lt_one : ‖y‖ < 1 := h_sub_lt
        have h_zero : y ^ 2 + y + 1 = 0 := by
          dsimp [y]
          calc
            (r - 1) ^ 2 + (r - 1) + 1 = (r ^ 2 - 2 * r + 1) + (r - 1) + 1 := by ring
            _ = r ^ 2 - r + 1 := by ring
            _ = (r - 1) - r + 1 := by rw [h_sq_eq]
            _ = 0 := by ring
        have hy_sq_lt_one : ‖y ^ 2‖ < 1 := by
          calc
            ‖y ^ 2‖ = ‖y‖ ^ 2 := norm_pow y 2
            _ < 1 ^ 2 := by
              have : 0 ≤ ‖y‖ := norm_nonneg _
              nlinarith
            _ = 1 := by norm_num
        have h_norm_sum : ‖y ^ 2 + y + 1‖ = 1 := by
          have h1 : ‖y ^ 2‖ ≠ ‖(1 : F)‖ := by
            simpa [norm_one] using ne_of_lt hy_sq_lt_one
          have h2 : ‖y ^ 2 + (1 : F)‖ = 1 := by
            rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1]
            simpa [norm_one] using max_eq_right hy_sq_lt_one.le
          have h3 : ‖y ^ 2 + (1 : F)‖ ≠ ‖y‖ := by
            rw [h2]
            exact (ne_of_lt hy_lt_one).symm
          calc
            ‖y ^ 2 + y + 1‖ = ‖(y ^ 2 + 1) + y‖ := by ring
            _ = max ‖y ^ 2 + 1‖ ‖y‖ :=
              IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h3
            _ = max 1 ‖y‖ := by rw [h2]
            _ = 1 := by simp [hy_lt_one.le]
        rw [h_zero] at h_norm_sum
        simp at h_norm_sum

/-- An element of odd norm exponent has no square root: `QuadraticAlgebra F δ 0` is a field. -/
theorem no_root_ram {F : Type*} [NormedField F] [IsUltrametricDist F]
    {π : F} (hπ : NormUnif π) {δ : F} {k : ℤ} (hδ : ‖δ‖ = ‖π‖ ^ k) (hk : Odd k) :
    ∀ r : F, r ^ 2 ≠ δ + 0 * r := by
  intro r
  intro h_eq
  -- h_eq : r ^ 2 = δ + 0 * r
  -- simplify to r ^ 2 = δ
  have h_eq' : r ^ 2 = δ := by
    simpa using h_eq
  -- Take norms
  have h_norm_sq : ‖r ^ 2‖ = ‖r‖ ^ 2 := by
    simpa using norm_pow r 2
  have h_norm_eq : ‖r‖ ^ 2 = ‖π‖ ^ k := by
    calc
      ‖r‖ ^ 2 = ‖r ^ 2‖ := by rw [h_norm_sq]
      _ = ‖δ‖ := by rw [h_eq']
      _ = ‖π‖ ^ k := hδ
  -- δ ≠ 0 because its norm is a positive power of ‖π‖
  have hπ_norm_pos : 0 < ‖π‖ := by
    rw [norm_pos_iff]
    exact hπ.ne_zero
  have hπ_norm_ne_zero : ‖π‖ ≠ 0 := by linarith
  have hδ_ne_zero : δ ≠ 0 := by
    intro hzero
    have hnorm0 : ‖δ‖ = 0 := by simpa [hzero] using norm_zero
    rw [hδ] at hnorm0
    have hzpow_ne_zero : ‖π‖ ^ k ≠ 0 := zpow_ne_zero k hπ_norm_ne_zero
    exact hzpow_ne_zero hnorm0
  -- So r ≠ 0
  have hr_ne_zero : r ≠ 0 := by
    intro hzero
    apply hδ_ne_zero
    simpa [hzero] using h_eq'.symm
  -- Use the discrete valuation property
  rcases hπ.disc r hr_ne_zero with ⟨n, hn⟩
  -- hn : ‖r‖ = ‖π‖ ^ n
  rw [hn] at h_norm_eq
  -- h_norm_eq : (‖π‖ ^ n) ^ 2 = ‖π‖ ^ k
  -- Convert (‖π‖ ^ n) ^ 2 to ‖π‖ ^ (2 * n)
  have h_pow_eq : (‖π‖ ^ n) ^ 2 = ‖π‖ ^ (2 * n) := by
    calc
      (‖π‖ ^ n) ^ 2 = (‖π‖ ^ n) * (‖π‖ ^ n) := by rw [pow_two]
      _ = ‖π‖ ^ (n + n) := by rw [zpow_add₀ hπ_norm_ne_zero n n]
      _ = ‖π‖ ^ (2 * n) := by rw [two_mul]
  rw [h_pow_eq] at h_norm_eq
  -- h_norm_eq : ‖π‖ ^ (2 * n) = ‖π‖ ^ k
  -- Use injectivity of zpow
  have hzpow_inj : Function.Injective fun (m : ℤ) => ‖π‖ ^ m :=
    zpow_right_injective₀ hπ_norm_pos (by linarith [hπ.norm_lt_one])
  have h_exp_eq : 2 * n = k :=
    hzpow_inj h_norm_eq
  -- Now h_exp_eq : 2 * n = k
  -- So k is even, but hk says k is odd, contradiction
  have h_even_k : Even k := by
    rw [← h_exp_eq]
    exact even_two_mul n
  -- Now derive contradiction from Odd k and Even k
  rcases hk with ⟨m, hm⟩
  rcases h_even_k with ⟨p, hp⟩
  -- hm : k = 2 * m + 1
  -- hp : k = p + p
  rw [hm] at hp
  -- hp : 2 * m + 1 = p + p
  have hp' : p + p = 2 * p := by ring
  rw [hp'] at hp
  -- hp : 2 * m + 1 = 2 * p
  -- So 1 = 2 * (p - m)
  have hdiv : (2 : ℤ) ∣ (1 : ℤ) := by
    have : (1 : ℤ) = 2 * (p - m) := by linarith
    rw [this]
    exact ⟨p - m, rfl⟩
  have hnot : ¬ (2 : ℤ) ∣ (1 : ℤ) := by norm_num
  exact hnot hdiv

end Residue

end FurioLombardo.Discharge.SelmerBasis
