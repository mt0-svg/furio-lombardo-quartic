import FurioLombardo.Discharge.SelmerBasis.Bridge
import FurioLombardo.Discharge.SelmerBasis.Echelon

/-!
# Generators of `F^×` modulo squares, and component facts from residue fields

For a proper ultrametric normed field `F` with a norm uniformizer `π`:

* `sb_span_dyadic`: with residue field `𝔽₂` and `‖2‖ = ‖π‖ ^ e`, `e > 0`, the elements
  `dyGen π i` (`π`, then `1 + π ^ i` for `1 ≤ i ≤ 2e`) span `F^×` modulo squares;
* `sb_span_odd`: in odd residue characteristic, `π` and a unit `u` with `u ^ N ≡ -1` span `F^×`
  modulo squares (Fermat and Euler congruences as hypotheses, from the residue field in Bridge.lean);
* `compOK_F2`, `compOK_F4`, `compOK_odd`: the `CompOK` facts of Echelon.lean for residue fields `𝔽₂`,
  `𝔽₄` (lifts `1, ω`) and odd residue characteristic.
-/

namespace FurioLombardo.Discharge.SelmerBasis

/-- The generators `π, 1 + π, 1 + π ^ 2, …` of `F^×` modulo squares (residue field `𝔽₂`). -/
def dyGen {F : Type*} [NormedField F] (π : F) (i : ℕ) : F := if i = 0 then π else 1 + π ^ i

/-- Raising the depth: a unit at depth `i ≥ 1` times `1 + π ^ i` has depth `> i` (residue field `𝔽₂`). -/
theorem sb_depth_step {F : Type*} [NormedField F] [IsUltrametricDist F] {π : F} (hπ0 : π ≠ 0)
    (hπ1 : ‖π‖ < 1) (h21 : ‖(2 : F)‖ < 1)
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) {i : ℕ} (hi : 1 ≤ i) {z : F}
    (hz : ‖z - 1‖ = ‖π‖ ^ i) : ‖z * (1 + π ^ i) - 1‖ < ‖π‖ ^ i := by
  have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.mpr hπ0) i
  have hpi0 : π ^ i ≠ 0 := pow_ne_zero i hπ0
  set u := (z - 1) / π ^ i with hu
  have hzu : z - 1 = π ^ i * u := by rw [hu]; field_simp
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, hz, norm_pow, div_self hpi.ne']
  have hu2 : ‖u - 1‖ < 1 := by
    rcases hres u hu1.le with h | h
    · exact absurd hu1 h.ne
    · exact h
  have hu3 : ‖u + 1‖ < 1 := by
    have : u + 1 = (u - 1) + 2 := by ring
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hu2 h21)
  have hid : z * (1 + π ^ i) - 1 = π ^ i * (u + 1) + π ^ i * π ^ i * u := by
    have hz' : z = 1 + π ^ i * u := by rw [← hzu]; ring
    rw [hz']; ring
  rw [hid]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_pow]
    calc ‖π‖ ^ i * ‖u + 1‖ < ‖π‖ ^ i * 1 := mul_lt_mul_of_pos_left hu3 hpi
      _ = ‖π‖ ^ i := mul_one _
  · rw [norm_mul, norm_mul, norm_pow, hu1, mul_one]
    calc ‖π‖ ^ i * ‖π‖ ^ i < ‖π‖ ^ i * 1 :=
          mul_lt_mul_of_pos_left (pow_lt_one₀ (norm_nonneg _) hπ1 (by omega)) hpi
      _ = ‖π‖ ^ i := mul_one _

open Finset in
theorem prod_pow_update_one {M : Type*} [CommMonoid M] {n : ℕ} (g : Fin n → M)
    (c : Fin n → ZMod 2) (j : Fin n) (hj : c j = 0) :
    ∏ i, g i ^ (Function.update c j 1 i).val = (∏ i, g i ^ (c i).val) * g j := by
  classical
  rw [← Finset.mul_prod_erase univ _ (mem_univ j),
    ← Finset.mul_prod_erase univ (fun i => g i ^ (c i).val) (mem_univ j)]
  simp only [Function.update_self, hj, ZMod.val_zero, pow_zero, one_mul]
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, mul_comm]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

open Finset in
/-- The depth induction of `sb_span_dyadic` for a unit `u`. -/
theorem sb_span_unit_depth {F : Type*} [NormedField F] [IsUltrametricDist F]
    {π : F} (hπ : NormUnif π) {e : ℕ} (h21 : ‖(2 : F)‖ < 1)
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) {u : F} (hu : ‖u‖ = 1) :
    ∀ d : ℕ, d ≤ 2 * e → ∃ c : Fin (2 * e + 1) → ZMod 2, c 0 = 0 ∧
      (∀ i : Fin (2 * e + 1), d < i.val → c i = 0) ∧
      ‖u * ∏ i : Fin (2 * e + 1), dyGen π i ^ (c i).val - 1‖ < ‖π‖ ^ d := by
  have hπ0 := hπ.ne_zero
  have hπ1 := hπ.norm_lt_one
  have hp0 : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨0, rfl, fun _ _ => rfl, ?_⟩
    simp only [Pi.zero_apply, ZMod.val_zero, pow_zero, prod_const_one, mul_one]
    rcases hres u hu.le with h | h
    · exact absurd hu h.ne
    · exact h
  | succ d ih =>
    intro hd
    obtain ⟨c, hc0, hcd, hz⟩ := ih (by omega)
    set z := u * ∏ i : Fin (2 * e + 1), dyGen π i ^ (c i).val with hzdef
    by_cases hlt : ‖z - 1‖ < ‖π‖ ^ (d + 1)
    · exact ⟨c, hc0, fun i hi => hcd i (by omega), hlt⟩
    have hge : ‖π‖ ^ (d + 1) ≤ ‖z - 1‖ := not_lt.mp hlt
    have hz1 : z - 1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hge
      exact absurd hge (not_le.mpr (pow_pos hp0 _))
    obtain ⟨m, hm⟩ := hπ.disc _ hz1
    have hmd : m = ((d + 1 : ℕ) : ℤ) := by
      have h1 : ‖π‖ ^ (((d + 1 : ℕ) : ℤ)) ≤ ‖π‖ ^ m := by rw [zpow_natCast, ← hm]; exact hge
      have h2 : ‖π‖ ^ m < ‖π‖ ^ ((d : ℕ) : ℤ) := by rw [zpow_natCast, ← hm]; exact hz
      have h1' : m ≤ ((d + 1 : ℕ) : ℤ) := by
        by_contra h
        have := zpow_lt_zpow_right_of_lt_one₀ hp0 hπ1 (not_le.mp h)
        linarith
      have h2' : ((d : ℕ) : ℤ) < m := by
        by_contra h
        have := zpow_le_zpow_right_of_le_one₀ hp0 hπ1.le (not_lt.mp h)
        linarith
      push_cast at h1' h2' ⊢
      omega
    rw [hmd, zpow_natCast] at hm
    have hstep := sb_depth_step hπ0 hπ1 h21 hres (i := d + 1) (by omega) hm
    have hj : d + 1 < 2 * e + 1 := by omega
    set j : Fin (2 * e + 1) := ⟨d + 1, hj⟩
    refine ⟨Function.update c j 1, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by simp [j, Fin.ext_iff])]
      exact hc0
    · intro i hi
      rw [Function.update_of_ne (by intro h; subst h; simp [j] at hi)]
      exact hcd i (by omega)
    · rw [prod_pow_update_one _ c j (hcd j (by simp [j])), ← mul_assoc, ← hzdef]
      have hg : dyGen π j = 1 + π ^ (d + 1) := by simp [dyGen, j]
      rw [hg]
      exact hstep

/-- **Dyadic spanning** (residue field `𝔽₂`). -/
theorem sb_span_dyadic {F : Type*} [NormedField F] [IsUltrametricDist F] [ProperSpace F]
    {π : F} (hπ : NormUnif π) {e : ℕ} (he : 0 < e) (h2 : ‖(2 : F)‖ = ‖π‖ ^ e)
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (x : F) (hx : x ≠ 0) :
    ∃ c : Fin (2 * e + 1) → ZMod 2, IsSquare (x * ∏ i : Fin (2 * e + 1), dyGen π i ^ (c i).val) := by
  classical
  have hπ0 := hπ.ne_zero
  have hπ1 := hπ.norm_lt_one
  have hp0 : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have h21 : ‖(2 : F)‖ < 1 := by rw [h2]; exact pow_lt_one₀ (norm_nonneg _) hπ1 he.ne'
  have h20 : (2 : F) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact absurd h2.symm (pow_pos hp0 e).ne'
  obtain ⟨k, hk⟩ := hπ.disc x hx
  set u := x * π ^ (-k) with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_mul, norm_zpow, hk, ← zpow_add₀ hp0.ne', add_neg_cancel, zpow_zero]
  have hxu : x = π ^ k * u := by
    rw [hudef, ← mul_assoc, mul_comm (π ^ k) x, mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel,
      zpow_zero, mul_one]
  obtain ⟨c, hc0, -, hz⟩ := sb_span_unit_depth hπ h21 hres hu (2 * e) le_rfl
  have h4 : ‖(4 : F)‖ = ‖π‖ ^ (2 * e) := by
    rw [show (4 : F) = 2 * 2 by norm_num, norm_mul, h2, ← pow_add, two_mul]
  have hsqu : IsSquare (u * ∏ i : Fin (2 * e + 1), dyGen π i ^ (c i).val) :=
    isSquare_of_norm_sub_one_lt hπ h20 (by rw [h4]; exact hz)
  set a : ZMod 2 := if Even k then 0 else 1
  refine ⟨Function.update c 0 a, ?_⟩
  have hprod : ∏ i : Fin (2 * e + 1), dyGen π i ^ (Function.update c 0 a i).val =
      (∏ i : Fin (2 * e + 1), dyGen π i ^ (c i).val) * π ^ a.val := by
    by_cases hk2 : Even k
    · have ha : a = 0 := by simp [a, hk2]
      rw [ha, Function.update_eq_self_iff.mpr hc0.symm]
      simp
    · have ha : a = 1 := by simp [a, hk2]
      rw [ha, prod_pow_update_one _ c 0 hc0]
      simp [dyGen, show (1 : ZMod 2).val = 1 from rfl]
  rw [hprod, hxu]
  have hev : Even (k + (a.val : ℤ)) := by
    by_cases hk2 : Even k
    · simp [a, hk2]
    · simp only [a, hk2, ite_false, show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one]
      exact (Int.not_even_iff_odd.mp hk2).add_one
  obtain ⟨m, hm⟩ := hev
  have hsqπ : IsSquare (π ^ (k + (a.val : ℤ))) := ⟨π ^ m, by rw [hm, zpow_add₀ hπ0]⟩
  have hπa : π ^ k * π ^ a.val = π ^ (k + (a.val : ℤ)) := by
    rw [zpow_add₀ hπ0, zpow_natCast]
  have heq : π ^ k * u * ((∏ i : Fin (2 * e + 1), dyGen π i ^ (c i).val) * π ^ a.val) =
      π ^ (k + (a.val : ℤ)) * (u * ∏ i : Fin (2 * e + 1), dyGen π i ^ (c i).val) := by
    rw [← hπa]; ring
  rw [heq]
  exact hsqπ.mul hsqu


/-- **Spanning in odd residue characteristic.** -/
theorem sb_span_odd {F : Type*} [NormedField F] [IsUltrametricDist F] [ProperSpace F]
    {π : F} (hπ : NormUnif π) (h2 : ‖(2 : F)‖ = 1) {N : ℕ}
    (hferm : ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ (2 * N) - 1‖ < 1)
    (heuler : ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ N - 1‖ < 1 → ∃ s : F, ‖ξ - s ^ 2‖ < 1)
    {u : F} (hu : ‖u‖ = 1) (hun : ‖u ^ N + 1‖ < 1) (x : F) (hx : x ≠ 0) :
    ∃ c : Fin 2 → ZMod 2, IsSquare (x * ∏ l : Fin 2, ![π, u] l ^ (c l).val) := by
  have h2_ne_zero : (2 : F) ≠ 0 := by
    intro hzero; rw [hzero, norm_zero] at h2; linarith
  obtain ⟨n, hn⟩ := hπ.disc x hx
  have hπ_ne_zero : π ≠ 0 := hπ.ne_zero
  set ξ := x * (π ^ n)⁻¹ with hξ_def
  have hξ_norm : ‖ξ‖ = 1 := by
    rw [hξ_def, norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [hn, norm_zpow]
    have hpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ_ne_zero
    have hpos' : 0 < ‖π‖ ^ n := zpow_pos hpos n
    exact div_self hpos'.ne'
  let c0 : ZMod 2 := (n : ZMod 2)
  have h_cases : c0 = 0 ∨ c0 = 1 := by
    have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact h_all c0
  have hx2N : ‖ξ ^ (2 * N) - 1‖ < 1 := hferm ξ hξ_norm
  have hprod : (ξ ^ N - 1) * (ξ ^ N + 1) = ξ ^ (2 * N) - 1 := by ring
  have hprod_norm : ‖(ξ ^ N - 1) * (ξ ^ N + 1)‖ < 1 := by rw [hprod]; exact hx2N
  have hle1 : ‖ξ ^ N - 1‖ ≤ 1 := by
    have : ‖ξ ^ N - 1‖ = ‖ξ ^ N + (-1)‖ := by ring_nf
    rw [this]
    calc
      ‖ξ ^ N + (-1)‖ ≤ max (‖ξ ^ N‖) (‖(-1 : F)‖) := IsUltrametricDist.norm_add_le_max _ _
      _ = max (‖ξ‖ ^ N) 1 := by simp [norm_pow]
      _ = max (1 ^ N) 1 := by rw [hξ_norm]
      _ = 1 := by simp
  have hle2 : ‖ξ ^ N + 1‖ ≤ 1 := by
    calc
      ‖ξ ^ N + 1‖ ≤ max (‖ξ ^ N‖) (‖(1 : F)‖) := IsUltrametricDist.norm_add_le_max _ _
      _ = max (‖ξ‖ ^ N) 1 := by simp [norm_pow]
      _ = max (1 ^ N) 1 := by rw [hξ_norm]
      _ = 1 := by simp
  by_cases hcase : ‖ξ ^ N - 1‖ < 1
  · -- Case 1: ‖ξ^N - 1‖ < 1
    obtain ⟨s, hs⟩ := heuler ξ hξ_norm hcase
    have hs_norm : ‖s‖ = 1 := by
      have h_sq_le_one : ‖s ^ 2‖ ≤ 1 := by
        have h_eq : s ^ 2 = ξ + (-(ξ - s ^ 2)) := by ring_nf
        rw [h_eq]
        calc
          ‖ξ + (-(ξ - s ^ 2))‖ ≤ max (‖ξ‖) (‖-(ξ - s ^ 2)‖) :=
            IsUltrametricDist.norm_add_le_max _ _
          _ = max (‖ξ‖) (‖ξ - s ^ 2‖) := by rw [norm_neg]
          _ = max 1 (‖ξ - s ^ 2‖) := by rw [hξ_norm]
          _ = 1 := max_eq_left (by linarith)
      have h_one_le_sq : 1 ≤ ‖s ^ 2‖ := by
        have h_eq : ‖ξ‖ = ‖(ξ - s ^ 2) + s ^ 2‖ := by ring_nf
        rw [h_eq] at hξ_norm
        have h_max : ‖(ξ - s ^ 2) + s ^ 2‖ ≤ max (‖ξ - s ^ 2‖) (‖s ^ 2‖) :=
          IsUltrametricDist.norm_add_le_max _ _
        rw [hξ_norm] at h_max
        have h' : 1 ≤ max (‖ξ - s ^ 2‖) (‖s ^ 2‖) := h_max
        rcases le_max_iff.mp h' with (h | h)
        · linarith
        · exact h
      have h_sq_eq_one : ‖s ^ 2‖ = 1 := by linarith
      have h_norm_sq : ‖s ^ 2‖ = ‖s‖ ^ 2 := norm_pow _ 2
      rw [h_norm_sq] at h_sq_eq_one
      have h_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
      nlinarith
    have hs_ne_zero : s ≠ 0 := by
      intro hzero; rw [hzero, norm_zero] at hs_norm; linarith
    have h_sq_ξ : IsSquare ξ := by
      apply isSquare_of_norm_div_sq_sub_one_lt hπ h2_ne_zero hs_ne_zero
      have h_norm_four : ‖(4 : F)‖ = 1 := by
        calc
          ‖(4 : F)‖ = ‖(2 : F) ^ 2‖ := by norm_num
          _ = ‖(2 : F)‖ ^ 2 := norm_pow _ 2
          _ = 1 ^ 2 := by rw [h2]
          _ = 1 := by norm_num
      rw [h_norm_four]
      -- Need to show ‖ξ / s^2 - 1‖ < 1
      -- We have ‖ξ - s^2‖ < 1 and ‖s‖ = 1
      -- ‖ξ / s^2 - 1‖ = ‖(ξ - s^2) / s^2‖ = ‖ξ - s^2‖ / ‖s^2‖ = ‖ξ - s^2‖ < 1
      have hgoal : ‖ξ / s ^ 2 - 1‖ < 1 := by
        calc
          ‖ξ / s ^ 2 - 1‖ = ‖(ξ - s ^ 2) / s ^ 2‖ := by field_simp [hs_ne_zero]
          _ = ‖ξ - s ^ 2‖ / ‖s ^ 2‖ := by rw [norm_div]
          _ = ‖ξ - s ^ 2‖ / 1 := by rw [norm_pow, hs_norm, one_pow]
          _ = ‖ξ - s ^ 2‖ := by simp
          _ < 1 := hs
      exact hgoal
    -- Build c
    let c : Fin 2 → ZMod 2 := λ i => match i with | 0 => c0 | 1 => 0
    refine ⟨c, ?_⟩
    have h_prod : (∏ l : Fin 2, ![π, u] l ^ (c l).val) = π ^ (c 0).val * u ^ (c 1).val := by
      simp [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h_prod]
    have hc0_val : (c 0).val = (c0 : ZMod 2).val := rfl
    have hc1_val : (c 1).val = (0 : ZMod 2).val := rfl
    simp [hc0_val, hc1_val, ZMod.val_zero]
    -- Goal: IsSquare (x * π ^ (c0.val))
    have hx_eq : x = ξ * π ^ n := by
      rw [hξ_def]; field_simp [zpow_ne_zero n hπ_ne_zero]
    rw [hx_eq]
    -- Goal: IsSquare ((ξ * π ^ n) * π ^ (c0.val))
    rcases h_cases with (hc0_zero | hc0_one)
    · -- c0 = 0, so c0.val = 0 and n is even
      have h_val : (c0 : ZMod 2).val = 0 := by simp [hc0_zero]
      rw [h_val, pow_zero, mul_one]
      -- Goal: IsSquare (ξ * π ^ n)
      -- Since n is even, π^n is a square
      have h_mod2 : (n : ZMod 2) = (0 : ZMod 2) := by
        simpa [c0] using hc0_zero
      have h_cong : n ≡ (0 : ℤ) [ZMOD 2] :=
        (ZMod.intCast_eq_intCast_iff (a := n) (b := (0 : ℤ)) (c := 2)).mp h_mod2
      have h_dvd : (2 : ℤ) ∣ n := by
        have h := (Int.modEq_iff_dvd.mp h_cong)
        simpa [sub_zero, dvd_neg] using h
      obtain ⟨k, hk⟩ := h_dvd
      have h_sq_pi : IsSquare (π ^ n) := by
        rw [hk]
        -- Goal: IsSquare (π ^ (2 * k : ℤ))
        have h_eq : π ^ (2 * k : ℤ) = (π ^ k) ^ 2 := by
          simpa [mul_comm] using zpow_mul (a := π) (m := k) (n := 2)
        rw [h_eq]
        exact ⟨π ^ k, pow_two _⟩
      rcases h_sq_ξ with ⟨a, ha⟩
      rcases h_sq_pi with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        ξ * π ^ n = (a * a) * (b * b) := by rw [ha, hb]
        _ = a * b * (a * b) := by ring_nf
        _ = (a * b) * (a * b) := by ring
    · -- c0 = 1, so c0.val = 1 and n is odd, so n+1 is even
      have h_val : (c0 : ZMod 2).val = 1 := by
        simp [hc0_one, ZMod.val_one]
      rw [h_val, pow_one]
      -- Goal: IsSquare (ξ * π ^ n * π)
      have h_mod2 : (n : ZMod 2) = (1 : ZMod 2) := by
        simpa [c0] using hc0_one
      have h_cong : n ≡ (1 : ℤ) [ZMOD 2] :=
        (ZMod.intCast_eq_intCast_iff (a := n) (b := (1 : ℤ)) (c := 2)).mp h_mod2
      have h_dvd : (2 : ℤ) ∣ n + 1 := by
        have h_dvd_sub : (2 : ℤ) ∣ n - 1 := by
          have h := (Int.modEq_iff_dvd.mp h_cong)
          -- h : 2 ∣ 1 - n
          have : (1 : ℤ) - n = -(n - 1) := by ring
          rw [this] at h
          rwa [dvd_neg] at h
        have : n + 1 = (n - 1) + 2 := by ring
        rw [this]
        exact h_dvd_sub.add (by norm_num)
      obtain ⟨k, hk⟩ := h_dvd
      have h_sq_pi : IsSquare (π ^ n * π) := by
        have h_eq : π ^ n * π = π ^ k * π ^ k := by
          calc
            π ^ n * π = π ^ n * π ^ (1 : ℤ) := by simp
            _ = π ^ (n + 1 : ℤ) := by
              rw [zpow_add' (Or.inl hπ_ne_zero) (a := π) (m := n) (n := (1 : ℤ))]
            _ = π ^ (2 * k : ℤ) := by rw [hk]
            _ = (π ^ k) ^ 2 := by
              simpa [mul_comm, sq] using zpow_mul (a := π) (m := k) (n := 2)
            _ = π ^ k * π ^ k := by rw [sq]
        exact ⟨π ^ k, h_eq⟩
      rcases h_sq_ξ with ⟨a, ha⟩
      rcases h_sq_pi with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        ξ * π ^ n * π = ξ * (π ^ n * π) := by ring
        _ = (a * a) * (b * b) := by rw [ha, hb]
        _ = a * b * (a * b) := by ring_nf
        _ = (a * b) * (a * b) := by ring
  · -- Case 2: ‖ξ^N - 1‖ ≥ 1, so ‖ξ^N + 1‖ < 1
    have hcase2 : ‖ξ ^ N + 1‖ < 1 := by
      have h_eq_one : ‖ξ ^ N - 1‖ = 1 := by linarith
      have h_mul_norm : ‖(ξ ^ N - 1) * (ξ ^ N + 1)‖ = ‖ξ ^ N - 1‖ * ‖ξ ^ N + 1‖ := norm_mul _ _
      rw [h_mul_norm] at hprod_norm
      rw [h_eq_one] at hprod_norm
      have : 0 ≤ ‖ξ ^ N + 1‖ := norm_nonneg _
      linarith
    have h_norm_xu : ‖ξ * u‖ = 1 := by
      rw [norm_mul, hξ_norm, hu, mul_one]
    have h_xu_N_near_one : ‖(ξ * u) ^ N - 1‖ < 1 := by
      have ha_norm : ‖ξ ^ N + 1‖ < 1 := hcase2
      have hb_norm : ‖u ^ N + 1‖ < 1 := hun
      set a := ξ ^ N + 1 with ha_def
      set b := u ^ N + 1 with hb_def
      have ha_norm' : ‖a‖ < 1 := ha_norm
      have hb_norm' : ‖b‖ < 1 := hb_norm
      rw [mul_pow]
      have h_expand : ξ ^ N * u ^ N = 1 - a - b + a * b := by
        rw [ha_def, hb_def]; ring_nf
      rw [h_expand]
      have : (1 - a - b + a * b) - 1 = -(a + b - a * b) := by ring_nf
      rw [this]
      rw [norm_neg]
      have h_inner : ‖a + b - a * b‖ = ‖a + (b - a * b)‖ := by ring_nf
      rw [h_inner]
      have h_le : ‖a + (b - a * b)‖ ≤ max (‖a‖) (‖b - a * b‖) :=
        IsUltrametricDist.norm_add_le_max _ _
      have h_le2 : ‖b - a * b‖ ≤ max (‖b‖) (‖a * b‖) := by
        rw [sub_eq_add_neg]
        calc
          ‖b + (-(a * b))‖ ≤ max (‖b‖) (‖-(a * b)‖) := IsUltrametricDist.norm_add_le_max _ _
          _ = max (‖b‖) (‖a * b‖) := by rw [norm_neg]
      have h_mul : ‖a * b‖ = ‖a‖ * ‖b‖ := norm_mul _ _
      rw [h_mul] at h_le2
      have h_max_le : max (‖a‖) (‖b - a * b‖) ≤ max (‖a‖) (max (‖b‖) (‖a‖ * ‖b‖)) := by
        refine max_le_max (le_refl _) ?_
        exact h_le2
      have h_max_lt : max (‖a‖) (max (‖b‖) (‖a‖ * ‖b‖)) < 1 := by
        refine max_lt ha_norm' ?_
        refine max_lt hb_norm' ?_
        nlinarith [norm_nonneg a, norm_nonneg b]
      linarith
    obtain ⟨s, hs⟩ := heuler (ξ * u) h_norm_xu h_xu_N_near_one
    have hs_norm : ‖s‖ = 1 := by
      have h_sq_le_one : ‖s ^ 2‖ ≤ 1 := by
        have h_eq : s ^ 2 = (ξ * u) + (-((ξ * u) - s ^ 2)) := by ring
        rw [h_eq]
        calc
          ‖(ξ * u) + (-((ξ * u) - s ^ 2))‖ ≤ max (‖ξ * u‖) (‖-((ξ * u) - s ^ 2)‖) :=
            IsUltrametricDist.norm_add_le_max _ _
          _ = max (‖ξ * u‖) (‖(ξ * u) - s ^ 2‖) := by rw [norm_neg]
          _ = max 1 (‖(ξ * u) - s ^ 2‖) := by rw [h_norm_xu]
          _ = 1 := max_eq_left (by linarith)
      have h_one_le_sq : 1 ≤ ‖s ^ 2‖ := by
        have h_eq : ‖ξ * u‖ = ‖((ξ * u) - s ^ 2) + s ^ 2‖ := by ring
        rw [h_eq] at h_norm_xu
        have h_max : ‖((ξ * u) - s ^ 2) + s ^ 2‖ ≤ max (‖(ξ * u) - s ^ 2‖) (‖s ^ 2‖) :=
          IsUltrametricDist.norm_add_le_max _ _
        rw [h_norm_xu] at h_max
        have h' : 1 ≤ max (‖(ξ * u) - s ^ 2‖) (‖s ^ 2‖) := h_max
        rcases le_max_iff.mp h' with (h | h)
        · linarith
        · exact h
      have h_sq_eq_one : ‖s ^ 2‖ = 1 := by linarith
      have h_norm_sq : ‖s ^ 2‖ = ‖s‖ ^ 2 := norm_pow _ 2
      rw [h_norm_sq] at h_sq_eq_one
      have h_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
      nlinarith
    have hs_ne_zero : s ≠ 0 := by
      intro hzero; rw [hzero, norm_zero] at hs_norm; linarith
    have h_sq_xu : IsSquare (ξ * u) := by
      apply isSquare_of_norm_div_sq_sub_one_lt hπ h2_ne_zero hs_ne_zero
      have h_norm_four : ‖(4 : F)‖ = 1 := by
        calc
          ‖(4 : F)‖ = ‖(2 : F) ^ 2‖ := by norm_num
          _ = ‖(2 : F)‖ ^ 2 := norm_pow _ 2
          _ = 1 ^ 2 := by rw [h2]
          _ = 1 := by norm_num
      rw [h_norm_four]
      have hgoal : ‖(ξ * u) / s ^ 2 - 1‖ < 1 := by
        calc
          ‖(ξ * u) / s ^ 2 - 1‖ = ‖((ξ * u) - s ^ 2) / s ^ 2‖ := by
            field_simp [hs_ne_zero]
          _ = ‖(ξ * u) - s ^ 2‖ / ‖s ^ 2‖ := by rw [norm_div]
          _ = ‖(ξ * u) - s ^ 2‖ / 1 := by rw [norm_pow, hs_norm, one_pow]
          _ = ‖(ξ * u) - s ^ 2‖ := by simp
          _ < 1 := hs
      exact hgoal
    -- Build c with c1 = 1
    let c : Fin 2 → ZMod 2 := λ i => match i with | 0 => c0 | 1 => 1
    refine ⟨c, ?_⟩
    have h_prod : (∏ l : Fin 2, ![π, u] l ^ (c l).val) = π ^ (c 0).val * u ^ (c 1).val := by
      simp [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h_prod]
    have hc0_val : (c 0).val = (c0 : ZMod 2).val := rfl
    have hc1_val : (c 1).val = (1 : ZMod 2).val := rfl
    simp [hc0_val, hc1_val, ZMod.val_one]
    -- Goal: IsSquare (x * π ^ (c0.val) * u)
    have hx_eq : x = ξ * π ^ n := by
      rw [hξ_def]; field_simp [zpow_ne_zero n hπ_ne_zero]
    rw [hx_eq]
    -- Goal: IsSquare ((ξ * π ^ n) * π ^ (c0.val) * u)
    -- Rearrange to IsSquare ((ξ * u) * (π ^ n * π ^ (c0.val)))
    ring_nf
    -- After ring_nf: IsSquare (ξ * u * (π ^ n * π ^ (c0.val)))
    rcases h_cases with (hc0_zero | hc0_one)
    · -- c0 = 0, so c0.val = 0 and n is even
      have h_val : (c0 : ZMod 2).val = 0 := by simp [hc0_zero]
      rw [h_val, pow_zero, mul_one]
      -- Goal: IsSquare (ξ * u * π ^ n)
      -- Since n is even, π^n is a square
      have h_mod2 : (n : ZMod 2) = (0 : ZMod 2) := by
        simpa [c0] using hc0_zero
      have h_cong : n ≡ (0 : ℤ) [ZMOD 2] :=
        (ZMod.intCast_eq_intCast_iff (a := n) (b := (0 : ℤ)) (c := 2)).mp h_mod2
      have h_dvd : (2 : ℤ) ∣ n := by
        have h := (Int.modEq_iff_dvd.mp h_cong)
        simpa [sub_zero, dvd_neg] using h
      obtain ⟨k, hk⟩ := h_dvd
      have h_sq_pi : IsSquare (π ^ n) := by
        rw [hk]
        -- Goal: IsSquare (π ^ (2 * k : ℤ))
        have h_eq : π ^ (2 * k : ℤ) = (π ^ k) ^ 2 := by
          simpa [mul_comm] using zpow_mul (a := π) (m := k) (n := 2)
        rw [h_eq]
        exact ⟨π ^ k, pow_two _⟩
      rcases h_sq_xu with ⟨a, ha⟩
      rcases h_sq_pi with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        ξ * π ^ n * u = (ξ * u) * π ^ n := by ring
        _ = (a * a) * π ^ n := by rw [ha]
        _ = (a * a) * (b * b) := by rw [hb]
        _ = a * b * (a * b) := by ring_nf
        _ = (a * b) * (a * b) := by ring
    · -- c0 = 1, so c0.val = 1 and n is odd, so n+1 is even
      have h_val : (c0 : ZMod 2).val = 1 := by
        simp [hc0_one, ZMod.val_one]
      rw [h_val, pow_one]
      -- Goal: IsSquare (ξ * u * π ^ n * π)
      have h_mod2 : (n : ZMod 2) = (1 : ZMod 2) := by
        simpa [c0] using hc0_one
      have h_cong : n ≡ (1 : ℤ) [ZMOD 2] :=
        (ZMod.intCast_eq_intCast_iff (a := n) (b := (1 : ℤ)) (c := 2)).mp h_mod2
      have h_dvd : (2 : ℤ) ∣ n + 1 := by
        have h_dvd_sub : (2 : ℤ) ∣ n - 1 := by
          have h := (Int.modEq_iff_dvd.mp h_cong)
          -- h : 2 ∣ 1 - n
          have : (1 : ℤ) - n = -(n - 1) := by ring
          rw [this] at h
          rwa [dvd_neg] at h
        have : n + 1 = (n - 1) + 2 := by ring
        rw [this]
        exact h_dvd_sub.add (by norm_num)
      obtain ⟨k, hk⟩ := h_dvd
      have h_sq_pi : IsSquare (π ^ n * π) := by
        have h_eq : π ^ n * π = π ^ k * π ^ k := by
          calc
            π ^ n * π = π ^ n * π ^ (1 : ℤ) := by simp
            _ = π ^ (n + 1 : ℤ) := by
              rw [zpow_add' (Or.inl hπ_ne_zero) (a := π) (m := n) (n := (1 : ℤ))]
            _ = π ^ (2 * k : ℤ) := by rw [hk]
            _ = (π ^ k) ^ 2 := by
              simpa [mul_comm, sq] using zpow_mul (a := π) (m := k) (n := 2)
            _ = π ^ k * π ^ k := by rw [sq]
        exact ⟨π ^ k, h_eq⟩
      rcases h_sq_xu with ⟨a, ha⟩
      rcases h_sq_pi with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      calc
        ξ * π ^ n * π * u = (ξ * u) * (π ^ n * π) := by ring
        _ = (a * a) * (b * b) := by rw [ha, hb]
        _ = a * b * (a * b) := by ring_nf
        _ = (a * b) * (a * b) := by ring

/-- A unit that is a square in the field is a square in the unit group. -/
theorem isSquare_units_of_isSquare {F : Type*} [Field F] (x : Fˣ) (h : IsSquare (x : F)) :
    IsSquare x := by
  rcases h with ⟨s, hs⟩
  have hs_ne_zero : s ≠ 0 := by
    intro hzero
    apply Units.ne_zero x
    rw [hs, hzero, zero_mul]
  refine ⟨Units.mk0 s hs_ne_zero, ?_⟩
  apply Units.ext
  simpa [Units.val_mk0] using hs

/-- `CompOK` for residue field `𝔽₂`: lift `1`, trace bitmask `1`. -/
theorem compOK_F2 {F : Type*} [NormedField F] [IsUltrametricDist F] {π : F} (hπ : NormUnif π)
    {e : ℕ} (he : 0 < e) (h2 : ‖(2 : F)‖ = ‖π‖ ^ e)
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (N : ℕ) :
    CompOK ⟨e, 1, 1, N⟩ π ![1] := by
  have h_norm_two_lt_one : ‖(2 : F)‖ < 1 := by
    rw [h2]
    have hπ_lt_one : ‖π‖ < 1 := hπ.norm_lt_one
    have hπ_nonneg : 0 ≤ ‖π‖ := norm_nonneg _
    exact pow_lt_one₀ hπ_nonneg hπ_lt_one (by omega)
  have h_norm_one : ‖(1 : F)‖ = 1 := norm_one
  have h_bitv : bitv 1 1 0 = (1 : ZMod 2) := by
    simp [bitv]
  have h_zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hx_val_lt : x.val < 2 := ZMod.val_lt x
    have hx_val_nonneg : 0 ≤ x.val := Nat.zero_le _
    have hx_val_cases : x.val = 0 ∨ x.val = 1 := by omega
    rcases hx_val_cases with (h | h)
    · left; apply ZMod.val_injective; exact h
    · right; apply ZMod.val_injective; exact h
  refine
    { unif := hπ
      two := h2
      lift_le := ?_
      lift_ind := ?_
      trace := ?_
      fermat := ?_ }
  · -- lift_le: ∀ l, ‖w l‖ ≤ 1
    intro l
    simp [h_norm_one]
  · -- lift_ind: ∀ C : Fin 1 → ZMod 2, C ≠ 0 → ‖∑ l, ((C l).val : F) * w l‖ = 1
    intro C hC
    have hC0 : C 0 ≠ 0 := by
      intro hzero
      apply hC
      ext i
      fin_cases i
      exact hzero
    have hC0val : (C 0).val = 1 := by
      rcases h_zmod2_cases (C 0) with (h | h)
      · exact absurd h hC0
      · rw [h]
        decide
    have hsum : ∑ l : Fin 1, ((C l).val : F) * (![1] : Fin 1 → F) l = ((C 0).val : F) * 1 := by
      simp
    rw [hsum]
    simp [hC0val, h_norm_one]
  · -- trace: 0 < e → ∀ y, ∀ C, ...
    intro ye y C hy_norm h_lt
    have h_sum_eq : ∑ l : Fin 1, ((C l).val : F) * (![1] : Fin 1 → F) l = ((C 0).val : F) * 1 := by
      simp
    rw [h_sum_eq] at h_lt
    -- h_lt : ‖y ^ 2 + y - ((C 0).val : F) * 1‖ < 1
    have h_goal : ∑ l : Fin 1, C l * bitv 1 1 l = C 0 := by
      simp [h_bitv]
    rw [h_goal]
    by_cases hC0 : C 0 = 0
    · simp [hC0]
    · -- C 0 ≠ 0, so C 0 = 1, derive contradiction
      have hC0_one : C 0 = 1 := by
        rcases h_zmod2_cases (C 0) with (h | h)
        · exact absurd h hC0
        · exact h
      have hC0val_one : (C 0).val = 1 := by
        rw [hC0_one]
        decide
      rw [hC0val_one] at h_lt
      simp at h_lt
      -- h_lt : ‖y ^ 2 + y - 1‖ < 1
      rcases hres y hy_norm with (hy_lt | hy_sub_lt)
      · -- case ‖y‖ < 1
        have hy_sq_lt_one : ‖y ^ 2‖ < 1 := by
          rw [sq, norm_mul]
          have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
          have hy_lt_one : ‖y‖ < 1 := hy_lt
          nlinarith
        have hy_sq_add_y_lt_one : ‖y ^ 2 + y‖ < 1 := by
          have hmax := IsUltrametricDist.norm_add_le_max (y ^ 2) y
          have hmax_lt : max ‖y ^ 2‖ ‖y‖ < 1 :=
            max_lt hy_sq_lt_one hy_lt
          linarith
        have h_lt_norm : ‖y ^ 2 + y‖ ≠ ‖(-1 : F)‖ := by
          rw [norm_neg, h_norm_one]
          linarith
        have h_eq : ‖(y ^ 2 + y) + (-1 : F)‖ = max ‖y ^ 2 + y‖ ‖(-1 : F)‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_lt_norm
        have h_eq' : ‖y ^ 2 + y - 1‖ = 1 := by
          rw [sub_eq_add_neg]
          rw [h_eq]
          rw [norm_neg, h_norm_one]
          have hmax_eq : max ‖y ^ 2 + y‖ 1 = 1 :=
            max_eq_right (by linarith)
          rw [hmax_eq]
        rw [h_eq'] at h_lt
        linarith
      · -- case ‖y - 1‖ < 1
        have hy_add_one_lt_one : ‖y + 1‖ < 1 := by
          have : y + 1 = (y - 1) + 2 := by ring
          rw [this]
          have hmax := IsUltrametricDist.norm_add_le_max (y - 1) (2 : F)
          have hmax_lt : max ‖y - 1‖ ‖(2 : F)‖ < 1 :=
            max_lt hy_sub_lt h_norm_two_lt_one
          linarith
        have hy_sq_add_y_lt_one : ‖y ^ 2 + y‖ < 1 := by
          have : y ^ 2 + y = y * (y + 1) := by ring
          rw [this, norm_mul]
          have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
          have hy_add_one_nonneg : 0 ≤ ‖y + 1‖ := norm_nonneg _
          nlinarith
        have h_lt_norm : ‖y ^ 2 + y‖ ≠ ‖(-1 : F)‖ := by
          rw [norm_neg, h_norm_one]
          linarith
        have h_eq : ‖(y ^ 2 + y) + (-1 : F)‖ = max ‖y ^ 2 + y‖ ‖(-1 : F)‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_lt_norm
        have h_eq' : ‖y ^ 2 + y - 1‖ = 1 := by
          rw [sub_eq_add_neg]
          rw [h_eq]
          rw [norm_neg, h_norm_one]
          have hmax_eq : max ‖y ^ 2 + y‖ 1 = 1 :=
            max_eq_right (by linarith)
          rw [hmax_eq]
        rw [h_eq'] at h_lt
        linarith
  · -- fermat: e = 0 → ...
    intro he0
    have he0' : e = 0 := he0
    omega

/-- `CompOK` for residue field `𝔽₄ = 𝔽₂(ω̄)`: lifts `1, ω`, trace bitmask `2` (`Tr 1 = 0`,
`Tr ω̄ = 1`). -/
theorem compOK_F4 {F : Type*} [NormedField F] [IsUltrametricDist F] {π : F} (hπ : NormUnif π)
    {e : ℕ} (he : 0 < e) (h2 : ‖(2 : F)‖ = ‖π‖ ^ e) {ω : F} (hω : ‖ω‖ ≤ 1)
    (hω2 : ‖ω ^ 2 + ω + 1‖ < 1)
    (hres : ∀ y : F, ‖y‖ ≤ 1 → ∃ a b : ZMod 2, ‖y - ((a.val : F) + (b.val : F) * ω)‖ < 1) (N : ℕ) :
    CompOK ⟨e, 2, 2, N⟩ π ![1, ω] := by
  have hπ_ne_zero : π ≠ 0 := hπ.ne_zero
  have hπ_norm_lt_one : ‖π‖ < 1 := hπ.norm_lt_one
  have h2lt : ‖(2 : F)‖ < 1 := by
    rw [h2]
    have hpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ_ne_zero
    exact pow_lt_one₀ hpos.le hπ_norm_lt_one he.ne'
  have hω1 : ‖ω‖ = 1 := by
    by_contra! hne
    have hlt : ‖ω‖ < 1 := lt_of_le_of_ne hω hne
    have h_sq_le : ‖ω ^ 2‖ ≤ ‖ω‖ := by
      have hω_nonneg : 0 ≤ ‖ω‖ := norm_nonneg _
      calc
        ‖ω ^ 2‖ ≤ ‖ω‖ ^ 2 := norm_pow_le ω 2
        _ ≤ ‖ω‖ := by
          nlinarith
    have h_sq_lt_one : ‖ω ^ 2‖ < 1 := lt_of_le_of_lt h_sq_le hlt
    have h_sum_lt_one : ‖ω ^ 2 + ω‖ < 1 := by
      calc
        ‖ω ^ 2 + ω‖ ≤ max ‖ω ^ 2‖ ‖ω‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt h_sq_lt_one hlt
    have h_ne : ‖ω ^ 2 + ω‖ ≠ ‖(1 : F)‖ := by
      rw [norm_one]
      exact ne_of_lt h_sum_lt_one
    have h_eq : ‖(ω ^ 2 + ω) + 1‖ = max ‖ω ^ 2 + ω‖ ‖(1 : F)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
    rw [h_eq, norm_one, max_eq_right (by linarith)] at hω2
    linarith
  have h1ω : ‖1 + ω‖ = 1 := by
    by_contra! hne
    have hle : ‖1 + ω‖ ≤ 1 := by
      calc
        ‖1 + ω‖ ≤ max ‖(1 : F)‖ ‖ω‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max 1 ‖ω‖ := by rw [norm_one]
        _ = 1 := max_eq_left hω
    have hlt : ‖1 + ω‖ < 1 := lt_of_le_of_ne hle hne
    have h_nonneg : 0 ≤ ‖1 + ω‖ := norm_nonneg _
    have h_sq_lt_one : ‖(1 + ω) ^ 2‖ < 1 := by
      calc
        ‖(1 + ω) ^ 2‖ = ‖1 + ω‖ ^ 2 := norm_pow _ 2
        _ < 1 ^ 2 := by
          nlinarith
        _ = 1 := by norm_num
    have h_sum_lt_one : ‖(1 + ω) ^ 2 - (1 + ω)‖ < 1 := by
      calc
        ‖(1 + ω) ^ 2 - (1 + ω)‖ = ‖(1 + ω) ^ 2 + (-(1 + ω))‖ := by ring
        _ ≤ max ‖(1 + ω) ^ 2‖ ‖-(1 + ω)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖(1 + ω) ^ 2‖ ‖1 + ω‖ := by rw [norm_neg]
        _ < 1 := max_lt h_sq_lt_one hlt
    have h_ne : ‖(1 + ω) ^ 2 - (1 + ω)‖ ≠ ‖(1 : F)‖ := by
      rw [norm_one]
      exact ne_of_lt h_sum_lt_one
    have h_eq : ‖((1 + ω) ^ 2 - (1 + ω)) + 1‖ = max ‖(1 + ω) ^ 2 - (1 + ω)‖ ‖(1 : F)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
    have h_target : ω ^ 2 + ω + 1 = ((1 + ω) ^ 2 - (1 + ω)) + 1 := by
      ring
    rw [h_target, h_eq, norm_one, max_eq_right (by linarith)] at hω2
    linarith
  refine
    { unif := hπ
      two := h2
      lift_le := ?_
      lift_ind := ?_
      trace := ?_
      fermat := ?_ }
  · intro l
    fin_cases l <;> simp [norm_one, hω1]
  · intro C hC
    have hC0 : C 0 = 0 ∨ C 0 = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact this (C 0)
    have hC1 : C 1 = 0 ∨ C 1 = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact this (C 1)
    have hsum : (∑ l : Fin 2, ((C l).val : F) * ![1, ω] l) =
        ((C 0).val : F) * (1 : F) + ((C 1).val : F) * ω := by
      simp [Fin.sum_univ_two]
    rw [hsum]
    have hval0 : ((0 : ZMod 2).val : F) = (0 : F) := by norm_num
    have hval1 : ((1 : ZMod 2).val : F) = (1 : F) := by
      have h : (1 : ZMod 2).val = (1 : ℕ) := by decide
      simpa [h]
    rcases hC0 with (h0 | h0) <;> rcases hC1 with (h1 | h1)
    · exfalso; apply hC; ext l; fin_cases l <;> simp [h0, h1]
    · simpa [h0, h1, hval0, hval1] using hω1
    · simpa [h0, h1, hval0, hval1] using (by simp : ‖(1 : F)‖ = 1)
    · simpa [h0, h1, hval0, hval1] using h1ω
  · intro h_e_pos y coeffs hy h_lt
    dsimp at ⊢
    have h_bitv0 : bitv 2 2 (0 : Fin 2) = 0 := by decide
    have h_bitv1 : bitv 2 2 (1 : Fin 2) = 1 := by decide
    have h_sum_bitv : (∑ l : Fin 2, coeffs l * bitv 2 2 l) = coeffs 1 := by
      simp [Fin.sum_univ_two, h_bitv0, h_bitv1]
    rw [h_sum_bitv]
    by_contra! hC1
    have hC1_eq_one : coeffs 1 = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases this (coeffs 1) with (h | h)
      · exfalso; exact hC1 h
      · exact h
    have hC0_val : (coeffs 0).val = (0 : ℕ) ∨ (coeffs 0).val = (1 : ℕ) := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases this (coeffs 0) with (h | h)
      · left; simpa [h]
      · right; simpa [h] using (by decide : (1 : ZMod 2).val = (1 : ℕ))
    rcases hres y hy with ⟨a, b, h_y_z⟩
    let z := (a.val : F) + (b.val : F) * ω
    have hz_norm_le_one : ‖z‖ ≤ 1 := by
      have ha : ‖(a.val : F)‖ ≤ 1 := by
        have : a.val = (0 : ℕ) ∨ a.val = (1 : ℕ) := by
          have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
          rcases this a with (h | h)
          · left; simpa [h]
          · right; simpa [h] using (by decide : (1 : ZMod 2).val = (1 : ℕ))
        rcases this with (h | h)
        · simpa [h]
        · simpa [h]
      have hbω : ‖(b.val : F) * ω‖ ≤ 1 := by
        have hb_val : ‖(b.val : F)‖ ≤ 1 := by
          have : b.val = (0 : ℕ) ∨ b.val = (1 : ℕ) := by
            have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
            rcases this b with (h | h)
            · left; simpa [h]
            · right; simpa [h] using (by decide : (1 : ZMod 2).val = (1 : ℕ))
          rcases this with (h | h)
          · simpa [h]
          · simpa [h]
        calc
          ‖(b.val : F) * ω‖ = ‖(b.val : F)‖ * ‖ω‖ := norm_mul _ _
          _ ≤ 1 * 1 := mul_le_mul hb_val hω (norm_nonneg _) (by linarith)
          _ = 1 := by simp
      calc
        ‖z‖ = ‖(a.val : F) + (b.val : F) * ω‖ := rfl
        _ ≤ max ‖(a.val : F)‖ ‖(b.val : F) * ω‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max 1 1 := max_le_max ha hbω
        _ = 1 := by simp
    have h_yz_norm : ‖y - z‖ < 1 := h_y_z
    have h_yz_sum_norm : ‖y + z + 1‖ ≤ 1 := by
      calc
        ‖y + z + 1‖ ≤ max ‖y + z‖ ‖(1 : F)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max (max ‖y‖ ‖z‖) (max ‖(1 : F)‖ ‖(1 : F)‖) :=
          max_le_max (IsUltrametricDist.norm_add_le_max _ _) (by simp)
        _ = max (max ‖y‖ ‖z‖) 1 := by simp
        _ ≤ max (max 1 1) 1 := max_le_max (max_le_max hy hz_norm_le_one) (le_refl _)
        _ = 1 := by simp
    have h_diff_sq : ‖y ^ 2 + y - (z ^ 2 + z)‖ < 1 := by
      have h_eq : y ^ 2 + y - (z ^ 2 + z) = (y - z) * (y + z + 1) := by
        ring
      rw [h_eq, norm_mul]
      have h1 : ‖y - z‖ < 1 := h_yz_norm
      have h2 : ‖y + z + 1‖ ≤ 1 := h_yz_sum_norm
      have h_nonneg : 0 ≤ ‖y + z + 1‖ := norm_nonneg _
      have h_mul : ‖y - z‖ * ‖y + z + 1‖ < 1 := lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) h1
      simpa using h_mul
    have h_z_eq : ‖z ^ 2 + z - (((coeffs 0).val : F) + ω)‖ < 1 := by
      have h_sum_eq : z ^ 2 + z - (((coeffs 0).val : F) + ω) =
          (z ^ 2 + z - (y ^ 2 + y)) + (y ^ 2 + y - (((coeffs 0).val : F) + ω)) := by
        ring
      rw [h_sum_eq]
      have h_term1 : ‖z ^ 2 + z - (y ^ 2 + y)‖ < 1 := by
        rw [norm_sub_rev]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_diff_sq
      have h_term2 : ‖y ^ 2 + y - (((coeffs 0).val : F) + ω)‖ < 1 := by
        have h_sum : (∑ l : Fin 2, ((coeffs l).val : F) * ![1, ω] l) = ((coeffs 0).val : F) + ω := by
          calc
            (∑ l : Fin 2, ((coeffs l).val : F) * ![1, ω] l)
                = ((coeffs 0).val : F) * (![1, ω] 0 : F) + ((coeffs 1).val : F) * (![1, ω] 1 : F) := by
              simp [Fin.sum_univ_two]
            _ = ((coeffs 0).val : F) * (1 : F) + ((coeffs 1).val : F) * ω := by simp
            _ = ((coeffs 0).val : F) + ((coeffs 1).val : F) * ω := by simp
            _ = ((coeffs 0).val : F) + ((1 : ZMod 2).val : F) * ω := by rw [hC1_eq_one]
            _ = ((coeffs 0).val : F) + (1 : F) * ω := by
              have h : (1 : ZMod 2).val = (1 : ℕ) := by decide
              simp [h]
            _ = ((coeffs 0).val : F) + ω := by simp
        rw [h_sum] at h_lt
        exact h_lt
      calc
        ‖(z ^ 2 + z - (y ^ 2 + y)) + (y ^ 2 + y - (((coeffs 0).val : F) + ω))‖
            ≤ max ‖z ^ 2 + z - (y ^ 2 + y)‖ ‖y ^ 2 + y - (((coeffs 0).val : F) + ω)‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt h_term1 h_term2
    have ha_cases : a = 0 ∨ a = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact this a
    have hb_cases : b = 0 ∨ b = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact this b
    rcases ha_cases with (ha | ha) <;> rcases hb_cases with (hb | hb)
    · -- a = 0, b = 0: z = 0, z^2+z = 0
      have hz_sq : z ^ 2 + z = 0 := by
        dsimp [z]; rw [ha, hb]; simp
      rw [hz_sq] at h_z_eq
      rcases hC0_val with (hC0 | hC0)
      · -- C0 = 0: 0 - ω, norm = 1
        have h_simp : (0 : F) - (((coeffs 0).val : F) + ω) = -ω := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        rw [norm_neg] at h_z_eq
        linarith [hω1, h_z_eq]
      · -- C0 = 1: 0 - (1+ω), norm = 1
        have h_simp : (0 : F) - (((coeffs 0).val : F) + ω) = -(1 + ω) := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        rw [norm_neg] at h_z_eq
        linarith [h1ω, h_z_eq]
    · -- a = 0, b = 1: z = ω, z^2+z = ω^2+ω
      have hz_sq : z ^ 2 + z = ω ^ 2 + ω := by
        dsimp [z]; rw [ha, hb]
        have h0v : ((0 : ZMod 2).val : F) = (0 : F) := by norm_num
        have h1v : ((1 : ZMod 2).val : F) = (1 : F) := by
          have h : (1 : ZMod 2).val = (1 : ℕ) := by decide
          simpa [h]
        rw [h0v, h1v]
        ring
      rw [hz_sq] at h_z_eq
      rcases hC0_val with (hC0 | hC0)
      · -- C0 = 0: ω^2+ω - ω = ω^2, norm = 1
        have h_simp : ω ^ 2 + ω - (((coeffs 0).val : F) + ω) = ω ^ 2 := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        have hω_sq_norm : ‖ω ^ 2‖ = 1 := by
          calc
            ‖ω ^ 2‖ = ‖ω‖ ^ 2 := by simpa using norm_pow ω 2
            _ = 1 ^ 2 := by rw [hω1]
            _ = 1 := by norm_num
        rw [hω_sq_norm] at h_z_eq
        linarith
      · -- C0 = 1: ω^2+ω - (1+ω) = ω^2-1
        have h_simp : ω ^ 2 + ω - (((coeffs 0).val : F) + ω) = ω ^ 2 - 1 := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        have h_aux : ‖ω ^ 2 - 1‖ < 1 := h_z_eq
        have h_lt_ωm1 : ‖ω - 1‖ < 1 := by
          have h_prod : ‖(ω - 1) * (ω + 1)‖ < 1 := by
            have : (ω - 1) * (ω + 1) = ω ^ 2 - 1 := by ring
            rw [this]
            exact h_aux
          rw [norm_mul] at h_prod
          have h_norm_ωp1 : ‖ω + 1‖ = 1 := by rw [add_comm, h1ω]
          rw [h_norm_ωp1] at h_prod
          have h_nonneg : 0 ≤ ‖ω - 1‖ := norm_nonneg _
          nlinarith
        have h_ne : ‖ω - 1‖ ≠ ‖ω + 1‖ := by
          rw [add_comm ω 1, h1ω]
          exact ne_of_lt h_lt_ωm1
        have h_sum_eq : (ω - 1) + (ω + 1) = 2 * ω := by ring
        have h_sum_norm : ‖(ω - 1) + (ω + 1)‖ = max ‖ω - 1‖ ‖ω + 1‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
        rw [h_sum_eq] at h_sum_norm
        have h_norm_mul : ‖(2 : F) * ω‖ = ‖(2 : F)‖ * ‖ω‖ := norm_mul _ _
        rw [h_norm_mul, hω1, mul_one] at h_sum_norm
        have h_max : max ‖ω - 1‖ ‖ω + 1‖ = 1 := by
          rw [add_comm ω 1, h1ω]
          exact max_eq_right (by linarith)
        rw [h_max] at h_sum_norm
        linarith [h2lt, h_sum_norm]
    · -- a = 1, b = 0: z = 1, z^2+z = 2
      have hz_sq : z ^ 2 + z = (2 : F) := by
        dsimp [z]; rw [ha, hb]
        have h0v : ((0 : ZMod 2).val : F) = (0 : F) := by norm_num
        have h1v : ((1 : ZMod 2).val : F) = (1 : F) := by
          have h : (1 : ZMod 2).val = (1 : ℕ) := by decide
          simpa [h]
        rw [h0v, h1v]
        ring
      rw [hz_sq] at h_z_eq
      rcases hC0_val with (hC0 | hC0)
      · -- C0 = 0: 2 - ω
        have h_simp : (2 : F) - (((coeffs 0).val : F) + ω) = 2 - ω := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        have h_ne : ‖(2 : F) - ω‖ ≠ ‖ω‖ := by
          rw [hω1]
          linarith
        have h_sum_eq : ((2 : F) - ω) + ω = (2 : F) := by ring
        have h_sum_norm : ‖((2 : F) - ω) + ω‖ = max ‖(2 : F) - ω‖ ‖ω‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
        rw [h_sum_eq] at h_sum_norm
        have h_max : max ‖(2 : F) - ω‖ ‖ω‖ = 1 := by
          rw [hω1]
          exact max_eq_right (by linarith)
        rw [h_max] at h_sum_norm
        linarith [h2lt, h_sum_norm]
      · -- C0 = 1: 2 - (1+ω) = 1-ω
        have h_simp : (2 : F) - (((coeffs 0).val : F) + ω) = 1 - ω := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        have h_aux : ‖1 - ω‖ < 1 := h_z_eq
        have h_ne : ‖1 - ω‖ ≠ ‖1 + ω‖ := by
          rw [h1ω]
          exact ne_of_lt h_aux
        have h_sum_eq : (1 - ω) + (1 + ω) = (2 : F) := by ring
        have h_sum_norm : ‖(1 - ω) + (1 + ω)‖ = max ‖1 - ω‖ ‖1 + ω‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
        rw [h_sum_eq] at h_sum_norm
        have h_max : max ‖1 - ω‖ ‖1 + ω‖ = 1 := by
          rw [h1ω]
          exact max_eq_right (by linarith)
        rw [h_max] at h_sum_norm
        linarith [h2lt, h_sum_norm]
    · -- a = 1, b = 1: z = 1+ω, z^2+z = ω^2+3ω+2
      have hz_sq : z ^ 2 + z = ω ^ 2 + 3 * ω + 2 := by
        dsimp [z]; rw [ha, hb]
        have h1v : ((1 : ZMod 2).val : F) = (1 : F) := by
          have h : (1 : ZMod 2).val = (1 : ℕ) := by decide
          simpa [h]
        rw [h1v]
        ring
      rw [hz_sq] at h_z_eq
      rcases hC0_val with (hC0 | hC0)
      · -- C0 = 0: ω^2+3ω+2 - ω = ω^2+2ω+2 = (ω^2+ω+1)+(ω+1)
        have h_simp : ω ^ 2 + 3 * ω + 2 - (((coeffs 0).val : F) + ω) = (ω ^ 2 + ω + 1) + (ω + 1) := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        have h_aux : ‖(ω ^ 2 + ω + 1) + (ω + 1)‖ < 1 := h_z_eq
        have h_ne : ‖ω ^ 2 + ω + 1‖ ≠ ‖ω + 1‖ := by
          rw [add_comm ω 1, h1ω]
          exact ne_of_lt hω2
        have h_norm : ‖(ω ^ 2 + ω + 1) + (ω + 1)‖ = max ‖ω ^ 2 + ω + 1‖ ‖ω + 1‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
        rw [h_norm] at h_aux
        have h_max : max ‖ω ^ 2 + ω + 1‖ ‖ω + 1‖ = 1 := by
          rw [add_comm ω 1, h1ω]
          exact max_eq_right (by linarith)
        rw [h_max] at h_aux
        linarith
      · -- C0 = 1: ω^2+3ω+2 - (1+ω) = ω^2+2ω+1 = (ω^2+ω+1)+ω
        have h_simp : ω ^ 2 + 3 * ω + 2 - (((coeffs 0).val : F) + ω) = (ω ^ 2 + ω + 1) + ω := by
          rw [hC0]; ring
        rw [h_simp] at h_z_eq
        have h_aux : ‖(ω ^ 2 + ω + 1) + ω‖ < 1 := h_z_eq
        have h_ne : ‖ω ^ 2 + ω + 1‖ ≠ ‖ω‖ := by
          rw [hω1]
          exact ne_of_lt hω2
        have h_norm : ‖(ω ^ 2 + ω + 1) + ω‖ = max ‖ω ^ 2 + ω + 1‖ ‖ω‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
        rw [h_norm] at h_aux
        have h_max : max ‖ω ^ 2 + ω + 1‖ ‖ω‖ = 1 := by
          rw [hω1]
          exact max_eq_right (by linarith)
        rw [h_max] at h_aux
        linarith
  · intro h_e_zero ξ hξ_norm
    exfalso
    have h_e_zero' : e = 0 := by simpa using h_e_zero
    linarith

/-- `CompOK` in odd residue characteristic (no residue digits). -/
theorem compOK_odd {F : Type*} [NormedField F] [IsUltrametricDist F] {π : F} (hπ : NormUnif π)
    (h2 : ‖(2 : F)‖ = 1) {N : ℕ} (hferm : ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ (2 * N) - 1‖ < 1) :
    CompOK ⟨0, 0, 0, N⟩ π ![] := by
  refine
    { unif := hπ
      two := by
        simpa [pow_zero] using h2
      lift_le := λ l => Fin.elim0 l
      lift_ind := λ C hC => by
        exfalso
        apply hC
        ext l
        exact Fin.elim0 l
      trace := λ h => absurd h (Nat.lt_irrefl 0)
      fermat := λ _ => hferm }

end FurioLombardo.Discharge.SelmerBasis
