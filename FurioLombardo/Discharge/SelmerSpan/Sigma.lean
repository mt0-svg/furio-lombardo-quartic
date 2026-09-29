import FurioLombardo.Discharge.M3a.LocalRes

/-!
# Residues of `σ` modulo `2^58` (lane SelmerSpan)

Lane M4Cert's `θ⋆ = σ(θ)` is known to `2^-33` (`norm_θstar_sub`), so its residues of `σ (zkE a)` stop at
`2^28` (`approx_σ_zkE`). Here `θ1` is a sharper triple: the kernel checks `f(θ1) ≡ 0` modulo `2^70` and
`θ1 ≡ θ0` modulo `2^33`, and the estimate of `Hensel.lean` (`norm_eval_sub_eval_sub_le` at `θ0`, where
`‖f'(θ0)‖ ≥ 2^-7`) gives `‖θ⋆ - θ1‖ ≤ 2^-63` (`norm_θstar_sub1`). Hence the residues `zres1 a` of
`σ (zkE a)` modulo `2^58` (`approx_σ_zkE1`) and of the rational atoms `σ (zkE l / (2^j o))` modulo
`2^P`, `P + j ≤ 58` (`approx_σ_atom1`, kernel condition `SQok1`).
-/

namespace FurioLombardo.Discharge.SelmerSpan

open Polynomial FurioLombardo.M1 FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M3a.Bruin

/-- A triple congruent to `θ⋆` modulo `2^63`. -/
def θ1 : T3 := (309750227900445512569, 140709446414295352622, 937352080059315879928)

/-- An inverse of `Dodd` modulo `2^58`. -/
def uOdd1 : ℤ := 114458393891564631

theorem fL_θ1 : (2 : ℤ) ^ 70 ∣ (hornerZ θ1 fL).1 ∧ (2 : ℤ) ^ 70 ∣ (hornerZ θ1 fL).2.1 ∧
    (2 : ℤ) ^ 70 ∣ (hornerZ θ1 fL).2.2 := by
  decide +kernel

theorem θ1_θ0 : (2 : ℤ) ^ 33 ∣ (θ1 - θ0).1 ∧ (2 : ℤ) ^ 33 ∣ (θ1 - θ0).2.1 ∧
    (2 : ℤ) ^ 33 ∣ (θ1 - θ0).2.2 := by
  decide +kernel

theorem uOdd1_Dodd : (2 : ℤ) ^ 58 ∣ uOdd1 * Dodd - 1 := by decide +kernel

theorem norm_θstar_sub1 : ‖θstar - evZ θ1‖ ≤ (2⁻¹ : ℝ) ^ 63 := by
  set a := evZ θ0
  set z := evZ θ1
  have ha := norm_evZ_le_one θ0
  have hz := norm_evZ_le_one θ1
  have hw := norm_θstar_le_one
  have key := norm_eval_sub_eval_sub_le fK fK_coeff_le ha hz hw
  rw [fK_θstar, sub_zero] at key
  have hfz : ‖fK.eval z‖ ≤ (2⁻¹ : ℝ) ^ 70 := by
    rw [fK_eval, ← evZ_hornerZ]
    exact norm_evZ_le_of_dvd _ _ fL_θ1
  have hza : ‖z - a‖ ≤ (2⁻¹ : ℝ) ^ 33 := by
    rw [← evZ_sub]
    exact norm_evZ_le_of_dvd _ _ θ1_θ0
  have hwa : ‖θstar - a‖ ≤ (2⁻¹ : ℝ) ^ 33 := norm_θstar_sub
  have hd := norm_dfK_θ0
  set d := fK.derivative.eval a
  set e := ‖z - θstar‖
  have he0 : 0 ≤ e := norm_nonneg _
  have hmax : max ‖z - a‖ ‖θstar - a‖ ≤ (2⁻¹ : ℝ) ^ 33 := max_le hza hwa
  -- `d (z - θ⋆) = f(z) - (f(z) - d (z - θ⋆))`
  have hde : ‖d‖ * e ≤ max ‖fK.eval z‖ (e * (2⁻¹ : ℝ) ^ 33) := by
    have h1 : d * (z - θstar) = fK.eval z - (fK.eval z - d * (z - θstar)) := by ring
    calc ‖d‖ * e = ‖d * (z - θstar)‖ := (norm_mul _ _).symm
      _ = ‖fK.eval z - (fK.eval z - d * (z - θstar))‖ := by rw [← h1]
      _ ≤ max ‖fK.eval z‖ ‖fK.eval z - d * (z - θstar)‖ := norm_sub_le_max' _ _
      _ ≤ max ‖fK.eval z‖ (e * (2⁻¹ : ℝ) ^ 33) :=
          max_le_max le_rfl (key.trans (mul_le_mul_of_nonneg_left hmax he0))
  have h7 : (0 : ℝ) < (2⁻¹ : ℝ) ^ 7 := by positivity
  have hlt : (2⁻¹ : ℝ) ^ 33 < (2⁻¹ : ℝ) ^ 7 := pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by norm_num)
  rw [norm_sub_rev]
  show e ≤ _
  rcases le_total ‖fK.eval z‖ (e * (2⁻¹ : ℝ) ^ 33) with hc | hc
  · rw [max_eq_right hc] at hde
    have : e = 0 := by
      by_contra hne
      have hpos : 0 < e := lt_of_le_of_ne he0 (Ne.symm hne)
      have : (2⁻¹ : ℝ) ^ 7 * e ≤ (2⁻¹ : ℝ) ^ 33 * e := by nlinarith
      nlinarith
    rw [this]; positivity
  · rw [max_eq_left hc] at hde
    have : (2⁻¹ : ℝ) ^ 7 * e ≤ (2⁻¹ : ℝ) ^ 70 := by nlinarith
    calc e = ((2⁻¹ : ℝ) ^ 7 * e) / (2⁻¹ : ℝ) ^ 7 := by field_simp
      _ ≤ (2⁻¹ : ℝ) ^ 70 / (2⁻¹ : ℝ) ^ 7 := div_le_div_of_nonneg_right this h7.le
      _ = (2⁻¹ : ℝ) ^ 63 := by norm_num

/-- The kernel check behind `zres1`. -/
def zresOK1 (a : List ℤ) : Prop := Div32 (hornerZ θ1 (Kron.combo a zkNum))

instance : DecidablePred zresOK1 := fun a => by unfold zresOK1; infer_instance

/-- The triple congruent to `σ (zkE a)` modulo `2^58`. -/
def zres1 (a : List ℤ) : T3 := mulZ (div32T (hornerZ θ1 (Kron.combo a zkNum))) (uOdd1, 0, 0)

theorem norm_Dodd1 : ‖(uOdd1 : Kv) * (Dodd : Kv) - 1‖ ≤ (2⁻¹ : ℝ) ^ 58 := by
  have := norm_evZ_le_of_dvd (uOdd1 * Dodd - 1, 0, 0) 58 ⟨uOdd1_Dodd, dvd_zero _, dvd_zero _⟩
  rw [evZ_const] at this
  push_cast at this
  exact this

/-- **Residue of `σ (zkE a)`** modulo `2^n`, `n ≤ 58`. -/
theorem approx_σ_zkE1 (a : List ℤ) (ha : zresOK1 a) {n : ℕ} (hn : n ≤ 58) :
    Approx (σ (zkE a)) (zres1 a) n := by
  refine Approx.mono ?_ hn
  set L := Kron.combo a zkNum
  set N := hornerZ θ1 L
  set N' := div32T N
  have hD1 := norm_Dodd.1
  have hk := norm_Dodd1
  have hD0 : (Dodd : Kv) ≠ 0 := by
    intro h; rw [h, norm_zero] at hD1; exact zero_ne_one hD1
  have h32 : (32 : Kv) ≠ 0 := by
    have : ‖(32 : Kv)‖ = (2⁻¹ : ℝ) ^ 5 := by
      rw [show (32 : Kv) = 2 ^ 5 by norm_num, norm_pow, norm_two_Kv]
    intro h; rw [h, norm_zero] at this; norm_num at this
  have hn32 : ‖(32 : Kv)‖ = (2⁻¹ : ℝ) ^ 5 := by
    rw [show (32 : Kv) = 2 ^ 5 by norm_num, norm_pow, norm_two_Kv]
  set E := evalL θstar L - evZ N with hE
  have hEn : ‖E‖ ≤ (2⁻¹ : ℝ) ^ 63 := by
    rw [hE, evZ_hornerZ]
    exact (norm_evalL_sub_le norm_θstar_le_one (norm_evZ_le_one θ1) L).trans norm_θstar_sub1
  have hDz : ((Dz : ℕ) : Kv) = 32 * (Dodd : Kv) := by
    have := congrArg (fun z : ℤ => (z : Kv)) Dz_eq
    push_cast at this
    exact this
  have hσ : σ (zkE a) = (32 * (Dodd : Kv))⁻¹ * ((32 : Kv) * evZ N' + E) := by
    rw [σ_zkE, hDz, hE, ← evZ_div32T ha]; ring
  unfold Approx
  rw [hσ, zres1, evZ_mul, evZ_const]
  have key : (32 * (Dodd : Kv))⁻¹ * ((32 : Kv) * evZ N' + E) - evZ N' * (uOdd1 : Kv) =
      evZ N' * (Dodd : Kv)⁻¹ * -((uOdd1 : Kv) * (Dodd : Kv) - 1) + (32 * (Dodd : Kv))⁻¹ * E := by
    field_simp
    ring
  rw [key]
  refine (norm_add_le_max_Kv _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_mul, norm_neg, norm_inv, hD1, inv_one, mul_one]
    calc ‖evZ N'‖ * ‖(uOdd1 : Kv) * (Dodd : Kv) - 1‖ ≤ 1 * (2⁻¹ : ℝ) ^ 58 :=
          mul_le_mul (norm_evZ_le_one _) hk (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [norm_mul, norm_inv, norm_mul, hD1, mul_one, hn32]
    calc ((2⁻¹ : ℝ) ^ 5)⁻¹ * ‖E‖ ≤ ((2⁻¹ : ℝ) ^ 5)⁻¹ * (2⁻¹ : ℝ) ^ 63 :=
          mul_le_mul_of_nonneg_left hEn (by positivity)
      _ = (2⁻¹ : ℝ) ^ 58 := by norm_num

/-! ## Rational atoms -/

/-- The residue of `σ (zkE l / (2^j o))` modulo `2^P`, `oi` an inverse of `o` modulo `2^P`. -/
def sQres1 (l : List ℤ) (j : ℕ) (oi : ℤ) (P : ℕ) : T3 :=
  mulZ (divT (modT (zres1 l) (P + j)) (2 ^ j)) (oi, 0, 0)

/-- The conditions of `approx_σ_atom1` (a kernel check). -/
def SQok1 (l : List ℤ) (m j o : ℕ) (oi : ℤ) (P : ℕ) : Prop :=
  zresOK1 l ∧ m = 2 ^ j * o ∧ P + j ≤ 58 ∧ 1 ≤ P ∧ DvdT (modT (zres1 l) (P + j)) (2 ^ j) ∧
    modT (mulZ ((o : ℤ), 0, 0) (oi, 0, 0)) P = modT (1, 0, 0) P

instance (l : List ℤ) (m j o : ℕ) (oi : ℤ) (P : ℕ) : Decidable (SQok1 l m j o oi P) := by
  unfold SQok1; infer_instance

theorem approx_σ_atom1 {l : List ℤ} {m j o : ℕ} {oi : ℤ} {P : ℕ} (h : SQok1 l m j o oi P) :
    Approx (σ ((m : K21)⁻¹ * zkE l)) (sQres1 l j oi P) P := by
  obtain ⟨hz, hm, hP, hP1, hd, ho⟩ := h
  have h1 : Approx (σ (zkE l)) (modT (zres1 l) (P + j)) (P + j) := (approx_σ_zkE1 l hz hP).reduce
  have h2 := approx_div h1 hd
  have ho1 : Approx ((o : ℤ) : Kv) ((o : ℤ), 0, 0) P := by
    rw [← evZ_const]; exact approx_evZ _ _
  obtain ⟨ho0, ho2⟩ := approx_inv hP1 ho1 ho
  have h3 := h2.mul ho2
  unfold sQres1
  convert h3 using 2
  rw [hm, map_mul, map_inv₀, map_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_inv,
    div_eq_mul_inv, Int.cast_natCast]
  ring

end FurioLombardo.Discharge.SelmerSpan
