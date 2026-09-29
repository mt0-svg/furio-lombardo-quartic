import Mathlib
import FurioLombardo.Discharge.M4Cert.Embed
import FurioLombardo.Discharge.M4Cert.DataRes

/-!
# Residues modulo `2^n` in `K_v`

`Approx x b n` says that `x ∈ K_v` is congruent to the integer triple `b` modulo `2^n`
(`‖x - evZ b‖ ≤ 2^-n`). It is compatible with sums and products (`Approx.add`, `Approx.mul`),
with the reduction of the coordinates modulo `2^n` (`Approx.modT`), and determines the residue
(`modT_eq_of_approx`). Two sources of residues:

* `approx_σ_zkE`: the image under `σ` of the element `zkE a` of K21 (lane M1's integral basis
  coordinates) is congruent to the triple `zres a` modulo `2^n` for `n ≤ 28`, once `32` divides the
  coordinates of `N(θ0)`, `N` the numerator list of `zkE a` (`zresOK a`, a kernel check);
* `approx_inv`: the inverse of a unit from the inverse of its residue.

`not_sq_of_approx` is the non-square criterion: if `L` contains every square modulo `2^n`
(`SqClosed L n`, a kernel check) and the residue of `w` is not in `L`, then `w` is not a square
in `K_v`.
-/

namespace FurioLombardo.Discharge.M4Cert

open Polynomial FurioLombardo.M1

/-! ## Congruences -/

/-- `x ≡ evZ b` modulo `2^n`. -/
def Approx (x : Kv) (b : T3) (n : ℕ) : Prop := ‖x - evZ b‖ ≤ (2⁻¹ : ℝ) ^ n

theorem half_pow_le_one (n : ℕ) : (2⁻¹ : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem norm_add_le_max_Kv (x y : Kv) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  IsUltrametricDist.norm_add_le_max x y

theorem Approx.norm_le_one {x : Kv} {b : T3} {n : ℕ} (h : Approx x b n) : ‖x‖ ≤ 1 := by
  have e : x = (x - evZ b) + evZ b := by ring
  rw [e]
  exact (norm_add_le_max_Kv _ _).trans (max_le (h.trans (half_pow_le_one n)) (norm_evZ_le_one b))

theorem evZ_sub (a b : T3) : evZ (a - b) = evZ a - evZ b := by
  have h := evZ_add (a - b) b
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem approx_evZ (b : T3) (n : ℕ) : Approx (evZ b) b n := by
  unfold Approx; rw [sub_self, norm_zero]; positivity

theorem Approx.add {x y : Kv} {b c : T3} {n : ℕ} (hx : Approx x b n) (hy : Approx y c n) :
    Approx (x + y) (b + c) n := by
  unfold Approx at *
  rw [evZ_add, show x + y - (evZ b + evZ c) = (x - evZ b) + (y - evZ c) by ring]
  exact (norm_add_le_max_Kv _ _).trans (max_le hx hy)

theorem Approx.mul {x y : Kv} {b c : T3} {n : ℕ} (hx : Approx x b n) (hy : Approx y c n) :
    Approx (x * y) (mulZ b c) n := by
  have hx1 := hx.norm_le_one
  unfold Approx at *
  rw [evZ_mul, show x * y - evZ b * evZ c = x * (y - evZ c) + (x - evZ b) * evZ c by ring]
  refine (norm_add_le_max_Kv _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖x‖ * ‖y - evZ c‖ ≤ 1 * (2⁻¹ : ℝ) ^ n :=
          mul_le_mul hx1 hy (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [norm_mul]
    calc ‖x - evZ b‖ * ‖evZ c‖ ≤ (2⁻¹ : ℝ) ^ n * 1 :=
          mul_le_mul hx (norm_evZ_le_one c) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _

theorem Approx.mono {x : Kv} {b : T3} {n m : ℕ} (h : Approx x b n) (hmn : m ≤ n) : Approx x b m :=
  h.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)

/-- Reduction of the coordinates modulo `2^n`, into `[0, 2^n)`. -/
def modT (b : T3) (n : ℕ) : T3 := (b.1 % 2 ^ n, b.2.1 % 2 ^ n, b.2.2 % 2 ^ n)

theorem Approx.of_dvd {x : Kv} {b c : T3} {n : ℕ} (h : Approx x b n)
    (hd : (2 : ℤ) ^ n ∣ b.1 - c.1 ∧ (2 : ℤ) ^ n ∣ b.2.1 - c.2.1 ∧ (2 : ℤ) ^ n ∣ b.2.2 - c.2.2) :
    Approx x c n := by
  unfold Approx at *
  have hd' : ‖evZ (b - c)‖ ≤ (2⁻¹ : ℝ) ^ n := norm_evZ_le_of_dvd _ _ hd
  rw [show x - evZ c = (x - evZ b) + evZ (b - c) by rw [evZ_sub]; ring]
  exact (norm_add_le_max_Kv _ _).trans (max_le h hd')

theorem dvd_sub_emod (a : ℤ) (n : ℕ) : (2 : ℤ) ^ n ∣ a - a % 2 ^ n :=
  ⟨a / 2 ^ n, by rw [Int.emod_def]; ring⟩

theorem Approx.reduce {x : Kv} {b : T3} {n : ℕ} (h : Approx x b n) : Approx x (modT b n) n :=
  h.of_dvd ⟨dvd_sub_emod _ _, dvd_sub_emod _ _, dvd_sub_emod _ _⟩

theorem Approx.of_modT_eq {x : Kv} {b c : T3} {n : ℕ} (h : Approx x b n)
    (he : modT b n = modT c n) : Approx x c n := by
  simp only [modT, Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  exact h.of_dvd ⟨Int.ModEq.dvd h1.symm, Int.ModEq.dvd h2.symm, Int.ModEq.dvd h3.symm⟩

/-- Two triples congruent to the same element have the same residue. -/
theorem modT_eq_of_approx {x : Kv} {b c : T3} {n : ℕ} (hb : Approx x b n) (hc : Approx x c n) :
    modT b n = modT c n := by
  have h : ‖evZ (b - c)‖ ≤ (2⁻¹ : ℝ) ^ n := by
    rw [evZ_sub, show evZ b - evZ c = (x - evZ c) - (x - evZ b) by ring]
    exact (norm_sub_le_max' _ _).trans (max_le hc hb)
  obtain ⟨h1, h2, h3⟩ := dvd_of_norm_evZ_le _ _ h
  simp only [modT, Prod.mk.injEq]
  exact ⟨(Int.modEq_iff_dvd.mpr h1).symm, (Int.modEq_iff_dvd.mpr h2).symm,
    (Int.modEq_iff_dvd.mpr h3).symm⟩

/-! ## The non-square criterion -/

/-- `L` contains the residue modulo `2^n` of the square of every triple with coordinates in
`[0, 2^n)`. -/
def SqClosed (L : List T3) (n : ℕ) : Prop :=
  ∀ a : ℕ, a < 2 ^ n → ∀ b : ℕ, b < 2 ^ n → ∀ c : ℕ, c < 2 ^ n →
    modT (mulZ ((a : ℤ), (b : ℤ), (c : ℤ)) ((a : ℤ), (b : ℤ), (c : ℤ))) n ∈ L

theorem exists_nat_of_emod (z : ℤ) (n : ℕ) : ∃ a : ℕ, a < 2 ^ n ∧ z % 2 ^ n = (a : ℤ) := by
  have h2 : (0 : ℤ) < 2 ^ n := by positivity
  have h0 := Int.emod_nonneg z h2.ne'
  have hl := Int.emod_lt_of_pos z h2
  refine ⟨(z % 2 ^ n).toNat, ?_, (Int.toNat_of_nonneg h0).symm⟩
  have : (((z % 2 ^ n).toNat : ℕ) : ℤ) < 2 ^ n := by rw [Int.toNat_of_nonneg h0]; exact hl
  exact_mod_cast this

/-- **Non-square criterion.** -/
theorem not_sq_of_approx {w : Kv} {q : T3} {n : ℕ} {L : List T3} (hL : SqClosed L n)
    (hq : modT q n ∉ L) (hw : Approx w q n) (r : Kv) : w ≠ r ^ 2 := by
  intro hr
  have hw1 := hw.norm_le_one
  have hr1 : ‖r‖ ≤ 1 := by
    rw [hr, norm_pow] at hw1
    exact (pow_le_one_iff_of_nonneg (norm_nonneg r) two_ne_zero).1 hw1
  obtain ⟨b, hb⟩ := exists_evZ_approx r hr1 n
  have hb' : Approx r (modT b n) n := (show Approx r b n from hb).reduce
  have hsq : Approx w (mulZ (modT b n) (modT b n)) n := by
    rw [hr, pow_two]; exact hb'.mul hb'
  apply hq
  rw [modT_eq_of_approx hw hsq]
  obtain ⟨a1, h1, e1⟩ := exists_nat_of_emod b.1 n
  obtain ⟨a2, h2, e2⟩ := exists_nat_of_emod b.2.1 n
  obtain ⟨a3, h3, e3⟩ := exists_nat_of_emod b.2.2 n
  have : modT b n = ((a1 : ℤ), (a2 : ℤ), (a3 : ℤ)) := by
    simp only [modT, e1, e2, e3]
  rw [this]
  exact hL a1 h1 a2 h2 a3 h3

/-! ## Evaluation of integer lists -/

theorem ringHom_evalL {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : R) :
    ∀ L : List ℤ, φ (evalL t L) = evalL (φ t) L
  | [] => by simp [evalL]
  | a :: l => by simp [evalL, ringHom_evalL φ t l]

theorem norm_evalL_le_one {x : Kv} (hx : ‖x‖ ≤ 1) : ∀ L : List ℤ, ‖evalL x L‖ ≤ 1
  | [] => by simp [evalL]
  | a :: l => by
    rw [evalL_cons]
    refine (norm_add_le_max_Kv _ _).trans (max_le (norm_intCast_le_one a) ?_)
    rw [norm_mul]
    calc ‖x‖ * ‖evalL x l‖ ≤ 1 * 1 := mul_le_mul hx (norm_evalL_le_one hx l) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _

theorem norm_evalL_sub_le {x y : Kv} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∀ L : List ℤ, ‖evalL x L - evalL y L‖ ≤ ‖x - y‖
  | [] => by simp [evalL]
  | a :: l => by
    rw [evalL_cons, evalL_cons, show (a : Kv) + x * evalL x l - ((a : Kv) + y * evalL y l) =
      x * (evalL x l - evalL y l) + (x - y) * evalL y l by ring]
    refine (norm_add_le_max_Kv _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x‖ * ‖evalL x l - evalL y l‖ ≤ 1 * ‖x - y‖ :=
            mul_le_mul hx (norm_evalL_sub_le hx hy l) (norm_nonneg _) zero_le_one
        _ = ‖x - y‖ := one_mul _
    · rw [norm_mul]
      calc ‖x - y‖ * ‖evalL y l‖ ≤ ‖x - y‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_evalL_le_one hy l) (norm_nonneg _)
        _ = ‖x - y‖ := mul_one _

/-! ## Residues of the images of elements of K21 -/

theorem σ_zkE (a : List ℤ) :
    σ (zkE a) = ((Dz : ℕ) : Kv)⁻¹ * evalL θstar (Kron.combo a zkNum) := by
  have : zkE a = dInv * evalL θ (Kron.combo a zkNum) := rfl
  rw [this, map_mul, dInv, map_inv₀, map_natCast, ringHom_evalL, σ_θ]

/-- `32` divides the coordinates of a triple. -/
def Div32 (N : T3) : Prop := 32 ∣ N.1 ∧ 32 ∣ N.2.1 ∧ 32 ∣ N.2.2

instance : DecidablePred Div32 := fun N => by unfold Div32; infer_instance

/-- The kernel check behind the residue of `σ (zkE a)`. -/
def zresOK (a : List ℤ) : Prop := Div32 (hornerZ θ0 (Kron.combo a zkNum))

instance : DecidablePred zresOK := fun a => by unfold zresOK; infer_instance

/-- The coordinates divided by `32`. -/
def div32T (N : T3) : T3 := (N.1 / 32, N.2.1 / 32, N.2.2 / 32)

/-- The triple congruent to `σ (zkE a)`. -/
def zres (a : List ℤ) : T3 := mulZ (div32T (hornerZ θ0 (Kron.combo a zkNum))) (uOdd, 0, 0)

theorem Dz_eq : ((Dz : ℕ) : ℤ) = 32 * Dodd := by
  simp only [Dz, Dodd]; norm_num

theorem uOdd_Dodd : (2 : ℤ) ^ 28 ∣ uOdd * Dodd - 1 := by decide +kernel

theorem evZ_div32T {N : T3} (h : Div32 N) : evZ N = (32 : Kv) * evZ (div32T N) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : N = (32 * (N.1 / 32), 32 * (N.2.1 / 32), 32 * (N.2.2 / 32)) := by
    rw [Int.mul_ediv_cancel' h1, Int.mul_ediv_cancel' h2, Int.mul_ediv_cancel' h3]
  conv_lhs => rw [e]
  simp only [evZ, div32T]
  push_cast
  ring

theorem norm_Dodd : ‖(Dodd : Kv)‖ = 1 ∧ ‖(uOdd : Kv) * (Dodd : Kv) - 1‖ ≤ (2⁻¹ : ℝ) ^ 28 := by
  have hk : ‖(uOdd : Kv) * (Dodd : Kv) - 1‖ ≤ (2⁻¹ : ℝ) ^ 28 := by
    have := norm_evZ_le_of_dvd (uOdd * Dodd - 1, 0, 0) 28 ⟨uOdd_Dodd, dvd_zero _, dvd_zero _⟩
    rw [evZ_const] at this
    push_cast at this
    exact this
  refine ⟨le_antisymm (norm_intCast_le_one _) ?_, hk⟩
  have hlt : ‖(uOdd : Kv) * (Dodd : Kv) - 1‖ < 1 :=
    hk.trans_lt (pow_lt_one₀ (by norm_num) (by norm_num) (by norm_num))
  have h1 : (1 : ℝ) ≤ ‖(uOdd : Kv) * (Dodd : Kv)‖ := by
    by_contra hc
    push Not at hc
    have : ‖(1 : Kv)‖ ≤ max ‖(uOdd : Kv) * (Dodd : Kv)‖ ‖(uOdd : Kv) * (Dodd : Kv) - 1‖ := by
      have h := norm_sub_le_max' ((uOdd : Kv) * (Dodd : Kv)) ((uOdd : Kv) * (Dodd : Kv) - 1)
      rwa [sub_sub_cancel] at h
    rw [norm_one] at this
    exact absurd this (not_le.2 (max_lt hc hlt))
  calc (1 : ℝ) ≤ ‖(uOdd : Kv) * (Dodd : Kv)‖ := h1
    _ = ‖(uOdd : Kv)‖ * ‖(Dodd : Kv)‖ := norm_mul _ _
    _ ≤ 1 * ‖(Dodd : Kv)‖ := mul_le_mul_of_nonneg_right (norm_intCast_le_one _) (norm_nonneg _)
    _ = ‖(Dodd : Kv)‖ := one_mul _

/-- **Residue of `σ (zkE a)`** modulo `2^n`, `n ≤ 28`. -/
theorem approx_σ_zkE (a : List ℤ) (ha : zresOK a) {n : ℕ} (hn : n ≤ 28) :
    Approx (σ (zkE a)) (zres a) n := by
  refine Approx.mono ?_ hn
  set L := Kron.combo a zkNum
  set N := hornerZ θ0 L
  set N' := div32T N
  obtain ⟨hD1, hk⟩ := norm_Dodd
  have hD0 : (Dodd : Kv) ≠ 0 := by
    intro h; rw [h, norm_zero] at hD1; exact zero_ne_one hD1
  have h32 : (32 : Kv) ≠ 0 := by
    have : ‖(32 : Kv)‖ = (2⁻¹ : ℝ) ^ 5 := by
      rw [show (32 : Kv) = 2 ^ 5 by norm_num, norm_pow, norm_two_Kv]
    intro h; rw [h, norm_zero] at this; norm_num at this
  have hn32 : ‖(32 : Kv)‖ = (2⁻¹ : ℝ) ^ 5 := by
    rw [show (32 : Kv) = 2 ^ 5 by norm_num, norm_pow, norm_two_Kv]
  -- the error of the approximation θ0 of θ⋆
  set E := evalL θstar L - evZ N with hE
  have hEn : ‖E‖ ≤ (2⁻¹ : ℝ) ^ 33 := by
    rw [hE, evZ_hornerZ]
    exact (norm_evalL_sub_le norm_θstar_le_one (norm_evZ_le_one θ0) L).trans norm_θstar_sub
  have hDz : ((Dz : ℕ) : Kv) = 32 * (Dodd : Kv) := by
    have := congrArg (fun z : ℤ => (z : Kv)) Dz_eq
    push_cast at this
    exact this
  have hσ : σ (zkE a) = (32 * (Dodd : Kv))⁻¹ * ((32 : Kv) * evZ N' + E) := by
    rw [σ_zkE, hDz, hE, ← evZ_div32T ha]; ring
  unfold Approx
  rw [hσ, zres, evZ_mul, evZ_const]
  have key : (32 * (Dodd : Kv))⁻¹ * ((32 : Kv) * evZ N' + E) - evZ N' * (uOdd : Kv) =
      evZ N' * (Dodd : Kv)⁻¹ * -((uOdd : Kv) * (Dodd : Kv) - 1) + (32 * (Dodd : Kv))⁻¹ * E := by
    field_simp
    ring
  rw [key]
  refine (norm_add_le_max_Kv _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_mul, norm_neg, norm_inv, hD1, inv_one, mul_one]
    calc ‖evZ N'‖ * ‖(uOdd : Kv) * (Dodd : Kv) - 1‖ ≤ 1 * (2⁻¹ : ℝ) ^ 28 :=
          mul_le_mul (norm_evZ_le_one _) hk (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [norm_mul, norm_inv, norm_mul, hD1, mul_one, hn32]
    calc ((2⁻¹ : ℝ) ^ 5)⁻¹ * ‖E‖ ≤ ((2⁻¹ : ℝ) ^ 5)⁻¹ * (2⁻¹ : ℝ) ^ 33 :=
          mul_le_mul_of_nonneg_left hEn (by positivity)
      _ = (2⁻¹ : ℝ) ^ 28 := by norm_num

/-! ## Inverses -/

/-- The inverse of an element from a residue inverse (`n ≥ 1`). -/
theorem approx_inv {x : Kv} {b bi : T3} {n : ℕ} (hn : 1 ≤ n) (hx : Approx x b n)
    (hbi : modT (mulZ b bi) n = modT (1, 0, 0) n) : x ≠ 0 ∧ Approx x⁻¹ bi n := by
  have h1 : Approx (x * evZ bi) (1, 0, 0) n := (hx.mul (approx_evZ bi n)).of_modT_eq hbi
  unfold Approx at h1
  rw [show evZ ((1 : ℤ), (0 : ℤ), (0 : ℤ)) = 1 by simp [evZ]] at h1
  have hlt : ‖x * evZ bi - 1‖ < 1 :=
    h1.trans_lt (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
  have hge : (1 : ℝ) ≤ ‖x * evZ bi‖ := by
    by_contra hc
    push Not at hc
    have : ‖(1 : Kv)‖ ≤ max ‖x * evZ bi‖ ‖x * evZ bi - 1‖ := by
      have h := norm_sub_le_max' (x * evZ bi) (x * evZ bi - 1)
      rwa [sub_sub_cancel] at h
    rw [norm_one] at this
    exact absurd this (not_le.2 (max_lt hc hlt))
  have hx1 : ‖x‖ = 1 := by
    refine le_antisymm hx.norm_le_one ?_
    calc (1 : ℝ) ≤ ‖x * evZ bi‖ := hge
      _ = ‖x‖ * ‖evZ bi‖ := norm_mul _ _
      _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (norm_evZ_le_one bi) (norm_nonneg _)
      _ = ‖x‖ := mul_one _
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
  refine ⟨hx0, ?_⟩
  unfold Approx
  rw [show x⁻¹ - evZ bi = -(x⁻¹ * (x * evZ bi - 1)) by field_simp; ring, norm_neg, norm_mul,
    norm_inv, hx1, inv_one, one_mul]
  exact h1

end FurioLombardo.Discharge.M4Cert
