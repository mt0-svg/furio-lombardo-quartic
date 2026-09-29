import Mathlib
import FurioLombardo.M4.Defs

/-!
# Boxes of ℤ_[2] and the covering checker
-/


open FurioLombardo.M4

theorem FurioLombardo.M4.inBox_split {X : ℤ_[2]} {c s : ℕ} (h : InBox X c s) :
    InBox X c (s + 1) ∨ InBox X (c + 2 ^ s) (s + 1) := by
  rcases h with ⟨y, h⟩
  -- h : X = (c : ℤ_[2]) + 2 ^ s * y
  have h_exists := PadicInt.exists_mem_range (p := 2) y
  rcases h_exists with ⟨n, hn_lt, hn_mem⟩
  -- hn_lt : n < 2,  hn_mem : y - (n : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2]
  have hn_mem' : y - (n : ℤ_[2]) ∈ Ideal.span {(2 : ℤ_[2])} := by
    rw [PadicInt.maximalIdeal_eq_span_p (p := 2)] at hn_mem
    simpa using hn_mem
  have h_dvd : (2 : ℤ_[2]) ∣ y - (n : ℤ_[2]) :=
    (Ideal.mem_span_singleton (x := y - (n : ℤ_[2])) (y := (2 : ℤ_[2]))).mp hn_mem'
  rcases h_dvd with ⟨z, hz⟩
  -- hz : y - (n : ℤ_[2]) = (2 : ℤ_[2]) * z
  have hy : y = (n : ℤ_[2]) + 2 * z := by
    calc
      y = (y - (n : ℤ_[2])) + (n : ℤ_[2]) := by ring
      _ = (2 : ℤ_[2]) * z + (n : ℤ_[2]) := by rw [hz]
      _ = (n : ℤ_[2]) + 2 * z := by ring
  have hn_cases : n = 0 ∨ n = 1 := by
    omega
  rcases hn_cases with (hn | hn)
  · -- n = 0
    left
    rw [hn] at hy
    -- hy : y = 0 + 2 * z
    refine ⟨z, ?_⟩
    rw [h, hy]
    push_cast
    ring
  · -- n = 1
    right
    rw [hn] at hy
    -- hy : y = 1 + 2 * z
    refine ⟨z, ?_⟩
    rw [h, hy]
    push_cast
    ring

theorem FurioLombardo.M4.inBox_of_boxLe {X : ℤ_[2]} {b : ℕ × ℕ} {c s : ℕ} (hb : boxLe b c s = true) (h : InBox X c s) :
    InBox X b.1 b.2 := by
  -- Unpack hb: boxLe b c s = decide (b.2 ≤ s) && (c % 2 ^ b.2 == b.1 % 2 ^ b.2)
  have h_and : decide (b.2 ≤ s) = true ∧ (c % 2 ^ b.2 == b.1 % 2 ^ b.2) = true := by
    simpa [boxLe] using hb
  rcases h_and with ⟨h_le_dec, h_mod_eq⟩
  have h_le : b.2 ≤ s := by simpa using h_le_dec
  have h_mod : c % 2 ^ b.2 = b.1 % 2 ^ b.2 := by simpa using h_mod_eq
  rcases h with ⟨y, hy⟩
  -- Write s = b.2 + t
  rcases Nat.exists_eq_add_of_le h_le with ⟨t, ht⟩
  -- Use Nat.mod_add_div to express c and b.1 in ℕ
  have hc_nat : c % 2 ^ b.2 + 2 ^ b.2 * (c / 2 ^ b.2) = c := Nat.mod_add_div c (2 ^ b.2)
  have hb1_nat : b.1 % 2 ^ b.2 + 2 ^ b.2 * (b.1 / 2 ^ b.2) = b.1 := Nat.mod_add_div b.1 (2 ^ b.2)
  -- Cast to ℤ_[2]
  have hc_eq : ((c % 2 ^ b.2 : ℕ) : ℤ_[2]) + ((2 ^ b.2 : ℕ) : ℤ_[2]) * ((c / 2 ^ b.2 : ℕ) : ℤ_[2]) = (c : ℤ_[2]) := by
    exact_mod_cast hc_nat
  have hb1_eq : ((b.1 % 2 ^ b.2 : ℕ) : ℤ_[2]) + ((2 ^ b.2 : ℕ) : ℤ_[2]) * ((b.1 / 2 ^ b.2 : ℕ) : ℤ_[2]) = (b.1 : ℤ_[2]) := by
    exact_mod_cast hb1_nat
  -- Since c % 2^b.2 = b.1 % 2^b.2, the remainders are equal
  have h_mod_eq' : (c % 2 ^ b.2 : ℕ) = (b.1 % 2 ^ b.2 : ℕ) := by exact_mod_cast h_mod
  -- Compute the difference c - b.1 in ℤ_[2]
  have h_diff : (c : ℤ_[2]) - (b.1 : ℤ_[2]) = ((2 ^ b.2 : ℕ) : ℤ_[2]) * (((c / 2 ^ b.2 : ℕ) : ℤ_[2]) - ((b.1 / 2 ^ b.2 : ℕ) : ℤ_[2])) := by
    rw [← hc_eq, ← hb1_eq, h_mod_eq']
    ring
  -- Express 2^s = 2^b.2 * 2^t
  have h_pow : (2 : ℤ_[2]) ^ s = (2 : ℤ_[2]) ^ b.2 * (2 : ℤ_[2]) ^ t := by
    rw [ht, pow_add]
  have h_cast_pow : ((2 ^ b.2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) ^ b.2 := by simp
  -- Provide the witness
  use ((c / 2 ^ b.2 : ℕ) : ℤ_[2]) - ((b.1 / 2 ^ b.2 : ℕ) : ℤ_[2]) + (2 : ℤ_[2]) ^ t * y
  rw [hy, h_pow, mul_assoc]
  calc
    (c : ℤ_[2]) + ((2 : ℤ_[2]) ^ b.2) * ((2 : ℤ_[2]) ^ t * y) = (b.1 : ℤ_[2]) + ((c : ℤ_[2]) - (b.1 : ℤ_[2])) + ((2 : ℤ_[2]) ^ b.2) * ((2 : ℤ_[2]) ^ t * y) := by ring
    _ = (b.1 : ℤ_[2]) + (((2 ^ b.2 : ℕ) : ℤ_[2]) * (((c / 2 ^ b.2 : ℕ) : ℤ_[2]) - ((b.1 / 2 ^ b.2 : ℕ) : ℤ_[2]))) + ((2 : ℤ_[2]) ^ b.2) * ((2 : ℤ_[2]) ^ t * y) := by rw [h_diff]
    _ = (b.1 : ℤ_[2]) + ((2 : ℤ_[2]) ^ b.2) * (((c / 2 ^ b.2 : ℕ) : ℤ_[2]) - ((b.1 / 2 ^ b.2 : ℕ) : ℤ_[2]) + (2 : ℤ_[2]) ^ t * y) := by rw [h_cast_pow]; ring

theorem FurioLombardo.M4.inBox_zero (X : ℤ_[2]) : InBox X 0 0 := by
  refine ⟨X, ?_⟩
  simp

theorem FurioLombardo.M4.inBox_mono {X : ℤ_[2]} {c s t : ℕ} (h : InBox X c s) (hts : t ≤ s) : InBox X c t := by
  rcases h with ⟨y, h⟩
  refine ⟨2 ^ (s - t) * y, ?_⟩
  calc
    X = (c : ℤ_[2]) + 2 ^ s * y := h
    _ = (c : ℤ_[2]) + (2 ^ t * 2 ^ (s - t)) * y := by
      rw [← pow_add 2 t (s - t), Nat.add_sub_cancel' hts]
    _ = (c : ℤ_[2]) + 2 ^ t * (2 ^ (s - t) * y) := by ring

theorem FurioLombardo.M4.coverCheck_sound (L : List (ℕ × ℕ)) (fuel c s : ℕ) (hc : coverCheck L fuel c s = true) (X : ℤ_[2])
    (hX : InBox X c s) : ∃ b ∈ L, InBox X b.1 b.2 := by
  induction fuel generalizing c s with
  | zero =>
    unfold coverCheck at hc
    rcases (List.any_eq_true.mp hc) with ⟨b, hb, hbox⟩
    refine ⟨b, hb, ?_⟩
    exact inBox_of_boxLe hbox hX
  | succ fuel ih =>
    unfold coverCheck at hc
    rw [Bool.or_eq_true] at hc
    rcases hc with (hany | hand)
    · rcases (List.any_eq_true.mp hany) with ⟨b, hb, hbox⟩
      refine ⟨b, hb, ?_⟩
      exact inBox_of_boxLe hbox hX
    · rw [Bool.and_eq_true] at hand
      rcases hand with ⟨hleft, hright⟩
      rcases inBox_split hX with (hX' | hX')
      · exact ih c (s + 1) hleft hX'
      · exact ih (c + 2 ^ s) (s + 1) hright hX'

theorem FurioLombardo.M4.cover_of_coverCheck (L : List (ℕ × ℕ)) (fuel : ℕ) (hc : coverCheck L fuel 0 0 = true) (X : ℤ_[2]) :
    ∃ b ∈ L, InBox X b.1 b.2 := by
  exact coverCheck_sound L fuel 0 0 hc X (inBox_zero X)

theorem FurioLombardo.M4.unit_eq_one_add_two {u : ℤ_[2]} (hu : IsUnit u) : ∃ w : ℤ_[2], u = 1 + 2 * w := by
  have h_range := PadicInt.exists_mem_range u
  rcases h_range with ⟨n, hn_lt, h_mem⟩
  have hn0 : n = 0 ∨ n = 1 := by
    omega
  rcases hn0 with (hn | hn)
  · -- n = 0 leads to contradiction: u would be in maximal ideal, hence not a unit
    have h_mem' : u ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      simpa [hn] using h_mem
    have h_not_unit : ¬ IsUnit u := by
      intro h_isUnit
      have h_not_mem : u ∉ IsLocalRing.maximalIdeal ℤ_[2] :=
        (IsLocalRing.notMem_maximalIdeal (x := u)).mpr h_isUnit
      exact h_not_mem h_mem'
    exact absurd hu h_not_unit
  · -- n = 1: u - 1 ∈ maximal ideal = span {2}, so 2 ∣ u - 1
    have h_mem' : u - 1 ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      simpa [hn] using h_mem
    rw [PadicInt.maximalIdeal_eq_span_p (p := 2)] at h_mem'
    rw [Ideal.mem_span_singleton] at h_mem'
    rcases h_mem' with ⟨w, hw⟩
    use w
    linear_combination hw

theorem FurioLombardo.M4.eq_zero_or_two_pow_mul_unit (X : ℤ_[2]) : X = 0 ∨ ∃ (j : ℕ) (u : ℤ_[2]), IsUnit u ∧ X = 2 ^ j * u := by
  by_cases hX : X = 0
  · left; exact hX
  · right
    refine ⟨X.valuation, (PadicInt.unitCoeff hX : ℤ_[2]), Units.isUnit _, ?_⟩
    simpa [mul_comm] using PadicInt.unitCoeff_spec hX
