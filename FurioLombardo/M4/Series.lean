import Mathlib
import FurioLombardo.M4.Leading

/-!
# Divisibility of vectors and bounds on series
-/


open FurioLombardo.M4

theorem FurioLombardo.M4.dvdV_add {d B : ℕ} {x y : Fin d → ℤ_[2]} (hx : DvdV B x) (hy : DvdV B y) : DvdV B (x + y) := by
  intro i
  rw [Pi.add_apply]
  exact dvd_add (hx i) (hy i)

theorem FurioLombardo.M4.dvdV_mono {d B B' : ℕ} {x : Fin d → ℤ_[2]} (hB : B ≤ B') (h : DvdV B' x) : DvdV B x := by
  intro i
  have hpow : (2 : ℤ_[2]) ^ B ∣ (2 : ℤ_[2]) ^ B' := pow_dvd_pow 2 hB
  exact hpow.trans (h i)

theorem FurioLombardo.M4.dvdV_smul {d B : ℕ} {x : Fin d → ℤ_[2]} (c : ℤ_[2]) (hx : DvdV B x) : DvdV B (c • x) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul]
  exact (hx i).mul_left c

theorem FurioLombardo.M4.dvdV_sub {d B : ℕ} {x y : Fin d → ℤ_[2]} (hx : DvdV B x) (hy : DvdV B y) : DvdV B (x - y) := by
  intro i
  exact dvd_sub (hx i) (hy i)

theorem FurioLombardo.M4.dvdV_two_pow_smul_add {d B k : ℕ} {x : Fin d → ℤ_[2]} (hx : DvdV B x) : DvdV (B + k) ((2 : ℤ_[2]) ^ k • x) := by
  intro i
  have h := hx i
  rw [Pi.smul_apply, smul_eq_mul, pow_add]
  simpa [mul_comm] using mul_dvd_mul h (dvd_refl ((2 : ℤ_[2]) ^ k))

theorem FurioLombardo.M4.exists_eq_two_pow_smul {d B : ℕ} {x : Fin d → ℤ_[2]} (h : DvdV B x) : ∃ t : Fin d → ℤ_[2], x = (2 : ℤ_[2]) ^ B • t := by
  choose t ht using h
  refine ⟨t, ?_⟩
  funext i
  rw [Pi.smul_apply, smul_eq_mul, ht i]

theorem FurioLombardo.M4.succ_dvd_two_pow (n : ℕ) : ((n : ℤ_[2]) + 1) ∣ (2 : ℤ_[2]) ^ n := by
  by_cases hn : n + 1 = 0
  · -- impossible case: n+1 ≠ 0 for any n
    exact absurd hn (Nat.succ_ne_zero n)
  · -- n+1 ≠ 0, use factorization
    rcases Nat.exists_eq_two_pow_mul_odd hn with ⟨k, m, hm_odd, h_eq⟩
    -- h_eq: n + 1 = 2 ^ k * m
    -- hm_odd: Odd m
    have hm_pos : 0 < m := by
      by_contra! hmz
      -- hmz: m ≤ 0
      have hmz' : m = 0 := Nat.eq_zero_of_le_zero hmz
      have hzero : n + 1 = 0 := by
        simpa [hmz'] using h_eq
      exact hn hzero
    have hk_le_n : k ≤ n := by
      have h_pow_le : 2 ^ k ≤ 2 ^ n := by
        have h1 : 2 ^ k ≤ n + 1 := by
          calc
            2 ^ k = 2 ^ k * 1 := by simp
            _ ≤ 2 ^ k * m := Nat.mul_le_mul_left _ hm_pos
            _ = n + 1 := by rw [← h_eq]
        have h2 : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n))
        exact Nat.le_trans h1 h2
      exact ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h_pow_le)
    have hm_unit : IsUnit (m : ℤ_[2]) := by
      have h_coprime : Nat.Coprime 2 m := Odd.coprime_two_left hm_odd
      have h_norm : ‖(m : ℤ_[2])‖ = 1 :=
        (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := m)).mpr h_coprime
      exact ((PadicInt.isUnit_iff (p := 2)).mpr h_norm)
    have h_cast : ((n : ℤ_[2]) + 1) = ((2 : ℤ_[2]) ^ k) * (m : ℤ_[2]) := by
      calc
        ((n : ℤ_[2]) + 1) = ((n + 1 : ℕ) : ℤ_[2]) := by simp
        _ = ((2 ^ k * m : ℕ) : ℤ_[2]) := by rw [h_eq]
        _ = ((2 : ℤ_[2]) ^ k) * (m : ℤ_[2]) := by simp
    have h_pow_split : (2 : ℤ_[2]) ^ n = ((2 : ℤ_[2]) ^ k) * ((2 : ℤ_[2]) ^ (n - k)) := by
      calc
        (2 : ℤ_[2]) ^ n = (2 : ℤ_[2]) ^ (k + (n - k)) := by
          rw [Nat.add_sub_cancel' hk_le_n]
        _ = ((2 : ℤ_[2]) ^ k) * ((2 : ℤ_[2]) ^ (n - k)) := by rw [pow_add]
    rw [h_cast, h_pow_split]
    -- Need to show: (2^k * m) ∣ (2^k * 2^(n-k))
    -- Since m is a unit, multiply by m⁻¹
    let u := hm_unit.unit
    have hu_val : (u : ℤ_[2]) = (m : ℤ_[2]) := by simp [u]
    refine ⟨((2 : ℤ_[2]) ^ (n - k)) * ((u⁻¹ : Units ℤ_[2]) : ℤ_[2]), ?_⟩
    calc
      ((2 : ℤ_[2]) ^ k) * ((2 : ℤ_[2]) ^ (n - k))
          = ((2 : ℤ_[2]) ^ n) * 1 := by
        rw [h_pow_split, mul_one]
      _ = ((2 : ℤ_[2]) ^ n) * ((u : ℤ_[2]) * ((u⁻¹ : Units ℤ_[2]) : ℤ_[2])) := by simp
      _ = ((2 : ℤ_[2]) ^ n) * ((m : ℤ_[2]) * ((u⁻¹ : Units ℤ_[2]) : ℤ_[2])) := by rw [hu_val]
      _ = (((2 : ℤ_[2]) ^ k) * ((2 : ℤ_[2]) ^ (n - k))) * ((m : ℤ_[2]) * ((u⁻¹ : Units ℤ_[2]) : ℤ_[2])) := by rw [h_pow_split]
      _ = ((2 : ℤ_[2]) ^ k) * (m : ℤ_[2]) * (((2 : ℤ_[2]) ^ (n - k)) * ((u⁻¹ : Units ℤ_[2]) : ℤ_[2])) := by ring

theorem FurioLombardo.M4.dvdV_two_pow_smul {d B n : ℕ} {a : Fin d → ℤ_[2]} (h : DvdV B (((n : ℤ_[2]) + 1) • a)) :
    DvdV B ((2 : ℤ_[2]) ^ n • a) := by
  have h_succ_dvd : ((n : ℤ_[2]) + 1) ∣ (2 : ℤ_[2]) ^ n := succ_dvd_two_pow n
  rcases h_succ_dvd with ⟨c, hc⟩
  intro i
  have hi : (2 : ℤ_[2]) ^ B ∣ ((n : ℤ_[2]) + 1) • a i := h i
  have hi' : (2 : ℤ_[2]) ^ B ∣ ((n : ℤ_[2]) + 1) * a i := by
    simpa [smul_eq_mul] using hi
  have h_target : (2 : ℤ_[2]) ^ B ∣ ((2 : ℤ_[2]) ^ n) * a i := by
    rw [hc]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hi'.mul_right c
  simpa [smul_eq_mul, Pi.smul_apply] using h_target

theorem FurioLombardo.M4.dvdV_term {d B n : ℕ} {a : Fin d → ℤ_[2]} (T : ℤ_[2]) (h : DvdV B (((n : ℤ_[2]) + 1) • a)) :
    DvdV (B + 1) (((2 : ℤ_[2]) * T) ^ (n + 1) • a) := by
  intro i
  have h2 : DvdV B ((2 : ℤ_[2]) ^ n • a) := dvdV_two_pow_smul h
  have h2i := h2 i
  have h1 : (2 : ℤ_[2]) ^ (B + 1) ∣ (2 : ℤ_[2]) ^ (n + 1) * (a i) := by
    rw [pow_succ (2 : ℤ_[2]) B, pow_succ (2 : ℤ_[2]) n]
    -- Goal: (2 * 2^B) ∣ (2 * 2^n) * (a i)
    -- RHS = 2 * (2^n * (a i))
    -- From h2i: 2^B ∣ 2^n * (a i), multiply by 2
    have h2i' : (2 : ℤ_[2]) ^ B ∣ (2 : ℤ_[2]) ^ n * (a i) := by
      simpa [Pi.smul_apply, smul_eq_mul] using h2i
    simpa [mul_comm, mul_assoc, mul_left_comm] using mul_dvd_mul_left (2 : ℤ_[2]) h2i'
  have h2' : (2 : ℤ_[2]) ^ (n + 1) * (a i) ∣ ((2 : ℤ_[2]) * T) ^ (n + 1) * (a i) := by
    rw [mul_pow]
    -- Goal: 2^(n+1) * (a i) ∣ (2^(n+1) * T^(n+1)) * (a i)
    -- RHS = (2^(n+1) * (a i)) * T^(n+1)
    calc
      (2 : ℤ_[2]) ^ (n + 1) * (a i) ∣ ((2 : ℤ_[2]) ^ (n + 1) * (a i)) * (T ^ (n + 1)) :=
        dvd_mul_right _ _
      _ = ((2 : ℤ_[2]) ^ (n + 1) * T ^ (n + 1)) * (a i) := by ring
  exact dvd_trans h1 h2'

theorem FurioLombardo.M4.isClosed_two_pow_dvd (B : ℕ) : IsClosed {y : ℤ_[2] | (2 : ℤ_[2]) ^ B ∣ y} := by
  have h : {y : ℤ_[2] | (2 : ℤ_[2]) ^ B ∣ y} = Metric.closedBall 0 ((2 : ℝ) ^ (-(B : ℤ))) := by
    ext y
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    have := PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) y B
    push_cast at this
    rw [this, Ideal.mem_span_singleton]
  rw [h]
  exact Metric.isClosed_closedBall

theorem FurioLombardo.M4.dvdV_of_hasSum {d B : ℕ} {f : ℕ → Fin d → ℤ_[2]} {x : Fin d → ℤ_[2]} (hf : ∀ n, DvdV B (f n))
    (hx : HasSum f x) : DvdV B x := by
  intro i
  have hi : HasSum (fun n => f n i) (x i) := Pi.hasSum.mp hx i
  have hmem : x i ∈ ((Ideal.span {(2 : ℤ_[2]) ^ B} : Ideal ℤ_[2]) : Set ℤ_[2]) := by
    have hc : IsClosed ((Ideal.span {(2 : ℤ_[2]) ^ B} : Ideal ℤ_[2]) : Set ℤ_[2]) := by
      have : ((Ideal.span {(2 : ℤ_[2]) ^ B} : Ideal ℤ_[2]) : Set ℤ_[2]) = {y : ℤ_[2] | (2 : ℤ_[2]) ^ B ∣ y} := by
        ext y; simp [Ideal.mem_span_singleton]
      rw [this]; exact isClosed_two_pow_dvd B
    apply hc.mem_of_tendsto hi
    filter_upwards with s
    exact (Ideal.span _).sum_mem (fun n _ => Ideal.mem_span_singleton.mpr (hf n i))
  exact Ideal.mem_span_singleton.mp hmem

theorem FurioLombardo.M4.lip_of_series {d B : ℕ} {a : ℕ → Fin d → ℤ_[2]} {D : Fin d → ℤ_[2]} (T : ℤ_[2])
    (ha : ∀ n : ℕ, DvdV B (((n : ℤ_[2]) + 1) • a n))
    (hD : HasSum (fun n => ((2 : ℤ_[2]) * T) ^ (n + 1) • a n) D) : DvdV (B + 1) D := by
  exact dvdV_of_hasSum (fun n => dvdV_term T (ha n)) hD

theorem FurioLombardo.M4.tail_term {d B n t : ℕ} {a : Fin d → ℤ_[2]} (u : ℤ_[2]) (ht : 1 ≤ t) (hn : 1 ≤ n)
    (h : DvdV B (((n : ℤ_[2]) + 1) • a)) : DvdV (B + 2 * t - 1) (((2 : ℤ_[2]) ^ t * u) ^ (n + 1) • a) := by
  have h2 : DvdV B ((2 : ℤ_[2]) ^ n • a) := dvdV_two_pow_smul h
  intro i
  have hi : (2 : ℤ_[2]) ^ B ∣ (2 : ℤ_[2]) ^ n * a i := by
    simpa using h2 i
  have h_exp : n ≤ t * (n + 1) := by
    have : 1 * (n + 1) ≤ t * (n + 1) := Nat.mul_le_mul_right (n + 1) ht
    omega
  have h_ineq : n + 2 * t - 1 ≤ t * (n + 1) := by
    have hz : (n : ℤ) + 2 * (t : ℤ) - 1 ≤ (t : ℤ) * ((n : ℤ) + 1) := by
      have ht1 : (1 : ℤ) ≤ t := by exact_mod_cast ht
      have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hpos : 1 ≤ n + 2 * t := by omega
    have hz' : ((n + 2 * t - 1 : ℕ) : ℤ) ≤ (t * (n + 1) : ℤ) := by
      simpa [Nat.cast_sub hpos, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz
    exact_mod_cast hz'
  have h_exp2 : B + 2 * t - 1 ≤ B + (t * (n + 1) - n) := by
    have h_sub : n ≤ t * (n + 1) := h_exp
    omega
  have h_dvd_pow : (2 : ℤ_[2]) ^ (B + 2 * t - 1) ∣ (2 : ℤ_[2]) ^ (B + (t * (n + 1) - n)) :=
    pow_dvd_pow (2 : ℤ_[2]) h_exp2
  -- Key identity: ((2^t * u)^(n+1)) * a i = 2^(t*(n+1) - n) * (2^n * a i) * u^(n+1)
  have h_eq : ((2 : ℤ_[2]) ^ t * u) ^ (n + 1) * a i =
      ((2 : ℤ_[2]) ^ (t * (n + 1) - n)) * ((2 : ℤ_[2]) ^ n * a i) * (u ^ (n + 1)) := by
    calc
      ((2 : ℤ_[2]) ^ t * u) ^ (n + 1) * a i = (((2 : ℤ_[2]) ^ t) ^ (n + 1) * u ^ (n + 1)) * a i := by rw [mul_pow]
      _ = ((2 : ℤ_[2]) ^ (t * (n + 1)) * u ^ (n + 1)) * a i := by rw [← pow_mul, mul_comm t (n + 1)]
      _ = ((2 : ℤ_[2]) ^ (t * (n + 1))) * (u ^ (n + 1) * a i) := by ring
      _ = ((2 : ℤ_[2]) ^ (t * (n + 1) - n) * (2 : ℤ_[2]) ^ n) * (u ^ (n + 1) * a i) := by
        rw [← pow_add, Nat.sub_add_cancel h_exp]
      _ = ((2 : ℤ_[2]) ^ (t * (n + 1) - n)) * ((2 : ℤ_[2]) ^ n * a i) * (u ^ (n + 1)) := by ring
  -- Goal: 2^(B + 2*t - 1) ∣ ((2^t * u)^(n+1) • a) i
  -- Rewrite using Pi.smul_apply first
  rw [Pi.smul_apply]
  -- Goal: 2^(B + 2*t - 1) ∣ (2^t * u)^(n+1) • a i
  -- Now rewrite using h_eq
  have h_goal : ((2 : ℤ_[2]) ^ t * u) ^ (n + 1) • a i = ((2 : ℤ_[2]) ^ (t * (n + 1) - n)) * ((2 : ℤ_[2]) ^ n * a i) * (u ^ (n + 1)) := by
    simpa [smul_eq_mul] using h_eq
  rw [h_goal]
  -- Goal: 2^(B + 2*t - 1) ∣ (2^(t*(n+1) - n) * (2^n * a i)) * u^(n+1)
  rcases hi with ⟨k, hk⟩
  rw [hk]
  -- Goal: 2^(B + 2*t - 1) ∣ (2^(t*(n+1) - n) * (2^B * k)) * u^(n+1)
  have h_rhs : (2 : ℤ_[2]) ^ (t * (n + 1) - n) * ((2 : ℤ_[2]) ^ B * k) * (u ^ (n + 1)) =
      ((2 : ℤ_[2]) ^ B * (2 : ℤ_[2]) ^ (t * (n + 1) - n)) * (u ^ (n + 1) * k) := by ring
  rw [h_rhs]
  rw [pow_add] at h_dvd_pow
  -- h_dvd_pow : 2^(B + 2*t - 1) ∣ 2^B * 2^(t*(n+1) - n)
  -- Goal: 2^(B + 2*t - 1) ∣ (2^B * 2^(t*(n+1) - n)) * (u^(n+1) * k)
  simpa [mul_comm, mul_left_comm, mul_assoc] using dvd_mul_of_dvd_right h_dvd_pow (u ^ (n + 1) * k)

theorem FurioLombardo.M4.tail_of_series {d B t : ℕ} {a : ℕ → Fin d → ℤ_[2]} {D : Fin d → ℤ_[2]} (u : ℤ_[2]) (ht : 1 ≤ t)
    (ha : ∀ n : ℕ, 1 ≤ n → DvdV B (((n : ℤ_[2]) + 1) • a n))
    (hD : HasSum (fun n => ((2 : ℤ_[2]) ^ t * u) ^ (n + 1) • a n) D) :
    DvdV (B + 2 * t - 1) (D - ((2 : ℤ_[2]) ^ t * u) • a 0) := by
  have hD_tail : HasSum (fun n : ℕ => ((2 : ℤ_[2]) ^ t * u) ^ ((n + 1) + 1) • a (n + 1))
      (D - ((2 : ℤ_[2]) ^ t * u) • a 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hD
    simpa [Finset.sum_range_one, add_comm, add_left_comm, add_assoc] using this
  refine dvdV_of_hasSum ?_ hD_tail
  intro n
  apply tail_term u ht (by omega) (ha (n + 1) (by omega))

theorem FurioLombardo.M4.mem_of_dvdV {d B n : ℕ} {Λ : Submodule ℤ_[2] (Fin d → ℤ_[2])} (hΛ : ∀ x, DvdV B x → x ∈ Λ)
    {x : Fin d → ℤ_[2]} (h : DvdV (B + n) x) : ∃ l ∈ Λ, x = (2 : ℤ_[2]) ^ n • l := by
  choose t ht using h
  refine ⟨(2 : ℤ_[2]) ^ B • t, hΛ _ ?_, ?_⟩
  · intro i
    simpa using dvd_mul_right ((2 : ℤ_[2]) ^ B) (t i)
  · ext i
    calc
      x i = (2 : ℤ_[2]) ^ (B + n) * t i := ht i
      _ = ((2 : ℤ_[2]) ^ B * (2 : ℤ_[2]) ^ n) * t i := by rw [pow_add]
      _ = (2 : ℤ_[2]) ^ n * ((2 : ℤ_[2]) ^ B * t i) := by ring
      _ = ((2 : ℤ_[2]) ^ n • ((2 : ℤ_[2]) ^ B • t)) i := rfl
