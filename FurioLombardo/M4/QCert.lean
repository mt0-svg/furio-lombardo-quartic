import Mathlib
import FurioLombardo.M4.Lattice

/-!
# The leading level from the quadratic characters Q
-/


open FurioLombardo.M4

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

theorem FurioLombardo.M4.intCast_two_pow_dvd_iff (k : ℕ) (m : ℤ) : (2 : ℤ_[2]) ^ k ∣ (m : ℤ_[2]) ↔ (2 : ℤ) ^ k ∣ m := by
  have hp : Fact (Nat.Prime 2) := Nat.fact_prime_two
  constructor
  · intro h
    have h_mem : (m : ℤ_[2]) ∈ Ideal.span {(2 : ℤ_[2]) ^ k} := Ideal.mem_span_singleton.mpr h
    have h_norm : ‖(m : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-k : ℤ) :=
      ((PadicInt.norm_le_pow_iff_mem_span_pow (m : ℤ_[2]) k).mpr h_mem)
    exact ((PadicInt.norm_int_le_pow_iff_dvd (k := m) (n := k) (p := 2)).mp h_norm)
  · intro h
    simpa using map_dvd (Int.castRingHom ℤ_[2]) h

theorem FurioLombardo.M4.leading_of_Q {Λ S : Submodule ℤ_[2] V} {W : Set V} {m : ℕ} {Q : V →ₗ[ℤ_[2]] (Fin m → ℤ_[2])} {r ν : ℕ}
    (hQ : QChar Λ S Q r) (hν : ν + 1 ≤ r) {y : V} (hy : y ∈ Λ)
    (h1 : ∀ i, (2 : ℤ_[2]) ^ (ν + 2) ∣ Q y i)
    (h2 : ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ Q y i)
    (h3 : ∀ w ∈ W, ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ Q y i - 2 ^ ν * Q w i) :
    Leading Λ S W ν y := by
  rcases hQ with ⟨hSΛ, hQ⟩
  have hν_le_r : ν ≤ r := by omega
  -- Step 1: InSL Λ S ν y
  have hInSLνy : InSL Λ S ν y := ((hQ ν hν_le_r y hy).mpr h1)
  rcases hInSLνy with ⟨s0, hs0S, z0, hz0Λ, hy_eq⟩
  have hs0Λ : s0 ∈ Λ := hSΛ hs0S
  -- Step 2: 2^(ν+3) ∣ Q s0 i for all i
  have hInSLRs0 : InSL Λ S r s0 := ⟨s0, hs0S, 0, Submodule.zero_mem _, by simp⟩
  have hQs0_raw : ∀ i, (2 : ℤ_[2]) ^ (r + 2) ∣ Q s0 i := by
    intro i
    exact ((hQ r (le_refl r) s0 hs0Λ).mp hInSLRs0) i
  have h_pow_dvd : (2 : ℤ_[2]) ^ (ν + 3) ∣ (2 : ℤ_[2]) ^ (r + 2) := by
    apply pow_dvd_pow (2 : ℤ_[2])
    omega
  have hQs0 : ∀ i, (2 : ℤ_[2]) ^ (ν + 3) ∣ Q s0 i := by
    intro i
    exact dvd_trans h_pow_dvd (hQs0_raw i)
  -- Step 3: Q y i = Q s0 i + 2^ν * Q z0 i
  have hQy_eq : ∀ i, Q y i = Q s0 i + (2 : ℤ_[2]) ^ ν * Q z0 i := by
    intro i
    calc
      Q y i = Q (s0 + (2 : ℤ_[2]) ^ ν • z0) i := by rw [hy_eq]
      _ = (Q s0 + Q ((2 : ℤ_[2]) ^ ν • z0)) i := by rw [map_add]
      _ = Q s0 i + Q ((2 : ℤ_[2]) ^ ν • z0) i := rfl
      _ = Q s0 i + ((2 : ℤ_[2]) ^ ν • Q z0) i := by rw [map_smul]
      _ = Q s0 i + (2 : ℤ_[2]) ^ ν * Q z0 i := by rw [Pi.smul_apply, smul_eq_mul]
  -- Step 4: ¬ InSL Λ S 1 z0
  have h_not_InSL_z0 : ¬ InSL Λ S 1 z0 := by
    intro hInSL1z0
    have hQz0 : ∀ i, (2 : ℤ_[2]) ^ (1 + 2) ∣ Q z0 i :=
      ((hQ 1 (by omega) z0 hz0Λ).mp hInSL1z0)
    have hQz0_cube : ∀ i, (2 : ℤ_[2]) ^ 3 ∣ Q z0 i := by
      intro i
      simpa using hQz0 i
    have h_dvd : ∀ i, (2 : ℤ_[2]) ^ (ν + 3) ∣ Q y i := by
      intro i
      rw [hQy_eq i]
      have h1' : (2 : ℤ_[2]) ^ (ν + 3) ∣ Q s0 i := hQs0 i
      have h2' : (2 : ℤ_[2]) ^ (ν + 3) ∣ (2 : ℤ_[2]) ^ ν * Q z0 i := by
        have h_pow_add : (2 : ℤ_[2]) ^ (ν + 3) = (2 : ℤ_[2]) ^ ν * (2 : ℤ_[2]) ^ 3 := by
          rw [← pow_add]
        rw [h_pow_add]
        exact mul_dvd_mul_left _ (hQz0_cube i)
      exact dvd_add h1' h2'
    rcases h2 with ⟨i, hi⟩
    exact hi (h_dvd i)
  -- Step 5: ∀ w ∈ W, ¬ InSL Λ S 1 (z0 - w)
  have h_forall_w : ∀ w ∈ W, ¬ InSL Λ S 1 (z0 - w) := by
    intro w hw
    intro hInSL1zw
    have hzwΛ : z0 - w ∈ Λ := by
      rcases hInSL1zw with ⟨s, hsS, l, hlΛ, hzw_eq⟩
      rw [hzw_eq]
      exact Submodule.add_mem Λ (hSΛ hsS) (Submodule.smul_mem Λ (2 : ℤ_[2]) hlΛ)
    have hQzw : ∀ i, (2 : ℤ_[2]) ^ (1 + 2) ∣ Q (z0 - w) i :=
      ((hQ 1 (by omega) (z0 - w) hzwΛ).mp hInSL1zw)
    have hQzw_cube : ∀ i, (2 : ℤ_[2]) ^ 3 ∣ Q (z0 - w) i := by
      intro i
      simpa using hQzw i
    have h_sub_eq : ∀ i, Q z0 i - Q w i = Q (z0 - w) i := by
      intro i
      calc
        Q z0 i - Q w i = (Q z0 - Q w) i := by rw [Pi.sub_apply]
        _ = Q (z0 - w) i := by rw [← map_sub Q z0 w]
    have h_dvd : ∀ i, (2 : ℤ_[2]) ^ (ν + 3) ∣ Q y i - (2 : ℤ_[2]) ^ ν * Q w i := by
      intro i
      rw [hQy_eq i]
      have h_eq : Q s0 i + (2 : ℤ_[2]) ^ ν * Q z0 i - (2 : ℤ_[2]) ^ ν * Q w i
               = Q s0 i + (2 : ℤ_[2]) ^ ν * Q (z0 - w) i := by
        calc
          Q s0 i + (2 : ℤ_[2]) ^ ν * Q z0 i - (2 : ℤ_[2]) ^ ν * Q w i
              = Q s0 i + ((2 : ℤ_[2]) ^ ν * Q z0 i - (2 : ℤ_[2]) ^ ν * Q w i) := by ring
          _ = Q s0 i + (2 : ℤ_[2]) ^ ν * (Q z0 i - Q w i) := by ring
          _ = Q s0 i + (2 : ℤ_[2]) ^ ν * Q (z0 - w) i := by rw [h_sub_eq i]
      rw [h_eq]
      have h1' : (2 : ℤ_[2]) ^ (ν + 3) ∣ Q s0 i := hQs0 i
      have h2' : (2 : ℤ_[2]) ^ (ν + 3) ∣ (2 : ℤ_[2]) ^ ν * Q (z0 - w) i := by
        have h_pow_add : (2 : ℤ_[2]) ^ (ν + 3) = (2 : ℤ_[2]) ^ ν * (2 : ℤ_[2]) ^ 3 := by
          rw [← pow_add]
        rw [h_pow_add]
        exact mul_dvd_mul_left _ (hQzw_cube i)
      exact dvd_add h1' h2'
    rcases h3 w hw with ⟨i, hi⟩
    exact hi (h_dvd i)
  -- Assemble the Leading conclusion
  refine ⟨s0, hs0S, z0, hz0Λ, 0, Submodule.zero_mem _, ?_, h_not_InSL_z0, h_forall_w⟩
  simp [hy_eq]

theorem FurioLombardo.M4.leading_of_Q_approx {Λ S : Submodule ℤ_[2] V} {W : Set V} {m : ℕ} {Q : V →ₗ[ℤ_[2]] (Fin m → ℤ_[2])} {r ν q : ℕ}
    (hQ : QChar Λ S Q r) (hν : ν + 1 ≤ r) (hq : ν + 3 ≤ q) {y c t : V} (hy : y ∈ Λ)
    (hc : y = c + (2 : ℤ_[2]) ^ q • t)
    (h1 : ∀ i, (2 : ℤ_[2]) ^ (ν + 2) ∣ Q c i)
    (h2 : ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ Q c i)
    (h3 : ∀ w ∈ W, ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ Q c i - 2 ^ ν * Q w i) :
    Leading Λ S W ν y := by
  have hy' : y ∈ Λ := hy
  have hpow_le1 : ν + 2 ≤ q := by omega
  have hpow_le2 : ν + 3 ≤ q := hq
  have hdiv_q_1 : (2 : ℤ_[2]) ^ (ν + 2) ∣ (2 : ℤ_[2]) ^ q :=
    pow_dvd_pow (2 : ℤ_[2]) hpow_le1
  have hdiv_q_2 : (2 : ℤ_[2]) ^ (ν + 3) ∣ (2 : ℤ_[2]) ^ q :=
    pow_dvd_pow (2 : ℤ_[2]) hpow_le2
  have hQy_eq : ∀ i, Q y i = Q c i + (2 : ℤ_[2]) ^ q * Q t i := by
    intro i
    rw [hc, LinearMap.map_add, LinearMap.map_smul]
    simp [Pi.add_apply, Pi.smul_apply]
  have hQy1 : ∀ i, (2 : ℤ_[2]) ^ (ν + 2) ∣ Q y i := by
    intro i
    rw [hQy_eq i]
    apply dvd_add (h1 i)
    exact hdiv_q_1.mul_right (Q t i)
  have hQy2 : ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ Q y i := by
    rcases h2 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [hQy_eq i]
    intro h
    apply hi
    have hdiv_q_t : (2 : ℤ_[2]) ^ (ν + 3) ∣ (2 : ℤ_[2]) ^ q * Q t i := hdiv_q_2.mul_right (Q t i)
    exact ((dvd_add_right hdiv_q_t).mp (by simpa [add_comm] using h))
  have hQy3 : ∀ w ∈ W, ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ Q y i - 2 ^ ν * Q w i := by
    intro w hw
    rcases h3 w hw with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [hQy_eq i]
    intro h
    apply hi
    have hdiv_q_t : (2 : ℤ_[2]) ^ (ν + 3) ∣ (2 : ℤ_[2]) ^ q * Q t i := hdiv_q_2.mul_right (Q t i)
    have h_eq : (Q c i + (2 : ℤ_[2]) ^ q * Q t i - (2 : ℤ_[2]) ^ ν * Q w i) =
        (Q c i - (2 : ℤ_[2]) ^ ν * Q w i) + (2 : ℤ_[2]) ^ q * Q t i := by
      ring
    rw [h_eq] at h
    exact ((dvd_add_right hdiv_q_t).mp (by simpa [add_comm] using h))
  exact leading_of_Q hQ hν hy' hQy1 hQy2 hQy3
