import Mathlib

/-!
# Two valuation lemmas at a prime element

* `even_of_prime_pow_mul_eq_sq`: `π ^ n Y = s²` with `π ∤ Y` forces `n` even.
* `no_sq_of_defect`: if `2 = π ^ e U` with `π ∤ U`, then `(t - s)(t + s) = π ^ k Z` with `π ∤ s`,
  `π ∤ Z`, `k` odd and `k < 2 e` is impossible (a unit `A` with `A - s² = π ^ k Z` is not a square).
-/

namespace FurioLombardo.M1

theorem even_of_prime_pow_mul_eq_sq {R : Type*} [CommRing R] [IsDomain R] {π : R}
    (hπ : Prime π) (n : ℕ) (Y s : R) (hY : ¬ π ∣ Y) (h : π ^ n * Y = s ^ 2) : Even n := by
  revert Y s
  induction' n using Nat.strong_induction_on with n ih
  intro Y s hY h
  rcases n with (rfl | rfl | m)
  · -- n = 0
    exact ⟨0, by simp⟩
  · -- n = 1
    have hπ_dvd_s_sq : π ∣ s ^ 2 := by
      have : π ∣ π ^ 1 * Y := by
        simp [pow_one, dvd_mul_right]
      rw [h] at this
      exact this
    have hπ_dvd_s : π ∣ s := hπ.dvd_of_dvd_pow hπ_dvd_s_sq
    rcases hπ_dvd_s with ⟨s', hs⟩
    have h_eq : π * Y = π ^ 2 * (s' ^ 2) := by
      calc
        π * Y = s ^ 2 := by simpa [pow_one] using h
        _ = (π * s') ^ 2 := by rw [hs]
        _ = π ^ 2 * (s' ^ 2) := by ring
    have h_cancel := mul_left_cancel₀ hπ.ne_zero (by
      calc
        π * Y = π ^ 2 * (s' ^ 2) := h_eq
        _ = π * (π * s' ^ 2) := by ring
    )
    have hY' : Y = π * (s' ^ 2) := h_cancel
    have hπ_dvd_Y : π ∣ Y := by
      rw [hY']
      exact ⟨s' ^ 2, rfl⟩
    exact absurd hπ_dvd_Y hY
  · -- n = m + 2
    have hπ_dvd_s_sq : π ∣ s ^ 2 := by
      have : π ∣ π ^ (m + 2) * Y := dvd_mul_of_dvd_left (dvd_pow (dvd_refl π) (by omega)) Y
      rw [h] at this
      exact this
    have hπ_dvd_s : π ∣ s := hπ.dvd_of_dvd_pow hπ_dvd_s_sq
    rcases hπ_dvd_s with ⟨s', hs⟩
    have h_eq : π ^ (m + 2) * Y = π ^ 2 * (s' ^ 2) := by
      calc
        π ^ (m + 2) * Y = s ^ 2 := by simpa [add_comm, add_left_comm, add_assoc] using h
        _ = (π * s') ^ 2 := by rw [hs]
        _ = π ^ 2 * (s' ^ 2) := by ring
    have h_eq2 : π ^ 2 * (π ^ m * Y) = π ^ 2 * (s' ^ 2) := by
      calc
        π ^ 2 * (π ^ m * Y) = (π ^ 2 * π ^ m) * Y := by ring
        _ = π ^ (m + 2) * Y := by ring
        _ = π ^ 2 * (s' ^ 2) := h_eq
    have h_cancel := mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) h_eq2
    have hm_lt : m < m + 2 := by omega
    have h_induction : Even m := ih m hm_lt Y s' hY h_cancel
    rcases h_induction with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    omega

/-- Exact powers: `π ^ k Z = π ^ m Y` with `π ∤ Z`, `π ∤ Y` forces `k = m`. -/
theorem eq_of_prime_pow_mul_eq {R : Type*} [CommRing R] [IsDomain R] {π : R} (hπ : Prime π)
    {k m : ℕ} {Z Y : R} (hZ : ¬ π ∣ Z) (hY : ¬ π ∣ Y) (h : π ^ k * Z = π ^ m * Y) : k = m := by
  rcases lt_trichotomy k m with hkm | hkm | hkm
  · exfalso
    apply hZ
    have e : π ^ m = π ^ k * π ^ (m - k) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_assoc] at h
    have := mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero) h
    rw [this]
    exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
  · exact hkm
  · exfalso
    apply hY
    have e : π ^ k = π ^ m * π ^ (k - m) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_assoc] at h
    have := mul_left_cancel₀ (pow_ne_zero m hπ.ne_zero) h
    rw [← this]
    exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _

/-- An exact power of `π` dividing `D`, when `π ^ e ∤ D`. -/
theorem exists_exact_pow {R : Type*} [CommRing R] {π D : R} {e : ℕ} (hD : ¬ π ^ e ∣ D) :
    ∃ n < e, ∃ D1, D = π ^ n * D1 ∧ ¬ π ∣ D1 := by
  have hex : ∃ n, ¬ π ^ (n + 1) ∣ D := by
    rcases e with _ | e
    · exact absurd (by simp) hD
    · exact ⟨e, hD⟩
  classical
  let n := Nat.find hex
  have hn : ¬ π ^ (n + 1) ∣ D := Nat.find_spec hex
  have hn' : π ^ n ∣ D := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact one_dvd D
    · have := Nat.find_min hex (show n - 1 < n by omega)
      rw [not_not, show n - 1 + 1 = n by omega] at this
      exact this
  obtain ⟨D1, hD1⟩ := hn'
  refine ⟨n, ?_, D1, hD1, ?_⟩
  · by_contra hne
    exact hD ((pow_dvd_pow π (by omega)).trans ⟨D1, hD1⟩)
  · rintro ⟨D2, hD2⟩
    exact hn ⟨D2, by rw [hD1, hD2, pow_succ, mul_assoc]⟩

theorem no_sq_of_defect {R : Type*} [CommRing R] [IsDomain R] {π : R}
    (hπ : Prime π) (e : ℕ) (U : R) (h2 : (2 : R) = π ^ e * U) (hU : ¬ π ∣ U) (s t Z : R)
    (hs : ¬ π ∣ s) (hZ : ¬ π ∣ Z) (k : ℕ) (hk : Odd k) (hk2 : k < 2 * e)
    (h : (t - s) * (t + s) = π ^ k * Z) : False := by
  have hsum : t + s = (t - s) + π ^ e * (U * s) := by rw [← mul_assoc, ← h2]; ring
  by_cases hD : π ^ e ∣ t - s
  · -- then `π ^ (2 e)` divides `π ^ k Z`
    have hE : π ^ e ∣ t + s := by
      rw [hsum]; exact dvd_add hD (dvd_mul_right _ _)
    have h2e : π ^ (2 * e) ∣ π ^ k * Z := by
      rw [← h, two_mul, pow_add]; exact mul_dvd_mul hD hE
    have e1 : π ^ (2 * e) = π ^ k * π ^ (2 * e - k) := by rw [← pow_add]; congr 1; omega
    rw [e1] at h2e
    have h3 := (mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)).mp h2e
    exact hZ ((dvd_pow_self π (by omega)).trans h3)
  · obtain ⟨n, hn, D1, hD1, hD1'⟩ := exists_exact_pow hD
    have hE : t + s = π ^ n * (D1 + π ^ (e - n) * (U * s)) := by
      have ee : π ^ e = π ^ n * π ^ (e - n) := by rw [← pow_add]; congr 1; omega
      rw [hsum, hD1, ee]; ring
    have hE' : ¬ π ∣ D1 + π ^ (e - n) * (U * s) := by
      intro hdiv
      apply hD1'
      have : π ∣ π ^ (e - n) * (U * s) := dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
      simpa using (dvd_sub hdiv this)
    have hY : ¬ π ∣ D1 * (D1 + π ^ (e - n) * (U * s)) := by
      intro hdiv
      rcases hπ.dvd_or_dvd hdiv with h' | h'
      · exact hD1' h'
      · exact hE' h'
    have heq : π ^ k * Z = π ^ (2 * n) * (D1 * (D1 + π ^ (e - n) * (U * s))) := by
      rw [← h, hD1, hE, two_mul, pow_add]; ring
    have := eq_of_prime_pow_mul_eq hπ hZ hY heq
    obtain ⟨j, hj⟩ := hk
    omega

end FurioLombardo.M1
