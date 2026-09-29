import FurioLombardo.M2.Residue
import FurioLombardo.M2.SpecialData

/-!
# The special primes 2 and 7 (lane M2)

* 2: `fZ ≡ X^12 (X + 1)^9 mod 2`, so every prime `P` above 2 contains `θ` or `θ - 1`. With
  `θ = v α₂²`, `θ - 1 = w α₁⁴ α₃³` (`v`, `w` units, kernel `mulCheck`s) and `N(θ) = 4`,
  `N(θ - 1) = 128`, each `α_i` has norm 2, and `P = (α_i)` for the `α_i` it contains.
* 7: `α⁷ ε = 7` (`ε` a unit), so `N(α) = 7³` and `α ∈ P` for every `P` above 7; the factor
  certificates for `e = 1, 2` with no factor show `f(P) ≥ 3`, so `N(P) ≥ 7³` and `P = (α)`.
-/

namespace FurioLombardo.M2

open Polynomial NumberField Ideal Special

theorem elt_one : elt oneL = 1 := by
  have := comboEq_sound _ _ one_eq; simpa [evalZ] using this

theorem elt_th : elt thL = θ := by
  have := comboEq_sound _ _ th_eq; simpa [evalZ] using this

theorem elt_thm1 : elt thm1L = θ - 1 := by
  have := comboEq_sound _ _ thm1_eq; rw [this]; simp [evalZ]; ring

theorem elt_seven : elt sevenL = 7 := by
  have := comboEq_sound _ _ seven_eq; rw [this]; simp [evalZ]

/-- An element of a prime `P` whose principal ideal has prime absolute norm generates `P`. -/
theorem eq_span_of_absNorm_prime (P : Ideal (𝓞 K21)) [hP : P.IsPrime] (x : 𝓞 K21) (hx : x ∈ P)
    (hn : (absNorm (span {x})).Prime) : P = span {x} := by
  have hprime : (span {x} : Ideal (𝓞 K21)).IsPrime := isPrime_of_irreducible_absNorm hn
  have hne : (span {x} : Ideal (𝓞 K21)) ≠ ⊥ := by
    intro h; rw [h, absNorm_bot] at hn; exact Nat.not_prime_zero hn
  have hmax := hprime.isMaximal hne
  exact (hmax.eq_of_le hP.ne_top ((span_singleton_le_iff_mem _).mpr hx)).symm

theorem not_mem_of_mul_eq_one {P : Ideal (𝓞 K21)} [hP : P.IsPrime] {u v : 𝓞 K21} (h : u * v = 1) :
    u ∉ P := fun hu => hP.ne_top ((eq_top_iff_one _).mpr (h ▸ P.mul_mem_right v hu))

theorem mem_of_mul_mem_of_unit {P : Ideal (𝓞 K21)} [hP : P.IsPrime] {u v x : 𝓞 K21}
    (h : u * v = 1) (hx : u * x ∈ P) : x ∈ P :=
  (hP.mem_or_mem hx).resolve_left (not_mem_of_mul_eq_one h)

theorem special_two (P : Ideal (𝓞 K21)) (hP : P ∈ primesOver (span {(2 : ℤ)}) (𝓞 K21)) :
    Submodule.IsPrincipal P := by
  obtain ⟨_, h2P, _⟩ := primesOver_facts Nat.prime_two hP
  have hPp : P.IsPrime := hP.1
  -- θ^12 (θ + 1)^9 ∈ P
  have hf2 := evalZ_eq_zero_of_forall θ _ ((allZero_iff _).mp f_mod_two)
  rw [evalZ_addZ, evalZ_smulZ, evalZ_addZ, evalZ_smulZ, evalZ_θ_fL] at hf2
  have hmod2 : evalZ θ mod2L = θ ^ 12 * (θ + 1) ^ 9 := by simp [mod2L, evalZ]; ring
  have hmem : θ ^ 12 * (θ + 1) ^ 9 ∈ P := by
    have : θ ^ 12 * (θ + 1) ^ 9 = -(2 * evalZ θ h2L) := by
      rw [← hmod2]; push_cast at hf2; linear_combination -hf2
    rw [this]
    exact P.neg_mem (P.mul_mem_right _ (by exact_mod_cast h2P))
  have hv := mulCheck_sound _ _ _ mul_v2; rw [elt_th] at hv
  have hvi := mulCheck_sound _ _ _ mul_v2i; rw [elt_one] at hvi
  have hb2 := mulCheck_sound _ _ _ mul_b2
  have hw := mulCheck_sound _ _ _ mul_w2; rw [elt_thm1] at hw
  have hwi := mulCheck_sound _ _ _ mul_w2i; rw [elt_one] at hwi
  have ha12 := mulCheck_sound _ _ _ mul_a12
  have ha14 := mulCheck_sound _ _ _ mul_a14
  have ha32 := mulCheck_sound _ _ _ mul_a32
  have ha33 := mulCheck_sound _ _ _ mul_a33
  have hm2 := mulCheck_sound _ _ _ mul_m2
  have hθ : θ = elt v2 * elt al2 ^ 2 := by rw [← hv, ← hb2]; ring
  have hθ1 : θ - 1 = elt w2 * (elt al1 ^ 4 * elt al3 ^ 3) := by
    rw [← hw, ← hm2, ← ha14, ← ha33, ← ha12, ← ha32]; ring
  rcases hPp.mem_or_mem hmem with h | h
  · -- θ ∈ P: P = (α₂)
    have hθP := hPp.mem_of_pow_mem 12 h
    rw [hθ] at hθP
    have hα := hPp.mem_of_pow_mem 2 (mem_of_mul_mem_of_unit hvi hθP)
    have hn : absNorm (span {elt al2}) ^ 2 = 4 := by
      rw [← absNorm_pow, ← absNorm_θ, hθ, absNorm_mul, absNorm_of_mul_eq_one _ _ hvi, one_mul]
    have h2 : absNorm (span {elt al2}) = 2 :=
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) (by simpa using hn)
    exact ⟨⟨_, eq_span_of_absNorm_prime P _ hα (h2 ▸ Nat.prime_two)⟩⟩
  · -- θ + 1 ∈ P, so θ - 1 ∈ P: P = (α₁) or (α₃)
    have hθP : θ - 1 ∈ P := by
      have := P.sub_mem (hPp.mem_of_pow_mem 9 h) (show (2 : 𝓞 K21) ∈ P by exact_mod_cast h2P)
      convert this using 1; ring
    rw [hθ1] at hθP
    have hm := mem_of_mul_mem_of_unit hwi hθP
    have hn : absNorm (span {elt al1}) ^ 4 * absNorm (span {elt al3}) ^ 3 = 128 := by
      have := absNorm_θ_sub_one
      rw [hθ1, absNorm_mul, absNorm_of_mul_eq_one _ _ hwi, one_mul, absNorm_mul, absNorm_pow,
        absNorm_pow] at this
      exact this
    set n1 := absNorm (span {elt al1})
    set n3 := absNorm (span {elt al3})
    have hn1 : n1 ≠ 0 := by rintro h0; rw [h0] at hn; simp at hn
    have hn3 : n3 ≠ 0 := by rintro h0; rw [h0] at hn; simp at hn
    have hb1 : n1 ≤ 3 := by
      by_contra hc; push Not at hc
      have h4 : 4 ^ 4 ≤ n1 ^ 4 := Nat.pow_le_pow_left hc 4
      have h1 : 1 ≤ n3 ^ 3 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn3)
      nlinarith
    have hb3 : n3 ≤ 5 := by
      by_contra hc; push Not at hc
      have h4 : 6 ^ 3 ≤ n3 ^ 3 := Nat.pow_le_pow_left hc 3
      have h1 : 1 ≤ n1 ^ 4 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn1)
      nlinarith
    have hval : n1 = 2 ∧ n3 = 2 := by
      interval_cases n1 <;> interval_cases n3 <;> simp_all
    rcases hPp.mem_or_mem hm with h1 | h3
    · exact ⟨⟨_, eq_span_of_absNorm_prime P _ (hPp.mem_of_pow_mem 4 h1)
        (show Nat.Prime n1 by rw [hval.1]; exact Nat.prime_two)⟩⟩
    · exact ⟨⟨_, eq_span_of_absNorm_prime P _ (hPp.mem_of_pow_mem 3 h3)
        (show Nat.Prime n3 by rw [hval.2]; exact Nat.prime_two)⟩⟩

theorem special_seven (P : Ideal (𝓞 K21)) (hP : P ∈ primesOver (span {(7 : ℤ)}) (𝓞 K21)) :
    Submodule.IsPrincipal P := by
  have hp7 : Nat.Prime 7 := by norm_num
  obtain ⟨_, h7P, hnormP⟩ := primesOver_facts hp7 hP
  have hPp : P.IsPrime := hP.1
  have h72 := mulCheck_sound _ _ _ mul_b72
  have h74 := mulCheck_sound _ _ _ mul_b74
  have h76 := mulCheck_sound _ _ _ mul_b76
  have h77 := mulCheck_sound _ _ _ mul_b77
  have he := mulCheck_sound _ _ _ mul_eps7; rw [elt_seven] at he
  have hei := mulCheck_sound _ _ _ mul_eps7i; rw [elt_one] at hei
  have h7 : (7 : 𝓞 K21) = elt eps7 * elt al7 ^ 7 := by
    rw [← he, ← h77, ← h76, ← h74, ← h72]; ring
  -- α ∈ P
  have hα : elt al7 ∈ P := by
    have : elt eps7 * elt al7 ^ 7 ∈ P := by rw [← h7]; exact_mod_cast h7P
    exact hPp.mem_of_pow_mem 7 (mem_of_mul_mem_of_unit hei this)
  -- N(α) = 7^3
  have hn : absNorm (span {elt al7}) ^ 7 = (7 ^ 3) ^ 7 := by
    rw [← absNorm_pow, show (7 ^ 3) ^ 7 = (7 : ℕ) ^ 21 by norm_num, ← absNorm_natCast 7]
    rw [show ((7 : ℕ) : 𝓞 K21) = 7 by norm_num, h7, absNorm_mul,
      absNorm_of_mul_eq_one _ _ hei, one_mul]
  have hnα : absNorm (span {elt al7}) = 7 ^ 3 :=
    (Nat.pow_left_injective (by norm_num : 7 ≠ 0)) hn
  -- f(P) ≥ 3
  have hf : 3 ≤ P.inertiaDeg ℤ := by
    have hpos : 0 < P.inertiaDeg ℤ := by
      have : P.LiesOver (span {((7 : ℕ) : ℤ)}) := hP.2
      have : (span {((7 : ℕ) : ℤ)}).IsMaximal :=
        Int.ideal_span_isMaximal_of_prime 7
      exact inertiaDeg_pos ..
    by_contra hc; push Not at hc
    have hroot := root_fLow θ evalZ_θ_fL
    rw [fLow_length] at hroot
    have hlt : 7 ^ P.inertiaDeg ℤ < 2 ^ 64 := by
      calc 7 ^ P.inertiaDeg ℤ ≤ 7 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 2 ^ 64 := by norm_num
    interval_cases h : P.inertiaDeg ℤ
    · obtain ⟨fac, hfac, _⟩ := residue_factor hp7 (by norm_num) hP (by rw [h]; norm_num) θ fLow
        fLow_length hroot [] (by simp) s71 (by rw [h]; exact fac7_1)
      simp at hfac
    · obtain ⟨fac, hfac, _⟩ := residue_factor hp7 (by norm_num) hP (by rw [h]; norm_num) θ fLow
        fLow_length hroot [] (by simp) s72 (by rw [h]; exact fac7_2)
      simp at hfac
  -- (α) = P J with N(J) = 1
  have hle : span {elt al7} ≤ P := (span_singleton_le_iff_mem _).mpr hα
  obtain ⟨J, hJ⟩ := (dvd_iff_le.mpr hle : P ∣ span {elt al7})
  have hnJ : absNorm P * absNorm J = 7 ^ 3 := by rw [← map_mul, ← hJ, hnα]
  have hP3 : 7 ^ 3 ≤ absNorm P := by
    rw [hnormP]; exact Nat.pow_le_pow_right (by norm_num) hf
  have hJ1 : absNorm J = 1 := by
    have hJ0 : absNorm J ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hnJ; norm_num at hnJ
    have : absNorm P * absNorm J ≥ 7 ^ 3 * absNorm J := Nat.mul_le_mul_right _ hP3
    have : absNorm J ≤ 1 := by nlinarith
    omega
  rw [absNorm_eq_one_iff] at hJ1
  rw [hJ1, mul_top] at hJ
  exact ⟨⟨_, hJ.symm⟩⟩

end FurioLombardo.M2
