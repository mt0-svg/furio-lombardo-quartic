import FurioLombardo.Discharge.M4Cert.Excl
import FurioLombardo.Discharge.M3a.LocalQuad

/-!
# Residue certificates at `v` for the local facts (irr) and (nsq) (WP5 of the M3a discharge)

`K_v = ℚ_2[x]/(E)` and `σ : K21 → K_v` are lane M4's (`FurioLombardo.Discharge.M4Cert`);
`Approx x t n` says `x ≡ evZ t` modulo `2^n`.

* `approx_σ_atom`: the residue of `σ (zkE l / m)` modulo `2^P` for `m = 2^j o`, `o` odd
  (`SQok`, a kernel check: `2^j` divides the residue of `σ (zkE l)` modulo `2^(P + j)`, and `oi` is
  an inverse of `o` modulo `2^P`).
* `ne_zero_of_approx`: an element with a nonzero residue is nonzero.
* `not_sq_of_sqTest`: `x ≠ 2^e r²` when the residue of `x π^(2i) / 2^(2j+e)` modulo 8 is not the
  residue of a square (`SqTest`, a kernel check).
* `exists_sqrt`: Hensel's lemma for `X² - N` at an integer triple `b` with `b² ≡ N` modulo `2^M`
  and `2^(s+1) ∤ b` (`LowOK b s`), `2 s + 4 ≤ M`: a square root `n` of `N` with `n ≡ b` modulo
  `2^(M - s - 2)`.
* `not_isSquare_of_ZOK`: `z0 + z1 ω` is not a square in `K_v(ω)`, `ω² = δ`, from residues of `z0`
  and `z0² - δ z1²`, a square root certificate `b` of the latter and the tests of
  `(z0 ± n) / 2` (`ZOK`, a kernel check), by `not_isSquare_mk`.
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open Polynomial FurioLombardo.M1 FurioLombardo.Discharge.M4Cert

theorem approx_sub {x y : Kv} {b c : T3} {n : ℕ} (hx : Approx x b n) (hy : Approx y c n) :
    Approx (x - y) (b - c) n := by
  unfold Approx at *
  rw [evZ_sub, show x - y - (evZ b - evZ c) = (x - evZ b) - (y - evZ c) by ring]
  exact (norm_sub_le_max' _ _).trans (max_le hx hy)

theorem two_ne_zero_Kv : (2 : Kv) ≠ 0 := by
  intro h
  have := norm_two_Kv
  rw [h, norm_zero] at this
  norm_num at this

/-! ## Powers of the uniformizer and division by powers of 2 -/

/-- The triple of `pv ^ k`. -/
def pvT : ℕ → T3
  | 0 => (1, 0, 0)
  | k + 1 => mulZ (pvT k) (0, 1, 0)

theorem evZ_pvT : ∀ k : ℕ, evZ (pvT k) = pv ^ k
  | 0 => by simp [pvT, evZ]
  | k + 1 => by rw [pvT, evZ_mul, evZ_pvT k, pow_succ]; simp [evZ]

/-- Coordinatewise divisibility. -/
def DvdT (t : T3) (m : ℤ) : Prop := m ∣ t.1 ∧ m ∣ t.2.1 ∧ m ∣ t.2.2

instance (t : T3) (m : ℤ) : Decidable (DvdT t m) := by unfold DvdT; infer_instance

/-- Coordinatewise quotient. -/
def divT (t : T3) (m : ℤ) : T3 := (t.1 / m, t.2.1 / m, t.2.2 / m)

theorem evZ_divT {t : T3} {m : ℤ} (h : DvdT t m) : evZ t = (m : Kv) * evZ (divT t m) := by
  obtain ⟨t0, t1, t2⟩ := t
  obtain ⟨⟨u0, rfl⟩, ⟨u1, rfl⟩, ⟨u2, rfl⟩⟩ := h
  rcases eq_or_ne m 0 with rfl | hm
  · simp [evZ, divT]
  · simp only [evZ, divT, Int.mul_ediv_cancel_left _ hm]
    push_cast
    ring

theorem approx_div {x : Kv} {t : T3} {n j : ℕ} (h : Approx x t (n + j)) (hd : DvdT t (2 ^ j)) :
    Approx (x / 2 ^ j) (divT t (2 ^ j)) n := by
  unfold Approx at *
  have h2 : (2 : Kv) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero_Kv
  have e : x / 2 ^ j - evZ (divT t (2 ^ j)) = (x - evZ t) / 2 ^ j := by
    rw [evZ_divT hd]; push_cast; field_simp
  rw [e, norm_div, norm_pow, norm_two_Kv, div_le_iff₀ (by positivity)]
  calc ‖x - evZ t‖ ≤ (2⁻¹ : ℝ) ^ (n + j) := h
    _ = (2⁻¹ : ℝ) ^ n * (2⁻¹ : ℝ) ^ j := pow_add _ _ _

/-! ## Residues of rational atoms -/

/-- The residue of `σ (zkE l / (2^j o))` modulo `2^P`, `oi` an inverse of `o` modulo `2^P`. -/
def sQres (l : List ℤ) (j : ℕ) (oi : ℤ) (P : ℕ) : T3 :=
  mulZ (divT (modT (zres l) (P + j)) (2 ^ j)) (oi, 0, 0)

/-- The conditions of `approx_σ_atom` (a kernel check). -/
def SQok (l : List ℤ) (m j o : ℕ) (oi : ℤ) (P : ℕ) : Prop :=
  zresOK l ∧ m = 2 ^ j * o ∧ P + j ≤ 28 ∧ 1 ≤ P ∧ DvdT (modT (zres l) (P + j)) (2 ^ j) ∧
    modT (mulZ ((o : ℤ), 0, 0) (oi, 0, 0)) P = modT (1, 0, 0) P

instance (l : List ℤ) (m j o : ℕ) (oi : ℤ) (P : ℕ) : Decidable (SQok l m j o oi P) := by
  unfold SQok; infer_instance

theorem approx_σ_atom {l : List ℤ} {m j o : ℕ} {oi : ℤ} {P : ℕ} (h : SQok l m j o oi P) :
    Approx (σ ((m : K21)⁻¹ * zkE l)) (sQres l j oi P) P := by
  obtain ⟨hz, hm, hP, hP1, hd, ho⟩ := h
  have h1 : Approx (σ (zkE l)) (modT (zres l) (P + j)) (P + j) := (approx_σ_zkE l hz hP).reduce
  have h2 := approx_div h1 hd
  have ho1 : Approx ((o : ℤ) : Kv) ((o : ℤ), 0, 0) P := by
    rw [← evZ_const]; exact approx_evZ _ _
  obtain ⟨ho0, ho2⟩ := approx_inv hP1 ho1 ho
  have h3 := h2.mul ho2
  unfold sQres
  convert h3 using 2
  rw [hm, map_mul, map_inv₀, map_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_inv,
    div_eq_mul_inv, Int.cast_natCast]
  ring

theorem ne_zero_of_approx {x : Kv} {t : T3} {n : ℕ} (h : Approx x t n)
    (ht : modT t n ≠ modT (0, 0, 0) n) : x ≠ 0 := by
  rintro rfl
  have h0 : Approx 0 (0, 0, 0) n := by
    have := approx_evZ ((0 : ℤ), (0 : ℤ), (0 : ℤ)) n
    rwa [evZ_zero] at this
  exact ht (modT_eq_of_approx h h0)

/-! ## The non-square test -/

/-- The residue of `t π^(2i)` modulo `2^P` is divisible by `2^(2j+e)`, `2j + e + 3 ≤ P`, and the
quotient modulo 8 is not the residue of a square. -/
def SqTest (t : T3) (i j e P : ℕ) : Prop :=
  DvdT (modT (mulZ (modT t P) (pvT (2 * i))) P) (2 ^ (2 * j + e)) ∧ 2 * j + e + 3 ≤ P ∧
    modT (divT (modT (mulZ (modT t P) (pvT (2 * i))) P) (2 ^ (2 * j + e))) 3 ∉ sq8

instance (t : T3) (i j e P : ℕ) : Decidable (SqTest t i j e P) := by
  unfold SqTest; infer_instance

theorem not_sq_of_sqTest {x : Kv} {t : T3} {i j e P : ℕ} (hx : Approx x t P)
    (h : SqTest t i j e P) (r : Kv) : x ≠ 2 ^ e * r ^ 2 := by
  obtain ⟨hd, hP, hn⟩ := h
  set u := modT (mulZ (modT t P) (pvT (2 * i))) P
  have hpv : Approx (pv ^ (2 * i)) (pvT (2 * i)) P := by
    rw [← evZ_pvT]; exact approx_evZ _ _
  have h1 : Approx (x * pv ^ (2 * i)) u P := (hx.reduce.mul hpv).reduce
  have h1' : Approx (x * pv ^ (2 * i)) u ((P - (2 * j + e)) + (2 * j + e)) := by
    rwa [Nat.sub_add_cancel (by omega)]
  have h2 : Approx (x * pv ^ (2 * i) / 2 ^ (2 * j + e)) (divT u (2 ^ (2 * j + e))) 3 :=
    (approx_div h1' hd).mono (by omega)
  intro hxr
  refine not_sq_of_approx sq8_ok hn h2 (r * pv ^ i / 2 ^ j) ?_
  have h2 := two_ne_zero_Kv
  rw [hxr]
  field_simp
  ring

/-! ## Square roots by Hensel's lemma -/

/-- Some coordinate of `b` is not divisible by `2^(s+1)`. -/
def LowOK (b : T3) (s : ℕ) : Prop := ¬ DvdT b (2 ^ (s + 1))

instance (b : T3) (s : ℕ) : Decidable (LowOK b s) := by unfold LowOK; infer_instance

theorem exists_sqrt {N : Kv} {tN b : T3} {M s : ℕ} (hN : Approx N tN M)
    (hb : modT (mulZ b b) M = modT tN M) (hlow : LowOK b s) (hM : 2 * s + 4 ≤ M) :
    ∃ n : Kv, n ^ 2 = N ∧ Approx n b (M - (s + 2)) := by
  set a := evZ b with ha_def
  have hN' : Approx N (mulZ b b) M := hN.of_modT_eq hb.symm
  have hfa : ‖a ^ 2 - N‖ ≤ (2⁻¹ : ℝ) ^ M := by
    unfold Approx at hN'
    rw [evZ_mul] at hN'
    rw [norm_sub_rev, pow_two]; exact hN'
  have ha : (2⁻¹ : ℝ) ^ (s + 1) < ‖a‖ := by
    by_contra hc
    push Not at hc
    exact hlow (dvd_of_norm_evZ_le b (s + 1) hc)
  set f : Kv[X] := X ^ 2 - C N with hf_def
  have hf : ∀ i, ‖f.coeff i‖ ≤ 1 := by
    intro i
    rw [hf_def, coeff_sub, coeff_X_pow, coeff_C]
    have hN1 := hN.norm_le_one
    rcases i with _ | _ | _ | i <;> simp [hN1]
  have hfe : f.eval a = a ^ 2 - N := by simp [hf_def]
  have hfd : f.derivative.eval a = 2 * a := by norm_num [hf_def]
  have hd : ‖f.derivative.eval a‖ = 2⁻¹ * ‖a‖ := by rw [hfd, norm_mul, norm_two_Kv]
  have hpos : (0 : ℝ) < 2⁻¹ * (2⁻¹ : ℝ) ^ (s + 1) := by positivity
  have hdle : 2⁻¹ * (2⁻¹ : ℝ) ^ (s + 1) ≤ ‖f.derivative.eval a‖ := by
    rw [hd]; exact mul_le_mul_of_nonneg_left ha.le (by norm_num)
  have hlt : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2 := by
    rw [hfe]
    calc ‖a ^ 2 - N‖ ≤ (2⁻¹ : ℝ) ^ M := hfa
      _ ≤ (2⁻¹ : ℝ) ^ (2 * s + 4) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hM
      _ = (2⁻¹ * (2⁻¹ : ℝ) ^ (s + 1)) ^ 2 := by ring
      _ < ‖f.derivative.eval a‖ ^ 2 := by
        rw [hd]
        exact pow_lt_pow_left₀ (mul_lt_mul_of_pos_left ha (by norm_num)) hpos.le two_ne_zero
  obtain ⟨z, hz, hza⟩ := hensel_of_norm_lt f hf a (norm_evZ_le_one b) hlt
  refine ⟨z, ?_, ?_⟩
  · have : f.eval z = z ^ 2 - N := by simp [hf_def]
    rw [this] at hz
    exact sub_eq_zero.mp hz
  · unfold Approx
    calc ‖z - evZ b‖ ≤ ‖f.eval a‖ / ‖f.derivative.eval a‖ := hza
      _ ≤ (2⁻¹ : ℝ) ^ M / (2⁻¹ * (2⁻¹ : ℝ) ^ (s + 1)) :=
          div_le_div₀ (by positivity) (hfe ▸ hfa) hpos hdle
      _ = (2⁻¹ : ℝ) ^ (M - (s + 2)) := by
          rw [pow_sub₀ _ (by norm_num) (by omega)]; ring

/-! ## Non-squares of `K_v(ω)` -/

/-- The certificate that `z0 + z1 ω` is not a square, from the residue `t0` of `z0` modulo
`2^P` and the residue `tN` of `z0² - δ z1²` modulo `2^M`: `b² ≡ tN` modulo `2^M`, `2^(r-2) ∤ b`,
`2 r < M`, `P + r ≤ M`, and the tests of `(z0 + b) / 2`, `(z0 - b) / 2` modulo `2^P`. -/
def ZOK (t0 tN b : T3) (M r P ip jp im jm : ℕ) : Prop :=
  modT (mulZ b b) M = modT tN M ∧ LowOK b (r - 3) ∧ 3 ≤ r ∧ 2 * r < M ∧ P + r ≤ M ∧
    SqTest (t0 + b) ip jp 1 P ∧ SqTest (t0 - b) im jm 1 P

instance (t0 tN b : T3) (M r P ip jp im jm : ℕ) : Decidable (ZOK t0 tN b M r P ip jp im jm) := by
  unfold ZOK; infer_instance

theorem not_isSquare_two_mul {x : Kv} (h : ∀ w : Kv, x ≠ 2 ^ 1 * w ^ 2) : ¬ IsSquare (2 * x) := by
  rintro ⟨s, hs⟩
  apply h (s / 2)
  have h2 := two_ne_zero_Kv
  field_simp
  linear_combination hs

theorem not_isSquare_of_ZOK {δ z0 z1 : Kv} {t0 tN b : T3} {M r P ip jp im jm : ℕ}
    (h0 : Approx z0 t0 P) (hN : Approx (z0 ^ 2 - δ * z1 ^ 2) tN M)
    (h : ZOK t0 tN b M r P ip jp im jm) :
    ¬ IsSquare (⟨z0, z1⟩ : QuadraticAlgebra Kv δ 0) := by
  obtain ⟨hb, hlow, hr, hM, hP, hp, hm⟩ := h
  obtain ⟨n, hn, hnb⟩ := exists_sqrt hN hb hlow (by omega)
  have hnP : Approx n b P := hnb.mono (by omega)
  exact FurioLombardo.Discharge.M3a.not_isSquare_mk hn
    (not_isSquare_two_mul (not_sq_of_sqTest (h0.add hnP) hp))
    (not_isSquare_two_mul (not_sq_of_sqTest (approx_sub h0 hnP) hm))

end FurioLombardo.Discharge.M3a.Bruin
