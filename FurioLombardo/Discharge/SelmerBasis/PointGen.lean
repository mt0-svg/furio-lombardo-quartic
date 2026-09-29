import FurioLombardo.Discharge.SelmerBasis.PlaceWModel
import FurioLombardo.Discharge.SelmerBasis.TowerFacts
import FurioLombardo.Discharge.SelmerSpan.Mumford

/-!
# Local points at a w-place from integer Mumford data (lane selmer-basis w-places)

For a twist `k` and a place `σ : K21 →+* K_w` (`WPlace`), a `PtData` describes a point `[⟨U, Y - V⟩]`
of `Jac ((fRev k)^σ)` with `U = X² + (P/d) X + R/d`, `P, R` integral in `K21` (lane M4's divisors
reduced w-adically, code/selmer-local-conditions/local_data_w6.gp):

* `Z1, Z0` with `Z1 X + Z0 = d⁵ (4 fRev_k mod U)` (`zsE`: the recurrence of `divW` cleared of `d`);
* two Hensel certificates, `n0 = al^nj (1 + al nd)` with `n0² - N' = al^nM nR`,
  `N' = d (d Z0² - P Z1 Z0 + R Z1²)`, and `a0 = al^aj (1 + al ad)` with
  `a0² - (2 d Z0 - P Z1 + 2 n0) = al^aM aR`: in `K_w` they give `n'² = N'` and
  `a'² = 2 d Z0 - P Z1 + 2 n'` (`exists_pair_of_certs`), hence `V` (`mumford_of_scaled`, from
  SelmerSpan's `sq_sub_eq`);
* `tL`, `tN`: the coordinates of `Λ² U(α)` in `L42` and of `Λ² U(β)` in `N84` (`Λ = lamL, lamN`), one
  `checkLC` / `checkNC` against the tables of powers of TowerChecks.lean (`aeval_alphaR_csL`,
  `aeval_betaR_csN`).

`PtData.exists_point`: from `okD` and `okZ`, a point `D` with `μ(D) = [U(T)]`.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.M3a.Genus2
  FurioLombardo.Discharge.SelmerSpan FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.M3b

/-! ## The scaled remainder of a sextic -/

/-- `(Z1, Z0)` with `Z1 X + Z0 = d⁵ (Σ g_j X^j mod X² + (P/d) X + Q/d)`: the recurrence of `divW`
cleared of the denominator `d`. -/
def zsF {R : Type*} [CommRing R] (g : Fin 7 → R) (P Q : R) (d : ℕ) : R × R :=
  let w3 := (d : R) * g 5 - P * g 6
  let w2 := ((d ^ 2 : ℕ) : R) * g 4 - P * w3 - (d : R) * Q * g 6
  let w1 := ((d ^ 3 : ℕ) : R) * g 3 - P * w2 - (d : R) * Q * w3
  let w0 := ((d ^ 4 : ℕ) : R) * g 2 - P * w1 - (d : R) * Q * w2
  (((d ^ 5 : ℕ) : R) * g 1 - P * w0 - (d : R) * Q * w1, ((d ^ 5 : ℕ) : R) * g 0 - Q * w0)

/-- `zsF` on expressions (the form checked in the kernel by `PtData.okZ`). -/
def zsE (g : Fin 7 → KE) (P Q : KE) (d : ℕ) : KE × KE :=
  let D : KE := .int (d : ℤ)
  let w3 : KE := .sub (.mul D (g 5)) (.mul P (g 6))
  let w2 : KE := .sub (.sub (.mul (.int ((d ^ 2 : ℕ) : ℤ)) (g 4)) (.mul P w3)) (.mul (.mul D Q) (g 6))
  let w1 : KE := .sub (.sub (.mul (.int ((d ^ 3 : ℕ) : ℤ)) (g 3)) (.mul P w2)) (.mul (.mul D Q) w3)
  let w0 : KE := .sub (.sub (.mul (.int ((d ^ 4 : ℕ) : ℤ)) (g 2)) (.mul P w1)) (.mul (.mul D Q) w2)
  (.sub (.sub (.mul (.int ((d ^ 5 : ℕ) : ℤ)) (g 1)) (.mul P w0)) (.mul (.mul D Q) w1),
    .sub (.mul (.int ((d ^ 5 : ℕ) : ℤ)) (g 0)) (.mul Q w0))

theorem evK_zsE (g : Fin 7 → KE) (P Q : KE) (d : ℕ) :
    (evK (zsE g P Q d).1, evK (zsE g P Q d).2) = zsF (fun j => evK (g j)) (evK P) (evK Q) d := by
  unfold zsE zsF
  simp only [evK_sub, evK_mul, evK_int]
  ext <;> push_cast <;> ring

theorem map_zsF {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (g : Fin 7 → R) (P Q : R)
    (d : ℕ) : zsF (fun j => φ (g j)) (φ P) (φ Q) d = (φ (zsF g P Q d).1, φ (zsF g P Q d).2) := by
  unfold zsF
  simp

theorem zsF_eq_divR {F : Type*} [Field F] (g : Fin 7 → F) (P Q : F) {d : ℕ} (hd : (d : F) ≠ 0) :
    zsF g P Q d =
      ((d : F) ^ 5 * divR1 (P / d) (Q / d) (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6),
        (d : F) ^ 5 * divR0 (P / d) (Q / d) (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6)) := by
  unfold zsF divR1 divR0 divW
  push_cast
  field_simp [hd]

/-! ## The Mumford pair of a scaled point -/

/-- **`V² - f = U W` with `U = X² + (P/d) X + Q/d` coprime to `f`**, from the scaled square roots
`n² = d (d Z0² - P Z1 Z0 + Q Z1²)` and `a² = 2 d Z0 - P Z1 + 2 n` (`(Z1, Z0) = zsF g P Q d`,
`g_j = 4 f_j`). -/
theorem mumford_of_scaled {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {f : F[X]} (hf : f.natDegree ≤ 6)
    (g : Fin 7 → F) (hg : ∀ j : Fin 7, f.coeff j = g j / 4) (P Q : F) {d : ℕ} (hd : (d : F) ≠ 0)
    {n a : F}
    (hn : n ^ 2 = (d : F) * ((d : F) * (zsF g P Q d).2 ^ 2 - P * (zsF g P Q d).1 * (zsF g P Q d).2 +
      Q * (zsF g P Q d).1 ^ 2))
    (ha : a ^ 2 = 2 * (d : F) * (zsF g P Q d).2 - P * (zsF g P Q d).1 + 2 * n) (hn0 : n ≠ 0)
    (ha0 : a ≠ 0) :
    ∃ V W : F[X], V ^ 2 - f = quad (P / d) (Q / d) * W ∧ IsCoprime (quad (P / d) (Q / d)) f := by
  set p := P / (d : F) with hp
  set r := Q / (d : F) with hr
  set z1 := (zsF g P Q d).1 with hz1
  set z0 := (zsF g P Q d).2 with hz0
  have hd' : (d : F) ≠ 0 := hd
  have h4 : (4 : F) ≠ 0 := by
    intro h4zero
    have h4eq : (4 : F) = (2 : F) * (2 : F) := by norm_num
    rw [h4eq] at h4zero
    have h := mul_eq_zero.mp h4zero
    rcases h with (h2' | h2'')
    · exact h2 h2'
    · exact h2 h2''
  have h16 : (16 : F) ≠ 0 := by
    intro h16zero
    apply h4
    have h16eq : (16 : F) = (4 : F) * (4 : F) := by norm_num
    rw [h16eq] at h16zero
    have h := mul_eq_zero.mp h16zero
    rcases h with (h4' | h4'')
    · exact h4'
    · exact h4''
  set Z1 := z1 / ((d : F)^5) with hZ1
  set Z0 := z0 / ((d : F)^5) with hZ0
  set n' := n / ((d : F)^6) with hn'
  set a' := a / ((d : F)^3) with ha'
  have ha0' : a' ≠ 0 := by
    intro ha'zero
    apply ha0
    dsimp [a'] at ha'zero
    field_simp [hd'] at ha'zero
    simpa using ha'zero
  have hn' : n' ^ 2 = Z0 ^ 2 - p * Z1 * Z0 + r * Z1 ^ 2 := by
    dsimp [n', Z0, Z1, z0, z1, p, r]
    field_simp [hd']
    rw [hn]
    ring
  have ha' : a' ^ 2 = 2 * Z0 - p * Z1 + 2 * n' := by
    dsimp [a', n', Z0, Z1, z0, z1, p]
    field_simp [hd']
    rw [ha]
    ring
  have hdivR1_scale (g0 g1 g2 g3 g4 g5 g6 s : F) :
      divR1 p r (s * g0) (s * g1) (s * g2) (s * g3) (s * g4) (s * g5) (s * g6) = s * divR1 p r g0 g1 g2 g3 g4 g5 g6 := by
    dsimp [divR1, divW]
    ring
  have hdivR0_scale (g0 g1 g2 g3 g4 g5 g6 s : F) :
      divR0 p r (s * g0) (s * g1) (s * g2) (s * g3) (s * g4) (s * g5) (s * g6) = s * divR0 p r g0 g1 g2 g3 g4 g5 g6 := by
    dsimp [divR0, divW]
    ring
  have hZ1_pair := congr_arg Prod.fst (zsF_eq_divR g P Q hd)
  have hZ0_pair := congr_arg Prod.snd (zsF_eq_divR g P Q hd)
  have hZ1 : z1 / ((d : F)^5) = divR1 p r (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) := by
    dsimp [z1]
    rw [hZ1_pair, hp, hr]
    field_simp [hd']
  have hZ0 : z0 / ((d : F)^5) = divR0 p r (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) := by
    dsimp [z0]
    rw [hZ0_pair, hp, hr]
    field_simp [hd']
  have hdivR1_scaled : divR1 p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4) = Z1 / 4 := by
    calc
      divR1 p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4)
          = divR1 p r ((1/4 : F) * g 0) ((1/4 : F) * g 1) ((1/4 : F) * g 2) ((1/4 : F) * g 3) ((1/4 : F) * g 4) ((1/4 : F) * g 5) ((1/4 : F) * g 6) := by
            simp [div_eq_mul_inv, mul_comm]
      _ = (1/4 : F) * divR1 p r (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) := by rw [hdivR1_scale]
      _ = (1/4 : F) * Z1 := by rw [← hZ1]
      _ = Z1 / 4 := by ring
  have hdivR0_scaled : divR0 p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4) = Z0 / 4 := by
    calc
      divR0 p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4)
          = divR0 p r ((1/4 : F) * g 0) ((1/4 : F) * g 1) ((1/4 : F) * g 2) ((1/4 : F) * g 3) ((1/4 : F) * g 4) ((1/4 : F) * g 5) ((1/4 : F) * g 6) := by
            simp [div_eq_mul_inv, mul_comm]
      _ = (1/4 : F) * divR0 p r (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) := by rw [hdivR0_scale]
      _ = (1/4 : F) * Z0 := by rw [← hZ0]
      _ = Z0 / 4 := by ring
  have hf_eq : f = C (g 6 / 4) * X ^ 6 + C (g 5 / 4) * X ^ 5 + C (g 4 / 4) * X ^ 4 +
      C (g 3 / 4) * X ^ 3 + C (g 2 / 4) * X ^ 2 + C (g 1 / 4) * X + C (g 0 / 4) := by
    have h := eq_sextic_of_natDegree_le hf
    refine h.trans ?_
    apply Polynomial.ext
    intro i
    by_cases hi6 : i = 6
    · subst hi6; simp [coeff_add]; exact hg (6 : Fin 7)
    · by_cases hi5 : i = 5
      · subst hi5; simp [coeff_add]; exact hg (5 : Fin 7)
      · by_cases hi4 : i = 4
        · subst hi4; simp [coeff_add]; exact hg (4 : Fin 7)
        · by_cases hi3 : i = 3
          · subst hi3; simp [coeff_add]; exact hg (3 : Fin 7)
          · by_cases hi2 : i = 2
            · subst hi2; simp [coeff_add]; exact hg (2 : Fin 7)
            · by_cases hi1 : i = 1
              · subst hi1; simp [coeff_add]; exact hg (1 : Fin 7)
              · by_cases hi0 : i = 0
                · subst hi0; simp [coeff_add]; exact hg (0 : Fin 7)
                · have hi_gt_6 : 6 < i := by omega
                  simp [coeff_add, coeff_C, coeff_X, hi0, hi1, hi2, hi3, hi4, hi5, hi6, eq_comm]
  set V := C (sqB Z1 a') * X + C (sqC p Z1 a') with hV
  have hV_sq : V ^ 2 - (C (Z1 / 4) * X + C (Z0 / 4)) = C (sqB Z1 a' ^ 2) * quad p r := by
    rw [hV]
    exact sq_sub_eq h2 hn' ha' ha0'
  have h_remainder : C (divR1 p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4)) * X + C (divR0 p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4)) = C (Z1 / 4) * X + C (Z0 / 4) := by
    rw [hdivR1_scaled, hdivR0_scaled]
  have h_main : V ^ 2 - f = quad p r * (C (sqB Z1 a' ^ 2) - divQ p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4)) := by
    rw [hf_eq, sextic_eq p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4), h_remainder]
    calc
      V ^ 2 - (quad p r * divQ p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4) + (C (Z1 / 4) * X + C (Z0 / 4)))
          = (V ^ 2 - (C (Z1 / 4) * X + C (Z0 / 4))) - quad p r * divQ p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4) := by ring
      _ = (C (sqB Z1 a' ^ 2) * quad p r) - quad p r * divQ p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4) := by rw [hV_sq]
      _ = quad p r * (C (sqB Z1 a' ^ 2) - divQ p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4)) := by ring
  have hn0' : n' ≠ 0 := by
    intro hn0zero
    apply hn0
    dsimp [n'] at hn0zero
    field_simp [hd'] at hn0zero
    simpa using hn0zero
  have hrho : (Z0 / 4) ^ 2 - p * (Z1 / 4) * (Z0 / 4) + r * (Z1 / 4) ^ 2 ≠ 0 := by
    have h_eq : (Z0 / 4) ^ 2 - p * (Z1 / 4) * (Z0 / 4) + r * (Z1 / 4) ^ 2 = n' ^ 2 / 16 := by
      field_simp [h4]
      rw [hn']
      ring
    rw [h_eq]
    apply div_ne_zero
    · apply pow_ne_zero 2 hn0'
    · exact h16
  have h_coprime : IsCoprime (quad p r) (C (Z1 / 4) * X + C (Z0 / 4)) := by
    apply isCoprime_quad_lin
    exact hrho
  have h_coprime_f : IsCoprime (quad p r) f := by
    rw [hf_eq, sextic_eq p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4), h_remainder]
    rw [add_comm]
    exact IsCoprime.add_mul_left_right h_coprime _
  exact ⟨V, C (sqB Z1 a' ^ 2) - divQ p r (g 0 / 4) (g 1 / 4) (g 2 / 4) (g 3 / 4) (g 4 / 4) (g 5 / 4) (g 6 / 4), h_main, h_coprime_f⟩

/-! ## Square roots from Hensel certificates -/

section Hensel

theorem norm_pow_mul_one_add {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {π δ : K} (hπ : ‖π‖ < 1) (hδ : ‖δ‖ ≤ 1) (j : ℕ) :
    ‖π ^ j * (1 + π * δ)‖ = ‖π‖ ^ j := by
  have h_mul : ‖π * δ‖ < 1 := by
    calc
      ‖π * δ‖ ≤ ‖π‖ * ‖δ‖ := norm_mul_le _ _
      _ ≤ ‖π‖ * 1 := mul_le_mul_of_nonneg_left hδ (norm_nonneg _)
      _ = ‖π‖ := mul_one _
      _ < 1 := hπ
  have h_one_ne_mul : ‖(1 : K)‖ ≠ ‖π * δ‖ := by
    rw [norm_one]
    exact (ne_of_lt h_mul).symm
  have h_norm_add : ‖(1 : K) + π * δ‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_one_ne_mul, norm_one, max_eq_left (by linarith)]
  calc
    ‖π ^ j * (1 + π * δ)‖ = ‖π ^ j‖ * ‖(1 : K) + π * δ‖ := norm_mul _ _
    _ = ‖π‖ ^ j * ‖(1 : K) + π * δ‖ := by rw [norm_pow]
    _ = ‖π‖ ^ j * 1 := by rw [h_norm_add]
    _ = ‖π‖ ^ j := mul_one _

/-- **Hensel certificate.** `n0 = π^j (1 + π δ)` with `n0² - z = π^M ρ` and `M > 2e + 2j` gives a
square root of `z` within `‖π‖^(M - e - j)` of `n0`. -/
theorem exists_sqrt_of_cert {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {π z δ ρ : K} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) {e j M : ℕ}
    (h2 : ‖(2 : K)‖ = ‖π‖ ^ e) (hz : ‖z‖ ≤ 1) (hδ : ‖δ‖ ≤ 1) (hρ : ‖ρ‖ ≤ 1)
    (hM : 2 * e + 2 * j < M) (hc : (π ^ j * (1 + π * δ)) ^ 2 - z = π ^ M * ρ) :
    ∃ s : K, s ^ 2 = z ∧ ‖s - π ^ j * (1 + π * δ)‖ ≤ ‖π‖ ^ (M - e - j) := by
  set n0 := π ^ j * (1 + π * δ) with hn0
  have hπ_norm_pos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have hπ_norm_le_one : ‖π‖ ≤ 1 := le_of_lt hπ1
  have hπδ_norm_lt_one : ‖π * δ‖ < 1 := by
    calc
      ‖π * δ‖ = ‖π‖ * ‖δ‖ := norm_mul _ _
      _ ≤ ‖π‖ * 1 := mul_le_mul_of_nonneg_left hδ (norm_nonneg _)
      _ = ‖π‖ := mul_one _
      _ < 1 := hπ1
  have h_one_norm_ne_hπδ_norm : ‖(1 : K)‖ ≠ ‖π * δ‖ := by
    rw [norm_one]
    exact (ne_of_lt hπδ_norm_lt_one).symm
  have h_norm_one_plus_πδ : ‖(1 : K) + π * δ‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_one_norm_ne_hπδ_norm, norm_one,
      max_eq_left (le_of_lt hπδ_norm_lt_one)]
  have h_norm_n0 : ‖n0‖ = ‖π‖ ^ j := by
    rw [hn0, norm_mul, norm_pow, h_norm_one_plus_πδ, mul_one]
  have hn0_norm_le_one : ‖n0‖ ≤ 1 := by
    rw [h_norm_n0]
    exact pow_le_one₀ (norm_nonneg _) hπ_norm_le_one
  have h_main : ‖n0 ^ 2 - z‖ < ‖2 * n0‖ ^ 2 := by
    rw [hc]
    have h_bound : ‖π ^ M * ρ‖ ≤ ‖π‖ ^ M := by
      calc
        ‖π ^ M * ρ‖ ≤ ‖π ^ M‖ * ‖ρ‖ := norm_mul_le _ _
        _ = ‖π‖ ^ M * ‖ρ‖ := by rw [norm_pow]
        _ ≤ ‖π‖ ^ M * 1 := mul_le_mul_of_nonneg_left hρ (by positivity)
        _ = ‖π‖ ^ M := mul_one _
    have h_sq : ‖2 * n0‖ ^ 2 = ‖π‖ ^ (2 * e + 2 * j) := by
      rw [norm_mul, h2, h_norm_n0, ← pow_add, sq, pow_add]
      ring
    have h_lt : ‖π‖ ^ M < ‖π‖ ^ (2 * e + 2 * j) := by
      refine pow_lt_pow_right_of_lt_one₀ hπ_norm_pos hπ1 ?_
      omega
    calc
      ‖π ^ M * ρ‖ ≤ ‖π‖ ^ M := h_bound
      _ < ‖π‖ ^ (2 * e + 2 * j) := h_lt
      _ = ‖2 * n0‖ ^ 2 := by rw [h_sq]
  have h_exists : ∃ s : K, s ^ 2 = z ∧ ‖s - n0‖ ≤ ‖n0 ^ 2 - z‖ / ‖2 * n0‖ :=
    exists_sqrt_near hz hn0_norm_le_one h_main
  rcases h_exists with ⟨s, hs_sq, hs_bound⟩
  refine ⟨s, hs_sq, ?_⟩
  have h_pos : 0 < ‖2 * n0‖ := by
    rw [norm_mul, h2, h_norm_n0]
    have h1 : 0 < ‖π‖ ^ e := pow_pos hπ_norm_pos e
    have h2' : 0 < ‖π‖ ^ j := pow_pos hπ_norm_pos j
    positivity
  have h_norm_2n0 : ‖2 * n0‖ = ‖π‖ ^ (e + j) := by
    rw [norm_mul, h2, h_norm_n0, pow_add]
  have h_e_add_j_le_M : e + j ≤ M := by
    have : e + j ≤ 2 * e + 2 * j := by omega
    omega
  have h_pow_add : ‖π‖ ^ (M - e - j) * ‖π‖ ^ (e + j) = ‖π‖ ^ M := by
    have h_add : (M - e - j) + (e + j) = M := by omega
    rw [← pow_add, h_add]
  have h_goal : ‖π ^ M * ρ‖ ≤ ‖π‖ ^ (M - e - j) * ‖2 * n0‖ := by
    rw [h_norm_2n0]
    have h_temp : ‖π ^ M * ρ‖ ≤ ‖π‖ ^ M := by
      calc
        ‖π ^ M * ρ‖ ≤ ‖π ^ M‖ * ‖ρ‖ := norm_mul_le _ _
        _ = ‖π‖ ^ M * ‖ρ‖ := by rw [norm_pow]
        _ ≤ ‖π‖ ^ M * 1 := mul_le_mul_of_nonneg_left hρ (by positivity)
        _ = ‖π‖ ^ M := mul_one _
    calc
      ‖π ^ M * ρ‖ ≤ ‖π‖ ^ M := h_temp
      _ = ‖π‖ ^ (M - e - j) * ‖π‖ ^ (e + j) := by rw [h_pow_add.symm]
  have h_div_bound : ‖n0 ^ 2 - z‖ / ‖2 * n0‖ ≤ ‖π‖ ^ (M - e - j) := by
    rw [hc, div_le_iff₀ h_pos]
    exact h_goal
  calc
    ‖s - n0‖ ≤ ‖n0 ^ 2 - z‖ / ‖2 * n0‖ := hs_bound
    _ ≤ ‖π‖ ^ (M - e - j) := h_div_bound

/-- **The two square roots of a point.** Certificates for `n² = N` and for `a² = X + 2 n0` (with
`n0` in place of `n`) give `n² = N` and `a² = X + 2 n` exactly, both nonzero. -/
theorem exists_pair_of_certs {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {π N X δ ρ δa ρa : K} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    {e j M ja Ma : ℕ} (h2 : ‖(2 : K)‖ = ‖π‖ ^ e) (hN : ‖N‖ ≤ 1) (hX : ‖X‖ ≤ 1) (hδ : ‖δ‖ ≤ 1)
    (hρ : ‖ρ‖ ≤ 1) (hδa : ‖δa‖ ≤ 1) (hρa : ‖ρa‖ ≤ 1) (hM : 2 * e + 2 * j < M)
    (hMa : 2 * e + 2 * ja < Ma) (hMa' : 2 * e + 2 * ja + j < M)
    (hc : (π ^ j * (1 + π * δ)) ^ 2 - N = π ^ M * ρ)
    (hca : (π ^ ja * (1 + π * δa)) ^ 2 - (X + 2 * (π ^ j * (1 + π * δ))) = π ^ Ma * ρa) :
    ∃ n a : K, n ^ 2 = N ∧ a ^ 2 = X + 2 * n ∧ n ≠ 0 ∧ a ≠ 0 := by
  set n0 := π ^ j * (1 + π * δ) with hn0_def
  set a0 := π ^ ja * (1 + π * δa) with ha0_def
  have hn0_norm : ‖n0‖ = ‖π‖ ^ j := norm_pow_mul_one_add hπ1 hδ j
  have ha0_norm : ‖a0‖ = ‖π‖ ^ ja := norm_pow_mul_one_add hπ1 hδa ja
  have hπ_norm_pos : 0 < ‖π‖ := by
    rwa [norm_pos_iff]
  have hn0_norm_pos : 0 < ‖n0‖ := by
    rw [hn0_norm]
    exact pow_pos hπ_norm_pos j
  have ha0_norm_pos : 0 < ‖a0‖ := by
    rw [ha0_norm]
    exact pow_pos hπ_norm_pos ja
  have hn0_norm_le_one : ‖n0‖ ≤ 1 := by
    rw [hn0_norm]
    simpa [pow_zero] using pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.zero_le j)
  have ha0_norm_le_one : ‖a0‖ ≤ 1 := by
    rw [ha0_norm]
    simpa [pow_zero] using pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.zero_le ja)
  -- Step 1: get n from exists_sqrt_of_cert
  obtain ⟨n, hn_sq, hn_dist⟩ := exists_sqrt_of_cert hπ0 hπ1 h2 hN hδ hρ hM hc
  -- hn_dist: ‖n - π^j*(1+π*δ)‖ ≤ ‖π‖^(M - e - j), i.e., ‖n - n0‖ ≤ ‖π‖^(M - e - j)
  have hn_dist' : ‖n - n0‖ ≤ ‖π‖ ^ (M - e - j) := by
    simpa [hn0_def] using hn_dist
  -- Step 2: n ≠ 0
  have hMj_gt_j : j < M - e - j := by
    have h : e + 2 * j < M := by omega
    omega
  have hn_ne_zero : n ≠ 0 := by
    intro hzero
    have h_lt : ‖π‖ ^ (M - e - j) < ‖π‖ ^ j := by
      refine pow_lt_pow_right_of_lt_one₀ hπ_norm_pos hπ1 ?_
      omega
    have h_lt' : ‖n - n0‖ < ‖n0‖ := by
      calc
        ‖n - n0‖ ≤ ‖π‖ ^ (M - e - j) := hn_dist'
        _ < ‖π‖ ^ j := h_lt
        _ = ‖n0‖ := by symm; exact hn0_norm
    have h_eq : ‖n - n0‖ = ‖n0‖ := by
      simpa [hzero] using (norm_neg n0)
    linarith
  -- Step 3: ‖n‖ ≤ 1
  have hn_norm_le_one : ‖n‖ ≤ 1 := by
    calc
      ‖n‖ = ‖(n - n0) + n0‖ := by ring
      _ ≤ max ‖n - n0‖ ‖n0‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (‖π‖ ^ (M - e - j)) (‖π‖ ^ j) := by
        refine max_le_max hn_dist' (by rw [hn0_norm])
      _ ≤ 1 := by
        refine max_le ?_ ?_
        · simpa [pow_zero] using pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.zero_le _)
        · simpa [pow_zero] using pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.zero_le _)
  -- Step 4: set z = X + 2*n, show ‖z‖ ≤ 1
  set z := X + 2 * n with hz_def
  have hz_norm_le_one : ‖z‖ ≤ 1 := by
    rw [hz_def]
    calc
      ‖X + 2 * n‖ ≤ max ‖X‖ ‖2 * n‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max 1 (‖2 * n‖) := max_le_max hX (le_refl _)
      _ ≤ max 1 1 :=
        max_le (le_max_left _ _) (by
          calc
          ‖2 * n‖ = ‖(2 : K)‖ * ‖n‖ := norm_mul _ _
          _ = ‖π‖ ^ e * ‖n‖ := by rw [h2]
          _ ≤ ‖π‖ ^ e * 1 := mul_le_mul_of_nonneg_left hn_norm_le_one (pow_nonneg (norm_nonneg _) _)
          _ = ‖π‖ ^ e := mul_one _
          _ ≤ 1 := by
            simpa [pow_zero] using pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.zero_le e)
          _ ≤ max 1 1 := le_max_right _ _)
      _ = 1 := max_self _
  -- Step 5: show ‖a0^2 - z‖ < ‖2*a0‖^2
  have h_a0_sq_sub_z_norm_lt : ‖a0 ^ 2 - z‖ < ‖2 * a0‖ ^ 2 := by
    -- a0^2 - z = a0^2 - (X + 2*n) = (a0^2 - (X + 2*n0)) + 2*(n0 - n)
    -- = π^Ma * ρa - 2*(n - n0)  (by hca)
    have h_eq : a0 ^ 2 - z = π ^ Ma * ρa - 2 * (n - n0) := by
      calc
        a0 ^ 2 - z = a0 ^ 2 - (X + 2 * n) := rfl
        _ = (a0 ^ 2 - (X + 2 * n0)) + (2 * n0 - 2 * n) := by ring
        _ = (π ^ Ma * ρa) + (2 * n0 - 2 * n) := by
          rw [ha0_def, hn0_def, ← hca]
        _ = π ^ Ma * ρa - 2 * (n - n0) := by ring
    rw [h_eq]
    have h_ultrametric : ‖π ^ Ma * ρa - 2 * (n - n0)‖ ≤
        max (‖π ^ Ma * ρa‖) (‖2 * (n - n0)‖) := by
      simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max (π ^ Ma * ρa) (-(2 * (n - n0)))
    have h1 : ‖π ^ Ma * ρa‖ < ‖2 * a0‖ ^ 2 := by
      calc
        ‖π ^ Ma * ρa‖ = ‖π ^ Ma‖ * ‖ρa‖ := norm_mul _ _
        _ = ‖π‖ ^ Ma * ‖ρa‖ := by simp
        _ ≤ ‖π‖ ^ Ma * 1 := mul_le_mul_of_nonneg_left hρa (pow_nonneg (norm_nonneg _) _)
        _ = ‖π‖ ^ Ma := mul_one _
        _ < ‖π‖ ^ (2 * e + 2 * ja) := by
          refine pow_lt_pow_right_of_lt_one₀ hπ_norm_pos hπ1 ?_
          omega
        _ = (‖π‖ ^ (e + ja)) ^ 2 := by ring
        _ = (‖π‖ ^ e * ‖π‖ ^ ja) ^ 2 := by simp [pow_add]
        _ = (‖(2 : K)‖ * ‖a0‖) ^ 2 := by rw [h2, ha0_norm]
        _ = ‖2 * a0‖ ^ 2 := by simp [norm_mul]
    have h2' : ‖2 * (n - n0)‖ < ‖2 * a0‖ ^ 2 := by
      calc
        ‖2 * (n - n0)‖ = ‖(2 : K)‖ * ‖n - n0‖ := norm_mul _ _
        _ = ‖π‖ ^ e * ‖n - n0‖ := by rw [h2]
        _ ≤ ‖π‖ ^ e * (‖π‖ ^ (M - e - j)) :=
          mul_le_mul_of_nonneg_left hn_dist' (pow_nonneg (norm_nonneg _) _)
        _ = ‖π‖ ^ (e + (M - e - j)) := by simp [pow_add]
        _ = ‖π‖ ^ (M - j) := by
          have h_ej_lt_M : e + j < M := by omega
          congr 1
          omega
        _ < ‖π‖ ^ (2 * e + 2 * ja) := by
          refine pow_lt_pow_right_of_lt_one₀ hπ_norm_pos hπ1 ?_
          omega
        _ = (‖π‖ ^ (e + ja)) ^ 2 := by ring
        _ = (‖π‖ ^ e * ‖π‖ ^ ja) ^ 2 := by simp [pow_add]
        _ = (‖(2 : K)‖ * ‖a0‖) ^ 2 := by rw [h2, ha0_norm]
        _ = ‖2 * a0‖ ^ 2 := by simp [norm_mul]
    apply lt_of_le_of_lt h_ultrametric
    exact max_lt h1 h2'
  -- Step 6: apply exists_sqrt_near to get a
  obtain ⟨a, ha_sq, ha_dist⟩ := exists_sqrt_near hz_norm_le_one ha0_norm_le_one h_a0_sq_sub_z_norm_lt
  -- ha_sq: a^2 = z = X + 2*n
  -- ha_dist: ‖a - a0‖ ≤ ‖a0^2 - z‖ / ‖2*a0‖
  have ha_ne_zero : a ≠ 0 := by
    have h_two_a0_ne_zero : ‖2 * a0‖ ≠ 0 := by
      have hpos : 0 < ‖2 * a0‖ := by
        rw [norm_mul]
        exact mul_pos (by
          rw [h2]
          exact pow_pos hπ_norm_pos e) ha0_norm_pos
      exact ne_of_gt hpos
    have h_lt : ‖a - a0‖ < ‖a0‖ := by
      calc
        ‖a - a0‖ ≤ ‖a0 ^ 2 - z‖ / ‖2 * a0‖ := ha_dist
        _ < ‖2 * a0‖ ^ 2 / ‖2 * a0‖ := by
          have hpos : 0 < ‖2 * a0‖ :=
            lt_of_le_of_ne (norm_nonneg _) h_two_a0_ne_zero.symm
          exact div_lt_div_of_pos_right h_a0_sq_sub_z_norm_lt hpos
        _ = ‖2 * a0‖ := by
          field_simp [h_two_a0_ne_zero]
        _ ≤ ‖a0‖ := by
          calc
            ‖2 * a0‖ = ‖(2 : K)‖ * ‖a0‖ := norm_mul _ _
            _ = ‖π‖ ^ e * ‖a0‖ := by rw [h2]
            _ ≤ 1 * ‖a0‖ := mul_le_mul_of_nonneg_right
              (by simpa [pow_zero] using pow_le_pow_of_le_one (norm_nonneg _) hπ1.le (Nat.zero_le e))
              (norm_nonneg _)
            _ = ‖a0‖ := one_mul _
    have h_norm_pos : 0 < ‖a‖ := by
      have h_eq_norm : ‖a‖ = ‖a0‖ := by
        apply le_antisymm
        · -- ‖a‖ ≤ ‖a0‖
          calc
            ‖a‖ = ‖(a - a0) + a0‖ := by ring
            _ ≤ max ‖a - a0‖ ‖a0‖ := IsUltrametricDist.norm_add_le_max _ _
            _ = ‖a0‖ := max_eq_right (le_of_lt h_lt)
        · -- ‖a0‖ ≤ ‖a‖
          by_contra! h_lt'
          -- h_lt' : ‖a‖ < ‖a0‖
          have h_max_lt : max ‖a - a0‖ ‖a‖ < ‖a0‖ := by
            exact max_lt h_lt h_lt'
          have h_le : ‖a0‖ ≤ max ‖a - a0‖ ‖a‖ := by
            calc
              ‖a0‖ = ‖(a0 - a) + a‖ := by ring
              _ ≤ max ‖a0 - a‖ ‖a‖ := IsUltrametricDist.norm_add_le_max _ _
              _ = max ‖a - a0‖ ‖a‖ := by rw [← norm_neg, neg_sub]
          linarith
      rw [h_eq_norm]
      exact ha0_norm_pos
    exact (norm_pos_iff.mp h_norm_pos)
  refine ⟨n, a, hn_sq, ?_, hn_ne_zero, ha_ne_zero⟩
  simpa [hz_def] using ha_sq

end Hensel

/-! ## Squares up to a square factor -/

theorem isSquare_of_sq_mul {F : Type*} [Field F] {c x : F} (hc : c ≠ 0) (h : IsSquare (c ^ 2 * x)) :
    IsSquare x := by
  rcases h with ⟨s, hs⟩
  refine ⟨s / c, ?_⟩
  field_simp [hc]
  calc
    x * c ^ 2 = c ^ 2 * x := mul_comm _ _
    _ = s * s := hs
    _ = s ^ 2 := by ring

theorem isSquare_sq_mul {F : Type*} [Field F] (c : F) {x : F} (h : IsSquare x) :
    IsSquare (c ^ 2 * x) := by
  rcases h with ⟨s, hs⟩
  refine ⟨c * s, ?_⟩
  calc
    c ^ 2 * x = c ^ 2 * (s * s) := by rw [hs]
    _ = (c * s) * (c * s) := by ring

/-! ## Point data -/

/-- The coefficient `j` of `4 fRev_k` (`FE k (6 - j)` of M3a's data). -/
def gW (k : ℕ) (j : Fin 7) : KE := FE k (6 - (j : ℕ))

theorem fRev_coeff_gW (k : Fin 2) (j : Fin 7) : (fRev k).coeff j = evK (gW k j) / 4 := by
  rw [fRev, coeff_pQ, div_eq_inv_mul]
  congr 1
  fin_cases j <;> rfl

/-- A point at a w-place: `U = X² + (P/d) X + R/d`, the scaled remainder `Z1, Z0`, the Hensel
certificates of `n'` (`nj`, `nM`, `n0`, `nd`, `nR`) and of `a'` (`aj`, `aM`, `a0`, `ad`, `aR`) at
precision `prec`, and the values `Λ² U(α)` (`lamL`, `tL`) and `Λ² U(β)` (`lamN`, `tN`) at
precision `precT`. -/
structure PtData where
  P : List ℤ
  R : List ℤ
  d : ℕ
  Z1 : List ℤ
  Z0 : List ℤ
  nj : ℕ
  nM : ℕ
  n0 : List ℤ
  nd : List ℤ
  nR : List ℤ
  aj : ℕ
  aM : ℕ
  a0 : List ℤ
  ad : List ℤ
  aR : List ℤ
  prec : ℕ
  lamL : ℕ
  tL : List (List ℤ)
  lamN : ℕ
  tN : List (List ℤ)
  precT : ℕ
  deriving Inhabited

namespace PtData

variable (E : EisData) (g : Fin 7 → KE) (pt : PtData)

/-- `N' = d (d Z0² - P Z1 Z0 + R Z1²)`. -/
def Np : KE :=
  .mul (.int (pt.d : ℤ)) (.add (.sub (.mul (.int (pt.d : ℤ)) (.mul (.lin pt.Z0) (.lin pt.Z0)))
    (.mul (.lin pt.P) (.mul (.lin pt.Z1) (.lin pt.Z0)))) (.mul (.lin pt.R) (.mul (.lin pt.Z1) (.lin pt.Z1))))

/-- `2 d Z0 - P Z1`. -/
def Xa : KE := .sub (.mul (.int ((2 * pt.d : ℕ) : ℤ)) (.lin pt.Z0)) (.mul (.lin pt.P) (.lin pt.Z1))

/-- The exponent conditions. -/
def okD : Bool :=
  decide (0 < pt.d) && decide (pt.nj < E.alPow.length) && decide (pt.nM < E.alPow.length) &&
    decide (pt.aj < E.alPow.length) && decide (pt.aM < E.alPow.length) &&
    decide (2 * E.e + 2 * pt.nj < pt.nM) && decide (2 * E.e + 2 * pt.aj < pt.aM) &&
    decide (2 * E.e + 2 * pt.aj + pt.nj < pt.nM) && decide (0 < pt.lamL) && decide (0 < pt.lamN) &&
    decide (pt.lamL ^ 2 % pt.d = 0) && decide (pt.lamN ^ 2 % pt.d = 0)

/-- The six identities of the point in `K21`. -/
def okZ : Bool :=
  checkK pt.prec (.sub (.lin pt.Z1) (zsE g (.lin pt.P) (.lin pt.R) pt.d).1) &&
    checkK pt.prec (.sub (.lin pt.Z0) (zsE g (.lin pt.P) (.lin pt.R) pt.d).2) &&
    checkK pt.prec (.sub (.lin pt.n0) (.mul (.lin (E.alP pt.nj))
      (.add (.int 1) (.mul (.lin E.al) (.lin pt.nd))))) &&
    checkK pt.prec (.sub (.sub (.mul (.lin pt.n0) (.lin pt.n0)) pt.Np)
      (.mul (.lin (E.alP pt.nM)) (.lin pt.nR))) &&
    checkK pt.prec (.sub (.lin pt.a0) (.mul (.lin (E.alP pt.aj))
      (.add (.int 1) (.mul (.lin E.al) (.lin pt.ad))))) &&
    checkK pt.prec (.sub (.sub (.mul (.lin pt.a0) (.lin pt.a0)) (.add pt.Xa (.mul (.int 2) (.lin pt.n0))))
      (.mul (.lin (E.alP pt.aM)) (.lin pt.aR)))

/-- The coefficients of `Λ² U`, `Λ = lamL`, constant first. -/
def csL : List KE :=
  [.mul (.int ((pt.lamL ^ 2 / pt.d : ℕ) : ℤ)) (.lin pt.R),
    .mul (.int ((pt.lamL ^ 2 / pt.d : ℕ) : ℤ)) (.lin pt.P), .int ((pt.lamL ^ 2 : ℕ) : ℤ)]

/-- The coefficients of `Λ² U`, `Λ = lamN`, constant first. -/
def csN : List KE :=
  [.mul (.int ((pt.lamN ^ 2 / pt.d : ℕ) : ℤ)) (.lin pt.R),
    .mul (.int ((pt.lamN ^ 2 / pt.d : ℕ) : ℤ)) (.lin pt.P), .int ((pt.lamN ^ 2 : ℕ) : ℤ)]

/-- The values `Λ² U(α) = tL`, `Λ² U(β) = tN`. -/
def okT : Bool :=
  checkLC pt.precT (sumPL SUnitData.alphaDen 2 pt.csL TowerChecks.tabA)
      (smulLC (.int ((SUnitData.alphaDen ^ 2 * 1 : ℕ) : ℤ)) (ofL pt.tL)) &&
    checkNC pt.precT (sumPN SUnitData.betaPowDen 2 pt.csN TowerChecks.tabB)
      (smulNC (.int ((SUnitData.betaPowDen ^ 2 * 1 : ℕ) : ℤ)) (ofN pt.tN))

/-- `U = X² + (P/d) X + R/d` over `K21`. -/
noncomputable def U : K21[X] := quad (zkE pt.P / pt.d) (zkE pt.R / pt.d)

end PtData

/-- The coefficients `[q R, q P, Λ²]`, `q = Λ² / d`, are those of `Λ² (X² + (P/d) X + R/d)`. -/
theorem pQ_scaled (P R : List ℤ) {d lam : ℕ} (hd : d ≠ 0) (hdiv : d ∣ lam ^ 2) :
    pQ 1 [.mul (.int ((lam ^ 2 / d : ℕ) : ℤ)) (.lin R), .mul (.int ((lam ^ 2 / d : ℕ) : ℤ)) (.lin P),
      .int ((lam ^ 2 : ℕ) : ℤ)] = C ((lam : K21) ^ 2) * quad (zkE P / d) (zkE R / d) := by
  obtain ⟨q, hq⟩ := hdiv
  have hpos : 0 < d := Nat.pos_of_ne_zero hd
  have hq_div : (lam ^ 2 / d : ℕ) = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left _ hpos
  have hlam_sq_K : ((lam : K21) ^ 2) = ((d : K21) * (q : K21)) := by exact_mod_cast hq
  have hd_ne_zero_K : ((d : K21) ≠ 0) := by exact_mod_cast hd
  have hq_div_K : ((lam ^ 2 / d : ℕ) : K21) = (q : K21) := by exact_mod_cast hq_div
  -- Expand definitions: pQ 1 l = pK l, then expand pK and evK
  rw [pQ, quad]
  have h1 : C ((Nat.cast 1 : K21)⁻¹) = (1 : K21[X]) := by simp
  rw [h1, one_mul]
  have hpK : pK [.mul (.int ((lam ^ 2 / d : ℕ) : ℤ)) (.lin R),
      .mul (.int ((lam ^ 2 / d : ℕ) : ℤ)) (.lin P),
      .int ((lam ^ 2 : ℕ) : ℤ)] =
      C (((lam ^ 2 / d : ℕ) : K21) * zkE R) + X * (C (((lam ^ 2 / d : ℕ) : K21) * zkE P) + X * C (((lam ^ 2 : ℕ) : K21))) := by
    simp only [pK, evK_mul, evK_int, evK_lin, Int.cast_natCast, mul_zero, add_zero]
  rw [hpK]
  rw [hq_div_K, show ((lam ^ 2 : ℕ) : K21) = ((d : K21) * (q : K21)) by
    rw [show ((lam ^ 2 : ℕ) : K21) = ((lam : K21) ^ 2) by simp, hlam_sq_K]]
  rw [show (↑lam ^ 2 : K21) = ((d : K21) * (q : K21)) from by simpa using hlam_sq_K]
  -- Goal: C ((q : K21) * zkE R) + X * (C ((q : K21) * zkE P) + X * C ((d : K21) * (q : K21))) =
  --   C ((d : K21) * (q : K21)) * (X ^ 2 + C (zkE P / (d : K21)) * X + C (zkE R / (d : K21)))
  have hcoeff1 : C ((d : K21) * (q : K21)) * C (zkE P / (d : K21)) = C ((q : K21) * zkE P) := by
    rw [← C_mul]
    field_simp [hd_ne_zero_K]
  have hcoeff2 : C ((d : K21) * (q : K21)) * C (zkE R / (d : K21)) = C ((q : K21) * zkE R) := by
    rw [← C_mul]
    field_simp [hd_ne_zero_K]
  calc
    C ((q : K21) * zkE R) + X * (C ((q : K21) * zkE P) + X * C ((d : K21) * (q : K21)))
        = C ((q : K21) * zkE R) + C ((q : K21) * zkE P) * X + C ((d : K21) * (q : K21)) * X ^ 2 := by ring
    _ = C ((d : K21) * (q : K21)) * X ^ 2 + C ((q : K21) * zkE P) * X + C ((q : K21) * zkE R) := by ring
    _ = C ((d : K21) * (q : K21)) * X ^ 2 +
        (C ((d : K21) * (q : K21)) * C (zkE P / (d : K21))) * X +
        (C ((d : K21) * (q : K21)) * C (zkE R / (d : K21))) := by rw [hcoeff1, hcoeff2]
    _ = C ((d : K21) * (q : K21)) * (X ^ 2 + C (zkE P / (d : K21)) * X + C (zkE R / (d : K21))) := by ring

theorem PtData.pQ_csL {pt : PtData} (hd : pt.d ≠ 0) (hdiv : pt.d ∣ pt.lamL ^ 2) :
    pQ 1 pt.csL = C ((pt.lamL : K21) ^ 2) * pt.U :=
  pQ_scaled pt.P pt.R hd hdiv

theorem PtData.pQ_csN {pt : PtData} (hd : pt.d ≠ 0) (hdiv : pt.d ∣ pt.lamN ^ 2) :
    pQ 1 pt.csN = C ((pt.lamN : K21) ^ 2) * pt.U :=
  pQ_scaled pt.P pt.R hd hdiv

/-- `Λ² U(α) = tL`. -/
theorem PtData.aeval_alphaR_U (E : EisData) {pt : PtData} (hD : pt.okD E = true)
    (hT : pt.okT = true) : (pt.lamL : L42) ^ 2 * aeval alphaR pt.U = mkL pt.tL := by
  simp only [PtData.okD, PtData.okT, Bool.and_eq_true, decide_eq_true_eq] at hD hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hmL⟩, -⟩ := hD
  have h := aeval_pQ_of_checkL TowerFacts.alphaDen_ne_zero one_ne_zero (n := 2)
    (by simp [PtData.csL]) (by simp [PtData.csL, TowerChecks.tabA])
    (fun i hi => TowerFacts.tabA_spec i (by simp [PtData.csL] at hi; omega)) hT.1
  rw [PtData.pQ_csL (by omega) (Nat.dvd_of_mod_eq_zero hmL), map_mul, aeval_C, map_pow,
    map_natCast] at h
  rw [mkL_eq_evL]
  exact h

/-- `Λ² U(β) = tN`. -/
theorem PtData.aeval_betaR_U (E : EisData) {pt : PtData} (hD : pt.okD E = true)
    (hT : pt.okT = true) : (pt.lamN : N84) ^ 2 * aeval betaR pt.U = mkN pt.tN := by
  simp only [PtData.okD, PtData.okT, Bool.and_eq_true, decide_eq_true_eq] at hD hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd0, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hmN⟩ := hD
  have h := aeval_pQ_of_checkN TowerFacts.betaPowDen_ne_zero one_ne_zero (n := 2)
    (by simp [PtData.csN]) (by simp [PtData.csN, TowerChecks.tabB])
    (fun i hi => TowerFacts.tabB_spec i (by simp [PtData.csN] at hi; omega)) hT.2
  rw [PtData.pQ_csN (by omega) (Nat.dvd_of_mod_eq_zero hmN), map_mul, aeval_C, map_pow,
    map_natCast] at h
  rw [mkN_eq_evN]
  exact h

/-! ## The point in `Jac` -/

section Point

variable {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw]
  [CharZero Kw] {σ : K21 →+* Kw} {E : EisData}

/-- **The point of a `PtData`.** At a place `σ` (`WPlace`), passing `okD` and `okZ` give a point
`D` of `Jac ((fRev k)^σ)` with `μ(D) = [U(T)]`. -/
theorem PtData.exists_point (hW : WPlace σ E) (k : Fin 2) [GoodSextic ((fRev k).map σ)]
    {pt : PtData} (hD : pt.okD E = true) (hZ : pt.okZ E (gW k) = true) :
    ∃ (D : Jac ((fRev k).map σ))
      (hu : IsUnit (AdjoinRoot.mk ((fRev k).map σ) (pt.U.map σ))),
      muJ ((fRev k).map σ) D = (QuotientGroup.mk hu.unit : H ((fRev k).map σ)) := by
  simp only [PtData.okD, PtData.okZ, Bool.and_eq_true, decide_eq_true_eq] at hD hZ
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd0, hnj⟩, hnM⟩, haj⟩, haM⟩, hM⟩, hMa⟩, hMa'⟩, -⟩, -⟩, -⟩, -⟩ := hD
  obtain ⟨⟨⟨⟨⟨hZ1, hZ0⟩, hn0⟩, hnc⟩, ha0⟩, hac⟩ := hZ
  set f := (fRev k).map σ with hfdef
  set π := σ (zkE E.al) with hπ
  have hint := norm_evK_le_one σ hW.int
  have hπ0 : π ≠ 0 := hW.unif.ne_zero
  have hπ1 : ‖π‖ < 1 := hW.unif.norm_lt_one
  have h2 : (2 : Kw) ≠ 0 := two_ne_zero
  have hd : ((pt.d : ℕ) : Kw) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the coefficients of `f`
  set g : Fin 7 → Kw := fun j => σ (evK (gW k j)) with hg
  have hgf : ∀ j : Fin 7, f.coeff j = g j / 4 := by
    intro j
    rw [hfdef, coeff_map, fRev_coeff_gW, map_div₀, map_ofNat]
  have hf6 : f.natDegree ≤ 6 := (GoodSextic.natDegree_eq (f := f)).le
  -- the scaled remainder
  set P' := σ (zkE pt.P)
  set Q' := σ (zkE pt.R)
  have hzs : zsF g P' Q' pt.d = (σ (zkE pt.Z1), σ (zkE pt.Z0)) := by
    have e := map_zsF σ (fun j => evK (gW k j)) (zkE pt.P) (zkE pt.R) pt.d
    have e2 := evK_zsE (gW k) (.lin pt.P) (.lin pt.R) pt.d
    simp only [evK_lin] at e2
    rw [← e2] at e
    rw [e, ← evK_eq_of_check _ _ _ hZ1, ← evK_eq_of_check _ _ _ hZ0]
    rfl
  -- the two square roots
  have e_n0 := evK_eq_of_check _ _ _ hn0
  have e_nc := evK_eq_of_check _ _ _ hnc
  have e_a0 := evK_eq_of_check _ _ _ ha0
  have e_ac := evK_eq_of_check _ _ _ hac
  simp only [evK_lin, evK_mul, evK_add, evK_sub, evK_int, Int.cast_one, Int.cast_ofNat] at e_n0 e_nc e_a0 e_ac
  rw [EisData.ok_alP hW.ok _ hnj] at e_n0
  rw [EisData.ok_alP hW.ok _ hnM] at e_nc
  rw [EisData.ok_alP hW.ok _ haj] at e_a0
  rw [EisData.ok_alP hW.ok _ haM] at e_ac
  have hc : (π ^ pt.nj * (1 + π * σ (zkE pt.nd))) ^ 2 - σ (evK pt.Np) =
      π ^ pt.nM * σ (zkE pt.nR) := by
    have := congrArg σ e_nc
    rw [e_n0] at this
    simp only [map_sub, map_mul, map_pow, map_add, map_one] at this ⊢
    linear_combination this
  have hca : (π ^ pt.aj * (1 + π * σ (zkE pt.ad))) ^ 2 -
      (σ (evK pt.Xa) + 2 * (π ^ pt.nj * (1 + π * σ (zkE pt.nd)))) =
      π ^ pt.aM * σ (zkE pt.aR) := by
    have := congrArg σ e_ac
    rw [e_a0, e_n0] at this
    simp only [map_sub, map_mul, map_pow, map_add, map_one, map_ofNat] at this ⊢
    linear_combination this
  obtain ⟨n, a, hn, ha, hnz, haz⟩ := exists_pair_of_certs hπ0 hπ1 hW.two (hint _) (hint _)
    (hW.int _) (hW.int _) (hW.int _) (hW.int _) hM hMa hMa' hc hca
  have hNp : σ (evK pt.Np) = (pt.d : Kw) * ((pt.d : Kw) * (zsF g P' Q' pt.d).2 ^ 2 -
      P' * (zsF g P' Q' pt.d).1 * (zsF g P' Q' pt.d).2 + Q' * (zsF g P' Q' pt.d).1 ^ 2) := by
    rw [hzs]
    simp only [PtData.Np, evK_mul, evK_add, evK_sub, evK_int, evK_lin, map_mul, map_add, map_sub,
      map_intCast, Int.cast_natCast, map_natCast]
    ring
  have hXa : σ (evK pt.Xa) = 2 * (pt.d : Kw) * (zsF g P' Q' pt.d).2 - P' * (zsF g P' Q' pt.d).1 := by
    rw [hzs]
    simp only [PtData.Xa, evK_mul, evK_sub, evK_int, evK_lin, map_mul, map_sub, map_intCast,
      Int.cast_natCast, map_natCast]
    push_cast
    ring
  obtain ⟨V, W, hw, hcop⟩ := mumford_of_scaled h2 hf6 g hgf P' Q' hd (n := n) (a := a)
    (by rw [hn, hNp]) (by rw [ha, hXa]) hnz haz
  have hU : pt.U.map σ = quad (P' / pt.d) (Q' / pt.d) := by
    rw [PtData.U, quad_map, map_div₀, map_div₀, map_natCast]
  suffices ∀ u : Kw[X], u = quad (P' / pt.d) (Q' / pt.d) → ∃ (D : Jac f)
      (hu : IsUnit (AdjoinRoot.mk f u)), muJ f D = (QuotientGroup.mk hu.unit : H f) from
    this _ hU
  rintro u rfl
  exact ⟨_, _, muJ_mumfordJac f (quad_monic _ _) (quad_even _ _) hw
    (exists_coprime_of_squarefree GoodSextic.squarefree hw) hcop⟩

end Point

end FurioLombardo.Discharge.SelmerBasis
