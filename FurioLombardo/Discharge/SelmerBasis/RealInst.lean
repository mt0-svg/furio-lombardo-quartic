import FurioLombardo.Discharge.SelmerBasis.RealRoots
import FurioLombardo.Discharge.M3b.Signs

/-!
# Root order at the real places 5 and 6 (`realEmb 0`, `realEmb 1`) of twist 0

From the kernel identities and sign certificates of `RealRoots.lean`:

* `eval_q`, `eval_h_factor`: `q 0` at `σ = realEmb j` is a monic real quadratic, and `h 0` is the
  product `gR · gP` of two monic real quadratics, with `gP > 0` everywhere at places 5, 6;
* `place_ex`: the four real roots `r 0 < r 1 < r 2 < r 3` of `(fRev 0)^σ`, with `r i` between the
  separators `i` and `i + 1`, the roots of `q^σ` at positions `(0, 2)` at place 5 and `(1, 3)` at
  place 6, those of `h^σ` at the other two;
* `roots`, `roots_mono`, `roots_isRoot`, `roots_all`, and `imageIn_place`: `ImageIn` at both places.
-/

namespace FurioLombardo.Discharge.SelmerBasis.RealRoots

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3b
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin
  FurioLombardo.Discharge.SelmerBasis.RealRootData FurioLombardo.M3a.Genus2
  FurioLombardo.Discharge.SelmerSpan

/-! ## Real algebra on variables -/

theorem h_factor {H0 H1 H2 H3 P0 P1 R0 R1 u : ℝ}
    (e3 : 92 * H3 = 2 * 46 * P0)
    (e2 : 92 * 92 * H2 = 46 * (2 * 92 * R0 + (P0 * P0 - u * u * (P1 * P1))))
    (e1 : 92 * 92 * H1 = 46 * (2 * (P0 * R0) - 2 * (u * u * (P1 * R1))))
    (e0 : 92 * 92 * H0 = 46 * (R0 * R0 - u * u * (R1 * R1))) (x : ℝ) :
    x ^ 4 + H3 / 46 * x ^ 3 + H2 / 46 * x ^ 2 + H1 / 46 * x + H0 / 46 =
      (x ^ 2 + (P0 + u * P1) / 92 * x + (R0 + u * R1) / 92) *
      (x ^ 2 + (P0 - u * P1) / 92 * x + (R0 - u * R1) / 92) := by
  linear_combination (x ^ 3 / (46 * 92)) * e3 + (x ^ 2 / (46 * 92 * 92)) * e2 +
    (x / (46 * 92 * 92)) * e1 + (1 / (46 * 92 * 92)) * e0

theorem gP_pos {P0 P1 R0 R1 u Bv Nv : ℝ}
    (hB : Bv = 2 * (P0 * P1) - 4 * 92 * R1)
    (hN : Nv = (P0 * P0 + u * u * (P1 * P1) - 4 * 92 * R0) * (P0 * P0 + u * u * (P1 * P1) - 4 * 92 * R0)
      - u * u * (Bv * Bv))
    (huB : 0 < u * Bv) (hNn : Nv < 0) (x : ℝ) :
    0 < x ^ 2 + (P0 - u * P1) / 92 * x + (R0 - u * R1) / 92 := by
  apply quad_pos
  set A := P0 * P0 + u * u * (P1 * P1) - 4 * 92 * R0 with hA
  have hAB : A - u * Bv < 0 := by
    by_contra hc
    push Not at hc
    have h2 : 0 ≤ (A - u * Bv) * (A + u * Bv) := mul_nonneg hc (by linarith)
    have h3 : (A - u * Bv) * (A + u * Bv) = Nv := by rw [hN]; ring
    linarith
  have h4 : ((P0 - u * P1) / 92) ^ 2 - 4 * ((R0 - u * R1) / 92) = (A - u * Bv) / (92 * 92) := by
    rw [hA, hB]; ring
  rw [h4]
  exact div_neg_of_neg_of_pos hAB (by norm_num)

theorem sep_q {n d Q0 Q1 V s : ℝ} (hd : 0 < d) (hV : V = d * d * Q0 + n * d * Q1 + 46 * n * n)
    (hs : 0 < s * V) : 0 < s * ((n / d) ^ 2 + Q1 / 46 * (n / d) + Q0 / 46) := by
  have e : (n / d) ^ 2 + Q1 / 46 * (n / d) + Q0 / 46 = V / (46 * d * d) := by
    rw [hV]; field_simp; ring
  rw [e, mul_div_assoc']
  exact div_pos hs (by positivity)

theorem sep_h {n d H0 H1 H2 H3 V s : ℝ} (hd : 0 < d)
    (hV : V = d ^ 4 * H0 + n * d ^ 3 * H1 + n ^ 2 * d ^ 2 * H2 + n ^ 3 * d * H3 + 46 * n ^ 4)
    (hs : 0 < s * V) :
    0 < s * ((n / d) ^ 4 + H3 / 46 * (n / d) ^ 3 + H2 / 46 * (n / d) ^ 2 + H1 / 46 * (n / d) +
      H0 / 46) := by
  have e : (n / d) ^ 4 + H3 / 46 * (n / d) ^ 3 + H2 / 46 * (n / d) ^ 2 + H1 / 46 * (n / d) +
      H0 / 46 = V / (46 * d ^ 4) := by
    rw [hV]; field_simp; ring
  rw [e, mul_div_assoc']
  exact div_pos hs (by positivity)

/-! ## Evaluation at a real embedding -/

theorem qDen0 : qDenN 0 = 46 := rfl
theorem hDen0 : hDenN 0 = 46 := rfl
theorem rhDen_val : rhDen = 92 := rfl

theorem eval_q (j : Fin 3) (x : ℝ) : (q 0).eval₂ (realEmb j) x =
    x ^ 2 + realEmb j (evK (qE 0 1)) / 46 * x + realEmb j (evK (qE 0 0)) / 46 := by
  show (pQ (qDenN 0) (qL 0)).eval₂ (realEmb j) x = _
  simp only [pQ, qL, pK_cons, pK_nil, eval₂_mul, eval₂_C, eval₂_add, eval₂_X,
    mul_zero, add_zero, qDen0, evK_int, map_inv₀, map_natCast, map_intCast]
  push_cast
  simp only [eval₂_ofNat]
  field_simp
  ring

theorem eval_h (j : Fin 3) (x : ℝ) : (h 0).eval₂ (realEmb j) x =
    x ^ 4 + realEmb j (evK (hE 0 3)) / 46 * x ^ 3 + realEmb j (evK (hE 0 2)) / 46 * x ^ 2 +
      realEmb j (evK (hE 0 1)) / 46 * x + realEmb j (evK (hE 0 0)) / 46 := by
  show (pQ (hDenN 0) (hL 0)).eval₂ (realEmb j) x = _
  simp only [pQ, hL, pK_cons, pK_nil, eval₂_mul, eval₂_C, eval₂_add, eval₂_X,
    mul_zero, add_zero, hDen0, evK_int, map_inv₀, map_natCast, map_intCast]
  push_cast
  simp only [eval₂_ofNat]
  field_simp
  ring

/-! ## Real identities at `σ = realEmb j` -/

section Emb

variable (j : Fin 3)

noncomputable def Qr (i : ℕ) : ℝ := realEmb j (evK (qE 0 i))
noncomputable def Hr (i : ℕ) : ℝ := realEmb j (evK (hE 0 i))
noncomputable def P0r : ℝ := realEmb j (zkE rhP0)
noncomputable def P1r : ℝ := realEmb j (zkE rhP1)
noncomputable def R0r : ℝ := realEmb j (zkE rhR0)
noncomputable def R1r : ℝ := realEmb j (zkE rhR1)
noncomputable def er : ℝ := realEmb j epsK
noncomputable def Bv : ℝ := realEmb j (zkE rhD1)
noncomputable def Nv : ℝ := realEmb j (zkE rhN)

theorem re3 : 92 * Hr j 3 = 2 * 46 * P0r j := by
  have e := congrArg (realEmb j) (evK_eq_of_check _ _ _ ck_h3)
  simp only [evK_mul, evK_int, P0E, evK_lin, map_mul, map_intCast, rhDen_val, hDen0] at e
  push_cast at e
  unfold Hr P0r
  linear_combination e

theorem re2 : 92 * 92 * Hr j 2 = 46 * (2 * 92 * R0r j + (P0r j * P0r j - er j * (P1r j * P1r j))) := by
  have e := congrArg (realEmb j) (evK_eq_of_check _ _ _ ck_h2)
  simp only [evK_mul, evK_int, evK_add, evK_sub, P0E, P1E, R0E, epsE, evK_lin, map_mul, map_add,
    map_sub, map_intCast, rhDen_val, hDen0] at e
  push_cast at e
  unfold Hr P0r P1r R0r er
  rw [epsK_eq]
  linear_combination e

theorem re1 : 92 * 92 * Hr j 1 = 46 * (2 * (P0r j * R0r j) - 2 * (er j * (P1r j * R1r j))) := by
  have e := congrArg (realEmb j) (evK_eq_of_check _ _ _ ck_h1)
  simp only [evK_mul, evK_int, evK_sub, P0E, P1E, R0E, R1E, epsE, evK_lin, map_mul,
    map_sub, map_intCast, rhDen_val, hDen0] at e
  push_cast at e
  unfold Hr P0r P1r R0r R1r er
  rw [epsK_eq]
  linear_combination e

theorem re0 : 92 * 92 * Hr j 0 = 46 * (R0r j * R0r j - er j * (R1r j * R1r j)) := by
  have e := congrArg (realEmb j) (evK_eq_of_check _ _ _ ck_h0)
  simp only [evK_mul, evK_int, evK_sub, R0E, R1E, epsE, evK_lin, map_mul,
    map_sub, map_intCast, rhDen_val, hDen0] at e
  push_cast at e
  unfold Hr R0r R1r er
  rw [epsK_eq]
  linear_combination e

theorem reB : Bv j = 2 * (P0r j * P1r j) - 4 * 92 * R1r j := by
  have e := congrArg (realEmb j) (evK_eq_of_check _ _ _ ck_D1)
  simp only [BE, evK_mul, evK_int, evK_sub, P0E, P1E, R1E, evK_lin, map_mul,
    map_sub, map_intCast, rhDen_val] at e
  push_cast at e
  unfold Bv P0r P1r R1r
  linear_combination e

theorem reN : Nv j = (P0r j * P0r j + er j * (P1r j * P1r j) - 4 * 92 * R0r j) *
    (P0r j * P0r j + er j * (P1r j * P1r j) - 4 * 92 * R0r j) - er j * (Bv j * Bv j) := by
  have e := congrArg (realEmb j) (evK_eq_of_check _ _ _ ck_N)
  simp only [AE, BE, evK_mul, evK_int, evK_add, evK_sub, P0E, P1E, R0E, R1E, epsE, evK_lin,
    map_mul, map_add, map_sub, map_intCast, rhDen_val] at e
  push_cast at e
  rw [reB]
  unfold Nv P0r P1r R0r R1r er
  rw [epsK_eq]
  linear_combination e

end Emb

/-! ## The factors at places 5 and 6 -/

section Place

variable (k : Fin 2)

/-- `ς √σ(ε)`, with `ς = sign σ(Δ₁)`. -/
noncomputable def tu : ℝ := (sgnB k : ℝ) * sqrtEps (Fin.castSucc k)

theorem tu_mul : tu k * tu k = er (Fin.castSucc k) := by
  have h1 : (sgnB k : ℝ) * sgnB k = 1 := by fin_cases k <;> norm_num [sgnB]
  unfold tu er
  rw [← sqrtEps_mul]
  linear_combination (sqrtEps (Fin.castSucc k) * sqrtEps (Fin.castSucc k)) * h1

theorem tuB_pos : 0 < tu k * Bv (Fin.castSucc k) := by
  have h1 := elemAt_sign (ck_sgnB k)
  have h2 : 0 < sqrtEps (Fin.castSucc k) := Real.sqrt_pos.mpr (realEmb_epsK_pos _)
  unfold tu Bv
  calc (0 : ℝ) < sqrtEps (Fin.castSucc k) * ((sgnB k : ℝ) * realEmb (Fin.castSucc k) (zkE rhD1)) :=
        mul_pos h2 h1
    _ = _ := by ring

/-- The monic quadratic `q^σ = X² + qb X + qc`. -/
noncomputable def qb : ℝ := Qr (Fin.castSucc k) 1 / 46
noncomputable def qc : ℝ := Qr (Fin.castSucc k) 0 / 46
/-- The real-rooted factor `gR = X² + gRb X + gRc` of `h^σ`. -/
noncomputable def gRb : ℝ := (P0r (Fin.castSucc k) + tu k * P1r (Fin.castSucc k)) / 92
noncomputable def gRc : ℝ := (R0r (Fin.castSucc k) + tu k * R1r (Fin.castSucc k)) / 92
/-- The positive factor `gP` of `h^σ`. -/
noncomputable def gP (x : ℝ) : ℝ :=
  x ^ 2 + (P0r (Fin.castSucc k) - tu k * P1r (Fin.castSucc k)) / 92 * x +
    (R0r (Fin.castSucc k) - tu k * R1r (Fin.castSucc k)) / 92

theorem eval_q' (x : ℝ) : (q 0).eval₂ (realEmb (Fin.castSucc k)) x = x ^ 2 + qb k * x + qc k := by
  rw [eval_q]; rfl

theorem eval_h_factor (x : ℝ) :
    (h 0).eval₂ (realEmb (Fin.castSucc k)) x = (x ^ 2 + gRb k * x + gRc k) * gP k x := by
  rw [eval_h]
  have e2 := re2 (Fin.castSucc k)
  have e1 := re1 (Fin.castSucc k)
  have e0 := re0 (Fin.castSucc k)
  rw [← tu_mul k] at e2 e1 e0
  exact h_factor (re3 _) e2 e1 e0 x

theorem gP_pos' (x : ℝ) : 0 < gP k x := by
  have hN := reN (Fin.castSucc k)
  rw [← tu_mul k] at hN
  exact gP_pos (reB _) hN (tuB_pos k) (neg_of_cert (ck_sgnN k)) x

/-- The separator `n / d`. -/
noncomputable def sepR (i : ℕ) : ℝ := (sn k i : ℝ) / (sd k i : ℝ)

theorem sgn_q_sep (i : ℕ) (hi : i < 5) :
    0 < (sgnQ k ⟨i, hi⟩ : ℝ) * (sepR k i ^ 2 + qb k * sepR k i + qc k) := by
  have hc := congrArg (realEmb (Fin.castSucc k)) (evK_eq_of_check _ _ _ (ck_sepQ k ⟨i, hi⟩))
  simp only [qsE, evK_add, evK_mul, evK_int, evK_lin, map_add, map_mul, map_intCast, qDen0] at hc
  push_cast at hc
  exact sep_q (by exact_mod_cast sd_pos k ⟨i, hi⟩) (by rw [← hc]; unfold Qr; ring)
    (elemAt_sign (ck_sgnQ k ⟨i, hi⟩))

theorem sgn_g_sep (i : ℕ) (hi : i < 5) :
    0 < (sgnH k ⟨i, hi⟩ : ℝ) * (sepR k i ^ 2 + gRb k * sepR k i + gRc k) := by
  have hc := congrArg (realEmb (Fin.castSucc k)) (evK_eq_of_check _ _ _ (ck_sepH k ⟨i, hi⟩))
  simp only [hsE, evK_add, evK_mul, evK_int, evK_lin, map_add, map_mul, map_intCast, hDen0] at hc
  push_cast at hc
  have h1 : 0 < (sgnH k ⟨i, hi⟩ : ℝ) * (h 0).eval₂ (realEmb (Fin.castSucc k)) (sepR k i) := by
    rw [eval_h]
    exact sep_h (by exact_mod_cast sd_pos k ⟨i, hi⟩) (by rw [← hc])
      (elemAt_sign (ck_sgnH k ⟨i, hi⟩))
  rw [eval_h_factor, ← mul_assoc] at h1
  exact (mul_pos_iff_of_pos_right (gP_pos' k _)).mp h1

end Place

/-! ## The four roots -/

theorem pos_of_sgn {s : ℤ} {v : ℝ} (h : 0 < (s : ℝ) * v) (hs : s = 1) : 0 < v := by
  rw [hs, Int.cast_one, one_mul] at h; exact h

theorem neg_of_sgn {s : ℤ} {v : ℝ} (h : 0 < (s : ℝ) * v) (hs : s = -1) : v < 0 := by
  rw [hs] at h; push_cast at h; linarith

/-- Positions of the roots of `q^σ` (row `k` = place `k + 5`). -/
def qIdx : Fin 2 → Fin 2 → Fin 4 := ![![0, 2], ![1, 3]]
/-- Positions of the real roots of `h^σ`. -/
def hIdx : Fin 2 → Fin 2 → Fin 4 := ![![1, 3], ![0, 2]]

/-- The root layout at place `k + 5`: increasing, `r i` between the separators `i` and `i + 1`,
the roots of `q^σ` at `qIdx k`, the real roots of `h^σ` at `hIdx k`. -/
def RootsSpec (k : Fin 2) (r : Fin 4 → ℝ) : Prop :=
  StrictMono r ∧ (∀ i : Fin 4, sepR k i < r i ∧ r i < sepR k (i.val + 1)) ∧
    (∀ x, (q 0).eval₂ (realEmb (Fin.castSucc k)) x = 0 ↔ x = r (qIdx k 0) ∨ x = r (qIdx k 1)) ∧
    (∀ x, (h 0).eval₂ (realEmb (Fin.castSucc k)) x = 0 ↔ x = r (hIdx k 0) ∨ x = r (hIdx k 1))

theorem mono4 {r : Fin 4 → ℝ} (h01 : r 0 < r 1) (h12 : r 1 < r 2) (h23 : r 2 < r 3) :
    StrictMono r := by
  refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
  fin_cases i
  · exact h01
  · exact h12
  · exact h23

theorem h_zero_iff (k : Fin 2) {y1 y2 : ℝ}
    (hg : ∀ x, x ^ 2 + gRb k * x + gRc k = (x - y1) * (x - y2)) (x : ℝ) :
    (h 0).eval₂ (realEmb (Fin.castSucc k)) x = 0 ↔ x = y1 ∨ x = y2 := by
  rw [eval_h_factor, hg, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have := (gP_pos' k x).ne'
  tauto

theorem q_zero_iff (k : Fin 2) {x1 x2 : ℝ}
    (hq : ∀ x, x ^ 2 + qb k * x + qc k = (x - x1) * (x - x2)) (x : ℝ) :
    (q 0).eval₂ (realEmb (Fin.castSucc k)) x = 0 ↔ x = x1 ∨ x = x2 := by
  rw [eval_q', hq, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem place5 : ∃ r, RootsSpec 0 r := by
  have s0 : sepR 0 0 = -5 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s1 : sepR 0 1 = 0 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s2 : sepR 0 2 = 1 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s3 : sepR 0 3 = 6 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s4 : sepR 0 4 = 178 := by norm_num [sepR, sn, sd, sepN, sepD]
  obtain ⟨x1, x2, y1, y2, c1, c2, c3, c4, c5, c6, c7, c8, hq, hg⟩ :=
    interlace (by rw [s0, s1]; norm_num) (by rw [s1, s2]; norm_num) (by rw [s2, s3]; norm_num)
      (by rw [s3, s4]; norm_num)
      (pos_of_sgn (sgn_q_sep 0 0 (by norm_num)) rfl) (neg_of_sgn (sgn_q_sep 0 1 (by norm_num)) rfl)
      (neg_of_sgn (sgn_q_sep 0 2 (by norm_num)) rfl) (pos_of_sgn (sgn_q_sep 0 3 (by norm_num)) rfl)
      (pos_of_sgn (sgn_g_sep 0 1 (by norm_num)) rfl) (neg_of_sgn (sgn_g_sep 0 2 (by norm_num)) rfl)
      (neg_of_sgn (sgn_g_sep 0 3 (by norm_num)) rfl) (pos_of_sgn (sgn_g_sep 0 4 (by norm_num)) rfl)
  refine ⟨![x1, y1, x2, y2], mono4 (by simpa using c2.trans c3) (by simpa using c4.trans c5)
    (by simpa using c6.trans c7), ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨c1, c2⟩
    · exact ⟨c3, c4⟩
    · exact ⟨c5, c6⟩
    · exact ⟨c7, c8⟩
  · exact q_zero_iff 0 hq
  · exact h_zero_iff 0 hg

theorem place6 : ∃ r, RootsSpec 1 r := by
  have s0 : sepR 1 0 = -1 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s1 : sepR 1 1 = 0 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s2 : sepR 1 2 = 1 / 10 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s3 : sepR 1 3 = 1 := by norm_num [sepR, sn, sd, sepN, sepD]
  have s4 : sepR 1 4 = 2 := by norm_num [sepR, sn, sd, sepN, sepD]
  obtain ⟨x1, x2, y1, y2, c1, c2, c3, c4, c5, c6, c7, c8, hg, hq⟩ :=
    interlace (by rw [s0, s1]; norm_num) (by rw [s1, s2]; norm_num) (by rw [s2, s3]; norm_num)
      (by rw [s3, s4]; norm_num)
      (pos_of_sgn (sgn_g_sep 1 0 (by norm_num)) rfl) (neg_of_sgn (sgn_g_sep 1 1 (by norm_num)) rfl)
      (neg_of_sgn (sgn_g_sep 1 2 (by norm_num)) rfl) (pos_of_sgn (sgn_g_sep 1 3 (by norm_num)) rfl)
      (pos_of_sgn (sgn_q_sep 1 1 (by norm_num)) rfl) (neg_of_sgn (sgn_q_sep 1 2 (by norm_num)) rfl)
      (neg_of_sgn (sgn_q_sep 1 3 (by norm_num)) rfl) (pos_of_sgn (sgn_q_sep 1 4 (by norm_num)) rfl)
  refine ⟨![x1, y1, x2, y2], mono4 (by simpa using c2.trans c3) (by simpa using c4.trans c5)
    (by simpa using c6.trans c7), ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨c1, c2⟩
    · exact ⟨c3, c4⟩
    · exact ⟨c5, c6⟩
    · exact ⟨c7, c8⟩
  · exact q_zero_iff 1 hq
  · exact h_zero_iff 1 hg

theorem place_ex (k : Fin 2) : ∃ r, RootsSpec k r := by
  fin_cases k
  · exact place5
  · exact place6

/-! ## `ImageIn` at places 5 and 6 -/

/-- The four real roots of `(fRev 0)^σ` at place `k + 5`, `σ = realEmb k`. -/
noncomputable def roots (k : Fin 2) : Fin 4 → ℝ := Classical.choose (place_ex k)

theorem roots_spec (k : Fin 2) : RootsSpec k (roots k) := Classical.choose_spec (place_ex k)

theorem roots_mono (k : Fin 2) : StrictMono (roots k) := (roots_spec k).1

theorem eval_fRev0 (j : Fin 3) (x : ℝ) : ((fRev 0).map (realEmb j)).eval x =
    realEmb j (c 0) * ((q 0).eval₂ (realEmb j) x * (h 0).eval₂ (realEmb j) x) := by
  rw [eval_map, fRev_eq_mul, eval₂_mul, eval₂_mul, eval₂_C]; ring

theorem idx_cover (k : Fin 2) (i : Fin 4) :
    i = qIdx k 0 ∨ i = qIdx k 1 ∨ i = hIdx k 0 ∨ i = hIdx k 1 := by
  fin_cases k <;> fin_cases i <;> decide

theorem roots_isRoot (k : Fin 2) (i : Fin 4) :
    ((fRev 0).map (realEmb (Fin.castSucc k))).IsRoot (roots k i) := by
  obtain ⟨-, -, hq, hh⟩ := roots_spec k
  rw [IsRoot.def, eval_fRev0]
  rcases idx_cover k i with rfl | rfl | rfl | rfl
  · rw [(hq _).2 (Or.inl rfl)]; ring
  · rw [(hq _).2 (Or.inr rfl)]; ring
  · rw [(hh _).2 (Or.inl rfl)]; ring
  · rw [(hh _).2 (Or.inr rfl)]; ring

theorem roots_all (k : Fin 2) (x : ℝ) (hx : ((fRev 0).map (realEmb (Fin.castSucc k))).IsRoot x) :
    ∃ i, x = roots k i := by
  obtain ⟨-, -, hq, hh⟩ := roots_spec k
  rw [IsRoot.def, eval_fRev0] at hx
  have hc : realEmb (Fin.castSucc k) (c 0) ≠ 0 := by
    have := realEmb_lc_neg 0 (Fin.castSucc k)
    rw [fRev_leadingCoeff] at this
    exact this.ne
  rcases mul_eq_zero.mp hx with h0 | h0
  · exact absurd h0 hc
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rcases (hq x).1 h1 with e | e
    · exact ⟨_, e⟩
    · exact ⟨_, e⟩
  · rcases (hh x).1 h1 with e | e
    · exact ⟨_, e⟩
    · exact ⟨_, e⟩

instance goodSextic_place (k : Fin 2) : GoodSextic ((fRev 0).map (realEmb (Fin.castSucc k))) :=
  goodSextic_real 0 _

/-- The image subgroup at place `k + 5`. -/
noncomputable def Wplace (k : Fin 2) : Subgroup (H ((fRev 0).map (realEmb (Fin.castSucc k)))) :=
  Wr _ (roots k) (roots_isRoot k)

theorem imageIn_place (k : Fin 2) :
    ImageIn ((fRev 0).map (realEmb (Fin.castSucc k))) (Wplace k) :=
  imageIn_real _ (roots k) (roots_mono k) (roots_isRoot k) (roots_all k)

end FurioLombardo.Discharge.SelmerBasis.RealRoots
