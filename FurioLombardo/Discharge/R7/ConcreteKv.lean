import Mathlib
import FurioLombardo.Discharge.R7.ChartKv
import FurioLombardo.Discharge.R7.ConcreteBase
import FurioLombardo.Discharge.M3a.LocalLead
import FurioLombardo.Discharge.M3a.LocalRes

/-!
# Base points over `Kv` for the twists `k = 0, 1`, and `LogChartFin` (item R7, `Concrete`)

For `k : Fin 2`, `F_k = (fRev k).map σ` is lane M3a's reversed Prym sextic over `Kv`, and
`f_k = F_k(X + a_k)` its translate by the base abscissa `a_k = k` (`fK`), so that
`f_k(X - a_k) = F_k` (`hF`). The base point is `P0 = (a_k, b_k)` with `b_k² = f_k(0)`:

* `goodSextic_fK`: `f_k` is a `GoodSextic` (separable, degree 6, leading coefficient that of `F_k`,
  a non-square by `lead_Kv`);
* `approx_g`: the residues modulo `2^16` of `g_j = 4 · coeff_j f_k`, from the residues of the
  `σ`-images of the zk coordinate lists of `4 fRev k` (`approx_σ_zkE`, one kernel check
  `tGL_ok`) and the binomial formula for the coefficients of `F(X + a)` (`coeff_comp_X_add_C`);
* `exists_b`: `b_k` by Hensel's lemma for `X² - g_0` (`exists_sqrt`) at the certificates
  `bT k` (`(bT k)² ≡ g_0` modulo `2^6`, and the root `y` satisfies `y ≡ bT k` modulo `2^3`), then
  `b_k = y / 2`, which keeps `2 b_k ≡ bT k` modulo `2^3` (`bK_approx`): this fixes the sign of `b_k`,
  since `‖2 b_k‖ > 2^-2` for both twists;
* `tR0_fK_ne`: `R0 ≠ 0` from the residue of `N0(g_0, ..., g_4) = 4⁴ N0(f)` modulo `2^16`
  (nonzero by the kernel check `res_ok`; PARI gives `v(N0(g)) = 42` for `k = 0` and `26` for
  `k = 1`, on the scale `v(pv) = 1`);
* `baseKv k : SetupKv`, with `V0 = b_k · β`, `c0 = R2`, `w0 = X² + (R1/R2) X + R0/R2`
  (`ConcreteBase.lean`);
* `logChartFin_fRev`: the conclusion of `logChartFin_of_setupKv` for `baseKv k`, under the finite
  index hypothesis `HFinIdx` for its chart, a theorem (`FinIdx.hFinIdx_of_setupKv`; the
  unconditional form is `FinIdx.logChartFin_fRev_uncond`).
-/

open Polynomial
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.G2Formal.Taylor FurioLombardo.Vendor.Toolbox.UnitBall
open FurioLombardo.M1 FurioLombardo.Discharge.M4Cert
open FurioLombardo.Discharge.M3a (goodSextic_of coeff_pQ)
open FurioLombardo.Discharge.M3a.Bruin (fRev FnData frevL FE lead_Kv goodSextic_fRev_Kv
  fRev_natDegree fRev_separable approx_sub ne_zero_of_approx exists_sqrt LowOK two_ne_zero_Kv)

namespace FurioLombardo.Discharge.R7.ConcreteKv

/-! ## Translation by `X ↦ X + a` -/

theorem separable_comp_X_add_C {K : Type*} [Field K] {f : K[X]} (hf : f.Separable) (a : K) :
    (f.comp (X + C a)).Separable := by
  rw [Polynomial.separable_def']
  rcases (Polynomial.separable_def' f).mp hf with ⟨u, v, h⟩
  refine ⟨u.comp (X + C a), v.comp (X + C a), ?_⟩
  calc (u.comp (X + C a)) * (f.comp (X + C a)) +
        (v.comp (X + C a)) * (derivative (f.comp (X + C a)))
      = (u.comp (X + C a)) * (f.comp (X + C a)) +
        (v.comp (X + C a)) * ((derivative f).comp (X + C a)) := by
        rw [Polynomial.derivative_comp, Polynomial.derivative_X_add_C, one_mul]
    _ = (u * f + v * derivative f).comp (X + C a) := by simp
    _ = (1 : K[X]).comp (X + C a) := by rw [h]
    _ = 1 := by simp

theorem natDegree_leadingCoeff_comp_X_add_C {K : Type*} [Field K] (f : K[X]) (a : K) :
    (f.comp (X + C a)).natDegree = f.natDegree ∧
      (f.comp (X + C a)).leadingCoeff = f.leadingCoeff := by
  have hd : (X + C a).natDegree = 1 := natDegree_X_add_C a
  have hl : (X + C a).leadingCoeff = 1 := leadingCoeff_X_add_C a
  refine ⟨?_, ?_⟩
  · rw [natDegree_comp, hd, mul_one]
  · rw [leadingCoeff_comp (by rw [hd]; exact one_ne_zero), hl, one_pow, mul_one]

theorem comp_X_add_C_comp_X_sub_C {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    (p.comp (X + C a)).comp (X - C a) = p := by
  rw [comp_assoc]
  simp

/-- The coefficients of `p(X + a)` for `p` of degree at most 6. -/
theorem coeff_comp_X_add_C {R : Type*} [CommRing R] (p : R[X]) (a : R) (hp : p.natDegree < 7)
    (j : ℕ) : (p.comp (X + C a)).coeff j =
      ∑ n ∈ Finset.range 7, ((n + j).choose j : R) * p.coeff (n + j) * a ^ n := by
  rw [← taylor_apply, taylor_coeff,
    eval_eq_sum_range' (n := 7) (lt_of_le_of_lt (natDegree_hasseDeriv_le p j) (by omega))]
  simp only [hasseDeriv_coeff]

/-! ## The translated models -/

/-- The base abscissa `a_k = k`. -/
noncomputable def aK (k : Fin 2) : Kv := ((k : ℕ) : Kv)

/-- The translated model `f_k = F_k(X + a_k)`, `F_k = (fRev k).map σ`. -/
noncomputable def fK (k : Fin 2) : Kv[X] := ((fRev k).map σ).comp (X + C (aK k))

theorem natDegree_FK (k : Fin 2) : ((fRev k).map σ).natDegree = 6 := by
  rw [natDegree_map, fRev_natDegree]

theorem fK_natDegree (k : Fin 2) : (fK k).natDegree = 6 := by
  rw [fK, (natDegree_leadingCoeff_comp_X_add_C _ _).1, natDegree_FK]

theorem fK_leadingCoeff (k : Fin 2) : (fK k).leadingCoeff = σ (fRev k).leadingCoeff := by
  rw [fK, (natDegree_leadingCoeff_comp_X_add_C _ _).2, leadingCoeff_map]

theorem fK_coeff_six (k : Fin 2) : (fK k).coeff 6 = σ (fRev k).leadingCoeff := by
  rw [← fK_leadingCoeff, leadingCoeff, fK_natDegree]

/-- **`f_k` is a good sextic.** -/
theorem goodSextic_fK (k : Fin 2) : GoodSextic (fK k) :=
  goodSextic_of (separable_comp_X_add_C (fRev_separable k).map _) (fK_natDegree k)
    (by rw [fK_leadingCoeff]; exact lead_Kv k) two_ne_zero_Kv

/-- **`f_k(X - a_k) = F_k`.** -/
theorem hF (k : Fin 2) : (fK k).comp (X - C (aK k)) = (fRev k).map σ :=
  comp_X_add_C_comp_X_sub_C _ _

/-! ## Residues of the coefficients -/

theorem approx_zero (n : ℕ) : Approx 0 0 n := by
  have h := approx_evZ ((0 : ℤ), (0 : ℤ), (0 : ℤ)) n
  rwa [evZ_zero] at h

theorem approx_int (c : ℤ) (n : ℕ) : Approx (c : Kv) (c, 0, 0) n := by
  have h := approx_evZ (c, 0, 0) n
  rwa [evZ_const] at h

theorem approx_sum_range (x : ℕ → Kv) (t : ℕ → T3) {n : ℕ} :
    ∀ N, (∀ i < N, Approx (x i) (t i) n) →
      Approx (∑ i ∈ Finset.range N, x i) (∑ i ∈ Finset.range N, t i) n
  | 0, _ => by rw [Finset.sum_range_zero, Finset.sum_range_zero]; exact approx_zero n
  | N + 1, h => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (approx_sum_range x t N fun i hi => h i (by omega)).add (h N (by omega))

/-- The zk coordinates of `4 · coeff_i (fRev k)`, `i ≤ 6`. -/
def rl (k : Fin 2) (i : ℕ) : List ℤ := (FnData.getD (k : ℕ) []).getD (6 - i) []

theorem evK_frevL (k : Fin 2) {i : ℕ} (hi : i < 7) :
    evK ((frevL (k : ℕ)).getD i (.int 0)) = zkE (rl k i) := by
  interval_cases i <;> rfl

/-- The residues modulo `2^16` of `σ (zkE (rl k i))`, `i = 0, ..., 6`. -/
def tGL : Fin 2 → List T3
  | 0 => [(61412, 43144, 18692), (57312, 29184, 63792), (6608, 40800, 4416),
      (55392, 22880, 32544), (52340, 28136, 53148), (49804, 58268, 21128), (32883, 3284, 29458)]
  | 1 => [(58460, 33456, 3416), (21536, 9440, 58480), (9520, 47328, 45168),
      (44768, 5728, 40704), (38156, 19776, 31344), (15388, 48932, 10140), (29153, 29124, 34331)]

/-- The residue triple of `4 · coeff_i F_k` (zero for `i ≥ 7`). -/
def tG (k : Fin 2) (i : ℕ) : T3 := (tGL k).getD i (0, 0, 0)

/-- Kernel check: the zk lists pass the residue test, with residues `tGL`. -/
theorem tGL_ok : ∀ k : Fin 2, ∀ i : Fin 7,
    zresOK (rl k i) ∧ modT (zres (rl k i)) 16 = tG k i := by
  decide +kernel

theorem four_mul_coeff_FK (k : Fin 2) {i : ℕ} (hi : i < 7) :
    4 * ((fRev k).map σ).coeff i = σ (zkE (rl k i)) := by
  rw [coeff_map, fRev, coeff_pQ, evK_frevL k hi, map_mul, map_inv₀, map_natCast,
    ← mul_assoc]
  have h4 : ((4 : ℕ) : Kv) ≠ 0 := by
    have := two_ne_zero_Kv
    push_cast
    intro h
    apply this
    linear_combination h / 2
  rw [show (4 : Kv) = ((4 : ℕ) : Kv) by push_cast; rfl, mul_inv_cancel₀ h4, one_mul]

theorem approx_G (k : Fin 2) (i : ℕ) : Approx (4 * ((fRev k).map σ).coeff i) (tG k i) 16 := by
  by_cases hi : i < 7
  · rw [four_mul_coeff_FK k hi]
    obtain ⟨hok, heq⟩ := tGL_ok k ⟨i, hi⟩
    have h := (approx_σ_zkE _ hok (by norm_num : 16 ≤ 28)).reduce
    rwa [heq] at h
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_FK]; omega), mul_zero]
    have : tG k i = 0 := by
      have hl : (tGL k).length = 7 := by fin_cases k <;> rfl
      unfold tG
      rw [List.getD_eq_default _ _ (by omega)]
      rfl
    rw [this]
    exact approx_zero 16

/-- The residue triple of `g_j = 4 · coeff_j f_k`. -/
def gT (k : Fin 2) (j : ℕ) : T3 :=
  ∑ n ∈ Finset.range 7, mulZ ((((n + j).choose j * (k : ℕ) ^ n : ℕ) : ℤ), 0, 0) (tG k (n + j))

/-- **Residues of the coefficients of `4 f_k` modulo `2^16`.** -/
theorem approx_g (k : Fin 2) (j : ℕ) : Approx (4 * (fK k).coeff j) (gT k j) 16 := by
  rw [fK, coeff_comp_X_add_C _ _ (by rw [natDegree_FK]; omega), Finset.mul_sum]
  refine approx_sum_range _ _ 7 fun n _ => ?_
  have e : 4 * (((n + j).choose j : Kv) * ((fRev k).map σ).coeff (n + j) * aK k ^ n) =
      (((((n + j).choose j * (k : ℕ) ^ n : ℕ) : ℤ)) : Kv) *
        (4 * ((fRev k).map σ).coeff (n + j)) := by
    rw [aK]; push_cast; ring
  rw [e]
  exact (approx_int _ 16).mul (approx_G k (n + j))

/-! ## The numerator of `R0` -/

/-- `tN0` on residue triples. -/
def tN0T (t0 t1 t2 t3 t4 : T3) : T3 :=
  mulZ (64, 0, 0) (mulZ (mulZ (mulZ t0 t0) t0) t4) -
    mulZ (16, 0, 0) (mulZ (mulZ t0 t0) (mulZ t2 t2)) -
    mulZ (32, 0, 0) (mulZ (mulZ (mulZ t0 t0) t1) t3) +
    mulZ (24, 0, 0) (mulZ (mulZ (mulZ t0 t1) t1) t2) -
    mulZ (5, 0, 0) (mulZ (mulZ (mulZ t1 t1) t1) t1)

theorem approx_tN0 {x0 x1 x2 x3 x4 : Kv} {t0 t1 t2 t3 t4 : T3} {n : ℕ} (h0 : Approx x0 t0 n)
    (h1 : Approx x1 t1 n) (h2 : Approx x2 t2 n) (h3 : Approx x3 t3 n) (h4 : Approx x4 t4 n) :
    Approx (tN0 x0 x1 x2 x3 x4) (tN0T t0 t1 t2 t3 t4) n := by
  have e : tN0 x0 x1 x2 x3 x4 = ((64 : ℤ) : Kv) * (x0 * x0 * x0 * x4) -
      ((16 : ℤ) : Kv) * (x0 * x0 * (x2 * x2)) - ((32 : ℤ) : Kv) * (x0 * x0 * x1 * x3) +
      ((24 : ℤ) : Kv) * (x0 * x1 * x1 * x2) - ((5 : ℤ) : Kv) * (x1 * x1 * x1 * x1) := by
    unfold tN0; push_cast; ring
  rw [e]
  exact approx_sub (((approx_sub (approx_sub
    ((approx_int 64 n).mul (((h0.mul h0).mul h0).mul h4))
    ((approx_int 16 n).mul ((h0.mul h0).mul (h2.mul h2))))
    ((approx_int 32 n).mul (((h0.mul h0).mul h1).mul h3)))).add
    ((approx_int 24 n).mul (((h0.mul h1).mul h1).mul h2)))
    ((approx_int 5 n).mul (((h1.mul h1).mul h1).mul h1))

/-- The square root certificates: `b ≡ bT k` modulo `2^3`, `b² ≡ g_0` modulo `2^6`. -/
def bT : Fin 2 → T3
  | 0 => (6, 6, 8)
  | 1 => (11, 11, 15)

/-- Kernel check: `g_0` and `N0(g)` have nonzero residues modulo `2^16`, and `bT k` is a square
root certificate of `g_0`. -/
theorem res_ok : ∀ k : Fin 2,
    modT (gT k 0) 16 ≠ modT (0, 0, 0) 16 ∧
    modT (tN0T (gT k 0) (gT k 1) (gT k 2) (gT k 3) (gT k 4)) 16 ≠ modT (0, 0, 0) 16 ∧
    modT (mulZ (bT k) (bT k)) 6 = modT (gT k 0) 6 ∧ LowOK (bT k) 1 := by
  decide +kernel

/-! ## The base point -/

theorem four_ne_zero_Kv : (4 : Kv) ≠ 0 := by
  have := two_ne_zero_Kv
  intro h
  apply this
  linear_combination h / 2

theorem fK_coeff_zero_ne (k : Fin 2) : (fK k).coeff 0 ≠ 0 := by
  intro h
  have := ne_zero_of_approx (approx_g k 0) (res_ok k).1
  rw [h, mul_zero] at this
  exact this rfl

/-- **A square root of `f_k(0)` in `Kv`.** -/
theorem exists_b (k : Fin 2) :
    ∃ b : Kv, b ^ 2 = (fK k).coeff 0 ∧ b ≠ 0 ∧ Approx (2 * b) (bT k) 3 := by
  obtain ⟨-, -, hb, hlow⟩ := res_ok k
  obtain ⟨y, hy, hya⟩ := exists_sqrt ((approx_g k 0).mono (by norm_num : 6 ≤ 16)) hb hlow
    (by norm_num)
  refine ⟨y / 2, ?_, ?_, ?_⟩
  · have h2 := two_ne_zero_Kv
    field_simp
    linear_combination hy
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · apply fK_coeff_zero_ne k
      have : 4 * (fK k).coeff 0 = 0 := by rw [← hy, h]; ring
      exact (mul_eq_zero.mp this).resolve_left four_ne_zero_Kv
    · exact two_ne_zero_Kv h
  · rwa [mul_div_cancel₀ y two_ne_zero_Kv]

/-- The ordinate `b_k` of the base point. -/
noncomputable def bK (k : Fin 2) : Kv := (exists_b k).choose

theorem bK_sq (k : Fin 2) : bK k ^ 2 = (fK k).coeff 0 := (exists_b k).choose_spec.1

theorem bK_ne (k : Fin 2) : bK k ≠ 0 := (exists_b k).choose_spec.2.1

/-- The residue of `2 b_k` modulo `2^3`, which fixes the sign of `b_k` (`‖2 b_k‖ > 2^-2`). -/
theorem bK_approx (k : Fin 2) : Approx (2 * bK k) (bT k) 3 := (exists_b k).choose_spec.2.2

theorem tR2_fK_ne (k : Fin 2) : tR2 (fK k) ≠ 0 :=
  tR2_ne_zero _ (bK_sq k) (by rw [fK_coeff_six]; exact lead_Kv k)

/-- **`R0 ≠ 0`** from the residue of `N0(4 f_k)`. -/
theorem tR0_fK_ne (k : Fin 2) : tR0 (fK k) ≠ 0 := by
  refine tR0_ne_zero _ (fK_coeff_zero_ne k) two_ne_zero_Kv fun h => ?_
  have hN := ne_zero_of_approx (approx_tN0 (approx_g k 0) (approx_g k 1) (approx_g k 2)
    (approx_g k 3) (approx_g k 4)) (res_ok k).2.1
  rw [tN0_smul, h, mul_zero] at hN
  exact hN rfl

/-- The monic quadratic `w0 = X² + (R1/R2) X + R0/R2`. -/
noncomputable def w0K (k : Fin 2) : Kv[X] :=
  X ^ 2 + C (tR1 (fK k) / tR2 (fK k)) * X + C (tR0 (fK k) / tR2 (fK k))

theorem fK_sub_sq (k : Fin 2) :
    fK k - (C (bK k) * tβ (fK k)) ^ 2 = C (tR2 (fK k)) * (X ^ 4 * w0K k) := by
  have hR2 := tR2_fK_ne k
  have e1 : (C (bK k) * tβ (fK k)) ^ 2 = C ((fK k).coeff 0) * tβ (fK k) ^ 2 := by
    rw [mul_pow, ← C_pow, bK_sq]
  have e2 : C (tR2 (fK k)) * (X ^ 4 * w0K k) =
      X ^ 4 * (C (tR0 (fK k)) + C (tR1 (fK k)) * X + C (tR2 (fK k)) * X ^ 2) := by
    have h1 : tR2 (fK k) * (tR1 (fK k) / tR2 (fK k)) = tR1 (fK k) := by field_simp
    have h0 : tR2 (fK k) * (tR0 (fK k) / tR2 (fK k)) = tR0 (fK k) := by field_simp
    calc C (tR2 (fK k)) * (X ^ 4 * w0K k) = X ^ 4 * (C (tR2 (fK k) * (tR0 (fK k) / tR2 (fK k))) +
          C (tR2 (fK k) * (tR1 (fK k) / tR2 (fK k))) * X + C (tR2 (fK k)) * X ^ 2) := by
          simp only [w0K, C_mul]; ring
      _ = _ := by rw [h1, h0]
  rw [e1, e2]
  exact taylor_identity _ (fK_natDegree k).le (fK_coeff_zero_ne k) two_ne_zero_Kv

/-- **The base point data of the twist `k` over `Kv`.** -/
noncomputable def baseKv (k : Fin 2) : SetupKv where
  f := fK k
  hf := (fK_natDegree k).le
  V0 := C (bK k) * tβ (fK k)
  hV0d := by rw [degree_C_mul (bK_ne k)]; exact tβ_degree_lt _
  hV00 := by rw [coeff_C_mul, tβ_coeff_zero, mul_one]; exact bK_ne k
  c0 := tR2 (fK k)
  hc0 := tR2_fK_ne k
  w0 := w0K k
  hw0m := by unfold w0K; monicity!
  hw0d := by unfold w0K; compute_degree!
  hfV0 := fK_sub_sq k
  hw00 := by
    have e : (w0K k).coeff 0 = tR0 (fK k) / tR2 (fK k) := by simp [w0K]
    rw [e]
    exact div_ne_zero (tR0_fK_ne k) (tR2_fK_ne k)

instance goodSextic_baseKv (k : Fin 2) : GoodSextic (baseKv k).f := goodSextic_fK k

instance goodSextic_FK (k : Fin 2) : GoodSextic ((fRev k).map σ) := goodSextic_fRev_Kv k

/-- **`LogChartFin` for `Jac F_k`, `k = 0, 1`**, under the finite index hypothesis `HFinIdx`
for the chart of the base point `baseKv k`, with the explicit logarithm on the image of
the ball. The hypothesis holds by `FinIdx.hFinIdx_of_setupKv`; the form without it is
`FinIdx.logChartFin_fRev_uncond`. -/
theorem logChartFin_fRev (k : Fin 2) :
    ∃ M, ∃ hM : (baseKv k).toSetup.Adm M,
      HFinIdx ((baseKv k).toSetup.fglO hM.good) ((baseKv k).toSetup.psi (hF k) hM)
        (pvO ^ (3 + 1)) →
      ∃ lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]), Analytic.LogChartFin lam ∧
        ∃ H' : AddSubgroup (Additive (Jac ((fRev k).map σ))),
          (H' : Set (Additive (Jac ((fRev k).map σ)))) = (baseKv k).toSetup.psi (hF k) hM ''
            (FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((baseKv k).toSetup.fglO hM.good) (pvO ^ (3 + 1)) :
              Set ((baseKv k).toSetup.fglO hM.good).Points) ∧
          H'.FiniteIndex ∧
          ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((baseKv k).toSetup.fglO hM.good) (pvO ^ (3 + 1)),
            ∀ y : Fin 2 → OKv, (∀ j, (z j : OKv) = pvO ^ (3 + 1) * y j) →
              lam ((baseKv k).toSetup.psi (hF k) hM z) = H'.index • coordEquiv
                (FurioLombardo.Vendor.Toolbox.FormalGroup.logVal ((baseKv k).toSetup.fglO hM.good)
                  (unitBall Kv).subtype (pvO ^ (3 + 1)) y) := by
  obtain ⟨M, hM⟩ := (baseKv k).toSetup.exists_adm
  exact ⟨M, hM, fun hH => logChartFin_of_setupKv (baseKv k) _ (aK k) (hF k) hM hH⟩

end FurioLombardo.Discharge.R7.ConcreteKv
