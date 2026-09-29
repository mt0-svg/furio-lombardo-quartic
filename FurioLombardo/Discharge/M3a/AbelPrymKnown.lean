import FurioLombardo.Discharge.M3a.AbelPrymCheck
import FurioLombardo.Discharge.M3a.AbelPrymRuling
import FurioLombardo.Discharge.M3a.Concrete

/-!
# The Abel-Prym map at the known lifts (WP4 of the M3a discharge)

`phiRev (Mmat 0) (Mmat 1) (Mmat 2) (δ k) (fRev k)` is Bruin's Abel-Prym map on the reversed model
(AbelPrym.lean). At the four known lifts it is computed by an explicit certificate, built with
`AbelPrym.Cert.ofEntry` from the kernel checks of AbelPrymCheck.lean:

* `phiRev_x0`, `phiRev_x2` (twist 0) and `phiRev_x1`, `phiRev_x3` (twist 1):
  `phiRev x_i = [⟨U_i, Y - V_i⟩]` with `U_i = apUp i` monic of degree 2 and `V_i = apVp i` of
  degree at most 1, the Mumford pairs of code/earlier-computations/phi_known_lifts.gp transported to the
  reversed model (`U' = U^rev / U(0)`, `V' = t³ V(1/t) mod U'`; checked by abel_prym_data.gp);
* `apUp_dvd`: `U_i ∣ V_i² - fRev`.

Along the way: `fRev_eq_det_swap` (`fRev = -δ det(M3 + 2t M2 + t² M1)`, the sextic of the swapped
forms), `neg_δ_det_Mmat0` (`-δ det M1 = c`, the leading coefficient of `fRev`), `δ_ne_zero`.
-/

namespace FurioLombardo.Discharge.M3a.AbelPrym

open Polynomial Matrix FurioLombardo.M3a

variable {L : Type*} [Field L]

/-- The entry `(1, 3)` of `G A G`. -/
theorem gram_plucker_gram_13 (M1 M2 M3 : Matrix (Fin 3) (Fin 3) L) (δ : L) (a b : Fin 4 → L[X]) :
    (gram M1 M2 M3 δ * plucker a b * gram M1 M2 M3 δ) 1 3 =
      -C δ * (pencil M1 M2 M3 1 0 * (a 0 * b 3 - b 0 * a 3) +
        pencil M1 M2 M3 1 1 * (a 1 * b 3 - b 1 * a 3) +
        pencil M1 M2 M3 1 2 * (a 2 * b 3 - b 2 * a 3)) := by
  simp [gram, plucker, Matrix.mul_apply, Fin.sum_univ_four, vecMulVec, Matrix.vecHead,
    Matrix.vecTail]
  ring

variable {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

theorem swapPt_p (x : DPoint L M1 M2 M3 δ) : (swapPt x).p = x.p := rfl

theorem pt_swapPt_fst (x : DPoint L M1 M2 M3 δ) : (pt (swapPt x)).1 = x.p := rfl

end FurioLombardo.Discharge.M3a.AbelPrym

namespace FurioLombardo.Discharge.M3a.Bruin

open Polynomial Matrix FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
open FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M3a.AbelPrym (V5 pt swapPt pencil gram bruinU plk plucker hodge
  quadD polarD Cert phiRev phiRev_eq_of_cert)

/-! ## The sextic of the swapped forms -/

theorem pK_NPs (a b : Fin 3) : pK (NPs a b) = 2 * pencil (Mmat 2) (Mmat 1) (Mmat 0) a b := by
  simp only [NPs, pK_cons, pK_nil, evK_mul, evK_int, evK_NE, pencil, Matrix.of_apply, map_mul]
  simp only [Int.cast_ofNat, map_ofNat]
  ring

theorem pK_detLhsS_eq (k : Fin 2) : pK (detLhsS k) = pK (detRhsS k) := by
  fin_cases k
  · exact pK_eq_of_eqCheck _ _ _ ck_detS0
  · exact pK_eq_of_eqCheck _ _ _ ck_detS1

/-- `fRev_k = -δ_k det(M3 + 2t M2 + t² M1)`: the Prym sextic of the swapped forms. -/
theorem fRev_eq_det_swap (k : Fin 2) :
    fRev k = -C (δ k) * (pencil (Mmat 2) (Mmat 1) (Mmat 0)).det := by
  have hck := pK_detLhsS_eq k
  have h2 : (Matrix.of fun a b => pK (NPs a b)) = (2 : K21[X]) • pencil (Mmat 2) (Mmat 1) (Mmat 0) := by
    ext a b; simp [pK_NPs]
  rw [detLhsS, detRhsS, pK_smulP, pK_smulP, pK_detP, h2, det_smul] at hck
  simp only [evK_int, evK_mul, evK_lin, Fintype.card_fin, Int.cast_ofNat, Int.cast_neg,
    Int.cast_one, map_ofNat, map_mul, map_neg, map_one] at hck
  have hP : pK (frevL k) = 4 * (-C (δ k) * (pencil (Mmat 2) (Mmat 1) (Mmat 0)).det) := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : K21[X]) ≠ 0)
    rw [hck]
    change -1 * C (δ k) * (2 ^ 3 * (pencil (Mmat 2) (Mmat 1) (Mmat 0)).det) =
      2 * (4 * (-C (δ k) * (pencil (Mmat 2) (Mmat 1) (Mmat 0)).det))
    ring
  rw [fRev, pQ, hP, ← mul_assoc, show (4 : K21[X]) = C ((4 : ℕ) : K21) by
    rw [C_eq_natCast, Nat.cast_ofNat], ← map_mul, inv_mul_cancel₀ (natCast_ne_zero (by norm_num)),
    map_one, one_mul]

/-- `-δ_k det M1 = c_k`, the leading coefficient of `fRev_k` (constant term of `f_k`). -/
theorem neg_δ_det_Mmat0 (k : Fin 2) : -δ k * (Mmat 0).det = c k := by
  have h := congrArg (fun p => p.coeff 0) (fδ_eq_det k)
  have h0 : (fδ k).coeff 0 = c k := by
    rw [fδ, coeff_pQ]; simp [c, fdeltaL]
  have h1 : (-C (δ k) * Mt.det).coeff 0 = -δ k * (Mmat 0).det := by
    rw [← map_neg, coeff_C_mul, coeff_zero_eq_eval_zero, ← coe_evalRingHom, RingHom.map_det]
    congr 2
    ext a b
    simp [Mt, RingHom.mapMatrix_apply]
  rw [← h1, ← h, h0]

theorem δ_ne_zero (k : Fin 2) : δ k ≠ 0 := fun h =>
  c_not_isSquare k ⟨0, by rw [← neg_δ_det_Mmat0, h]; ring⟩

theorem lc_not_isSquare (k : Fin 2) : ¬ IsSquare (-δ k * (Mmat 0).det) := by
  rw [neg_δ_det_Mmat0]; exact c_not_isSquare k

/-! ## Evaluation of the expressions -/

theorem evK_dot3E (u v : Fin 3 → KE) :
    evK (dot3E u v) = (fun a => evK (u a)) ⬝ᵥ (fun a => evK (v a)) := by
  simp [dot3E, dotProduct, Fin.sum_univ_three]

theorem evK_bil2E (j : Fin 3) (u v : Fin 3 → KE) :
    evK (bil2E j u v) = 2 * ((fun a => evK (u a)) ⬝ᵥ (Mmat j *ᵥ fun a => evK (v a))) := by
  simp only [bil2E, evK_dot3E, evK_NE]
  simp [dotProduct, mulVec, Fin.sum_univ_three]
  ring

/-- The swapped forms `(Q3, Q2, Q1)`. -/
noncomputable abbrev Msw : Fin 3 → Matrix (Fin 3) (Fin 3) K21 := ![Mmat 2, Mmat 1, Mmat 0]

theorem Mmat_sw (j : Fin 3) : Mmat (sw j) = Msw j := by fin_cases j <;> rfl

theorem Msw_symm : ∀ j, (Msw j)ᵀ = Msw j := AbelPrym.symm_fun (Mmat_symm 2) (Mmat_symm 1) (Mmat_symm 0)

/-- The tangent vector `T = (m, t1, 0, t3, t4)` of the certificate of the point `i`. -/
noncomputable def apTv (i : ℕ) : V5 K21 := (fun a => evK (TE i a), zkE (apTL i 1), zkE (apTL i 2))

theorem evK_pE (a b : ℤ) : (fun c => evK (pE a b c)) = ![(a : K21), (b : K21), 1] := by
  funext c; fin_cases c <;> simp [pE]

section Point

variable {k : Fin 2} (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) {i : ℕ} {a b : ℤ}

theorem pt_swapPt (hp : x.p = ![(a : K21), (b : K21), 1]) (hr : x.r = zkE (liftR i))
    (hs : x.s = zkE (liftS i)) :
    pt (swapPt x) = (fun c => evK (pE a b c), zkE (liftS i), zkE (liftR i)) := by
  simp only [pt, swapPt, hp, hr, hs, evK_pE]

theorem evK_tanE (hp : x.p = ![(a : K21), (b : K21), 1]) (hr : x.r = zkE (liftR i))
    (hs : x.s = zkE (liftS i)) (j : Fin 3) :
    evK (tanE i k a b j) = polarD Msw (δ k) j (pt (swapPt x)) (apTv i) := by
  rw [AbelPrym.polarD_symm Msw_symm, pt_swapPt x hp hr hs, ← Mmat_sw]
  simp only [tanE, evK_sub, evK_mul, evK_bil2E, apTv]
  congr 2
  fin_cases j <;> simp [wE, sE, rE, t3E, t4E]

theorem evK_q2E (j : Fin 3) : evK (q2E i k j) = 2 * quadD Msw (δ k) j (apTv i) := by
  simp only [q2E, evK_sub, evK_mul, evK_bil2E, quadD, apTv, ← Mmat_sw]
  fin_cases j <;> simp [sqE, t3E, t4E, dE, δ] <;> ring


/-- The component `j` of `2 (r² M3 - 2rs M2 + s² M1) p` for the swapped point. -/
theorem evK_nRowE (j : Fin 3) :
    evK (dot3E (nRowE i j) (pE a b)) = 2 * (((zkE (liftR i)) ^ 2 • Msw 0 -
      (2 * zkE (liftS i) * zkE (liftR i)) • Msw 1 + (zkE (liftS i)) ^ 2 • Msw 2) *ᵥ
        ![(a : K21), (b : K21), 1]) j := by
  simp only [evK_dot3E, nRowE, evK_add, evK_sub, evK_mul, evK_NE, evK_int, evK_pE]
  simp [rE, sE, dotProduct, mulVec, Fin.sum_univ_three]
  ring

end Point

/-! ## The certificate data as polynomials -/

/-- `U'` at the point `i`. -/
noncomputable def apUp (i : ℕ) : K21[X] := pQ (apUdN i) (uL i)

/-- `V'` at the point `i`. -/
noncomputable def apVp (i : ℕ) : K21[X] := pQ (apDN i) (vL i)

theorem apUp_monic {i : ℕ} (h : apUdN i ≠ 0) : (apUp i).Monic ∧ (apUp i).natDegree = 2 :=
  monic_pQ h rfl rfl

theorem apVp_degree (i : ℕ) : (apVp i).degree < 2 := by
  have h : (apVp i).natDegree ≤ 1 := natDegree_pQ_le (apDN i) (vL i)
  exact lt_of_le_of_lt (degree_le_of_natDegree_le h) (by norm_num)

theorem bruinU_apTv {i : ℕ} {k : Fin 2} {K0 K1 : ℕ} (hUd : apUdN i ≠ 0)
    (ha3 : quadD Msw (δ k) 2 (apTv i) ≠ 0) (h0 : checkK K0 (u0Chk i k) = true)
    (h1 : checkK K1 (u1Chk i k) = true) :
    bruinU (Mmat 2) (Mmat 1) (Mmat 0) (δ k) (apTv i) = apUp i := by
  have e0 := evK_eq_zero_of_check _ _ h0
  have e1 := evK_eq_zero_of_check _ _ h1
  simp only [u0Chk, u1Chk, evK_sub, evK_mul, evK_lin, evK_int, evK_q2E] at e0 e1
  push_cast at e0 e1
  have hUd' : ((apUdN i : ℕ) : K21) ≠ 0 := natCast_ne_zero hUd
  set a0 := quadD Msw (δ k) 0 (apTv i)
  set a1 := quadD Msw (δ k) 1 (apTv i)
  set a2 := quadD Msw (δ k) 2 (apTv i)
  set Ud : K21 := ((apUdN i : ℕ) : K21)
  have hβ : a0 / a2 = Ud⁻¹ * zkE (apUL i 0) := by
    rw [div_eq_iff ha3]
    have h : Ud * a0 = zkE (apUL i 0) * a2 := by linear_combination (-1 / 2 : K21) * e0
    calc a0 = Ud⁻¹ * (Ud * a0) := by field_simp
      _ = Ud⁻¹ * zkE (apUL i 0) * a2 := by rw [h]; ring
  have hα : 2 * a1 / a2 = Ud⁻¹ * zkE (apUL i 1) := by
    rw [div_eq_iff ha3]
    have h : Ud * (2 * a1) = zkE (apUL i 1) * a2 := by linear_combination (-1 / 2 : K21) * e1
    calc 2 * a1 = Ud⁻¹ * (Ud * (2 * a1)) := by field_simp
      _ = Ud⁻¹ * zkE (apUL i 1) * a2 := by rw [h]; ring
  have hU : C Ud⁻¹ * C Ud = 1 := by rw [← map_mul, inv_mul_cancel₀ hUd', map_one]
  unfold bruinU
  change X ^ 2 + C (2 * a1 / a2) * X + C (a0 / a2) = apUp i
  rw [hα, hβ]
  simp only [apUp, pQ, uL, pK_cons, pK_nil, evK_lin, evK_int, mul_zero, add_zero, Int.cast_natCast]
  rw [map_mul, map_mul]
  linear_combination (-(X ^ 2 : K21[X])) * hU

theorem pK_auL (i : ℕ) (a b : ℤ) (u : Fin 3) :
    pK (auL i a b u) = C (evK (pE a b u)) * (C (zkE (apTL i 1)) + X * C (zkE (apTL i 2))) -
      C (evK (TE i u)) * (C (zkE (liftS i)) + X * C (zkE (liftR i))) := by
  simp only [auL, pK_cons, pK_nil, evK_sub, evK_mul, t3E, t4E, sE, rE, evK_lin, map_sub, map_mul]
  ring

theorem evK_dE (k : Fin 2) : evK (dE k) = δ k := rfl

theorem apTv_fst (i : ℕ) : (apTv i).1 = ![(apMN i : K21), zkE (apTL i 0), 0] := by
  funext c; fin_cases c <;> simp [apTv, TE]

theorem plk_apTv (i : ℕ) : plk (apTv i) = ![C (apMN i : K21), C (zkE (apTL i 0)), 0,
    C (zkE (apTL i 1)) + X * C (zkE (apTL i 2))] := by
  funext c; fin_cases c <;> simp [plk, apTv, TE]

theorem plk_pt {k : Fin 2} (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) {i : ℕ} {a b : ℤ}
    (hp : x.p = ![(a : K21), (b : K21), 1]) (hr : x.r = zkE (liftR i))
    (hs : x.s = zkE (liftS i)) : plk (pt (swapPt x)) = ![C (a : K21), C (b : K21), 1,
      C (zkE (liftS i)) + X * C (zkE (liftR i))] := by
  rw [pt_swapPt x hp hr hs, evK_pE]
  funext c; fin_cases c <;> simp [plk]

/-- **The ruling entry `(1, 3)`**: `U' ∣ (G A G)_{13} - V' ⋆A_{13}`, from one kernel check. -/
theorem ent_dvd {k : Fin 2} (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) {i : ℕ} {a b : ℤ}
    (hp : x.p = ![(a : K21), (b : K21), 1]) (hr : x.r = zkE (liftR i))
    (hs : x.s = zkE (liftS i)) {K : ℕ} (hD : apDN i ≠ 0)
    (ha3 : quadD Msw (δ k) 2 (apTv i) ≠ 0)
    (hck : eqCheck K (entLhs i k a b) (entRhs i k) = true) :
    bruinU (Mmat 2) (Mmat 1) (Mmat 0) (δ k) (apTv i) ∣
      (gram (Mmat 2) (Mmat 1) (Mmat 0) (δ k) * plucker (plk (pt (swapPt x))) (plk (apTv i)) *
        gram (Mmat 2) (Mmat 1) (Mmat 0) (δ k)) 1 3 -
      apVp i * hodge (plucker (plk (pt (swapPt x))) (plk (apTv i))) 1 3 := by
  have key := pK_eq_of_eqCheck _ _ _ hck
  simp only [entLhs, entRhs, gag2L, uTL, vL, wL, pK_subP, pK_smulP, pK_addP, pK_mulP, pK_NPs,
    pK_auL, pK_cons, pK_nil, evK_lin, evK_int, evK_mul, evK_q2E, evK_dE, TE, pE,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at key
  have hC := AbelPrym.C_mul_bruinU (M1 := Mmat 2) (M2 := Mmat 1) (M3 := Mmat 0) (δ := δ k) ha3
  set U := bruinU (Mmat 2) (Mmat 1) (Mmat 0) (δ k) (apTv i)
  set a0 := quadD Msw (δ k) 0 (apTv i)
  set a1 := quadD Msw (δ k) 1 (apTv i)
  set a2 := quadD Msw (δ k) 2 (apTv i)
  have hD' : ((apDN i : ℕ) : K21) ≠ 0 := natCast_ne_zero hD
  have hDD : C ((apDN i : ℕ) : K21)⁻¹ * ((apDN i : ℕ) : K21[X]) = 1 := by
    rw [← map_natCast C, ← map_mul, inv_mul_cancel₀ hD', map_one]
  have hh : hodge (plucker (plk (pt (swapPt x))) (plk (apTv i))) 1 3 = ((apMN i : ℕ) : K21[X]) := by
    rw [AbelPrym.hodge_plk_13, pt_swapPt x hp hr hs, evK_pE, apTv_fst]
    simp
  rw [hh, AbelPrym.gram_plucker_gram_13, plk_pt x hp hr hs, plk_apTv]
  simp only [apVp, pQ, vL, pK_cons, pK_nil, evK_lin, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  push_cast at key ⊢
  simp only [map_intCast, map_natCast, map_mul, map_ofNat] at key ⊢
  have key' : ((apDN i : ℕ) : K21[X]) * (-C (δ k) *
      (pencil (Mmat 2) (Mmat 1) (Mmat 0) 1 0 * ((a : K21[X]) * (C (zkE (apTL i 1)) +
          X * C (zkE (apTL i 2))) - ((apMN i : ℕ) : K21[X]) * (C (zkE (liftS i)) +
          X * C (zkE (liftR i)))) +
        pencil (Mmat 2) (Mmat 1) (Mmat 0) 1 1 * ((b : K21[X]) * (C (zkE (apTL i 1)) +
          X * C (zkE (apTL i 2))) - C (zkE (apTL i 0)) * (C (zkE (liftS i)) +
          X * C (zkE (liftR i)))) +
        pencil (Mmat 2) (Mmat 1) (Mmat 0) 1 2 * (C (zkE (apTL i 1)) + X * C (zkE (apTL i 2))))) -
      ((apMN i : ℕ) : K21[X]) * (C (zkE (apVL i 0)) + X * C (zkE (apVL i 1))) =
      C a2 * U * pK (wL i) := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : K21[X]) ≠ 0)
    simp only [wL, pK_cons, pK_nil, evK_lin, map_neg, map_one, map_zero, mul_zero, add_zero,
      zero_mul, sub_zero, one_mul] at key ⊢
    simp only [map_mul, map_ofNat] at hC
    linear_combination key + (-2 * (C (zkE (apWL i 0)) + X * C (zkE (apWL i 1)))) * hC
  refine ⟨C (a2 * ((apDN i : ℕ) : K21)⁻¹) * pK (wL i), ?_⟩
  rw [map_mul]
  linear_combination C ((apDN i : ℕ) : K21)⁻¹ * key' + (C (δ k) *
      (pencil (Mmat 2) (Mmat 1) (Mmat 0) 1 0 * ((a : K21[X]) * (C (zkE (apTL i 1)) +
          X * C (zkE (apTL i 2))) - ((apMN i : ℕ) : K21[X]) * (C (zkE (liftS i)) +
          X * C (zkE (liftR i)))) +
        pencil (Mmat 2) (Mmat 1) (Mmat 0) 1 1 * ((b : K21[X]) * (C (zkE (apTL i 1)) +
          X * C (zkE (apTL i 2))) - C (zkE (apTL i 0)) * (C (zkE (liftS i)) +
          X * C (zkE (liftR i)))) +
        pencil (Mmat 2) (Mmat 1) (Mmat 0) 1 2 * (C (zkE (apTL i 1)) + X * C (zkE (apTL i 2))))) * hDD

/-! ## The certificate and the value of `phiRev` -/

theorem mumford0_congr {f : K21[X]} [GoodSextic f] {u u' : K21[X]} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (h : u = u') (v : K21[X]) : mumford0 f hu v = mumford0 f hu' v := by
  subst h; rfl

/-- **`phiRev` at a known lift from the kernel checks.** For a lift `x` over `(a : b : 1)` with
the coordinates `r`, `s` of `liftData[i]`, the checks of AbelPrymCheck.lean give a certificate
(`AbelPrym.Cert.ofEntry`) with `U = apUp i` and `V = apVp i`. -/
theorem phiRev_known {k : Fin 2} (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) {i : ℕ}
    {a b : ℤ} (hp : x.p = ![(a : K21), (b : K21), 1]) (hr : x.r = zkE (liftR i))
    (hs : x.s = zkE (liftS i)) {K1 K2 K3 K4 : ℕ}
    (htan : ∀ j : Fin 3, checkK K1 (.sub (tanE i k a b j) (.int 0)) = true)
    (hu : checkK K2 (u0Chk i k) = true ∧ checkK K2 (u1Chk i k) = true)
    (hn : checkK K3 (nChk i a b) = true) (hnz : zkE (apNL i) ≠ 0)
    (hent : eqCheck K4 (entLhs i k a b) (entRhs i k) = true)
    (hnat : apMN i ≠ 0 ∧ apUdN i ≠ 0 ∧ apDN i ≠ 0) :
    (phiRev (Mmat 0) (Mmat 1) (Mmat 2) (δ k) (fRev k) x : Pic (fRev k)) =
      ClassGroup.mk0 (mumford0 (fRev k) (apUp_monic hnat.2.1).1.ne_zero (apVp i)) ∧
    apUp i ∣ apVp i ^ 2 - fRev k := by
  obtain ⟨hm, hUd, hD⟩ := hnat
  have h2 : (2 : K21) ≠ 0 := two_ne_zero
  -- the tangent equations
  have hT : ∀ j, polarD ![Mmat 2, Mmat 1, Mmat 0] (δ k) j (pt (swapPt x)) (apTv i) = 0 :=
    fun j => by
      rw [← evK_tanE x hp hr hs j]
      simpa using evK_eq_of_check _ _ _ (htan j)
  -- the rank condition
  have hN : ((pt (swapPt x)).2.2 ^ 2 • Msw 0 - (2 * (pt (swapPt x)).2.1 * (pt (swapPt x)).2.2) •
      Msw 1 + (pt (swapPt x)).2.1 ^ 2 • Msw 2) *ᵥ (pt (swapPt x)).1 ≠ 0 := by
    intro h0
    have hj := congrFun h0 (apNjN i)
    have e := evK_eq_zero_of_check _ _ hn
    simp only [nChk, evK_sub, evK_lin, evK_nRowE] at e
    rw [pt_swapPt x hp hr hs, evK_pE] at hj
    simp only at hj
    rw [hj, Pi.zero_apply, mul_zero, sub_zero] at e
    exact hnz e
  have hrs : (pt (swapPt x)).2.1 ≠ 0 ∨ (pt (swapPt x)).2.2 ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hN
    rw [hc.1, hc.2]
    simp
  have hrank := AbelPrym.rank_of Msw_symm (δ_ne_zero k) h2 (pt (swapPt x)) hrs hN
  -- independence and `a₃ ≠ 0`
  have hmin : (swapPt x).p 2 * (apTv i).1 0 - (swapPt x).p 0 * (apTv i).1 2 = (apMN i : K21) := by
    rw [AbelPrym.swapPt_p, hp, apTv_fst]; simp
  have hm' : (apMN i : K21) ≠ 0 := natCast_ne_zero hm
  have hmin' : (swapPt x).p 1 * (apTv i).1 2 - (swapPt x).p 2 * (apTv i).1 1 ≠ 0 ∨
      (swapPt x).p 2 * (apTv i).1 0 - (swapPt x).p 0 * (apTv i).1 2 ≠ 0 ∨
      (swapPt x).p 0 * (apTv i).1 1 - (swapPt x).p 1 * (apTv i).1 0 ≠ 0 :=
    Or.inr (Or.inl (by rw [hmin]; exact hm'))
  have hp0 : (pt (swapPt x)).1 ≠ 0 := by rw [AbelPrym.pt_swapPt_fst]; exact x.ne_zero
  have hmin'' : (pt (swapPt x)).1 1 * (apTv i).1 2 - (pt (swapPt x)).1 2 * (apTv i).1 1 ≠ 0 ∨
      (pt (swapPt x)).1 2 * (apTv i).1 0 - (pt (swapPt x)).1 0 * (apTv i).1 2 ≠ 0 ∨
      (pt (swapPt x)).1 0 * (apTv i).1 1 - (pt (swapPt x)).1 1 * (apTv i).1 0 ≠ 0 := hmin'
  have hind : LinearIndependent K21 ![apTv i, pt (swapPt x)] :=
    AbelPrym.indep_of_minor hp0 hmin''
  have ha3 := AbelPrym.a3_ne_of (Mmat_symm 2) (Mmat_symm 1) (Mmat_symm 0) h2
    (lc_not_isSquare k) (swapPt x) hT hmin'
  -- the ruling entry
  have hl : hodge (plucker (plk (pt (swapPt x))) (plk (apTv i))) 1 3 = C (apMN i : K21) := by
    rw [AbelPrym.hodge_plk_13]; congr 1
  have hdvd := ent_dvd x hp hr hs hD ha3 hent
  rw [hl] at hdvd
  have hl' : hodge (plucker (plk (pt (swapPt x))) (plk (apTv i))) 1 3 = C (apMN i : K21) := by
    rw [AbelPrym.hodge_plk_13]; congr 1
  let c : Cert (Mmat 2) (Mmat 1) (Mmat 0) (δ k) (fRev k) (swapPt x) :=
    AbelPrym.Cert.ofEntry (Mmat_symm 2) (Mmat_symm 1) (Mmat_symm 0) h2 (fRev_eq_det_swap k)
      (swapPt x) (apTv i) hT hrank hind ha3 1 (by decide) hm' hl' (apVp i) (apVp_degree i)
      (by rw [hl']; exact hdvd)
  have hU := bruinU_apTv hUd ha3 hu.1 hu.2
  refine ⟨?_, ?_⟩
  · rw [phiRev_eq_of_cert c, AbelPrym.Cert.coe_cls]
    exact congrArg ClassGroup.mk0 (mumford0_congr _ _ hU _)
  · rw [← hU]; exact c.sq
/-! ## The four known lifts -/

theorem apN_ne_zero (i : Fin 4) : zkE (apNL i) ≠ 0 :=
  zkE_ne_zero_of_res (11 : ZMod 13) ck_root13 11 ck_DB13 1 ck_Dz13 _ (ck_nres i)

/-- `φ(x0) = [⟨U_0, Y - V_0⟩]` on `Y² = fRev_0` (twist 0, `x0` over `(0:0:1)`). -/
theorem phiRev_x0 :
    (phiRev (Mmat 0) (Mmat 1) (Mmat 2) δ0 (fRev 0) x0 : Pic (fRev 0)) =
      ClassGroup.mk0 (mumford0 (fRev 0) (apUp_monic (ck_apNZ 0).2.1).1.ne_zero (apVp 0)) ∧
    apUp 0 ∣ apVp 0 ^ 2 - fRev 0 :=
  phiRev_known (k := 0) x0 (i := 0) (a := 0) (b := 0) (by simp [x0]) rfl rfl ck_tan0 ck_u0 ck_n0
    (apN_ne_zero 0) ck_ent0 (ck_apNZ 0)

/-- `φ(x2) = [⟨U_2, Y - V_2⟩]` on `Y² = fRev_0` (twist 0, `x2` over `(2:0:1)`). -/
theorem phiRev_x2 :
    (phiRev (Mmat 0) (Mmat 1) (Mmat 2) δ0 (fRev 0) x2 : Pic (fRev 0)) =
      ClassGroup.mk0 (mumford0 (fRev 0) (apUp_monic (ck_apNZ 2).2.1).1.ne_zero (apVp 2)) ∧
    apUp 2 ∣ apVp 2 ^ 2 - fRev 0 :=
  phiRev_known (k := 0) x2 (i := 2) (a := 2) (b := 0) (by simp [x2]) rfl rfl ck_tan2 ck_u2 ck_n2
    (apN_ne_zero 2) ck_ent2 (ck_apNZ 2)

/-- `φ(x1) = [⟨U_1, Y - V_1⟩]` on `Y² = fRev_1` (twist 1, `x1` over `(1:1:1)`). -/
theorem phiRev_x1 :
    (phiRev (Mmat 0) (Mmat 1) (Mmat 2) δ1 (fRev 1) x1 : Pic (fRev 1)) =
      ClassGroup.mk0 (mumford0 (fRev 1) (apUp_monic (ck_apNZ 1).2.1).1.ne_zero (apVp 1)) ∧
    apUp 1 ∣ apVp 1 ^ 2 - fRev 1 :=
  phiRev_known (k := 1) x1 (i := 1) (a := 1) (b := 1) (by simp [x1]) rfl rfl ck_tan1 ck_u1 ck_n1
    (apN_ne_zero 1) ck_ent1 (ck_apNZ 1)

/-- `φ(x3) = [⟨U_3, Y - V_3⟩]` on `Y² = fRev_1` (twist 1, `x3` over `(-1:0:1)`). -/
theorem phiRev_x3 :
    (phiRev (Mmat 0) (Mmat 1) (Mmat 2) δ1 (fRev 1) x3 : Pic (fRev 1)) =
      ClassGroup.mk0 (mumford0 (fRev 1) (apUp_monic (ck_apNZ 3).2.1).1.ne_zero (apVp 3)) ∧
    apUp 3 ∣ apVp 3 ^ 2 - fRev 1 :=
  phiRev_known (k := 1) x3 (i := 3) (a := -1) (b := 0) (by simp [x3]) rfl rfl ck_tan3 ck_u3
    ck_n3 (apN_ne_zero 3) ck_ent3 (ck_apNZ 3)

end FurioLombardo.Discharge.M3a.Bruin
