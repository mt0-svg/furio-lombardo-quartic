import FurioLombardo.Discharge.M3a.ConcreteCheck
import FurioLombardo.M3a.Sections

/-!
# The concrete objects of the route over K21 (WP2 of the M3a discharge)

Definitions in ConcreteDefs.lean, kernel checks in ConcreteCheck.lean. For the twists
`k : Fin 2` (`δ0 = δ 0` with the known points `P0 = (0:0:1)`, `P2 = (2:0:1)`; `δ1 = δ 1` with
`P1 = (1:1:1)`, `P3 = (-1:0:1)`):

* `Mmat_quad`: `p ⬝ᵥ (Mmat i *ᵥ p)` is Bruin's quadric `Q_(i+1)` with its six coefficients;
* `fδ_eq_det`: `f_k = -δ_k det(M1 + 2t M2 + t² M3)`; `fRev_eq_reverse`: `fRev_k` is its reverse;
* `fRev_eq_mul`: `fRev_k = C (c k) * q k * h k`, `q k` monic of degree 2 dividing `fRev k`, `h k`
  monic of degree 4;
* `goodSextic_fRev` (instance): lane M3a's `GoodSextic (fRev k)`: separable (Bezout certificate),
  degree 6, leading coefficient `c k` not a square in K21 (non residue at a degree one prime);
* `goodSextic_fRev_map`: `GoodSextic ((fRev k).map σ)` for every field homomorphism `σ` for which
  `σ (c k)` is not a square;
* `d_not_isSquare`, `β_sq_sub`, `d_isSquare_adjoinRoot`: `d k = disc (q k)` is not a square in K21
  but is a square in `K21[T]/(fRev k)`: `β² - d = fRev · γ`;
* `x0`, `x2 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0`, `x1`, `x3 : ... δ1`: the known lifts, with
  `Over` proofs.
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open Polynomial Matrix NumberField FurioLombardo.M1 FurioLombardo.M1.Kron
  FurioLombardo.Discharge.M3a FurioLombardo.M3a FurioLombardo.M3a.Genus2

/-! ## Deliverable 1: the matrices of Bruin's quadrics -/

/-- `p ⬝ᵥ (Mmat i *ᵥ p) = Q_(i+1)(p)`. -/
theorem Mmat_quad (i : Fin 3) (p : Fin 3 → K21) : p ⬝ᵥ (Mmat i *ᵥ p) = Qform i p := by
  simp [Mmat, Qform, dotProduct, mulVec, Fin.sum_univ_three]
  ring

theorem Mmat_symm (i : Fin 3) : (Mmat i).transpose = Mmat i := by
  ext a b; fin_cases a <;> fin_cases b <;> rfl

/-! ## Deliverable 2: `f_δ` and its reverse -/

theorem evK_NE (i : Fin 3) (a b : Fin 3) : evK (NE i a b) = 2 * Mmat i a b := by
  fin_cases a <;> fin_cases b <;> simp [NE, idx, Mmat, Qc] <;> ring

theorem pK_NP (a b : Fin 3) : pK (NP a b) = 2 * Mt a b := by
  simp only [NP, pK_cons, pK_nil, evK_mul, evK_int, evK_NE, Mt, Matrix.of_apply, map_mul]
  simp only [Int.cast_ofNat, map_ofNat]
  ring

theorem pK_detP (E : Fin 3 → Fin 3 → List KE) :
    pK (detP E) = (Matrix.of fun a b => pK (E a b)).det := by
  rw [det_fin_three]
  simp only [detP, pK_addP, pK_subP, pK_mulP, Matrix.of_apply]

theorem pK_detLhs_eq (k : Fin 2) : pK (detLhs k) = pK (detRhs k) := by
  fin_cases k
  · exact pK_eq_of_eqCheck _ _ _ ck_det0
  · exact pK_eq_of_eqCheck _ _ _ ck_det1

/-- `f_k = -δ_k det(M1 + 2t M2 + t² M3)`. -/
theorem fδ_eq_det (k : Fin 2) : fδ k = -C (δ k) * Mt.det := by
  have hck := pK_detLhs_eq k
  have h2 : (Matrix.of fun a b => pK (NP a b)) = (2 : K21[X]) • Mt := by
    ext a b; simp [pK_NP]
  rw [detLhs, detRhs, pK_smulP, pK_smulP, pK_detP, h2, det_smul] at hck
  simp only [evK_int, evK_mul, evK_lin, Fintype.card_fin, Int.cast_ofNat, Int.cast_neg,
    Int.cast_one, map_ofNat, map_mul, map_neg, map_one] at hck
  have hP : pK (fdeltaL k) = 4 * (-C (δ k) * Mt.det) := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : K21[X]) ≠ 0)
    rw [hck]
    change -1 * C (δ k) * (2 ^ 3 * Mt.det) = 2 * (4 * (-C (δ k) * Mt.det))
    ring
  rw [fδ, pQ, hP, ← mul_assoc, show (4 : K21[X]) = C ((4 : ℕ) : K21) by rw [C_eq_natCast, Nat.cast_ofNat], ← map_mul,
    inv_mul_cancel₀ (natCast_ne_zero (by norm_num)), map_one, one_mul]

/-- The same, with the matrix `M1 + 2t M2 + t² M3` written as a combination of matrices. -/
theorem Mt_eq : Mt = (Mmat 0).map C + (2 * X : K21[X]) • (Mmat 1).map C +
    (X ^ 2 : K21[X]) • (Mmat 2).map C := by
  ext a b; simp [Mt]

theorem FE6_ne_zero (k : Fin 2) : evK (FE k 6) ≠ 0 := by
  fin_cases k
  · exact zkE_ne_zero_of_res (2 : ZMod 3) ck_root3 2 ck_DB3 2 ck_Dz3 _ ck_resF6.1
  · exact zkE_ne_zero_of_res (2 : ZMod 3) ck_root3 2 ck_DB3 2 ck_Dz3 _ ck_resF6.2

theorem fδ_natDegree (k : Fin 2) : (fδ k).natDegree = 6 :=
  natDegree_pQ (by norm_num) rfl (FE6_ne_zero k)

/-- `fRev_k(s) = s⁶ f_k(1/s)`: the reverse of `f_k`. -/
theorem fRev_eq_reverse (k : Fin 2) : fRev k = (fδ k).reverse := by
  rw [reverse, fδ_natDegree]
  ext i
  rw [coeff_reflect, fRev, fδ, coeff_pQ, coeff_pQ]
  rcases Nat.lt_or_ge i 7 with hi | hi
  · rw [revAt_le (by omega)]
    interval_cases i <;> rfl
  · rw [revAt_eq_self_of_lt (by omega), List.getD_eq_default _ _ (by simp [frevL]; omega),
      List.getD_eq_default _ _ (by simp [fdeltaL]; omega)]

/-! ## Deliverable 3: the factorization `fRev = c q h` -/

theorem q_monic_natDegree (k : Fin 2) : (q k).Monic ∧ (q k).natDegree = 2 :=
  monic_pQ (m := qDenN k) (by fin_cases k <;> simp [ck_dens.1, ck_dens.2.1]) rfl rfl

theorem q_monic (k : Fin 2) : (q k).Monic := (q_monic_natDegree k).1

theorem q_natDegree (k : Fin 2) : (q k).natDegree = 2 := (q_monic_natDegree k).2

theorem h_monic_natDegree (k : Fin 2) : (h k).Monic ∧ (h k).natDegree = 4 :=
  monic_pQ (m := hDenN k) (by fin_cases k <;> simp [ck_dens.2.2.1, ck_dens.2.2.2.1]) rfl rfl

theorem h_monic (k : Fin 2) : (h k).Monic := (h_monic_natDegree k).1

theorem h_natDegree (k : Fin 2) : (h k).natDegree = 4 := (h_monic_natDegree k).2

theorem pK_facLhs_eq (k : Fin 2) : pK (facLhs k) = pK (facRhs k) := by
  fin_cases k
  · exact pK_eq_of_eqCheck _ _ _ ck_fac0
  · exact pK_eq_of_eqCheck _ _ _ ck_fac1

/-- `fRev_k = c_k q_k h_k`. -/
theorem fRev_eq_mul (k : Fin 2) : fRev k = C (c k) * q k * h k := by
  have hq : qDenN k ≠ 0 := by fin_cases k <;> simp [ck_dens.1, ck_dens.2.1]
  have hh : hDenN k ≠ 0 := by fin_cases k <;> simp [ck_dens.2.2.1, ck_dens.2.2.2.1]
  have hc : C (c k) = pQ 4 [FE k 0] := by
    rw [← C_eq_pQ, c, Nat.cast_ofNat]
  rw [hc, q, h, pQ_mul, pQ_mul, fRev]
  exact pQ_eq_of (by norm_num) (by positivity) (pK_facLhs_eq k)

theorem q_dvd_fRev (k : Fin 2) : q k ∣ fRev k :=
  ⟨C (c k) * h k, by rw [fRev_eq_mul]; ring⟩

theorem h_dvd_fRev (k : Fin 2) : h k ∣ fRev k :=
  ⟨C (c k) * q k, by rw [fRev_eq_mul]; ring⟩

/-! ## Deliverable 4: `GoodSextic (fRev k)` -/

theorem evK_FE0_not_isSquare (k : Fin 2) : ¬ IsSquare (evK (FE k 0)) := by
  fin_cases k
  · exact not_isSquare_zkE_of_res (11 : ZMod 13) ck_root13 11 ck_DB13 1 ck_Dz13 _ ck_resLc0
  · exact not_isSquare_zkE_of_res (5 : ZMod 23) ck_root23 12 ck_DB23 4 ck_Dz23 _ ck_resLc1

/-- The leading coefficient `c_k = f_k(0)` of `fRev_k` is not a square in K21. -/
theorem c_not_isSquare (k : Fin 2) : ¬ IsSquare (c k) := by
  rw [c, show (4 : K21) = 2 ^ 2 by norm_num]
  exact not_isSquare_inv_sq_mul two_ne_zero (evK_FE0_not_isSquare k)

theorem evK_FE0_ne_zero (k : Fin 2) : evK (FE k 0) ≠ 0 := fun h0 =>
  evK_FE0_not_isSquare k ⟨0, by rw [h0, mul_zero]⟩

theorem fRev_natDegree (k : Fin 2) : (fRev k).natDegree = 6 :=
  natDegree_pQ (by norm_num) rfl (evK_FE0_ne_zero k)

theorem fRev_leadingCoeff (k : Fin 2) : (fRev k).leadingCoeff = c k := by
  rw [fRev, leadingCoeff_pQ (m := 4) (l := frevL k) (n := 6) (by norm_num) rfl (evK_FE0_ne_zero k), c,
    Nat.cast_ofNat]
  rfl

theorem pK_bezLhs_eq (k : Fin 2) : pK (bezLhs k) = pK [.int (bezMZ k)] := by
  fin_cases k
  · exact pK_eq_of_eqCheck _ _ _ ck_bez0
  · exact pK_eq_of_eqCheck _ _ _ ck_bez1

/-- `fRev_k` is separable: `(4 A / m) fRev + (4 B / m) fRev' = 1`. -/
theorem fRev_separable (k : Fin 2) : (fRev k).Separable := by
  have hck := pK_bezLhs_eq k
  rw [bezLhs, pK_addP, pK_mulP, pK_mulP, pK_derivP] at hck
  simp only [pK_cons, evK_int, pK_nil, mul_zero, add_zero] at hck
  have hm : (bezMZ k : K21) ≠ 0 :=
    Int.cast_ne_zero.mpr (by fin_cases k; exacts [ck_bezM.1, ck_bezM.2])
  rw [separable_def]
  refine ⟨C (4 * (bezMZ k : K21)⁻¹) * pK (bezAL k), C (4 * (bezMZ k : K21)⁻¹) * pK (bezBL k), ?_⟩
  rw [fRev, pQ, derivative_C_mul]
  calc C (4 * (bezMZ k : K21)⁻¹) * pK (bezAL k) * (C ((4 : ℕ) : K21)⁻¹ * pK (frevL k)) +
        C (4 * (bezMZ k : K21)⁻¹) * pK (bezBL k) * (C ((4 : ℕ) : K21)⁻¹ * derivative (pK (frevL k)))
      = C (4 * (bezMZ k : K21)⁻¹ * ((4 : ℕ) : K21)⁻¹) *
          (pK (bezAL k) * pK (frevL k) + pK (bezBL k) * derivative (pK (frevL k))) := by
        rw [map_mul C (4 * (bezMZ k : K21)⁻¹)]; ring
    _ = 1 := by
        rw [hck, ← map_mul, ← map_one C]
        congr 1
        rw [Nat.cast_ofNat]
        field_simp

/-- **Lane M3a's standing hypotheses for the reversed Prym sextics.** -/
instance goodSextic_fRev (k : Fin 2) : GoodSextic (fRev k) :=
  goodSextic_of (fRev_separable k) (fRev_natDegree k)
    (by rw [fRev_leadingCoeff]; exact c_not_isSquare k) two_ne_zero

/-! ## Deliverable 5: base change -/

/-- `GoodSextic ((fRev k).map σ)` as soon as the image of the leading coefficient is not a
square. For `σ : K21 → k_v` at the place `v` above 2 with `e = 3` this is the local fact
`f_k(0)` non square at `v` (code/genus2-curves/ideal_class_model_check.out), proved as `lead_Kv` (LocalLead.lean). -/
theorem goodSextic_fRev_map {kv : Type*} [Field kv] (σ : K21 →+* kv) (k : Fin 2)
    (hσ : ¬ IsSquare (σ (fRev k).leadingCoeff)) : GoodSextic ((fRev k).map σ) :=
  goodSextic_map σ (fRev_separable k) (fRev_natDegree k) two_ne_zero hσ

/-! ## Deliverable 6: the data of the `δ(-1) = 0` criterion for (K1) -/

theorem d_eq (k : Fin 2) : d k = ((qDenN k * qDenN k : ℕ) : K21)⁻¹ * zkE (dnL k) := by
  have hck : zkE (dnL k) = evK (dnRhs k) := by
    fin_cases k
    · exact evK_eq_of_check _ _ _ ck_dn0
    · exact evK_eq_of_check _ _ _ ck_dn1
  have hq : (qDenN k : K21) ≠ 0 :=
    natCast_ne_zero (by fin_cases k <;> simp [ck_dens.1, ck_dens.2.1])
  rw [d, q, coeff_pQ, coeff_pQ, hck]
  simp only [qL, List.getD_cons_zero, List.getD_cons_succ, dnRhs, evK_sub, evK_mul, evK_int]
  push_cast
  field_simp

/-- `d_k = disc(q_k)` is not a square in K21. -/
theorem d_not_isSquare (k : Fin 2) : ¬ IsSquare (d k) := by
  have hq : (qDenN k : K21) ≠ 0 :=
    natCast_ne_zero (by fin_cases k <;> simp [ck_dens.1, ck_dens.2.1])
  rw [d_eq, Nat.cast_mul, ← pow_two]
  refine not_isSquare_inv_sq_mul hq ?_
  fin_cases k
  · exact not_isSquare_zkE_of_res (11 : ZMod 13) ck_root13 11 ck_DB13 1 ck_Dz13 _ ck_resD0
  · exact not_isSquare_zkE_of_res (11 : ZMod 13) ck_root13 11 ck_DB13 1 ck_Dz13 _ ck_resD1

theorem pK_sqLhs_eq (k : Fin 2) : pK (sqLhs k) = pK (sqRhs k) := by
  fin_cases k
  · exact pK_eq_of_eqCheck _ _ _ ck_sq0
  · exact pK_eq_of_eqCheck _ _ _ ck_sq1

/-- `β_k² - d_k = fRev_k γ_k`: `d_k` is a square modulo `fRev_k`. -/
theorem β_sq_sub (k : Fin 2) : β k ^ 2 - C (d k) = fRev k * γ k := by
  have hq : qDenN k ≠ 0 := by fin_cases k <;> simp [ck_dens.1, ck_dens.2.1]
  have hb : betaDenN k ≠ 0 := by fin_cases k <;> simp [ck_dens.2.2.2.2.1, ck_dens.2.2.2.2.2.1]
  have hg : gamDenN k ≠ 0 := by
    fin_cases k <;> simp [ck_dens.2.2.2.2.2.2.1, ck_dens.2.2.2.2.2.2.2]
  have hd : C (d k) = pQ (qDenN k * qDenN k) [.lin (dnL k)] := by
    rw [d_eq, ← C_eq_pQ]; rfl
  rw [hd, β, pQ_sq, pQ_sub (Nat.mul_ne_zero hb hb) (Nat.mul_ne_zero hq hq), fRev, γ, pQ_mul]
  exact pQ_eq_of (Nat.mul_ne_zero (Nat.mul_ne_zero hb hb) (Nat.mul_ne_zero hq hq))
    (Nat.mul_ne_zero (by norm_num) hg) (pK_sqLhs_eq k)

theorem β_natDegree_le (k : Fin 2) : (β k).natDegree ≤ 5 := by
  have := natDegree_pQ_le (betaDenN k) (betaL k)
  have hl : (betaL k).length = 6 := by
    fin_cases k
    · exact ck_lengths.1
    · exact ck_lengths.2.1
  rw [hl] at this; exact this

theorem γ_natDegree_le (k : Fin 2) : (γ k).natDegree ≤ 4 := by
  have := natDegree_pQ_le (gamDenN k) (gamL k)
  have hl : (gamL k).length = 5 := by
    fin_cases k
    · exact ck_lengths.2.2.1
    · exact ck_lengths.2.2.2
  rw [hl] at this; exact this

/-- `d_k` is a square in the étale algebra `K21[T]/(fRev_k)`. -/
theorem d_isSquare_adjoinRoot (k : Fin 2) :
    IsSquare (AdjoinRoot.of (fRev k) (d k)) := by
  refine ⟨AdjoinRoot.mk (fRev k) (β k), ?_⟩
  rw [← AdjoinRoot.mk_C, ← map_mul, AdjoinRoot.mk_eq_mk]
  exact ⟨-γ k, by rw [← pow_two, mul_neg, ← β_sq_sub]; ring⟩

/-- `d_k` is a square modulo the quartic factor `h_k`. -/
theorem h_dvd_β_sq_sub (k : Fin 2) : h k ∣ β k ^ 2 - C (d k) := by
  rw [β_sq_sub]; exact (h_dvd_fRev k).mul_right _

/-! ## Deliverable 7: the known lifts -/

theorem evK_qformE (i : Fin 3) (a b c : ℤ) :
    evK (qformE i a b c) = Qform i ![(a : K21), (b : K21), (c : K21)] := by
  simp [qformE, Qform, Qc]
  ring

theorem lift_eqs {i : ℕ} (k : Fin 2) {a b c : ℤ} {K : ℕ}
    (hck : (liftEqs i k a b c).all (checkK K) = true) :
    Qform 0 ![(a : K21), (b : K21), (c : K21)] = δ k * zkE (liftR i) ^ 2 ∧
    Qform 1 ![(a : K21), (b : K21), (c : K21)] = δ k * (zkE (liftR i) * zkE (liftS i)) ∧
    Qform 2 ![(a : K21), (b : K21), (c : K21)] = δ k * zkE (liftS i) ^ 2 := by
  simp only [liftEqs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hck
  obtain ⟨h1, h2, h3⟩ := hck
  have e1 := evK_eq_of_check _ _ _ h1
  have e2 := evK_eq_of_check _ _ _ h2
  have e3 := evK_eq_of_check _ _ _ h3
  rw [evK_qformE] at e1 e2 e3
  simp only [evK_mul, evK_lin] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, pow_two]; rfl
  · rw [e2]; rfl
  · rw [e3, pow_two]; rfl

/-- The lift of `P0 = (0:0:1)` to `D_δ0` (`r = 0`: `Q1(P0) = Q2(P0) = 0`). -/
noncomputable def x0 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 where
  p := ![0, 0, 1]
  r := zkE (liftR 0)
  s := zkE (liftS 0)
  ne_zero := fun h0 => by simpa using congrFun h0 2
  eq1 := by rw [Mmat_quad]; simpa using (lift_eqs 0 ck_lift0).1
  eq2 := by rw [Mmat_quad]; simpa using (lift_eqs 0 ck_lift0).2.1
  eq3 := by rw [Mmat_quad]; simpa using (lift_eqs 0 ck_lift0).2.2

/-- The lift of `P2 = (2:0:1)` to `D_δ0`. -/
noncomputable def x2 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 where
  p := ![2, 0, 1]
  r := zkE (liftR 2)
  s := zkE (liftS 2)
  ne_zero := fun h0 => by simpa using congrFun h0 2
  eq1 := by rw [Mmat_quad]; simpa using (lift_eqs 0 ck_lift2).1
  eq2 := by rw [Mmat_quad]; simpa using (lift_eqs 0 ck_lift2).2.1
  eq3 := by rw [Mmat_quad]; simpa using (lift_eqs 0 ck_lift2).2.2

/-- The lift of `P1 = (1:1:1)` to `D_δ1` (`s = 0`: `Q2(P1) = Q3(P1) = 0`). -/
noncomputable def x1 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1 where
  p := ![1, 1, 1]
  r := zkE (liftR 1)
  s := zkE (liftS 1)
  ne_zero := fun h0 => by simpa using congrFun h0 2
  eq1 := by rw [Mmat_quad]; simpa using (lift_eqs 1 ck_lift1).1
  eq2 := by rw [Mmat_quad]; simpa using (lift_eqs 1 ck_lift1).2.1
  eq3 := by rw [Mmat_quad]; simpa using (lift_eqs 1 ck_lift1).2.2

/-- The lift of `P3 = (-1:0:1)` to `D_δ1`. -/
noncomputable def x3 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1 where
  p := ![-1, 0, 1]
  r := zkE (liftR 3)
  s := zkE (liftS 3)
  ne_zero := fun h0 => by simpa using congrFun h0 2
  eq1 := by rw [Mmat_quad]; simpa using (lift_eqs 1 ck_lift3).1
  eq2 := by rw [Mmat_quad]; simpa using (lift_eqs 1 ck_lift3).2.1
  eq3 := by rw [Mmat_quad]; simpa using (lift_eqs 1 ck_lift3).2.2

theorem x0_over : x0.Over 0 0 1 := ⟨1, one_ne_zero, by ext j; fin_cases j <;> simp [x0]⟩

theorem x2_over : x2.Over 2 0 1 := ⟨1, one_ne_zero, by ext j; fin_cases j <;> simp [x2]⟩

theorem x1_over : x1.Over 1 1 1 := ⟨1, one_ne_zero, by ext j; fin_cases j <;> simp [x1]⟩

theorem x3_over : x3.Over (-1) 0 1 := ⟨1, one_ne_zero, by ext j; fin_cases j <;> simp [x3]⟩

end FurioLombardo.Discharge.M3a.Bruin
