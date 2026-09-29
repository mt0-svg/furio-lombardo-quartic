import FurioLombardo.Discharge.SelmerBasis.TowerFacts
import FurioLombardo.Discharge.SelmerBasis.GlobalSpanGen

/-!
# The certificate for `μ(T)` (data `kapT_k` .. `prodNT_k` of SUnitData.lean, code/selmer-global-bound/mu_t_cert.gp)

`μ(T) = [(q - c h)(T)]` has the components `x₁ = -c h(α) ∈ L42` and `x₂ = q(β) ∈ N84`. With
`κ = kapT / kapTDen`, `y₁ = y1T / y1TDen`, `y₂ = y2T / y2TDen` and the exponent bits `aT`:

* `ck_prodLT_k`, `ck_prodNT_k` (Kronecker base `2^4096`, the products have degree 15 to 17 in the atoms):
  `prodLT = ∏_{s < 29} gensL_s^(a_s)`,
  `prodNT = ∏_{j < 53} gensN_j^(a_(29+j))` (`selProdL`, `selProdN`);
* `ck_muTL_k`: `-(FE k 0) · (D_L⁴ hDen h(α)) · prodLT · kapTDen y1TDen² = 4 hDen D_L⁴ kapT y1T²`;
* `ck_muTN_k`: `(D_N² qDen q(β)) · prodNT · kapTDen y2TDen² = qDen D_N² kapT y2T²`;

so `x₁ ∏ gensL^a = κ y₁²` and `x₂ ∏ gensN^a = κ y₂²` (`compCond_muT`, `CompCond` of
GlobalSpanGen.lean), given that the generators, `h(α)` and `q(β)` are nonzero.
-/

namespace FurioLombardo.Discharge.SelmerBasis.MuTCert

set_option maxRecDepth 100000

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.SelmerBasis.TowerChecks
  FurioLombardo.Discharge.SelmerBasis.TowerFacts FurioLombardo.Discharge.SelmerBasis.GlobalGen

/-! ## Products of selected generators -/

/-- `∏ g_i^(a_i)` for exponent bits `a_i` (the list `g` decides the number of factors). -/
def selProdL : List ℕ → List (List (List ℤ)) → LC
  | b :: a, x :: g => if b = 0 then selProdL a g else mulLC (ofL x) (selProdL a g)
  | _, _ => oneLC

/-- `∏ g_i^(a_i)` in `N84` coordinates. -/
def selProdN : List ℕ → List (List (List ℤ)) → NC
  | b :: a, x :: g => if b = 0 then selProdN a g else mulNC (ofN x) (selProdN a g)
  | _, _ => oneNC

theorem evL_selProdL : ∀ (g : List (List (List ℤ))) (a : List ℕ), g.length ≤ a.length →
    (∀ b ∈ a, b ≤ 1) →
    evL (selProdL a g) = ∏ i : Fin g.length, evL (ofL (g.getD i [])) ^ (a.getD i 0)
  | [], a, _, _ => by cases a <;> simp [selProdL]
  | x :: g, [], hl, _ => by simp at hl
  | x :: g, b :: a, hl, hb => by
    have ih := evL_selProdL g a (by simp at hl; omega) (fun b' hb' => hb b' (by simp [hb']))
    rw [List.length_cons, Fin.prod_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    rw [← ih]
    have hb1 : b ≤ 1 := hb b (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with rfl | rfl
    · simp [selProdL]
    · simp [selProdL]

theorem evN_selProdN : ∀ (g : List (List (List ℤ))) (a : List ℕ), g.length ≤ a.length →
    (∀ b ∈ a, b ≤ 1) →
    evN (selProdN a g) = ∏ i : Fin g.length, evN (ofN (g.getD i [])) ^ (a.getD i 0)
  | [], a, _, _ => by cases a <;> simp [selProdN]
  | x :: g, [], hl, _ => by simp at hl
  | x :: g, b :: a, hl, hb => by
    have ih := evN_selProdN g a (by simp at hl; omega) (fun b' hb' => hb b' (by simp [hb']))
    rw [List.length_cons, Fin.prod_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    rw [← ih]
    have hb1 : b ≤ 1 := hb b (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with rfl | rfl
    · simp [selProdN]
    · simp [selProdN]

theorem gL_length : SUnitData.gL.length = 29 := by decide +kernel

theorem gN_length : SUnitData.gN.length = 53 := by decide +kernel

/-! ## The certificate -/

theorem compCond_of_checks (k : Fin 2) {kapT : List ℤ} {kD : ℕ} {aT : List ℕ}
    {y1T : List (List ℤ)} {y1D : ℕ} {y2T : List (List ℤ)} {y2D : ℕ}
    {prodLT prodNT : List (List ℤ)} (hkD : kD ≠ 0) (hy1D : y1D ≠ 0) (hy2D : y2D ≠ 0)
    (hbits : ∀ b ∈ aT, b ≤ 1) (hlen : 82 ≤ aT.length)
    (hPL : checkLC 4096 (ofL prodLT) (selProdL aT SUnitData.gL) = true)
    (hPN : checkNC 4096 (ofN prodNT) (selProdN (aT.drop 29) SUnitData.gN) = true)
    (hcL : checkLC 1024
      (smulLC (.mul (.int (-((kD * y1D ^ 2 : ℕ) : ℤ))) (FE k 0))
        (mulLC (sumPL SUnitData.alphaDen 4 (hL k) tabA) (ofL prodLT)))
      (smulLC (.mul (.int ((4 * hDenN k * SUnitData.alphaDen ^ 4 : ℕ) : ℤ)) (.lin kapT))
        (mulLC (ofL y1T) (ofL y1T))) = true)
    (hcN : checkNC 1024
      (smulNC (.int ((kD * y2D ^ 2 : ℕ) : ℤ))
        (mulNC (sumPN SUnitData.betaPowDen 2 (qL k) tabB) (ofN prodNT)))
      (smulNC (.mul (.int ((qDenN k * SUnitData.betaPowDen ^ 2 : ℕ) : ℤ)) (.lin kapT))
        (mulNC (ofN y2T) (ofN y2T))) = true)
    (hc : c k ≠ 0) (hH : aeval alphaR (h k) ≠ 0) (hQ : aeval betaR (q k) ≠ 0) (h0L : ∀ i, gensL i ≠ 0)
    (h0N : ∀ j, gensN j ≠ 0) :
    CompCond K21 (aeval alphaR (q k - C (c k) * h k)) (aeval betaR (q k - C (c k) * h k))
      (fun s : Fin 82 => aeval alphaR (Pgen s)) (fun s : Fin 82 => aeval betaR (Pgen s)) := by
  set r := algebraMap K21 L42 with hr
  set rN := algebraMap K21 N84 with hrN
  -- the products of generators
  have hP29 : evL (ofL prodLT) = ∏ i : Fin 29, gensL i ^ aT.getD i 0 := by
    rw [evL_eq_of_checkLC hPL, evL_selProdL SUnitData.gL aT (by rw [gL_length]; omega) hbits,
      gL_length]
    rfl
  have hP53 : evN (ofN prodNT) = ∏ j : Fin 53, gensN j ^ aT.getD (29 + j) 0 := by
    rw [evN_eq_of_checkNC hPN, evN_selProdN SUnitData.gN (aT.drop 29)
      (by rw [gN_length, List.length_drop]; omega) (fun b hb => hbits b (List.mem_of_mem_drop hb)),
      gN_length]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rfl
  have hPA : ∏ s : Fin 82, aeval alphaR (Pgen s) ^ aT.getD s 0 = evL (ofL prodLT) := by
    rw [hP29]
    show ∏ s : Fin (29 + 53), aeval alphaR (Pgen s) ^ aT.getD s 0 = _
    rw [Fin.prod_univ_add]
    simp only [Pgen_alphaR_left, Pgen_alphaR_right, one_pow, Finset.prod_const_one, mul_one,
      Fin.coe_castAdd]
  have hPB : ∏ s : Fin 82, aeval betaR (Pgen s) ^ aT.getD s 0 = evN (ofN prodNT) := by
    rw [hP53]
    show ∏ s : Fin (29 + 53), aeval betaR (Pgen s) ^ aT.getD s 0 = _
    rw [Fin.prod_univ_add]
    simp only [Pgen_betaR_left, Pgen_betaR_right, one_pow, Finset.prod_const_one, one_mul,
      Fin.coe_natAdd]
  have hPL0 : evL (ofL prodLT) ≠ 0 := by
    rw [hP29]; exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (h0L i)
  have hPN0 : evN (ofN prodNT) ≠ 0 := by
    rw [hP53]; exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (h0N j)
  -- the two components
  have hx1 : aeval alphaR (q k - C (c k) * h k) = -(r (c k) * aeval alphaR (h k)) := by
    rw [map_sub, map_mul, aeval_C, aeval_alphaR_q, zero_sub]
  have hx2 : aeval betaR (q k - C (c k) * h k) = aeval betaR (q k) := by
    rw [map_sub, map_mul, aeval_C, aeval_betaR_h, mul_zero, sub_zero]
  have hhk : aeval alphaR (h k) = r ((hDenN k : K21)⁻¹) * aeval alphaR (pK (hL k)) := by
    rw [h, pQ, map_mul, aeval_C]
  have hqk : aeval betaR (q k) = rN ((qDenN k : K21)⁻¹) * aeval betaR (pK (qL k)) := by
    rw [q, pQ, map_mul, aeval_C]
  have hhD : (hDenN k : K21) ≠ 0 := natCast_ne_zero (by fin_cases k <;> decide)
  have hqD : (qDenN k : K21) ≠ 0 := natCast_ne_zero (by fin_cases k <;> decide)
  have hkD' : (kD : K21) ≠ 0 := natCast_ne_zero hkD
  have hy1D' : (y1D : K21) ≠ 0 := natCast_ne_zero hy1D
  have hy2D' : (y2D : K21) ≠ 0 := natCast_ne_zero hy2D
  have hDL : (SUnitData.alphaDen : K21) ≠ 0 := natCast_ne_zero alphaDen_ne_zero
  have hDN : (SUnitData.betaPowDen : K21) ≠ 0 := natCast_ne_zero betaPowDen_ne_zero
  -- the identity in L42
  have sL := evL_sumPL SUnitData.alphaDen alphaR (hL k) 4 tabA 1 (by simp [hL])
    (by simp [hL, tabA]) (fun i hi => by rw [one_mul]; exact tabA_spec i (by simp [hL] at hi; omega))
  have eL := evL_eq_of_checkLC hcL
  simp only [evL_smulLC, evL_mulLC, evK_mul, evK_int, evK_lin, sL, one_mul] at eL
  -- the identity in N84
  have sN := evN_sumPN SUnitData.betaPowDen betaR (qL k) 2 tabB 1 (by simp [qL])
    (by simp [qL, tabB]) (fun i hi => by rw [one_mul]; exact tabB_spec i (by simp [qL] at hi; omega))
  have eN' := evN_eq_of_checkNC hcN
  simp only [evN_smulNC, evN_mulNC, evK_mul, evK_int, evK_lin, sN, one_mul] at eN'
  set H := aeval alphaR (pK (hL k)) with hH'
  set Q' := aeval betaR (pK (qL k)) with hQ'
  set P := evL (ofL prodLT)
  set PN := evN (ofN prodNT)
  set Y := evL (ofL y1T)
  set Y2 := evN (ofN y2T)
  set K := zkE kapT
  set Fk := evK (FE k 0) with hFk
  have hF0 : Fk ≠ 0 := fun h0 => hc (by rw [c, ← hFk, h0, mul_zero])
  have hH0 : H ≠ 0 := fun h0 => hH (by rw [hhk, h0, mul_zero])
  have hQ0 : Q' ≠ 0 := fun h0 => hQ (by rw [hqk, h0, mul_zero])
  have hz1 : ((-((kD * y1D ^ 2 : ℕ) : ℤ) : ℤ) : K21) ≠ 0 := by
    push_cast; exact neg_ne_zero.mpr (mul_ne_zero hkD' (pow_ne_zero _ hy1D'))
  have hzz : (((kD * y2D ^ 2 : ℕ) : ℤ) : K21) ≠ 0 := by
    push_cast; exact mul_ne_zero hkD' (pow_ne_zero _ hy2D')
  have hLHS : r (((-((kD * y1D ^ 2 : ℕ) : ℤ) : ℤ) : K21) * Fk) *
      (r ((SUnitData.alphaDen : K21) ^ 4) * H * P) ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero _).mpr (mul_ne_zero hz1 hF0))
      (mul_ne_zero (mul_ne_zero ((_root_.map_ne_zero _).mpr (pow_ne_zero _ hDL)) hH0) hPL0)
  have hNLHS : rN (((kD * y2D ^ 2 : ℕ) : ℤ) : K21) *
      (rN ((SUnitData.betaPowDen : K21) ^ 2) * Q' * PN) ≠ 0 :=
    mul_ne_zero ((_root_.map_ne_zero _).mpr hzz)
      (mul_ne_zero (mul_ne_zero ((_root_.map_ne_zero _).mpr (pow_ne_zero _ hDN)) hQ0) hPN0)
  have hK0 : K ≠ 0 := fun h0 => hLHS (by rw [eL, h0]; simp)
  have hY1 : Y ≠ 0 := fun h0 => hLHS (by rw [eL, h0]; simp)
  have hY2 : Y2 ≠ 0 := fun h0 => hNLHS (by rw [eN', h0]; simp)
  -- the scaled identities
  have hS : r (4 * hDenN k * (SUnitData.alphaDen : K21) ^ 4 * kD * y1D ^ 2) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (by have := natCast_ne_zero (m := 4) (by decide); rwa [Nat.cast_ofNat] at this) hhD)
      (pow_ne_zero _ hDL)) hkD') (pow_ne_zero _ hy1D'))
  have hS' : rN (qDenN k * (SUnitData.betaPowDen : K21) ^ 2 * kD * y2D ^ 2) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero hqD (pow_ne_zero _ hDN))
      hkD') (pow_ne_zero _ hy2D'))
  have e1 : r (((-((kD * y1D ^ 2 : ℕ) : ℤ) : ℤ) : K21) * Fk) * r ((SUnitData.alphaDen : K21) ^ 4) =
      r (4 * hDenN k * (SUnitData.alphaDen : K21) ^ 4 * kD * y1D ^ 2) *
        r (-(c k * ((hDenN k : K21))⁻¹)) := by
    rw [← map_mul, ← map_mul, c, ← hFk]
    congr 1
    push_cast
    field_simp
  have e2 : r ((((4 * hDenN k * SUnitData.alphaDen ^ 4 : ℕ) : ℤ) : K21) * K) =
      r (4 * hDenN k * (SUnitData.alphaDen : K21) ^ 4 * kD * y1D ^ 2) *
        r (K / kD * ((y1D : K21)⁻¹) ^ 2) := by
    rw [← map_mul]
    congr 1
    push_cast
    field_simp
  have e1' : rN (((kD * y2D ^ 2 : ℕ) : ℤ) : K21) * rN ((SUnitData.betaPowDen : K21) ^ 2) =
      rN (qDenN k * (SUnitData.betaPowDen : K21) ^ 2 * kD * y2D ^ 2) *
        rN (((qDenN k : K21))⁻¹) := by
    rw [← map_mul, ← map_mul]
    congr 1
    push_cast
    field_simp
  have e2' : rN ((((qDenN k * SUnitData.betaPowDen ^ 2 : ℕ) : ℤ) : K21) * K) =
      rN (qDenN k * (SUnitData.betaPowDen : K21) ^ 2 * kD * y2D ^ 2) *
        rN (K / kD * ((y2D : K21)⁻¹) ^ 2) := by
    rw [← map_mul]
    congr 1
    push_cast
    field_simp
  have eL2 : r (4 * hDenN k * (SUnitData.alphaDen : K21) ^ 4 * kD * y1D ^ 2) *
      (r (-(c k * ((hDenN k : K21))⁻¹)) * (H * P)) =
      r (4 * hDenN k * (SUnitData.alphaDen : K21) ^ 4 * kD * y1D ^ 2) *
        (r (K / kD * ((y1D : K21)⁻¹) ^ 2) * (Y * Y)) := by
    linear_combination eL - (H * P) * e1 + (Y * Y) * e2
  have eN2 : rN (qDenN k * (SUnitData.betaPowDen : K21) ^ 2 * kD * y2D ^ 2) *
      (rN (((qDenN k : K21))⁻¹) * (Q' * PN)) =
      rN (qDenN k * (SUnitData.betaPowDen : K21) ^ 2 * kD * y2D ^ 2) *
        (rN (K / kD * ((y2D : K21)⁻¹) ^ 2) * (Y2 * Y2)) := by
    linear_combination eN' - (Q' * PN) * e1' + (Y2 * Y2) * e2'
  have eL3 := mul_left_cancel₀ hS eL2
  have eN3 := mul_left_cancel₀ hS' eN2
  rw [map_neg, map_mul, map_mul, map_pow] at eL3
  rw [map_mul, map_pow] at eN3
  refine ⟨K / kD, div_ne_zero hK0 hkD', fun s => aT.getD s 0, r ((y1D : K21)⁻¹) * Y,
    rN ((y2D : K21)⁻¹) * Y2,
    mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hy1D')) hY1,
    mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hy2D')) hY2, ?_, ?_⟩
  · rw [hPA, hx1, hhk]
    linear_combination eL3
  · rw [hPB, hx2, hqk]
    linear_combination eN3

theorem ck_prodLT_0 : checkLC 4096 (ofL SUnitData.prodLT_0) (selProdL SUnitData.aT_0 SUnitData.gL) = true := by
  decide +kernel

theorem ck_prodNT_0 :
    checkNC 4096 (ofN SUnitData.prodNT_0) (selProdN (SUnitData.aT_0.drop 29) SUnitData.gN) = true := by
  decide +kernel

theorem ck_muTL_0 : checkLC 1024
    (smulLC (.mul (.int (-((SUnitData.kapTDen_0 * SUnitData.y1TDen_0 ^ 2 : ℕ) : ℤ))) (FE 0 0))
      (mulLC (sumPL SUnitData.alphaDen 4 (hL 0) tabA) (ofL SUnitData.prodLT_0)))
    (smulLC (.mul (.int ((4 * hDenN 0 * SUnitData.alphaDen ^ 4 : ℕ) : ℤ)) (.lin SUnitData.kapT_0))
      (mulLC (ofL SUnitData.y1T_0) (ofL SUnitData.y1T_0))) = true := by
  decide +kernel

theorem ck_muTN_0 : checkNC 1024
    (smulNC (.int ((SUnitData.kapTDen_0 * SUnitData.y2TDen_0 ^ 2 : ℕ) : ℤ))
      (mulNC (sumPN SUnitData.betaPowDen 2 (qL 0) tabB) (ofN SUnitData.prodNT_0)))
    (smulNC (.mul (.int ((qDenN 0 * SUnitData.betaPowDen ^ 2 : ℕ) : ℤ)) (.lin SUnitData.kapT_0))
      (mulNC (ofN SUnitData.y2T_0) (ofN SUnitData.y2T_0))) = true := by
  decide +kernel

theorem aT_bits_0 : ∀ b ∈ SUnitData.aT_0, b ≤ 1 := by decide +kernel

theorem aT_length_0 : 82 ≤ SUnitData.aT_0.length := by decide +kernel

theorem ck_prodLT_1 : checkLC 4096 (ofL SUnitData.prodLT_1) (selProdL SUnitData.aT_1 SUnitData.gL) = true := by
  decide +kernel

theorem ck_prodNT_1 :
    checkNC 4096 (ofN SUnitData.prodNT_1) (selProdN (SUnitData.aT_1.drop 29) SUnitData.gN) = true := by
  decide +kernel

theorem ck_muTL_1 : checkLC 1024
    (smulLC (.mul (.int (-((SUnitData.kapTDen_1 * SUnitData.y1TDen_1 ^ 2 : ℕ) : ℤ))) (FE 1 0))
      (mulLC (sumPL SUnitData.alphaDen 4 (hL 1) tabA) (ofL SUnitData.prodLT_1)))
    (smulLC (.mul (.int ((4 * hDenN 1 * SUnitData.alphaDen ^ 4 : ℕ) : ℤ)) (.lin SUnitData.kapT_1))
      (mulLC (ofL SUnitData.y1T_1) (ofL SUnitData.y1T_1))) = true := by
  decide +kernel

theorem ck_muTN_1 : checkNC 1024
    (smulNC (.int ((SUnitData.kapTDen_1 * SUnitData.y2TDen_1 ^ 2 : ℕ) : ℤ))
      (mulNC (sumPN SUnitData.betaPowDen 2 (qL 1) tabB) (ofN SUnitData.prodNT_1)))
    (smulNC (.mul (.int ((qDenN 1 * SUnitData.betaPowDen ^ 2 : ℕ) : ℤ)) (.lin SUnitData.kapT_1))
      (mulNC (ofN SUnitData.y2T_1) (ofN SUnitData.y2T_1))) = true := by
  decide +kernel

theorem aT_bits_1 : ∀ b ∈ SUnitData.aT_1, b ≤ 1 := by decide +kernel

theorem aT_length_1 : 82 ≤ SUnitData.aT_1.length := by decide +kernel

/-- **The certificate for `μ(T)`**, given that `c k`, `h(α)`, `q(β)` and the generators are
nonzero. -/
theorem compCond_muT (k : Fin 2) (hc : c k ≠ 0) (hH : aeval alphaR (h k) ≠ 0)
    (hQ : aeval betaR (q k) ≠ 0) (h0L : ∀ i, gensL i ≠ 0) (h0N : ∀ j, gensN j ≠ 0) :
    CompCond K21 (aeval alphaR (q k - C (c k) * h k)) (aeval betaR (q k - C (c k) * h k))
      (fun s : Fin 82 => aeval alphaR (Pgen s)) (fun s : Fin 82 => aeval betaR (Pgen s)) := by
  fin_cases k
  · exact compCond_of_checks 0 (by decide) (by decide) (by decide) aT_bits_0 aT_length_0
      ck_prodLT_0 ck_prodNT_0 ck_muTL_0 ck_muTN_0 hc hH hQ h0L h0N
  · exact compCond_of_checks 1 (by decide) (by decide) (by decide) aT_bits_1 aT_length_1
      ck_prodLT_1 ck_prodNT_1 ck_muTL_1 ck_muTN_1 hc hH hQ h0L h0N

end FurioLombardo.Discharge.SelmerBasis.MuTCert
