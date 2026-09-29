import FurioLombardo.Discharge.SelmerBasis.SchaeferModel
import FurioLombardo.Discharge.SelmerBasis.SchaeferCertCheck
import FurioLombardo.Discharge.M3a.Concrete

/-!
# The certificates of SchaeferCertCheck.lean as polynomial identities over K21

`affModel_fRev`: the affine model of `fRev k` at `π = piK`, `a = -469` is `F / 4`;
`invModel_f1`: its inverted models are `F2 / 4`; `bez1_f1`, `bez2_f1`, `yz_f1`: the Bezout
identities and the unit certificate in the form asked by `schaefer_global_of_certs`;
integrality of the coefficients after scaling by `14 ^ 31`.
-/
open Polynomial NumberField FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin
open scoped nonZeroDivisors
open FurioLombardo.Discharge.SelmerBasis.Schaefer

namespace FurioLombardo.Discharge.SelmerBasis.Cert

theorem comp_ok (k : Fin 2) : compCheck k 1024 = true := by
  fin_cases k
  exacts [comp_ok_0, comp_ok_1]

theorem bez1_ok (k : Fin 2) : bez1Check k 768 = true := by
  fin_cases k
  exacts [bez1_ok_0, bez1_ok_1]

theorem e_ok (k : Fin 2) : eCheck k 768 = true := by
  fin_cases k
  exacts [e_ok_0, e_ok_1]

theorem rev_ok (k : Fin 2) (i : ℕ) (hi : i ≤ 2) : revCheck k i 768 = true := by
  fin_cases k <;> interval_cases i
  exacts [rev_ok_0_0, rev_ok_0_1, rev_ok_0_2, rev_ok_1_0, rev_ok_1_1, rev_ok_1_2]

theorem bez2_ok (k : Fin 2) (i : ℕ) (hi : i ≤ 2) : bez2Check k i 1024 = true := by
  fin_cases k <;> interval_cases i
  exacts [bez2_ok_0_0, bez2_ok_0_1, bez2_ok_0_2, bez2_ok_1_0, bez2_ok_1_1, bez2_ok_1_2]

theorem yz_ok (k : Fin 2) (i : ℕ) (hi : i ≤ 2) : yzCheck k i 1024 = true := by
  fin_cases k <;> interval_cases i
  exacts [yz_ok_0_0, yz_ok_0_1, yz_ok_0_2, yz_ok_1_0, yz_ok_1_1, yz_ok_1_2]

theorem piK_ne_zero : piK ≠ 0 := by
  have h := evK_eq_zero_of_check _ _ pi_ok
  simp only [evK_sub, evK_mul, evK_lin, evK_int] at h
  intro h0
  rw [piK] at h0
  rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
  norm_num at h

theorem evK_piE : evK piE = piK := rfl

theorem isIntegral_linL (L : List (List ℤ)) (i : ℕ) :
    IsIntegral ℤ (evK ((linL L).getD i (.int 0))) := by
  unfold linL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? with
  | none => simp only [Option.map_none, Option.getD_none, evK_int, Int.cast_zero]; exact isIntegral_zero
  | some a => simp only [Option.map_some, Option.getD_some, evK_lin]; exact isIntegral_zkE a

theorem fourteen_pow_mul_inv : (14 : K21) ^ 31 * (4 : K21)⁻¹ = 49 * 14 ^ 29 := by
  field_simp
  ring

theorem isIntegral_scaled_pQ (L : List (List ℤ)) (j : ℕ) :
    IsIntegral ℤ ((((14 : ℕ) : K21)) ^ 31 * (pQ 4 (linL L)).coeff j) := by
  rw [coeff_pQ, ← mul_assoc, Nat.cast_ofNat, Nat.cast_ofNat, fourteen_pow_mul_inv]
  refine IsIntegral.mul ?_ (isIntegral_linL L j)
  exact IsIntegral.mul (by exact_mod_cast isIntegral_algebraMap (x := (49 : ℤ)))
    (IsIntegral.pow (by exact_mod_cast isIntegral_algebraMap (x := (14 : ℤ))) _)

theorem isIntegral_scaled_pK (L : List (List ℤ)) (j : ℕ) :
    IsIntegral ℤ ((((14 : ℕ) : K21)) ^ 31 * (pK (linL L)).coeff j) := by
  rw [coeff_pK]
  refine IsIntegral.mul (IsIntegral.pow ?_ _) (isIntegral_linL L j)
  exact_mod_cast isIntegral_algebraMap (x := (14 : ℤ))

/-- The affine model of `fRev k` is `F / 4`. -/
theorem affModel_fRev (k : Fin 2) : affModel piK (-469) 6 (fRev k) = pQ 4 (FL k) := by
  have hc := pK_eq_of_eqCheck _ _ _ (comp_ok k)
  rw [pK_smulP, pK_compP, pK_smulP, pK_smulP] at hc
  have h2 : pK [aE, piE] = C (-469 : K21) + C piK * X := by
    simp only [pK_cons, pK_nil, aE, evK_int, evK_piE, mul_zero, add_zero, Int.cast_neg,
      Int.cast_ofNat]
    ring
  rw [h2, evK_int, evK_int, evK_pow, evK_piE] at hc
  have hm : ((m1N k : ℤ) : K21) = 4 := by rw [m1N_eq]; norm_num
  rw [hm] at hc
  have h4 : (C (4 : K21) : K21[X]) ≠ 0 := by rw [Ne, C_eq_zero]; norm_num
  simp only [Int.cast_ofNat] at hc
  have hc' := mul_left_cancel₀ h4 hc
  have hπ6 : piK ^ 6 ≠ 0 := pow_ne_zero _ piK_ne_zero
  rw [affModel, fRev, pQ, pQ, mul_comp, C_comp, hc']
  have e1 : C (piK ^ 6)⁻¹ * C (piK ^ 6) = (1 : K21[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hπ6, C_1]
  push_cast
  linear_combination (C ((4 : K21)⁻¹) * pK (FL ↑k)) * e1

theorem natDegree_f1 (k : Fin 2) : (pQ 4 (FL k)).natDegree = 6 := by
  rw [← affModel_fRev, affModel_natDegree _ piK_ne_zero, fRev_natDegree]

theorem leadingCoeff_f1 (k : Fin 2) :
    (pQ 4 (FL k)).leadingCoeff = (4 : K21)⁻¹ * evK ((FL k).getD 6 (.int 0)) := by
  rw [leadingCoeff, natDegree_f1, coeff_pQ]
  norm_num

/-- The inverted model of `F / 4` at the shift `i` is `F2 / 4`. -/
theorem invModel_f1 (k : Fin 2) (i : ℕ) (hi : i ≤ 2) :
    invModel (i : K21) 6 (pQ 4 (FL k)) = pQ 4 (F2L k i) := by
  have hr := pK_eq_of_eqCheck _ _ _ (rev_ok k i hi)
  have hlen : (compP (FL k) [.int i, .int 1]).length = 6 + 1 := by
    have := compP_FL_length k ⟨i, by omega⟩
    simpa using this
  rw [← reflect_pK 6 _ hlen, pK_compP] at hr
  have h2 : pK [.int (i : ℤ), .int 1] = X + C (i : K21) := by
    simp only [pK_cons, pK_nil, evK_int, mul_zero, add_zero, Int.cast_natCast, Int.cast_one,
      map_one, mul_one]
    ring
  rw [h2] at hr
  rw [pQ, invModel_C_mul, pQ, invModel, hr]

theorem bez1_f1 (k : Fin 2) :
    pK (AL k) * pQ 4 (FL k) + pK (BL k) * derivative (pQ 4 (FL k)) =
      C (zkE (e1L k) * (pQ 4 (FL k)).leadingCoeff) := by
  have hb := pK_eq_of_eqCheck _ _ _ (bez1_ok k)
  rw [pK_addP, pK_mulP, pK_mulP, pK_derivP] at hb
  simp only [pK_cons, pK_nil, evK_mul, evK_lin, mul_zero, add_zero] at hb
  rw [leadingCoeff_f1, pQ, derivative_C_mul]
  have e : C (zkE (e1L ↑k) * ((4 : K21)⁻¹ * evK ((FL ↑k).getD 6 (KE.int 0)))) =
      C ((4 : K21)⁻¹) * C (zkE (e1L ↑k) * evK ((FL ↑k).getD 6 (KE.int 0))) := by
    rw [← C_mul]; ring_nf
  rw [e, ← hb]
  push_cast
  ring

theorem bez2_f1 (k : Fin 2) (i : ℕ) (hi : i ≤ 2) :
    pK (A2L k i) * invModel (i : K21) 6 (pQ 4 (FL k)) +
      pK (B2L k i) * derivative (invModel (i : K21) 6 (pQ 4 (FL k))) =
      C (zkE (R2L k i) / 4) := by
  have hb := pK_eq_of_eqCheck _ _ _ (bez2_ok k i hi)
  rw [pK_addP, pK_mulP, pK_mulP, pK_derivP] at hb
  simp only [pK_cons, pK_nil, evK_lin, mul_zero, add_zero] at hb
  rw [invModel_f1 k i hi, pQ, derivative_C_mul]
  have e : C (zkE (R2L ↑k i) / 4) = C ((4 : K21)⁻¹) * C (zkE (R2L ↑k i)) := by
    rw [← C_mul, div_eq_inv_mul]
  rw [e, ← hb]
  push_cast
  ring

theorem yz_f1 (k : Fin 2) (i : ℕ) (hi : i ≤ 2) :
    zkE (yL k i) * (pQ 4 (FL k)).leadingCoeff +
      zkE (zL k i) * (pQ 4 (FL k)).eval (i : K21) * (zkE (R2L k i) / 4) =
      ((14 : ℕ) : K21) ^ 31 := by
  have h := evK_eq_of_check _ _ _ (yz_ok k i hi)
  simp only [evK_add, evK_mul, evK_lin, evK_int] at h
  have hev : (pQ 4 (FL k)).eval (i : K21) = (4 : K21)⁻¹ * evK ((F2L k i).getD 6 (.int 0)) := by
    rw [← invModel_coeff, invModel_f1 k i hi, coeff_pQ]
    norm_num
  rw [leadingCoeff_f1, hev]
  rw [m1N_eq] at h
  push_cast at h ⊢
  rw [expN] at h
  linear_combination h / 16

end FurioLombardo.Discharge.SelmerBasis.Cert
