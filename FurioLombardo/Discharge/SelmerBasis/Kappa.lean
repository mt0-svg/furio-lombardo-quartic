import FurioLombardo.Discharge.SelmerBasis.AssemblyData
import FurioLombardo.Discharge.SelmerBasis.GlobalGens
import FurioLombardo.Discharge.SelmerBasis.KappaCheck
import FurioLombardo.M1.Descent

/-!
# The relations `κ_t` among the global generators

`κ_t` (`t = 1..15`, data `Assembly.kapRows`, the columns of `SBX_kappa` of
code/selmer-global-bound/sunit_export_data.gp) is the class of the scalar `c_t = M1.gensL t ∈ K21`:
`c_t ∏ gensL^a = y1²` in `L42` and `c_t ∏ gensN^b = y2²` in `N84` (KappaData.lean, written and checked by
code/selmer-assembly/kappa_data.gp; kernel checks in KappaCheck.lean). So `∏ s, gK k s ^ κ_t s = 1` in
`H (fRev k)` for both twists (`GlobalGen.mk_eq_prod_of_components` with `z = 1`, through `psi k`).

* `prod_gK_eq_one_of_checks`: the class of `∏ Pgen^a` is trivial, given the four checks;
* `kappa_rel`: the relations `κ_t`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.Kappa

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.M3a.Genus2
  FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.Tower
  FurioLombardo.Discharge.SelmerBasis.MuTCert FurioLombardo.Discharge.SelmerBasis.GlobalK21
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.M3a.Bruin

/-- The vectors `κ_1, ..., κ_15`. -/
def κK (t : Fin 15) : Fin 82 → ℕ := fun s => if (Assembly.kapRows.getD t 0).testBit s then 1 else 0

/-- **A trivial class from exact square roots**: `c ∏ gensL^a = (y1T / y1D)²` and
`c ∏ gensN^b = (y2T / y2D)²` give `∏ s, gK k s ^ a_s = 1`. -/
theorem prod_gK_eq_one_of_checks (k : Fin 2) {gO : List ℤ} {aT : List ℕ}
    {y1T y2T prodLT prodNT : List (List ℤ)} {y1D y2D bPL bPN bSL bSN : ℕ} (hy1D : y1D ≠ 0)
    (hy2D : y2D ≠ 0) (hbits : ∀ b ∈ aT, b ≤ 1) (hlen : 82 ≤ aT.length)
    (hPL : checkLC bPL (ofL prodLT) (selProdL aT SUnitData.gL) = true)
    (hPN : checkNC bPN (ofN prodNT) (selProdN (aT.drop 29) SUnitData.gN) = true)
    (hSL : checkLC bSL (smulLC (.mul (.int ((y1D ^ 2 : ℕ) : ℤ)) (.lin gO)) (ofL prodLT))
      (mulLC (ofL y1T) (ofL y1T)) = true)
    (hSN : checkNC bSN (smulNC (.mul (.int ((y2D ^ 2 : ℕ) : ℤ)) (.lin gO)) (ofN prodNT))
      (mulNC (ofN y2T) (ofN y2T)) = true)
    (hg : zkE gO ≠ 0) :
    ∏ s : Fin 82, gK k s ^ aT.getD s 0 = 1 := by
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
      Fin.val_castAdd]
  have hPB : ∏ s : Fin 82, aeval betaR (Pgen s) ^ aT.getD s 0 = evN (ofN prodNT) := by
    rw [hP53]
    show ∏ s : Fin (29 + 53), aeval betaR (Pgen s) ^ aT.getD s 0 = _
    rw [Fin.prod_univ_add]
    simp only [Pgen_betaR_left, Pgen_betaR_right, one_pow, Finset.prod_const_one, one_mul,
      Fin.val_natAdd]
  have hPL0 : evL (ofL prodLT) ≠ 0 := by
    rw [hP29]; exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (gensL_ne_zero i)
  have hPN0 : evN (ofN prodNT) ≠ 0 := by
    rw [hP53]; exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (gensN_ne_zero j)
  -- the square identities
  have eL := evL_eq_of_checkLC hSL
  simp only [evL_smulLC, evL_mulLC, evK_mul, evK_int, evK_lin] at eL
  have eN' := evN_eq_of_checkNC hSN
  simp only [evN_smulNC, evN_mulNC, evK_mul, evK_int, evK_lin] at eN'
  set P := evL (ofL prodLT)
  set PN := evN (ofN prodNT)
  set Y := evL (ofL y1T)
  set Y2 := evN (ofN y2T)
  set G := zkE gO
  have hy1D' : (y1D : K21) ≠ 0 := Nat.cast_ne_zero.mpr hy1D
  have hy2D' : (y2D : K21) ≠ 0 := Nat.cast_ne_zero.mpr hy2D
  have hc1 : r (((((y1D ^ 2 : ℕ) : ℤ) : K21)) * G) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (mul_ne_zero (by push_cast; exact pow_ne_zero _ hy1D') hg)
  have hc2 : rN (((((y2D ^ 2 : ℕ) : ℤ) : K21)) * G) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (mul_ne_zero (by push_cast; exact pow_ne_zero _ hy2D') hg)
  have hY : Y ≠ 0 := fun h0 => mul_ne_zero hc1 hPL0 (by rw [eL, h0, mul_zero])
  have hY2 : Y2 ≠ 0 := fun h0 => mul_ne_zero hc2 hPN0 (by rw [eN', h0, mul_zero])
  have hGy1 : (y1D : K21) * G ≠ 0 := mul_ne_zero hy1D' hg
  have hGy2 : (y2D : K21) * G ≠ 0 := mul_ne_zero hy2D' hg
  have hmk := GlobalGen.mk_eq_prod_of_components (psi k) (gKu k) 1 G hg (fun s => aT.getD s 0)
    (r (((y1D : K21) * G)⁻¹) * Y) (rN (((y2D : K21) * G)⁻¹) * Y2)
    (mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hGy1)) hY)
    (mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hGy2)) hY2) ?_ ?_
  · rw [QuotientGroup.mk_one] at hmk
    exact hmk.symm
  · have hs : ∀ s, (psi k (gKu k s : AdjoinRoot (fRev k))).1 = aeval alphaR (Pgen s) := fun s => by
      rw [gKu_coe, psi_mk]
    simp only [Units.val_one, map_one, Prod.fst_one, one_mul, hs, hPA]
    have hc : (((y1D ^ 2 : ℕ) : ℤ) : K21) = (y1D : K21) ^ 2 := by push_cast; ring
    rw [hc] at eL
    calc P = r (G * ((y1D : K21) * G)⁻¹ ^ 2) * (r ((y1D : K21) ^ 2 * G) * P) := by
          rw [← mul_assoc, ← map_mul]
          have h1 : G * ((y1D : K21) * G)⁻¹ ^ 2 * ((y1D : K21) ^ 2 * G) = 1 := by field_simp
          rw [h1, map_one, one_mul]
      _ = r G * (r (((y1D : K21) * G)⁻¹) * Y) ^ 2 := by rw [eL, map_mul, map_pow]; ring
  · have hs : ∀ s, (psi k (gKu k s : AdjoinRoot (fRev k))).2 = aeval betaR (Pgen s) := fun s => by
      rw [gKu_coe, psi_mk]
    simp only [Units.val_one, map_one, Prod.snd_one, one_mul, hs, hPB]
    have hc : (((y2D ^ 2 : ℕ) : ℤ) : K21) = (y2D : K21) ^ 2 := by push_cast; ring
    rw [hc] at eN'
    calc PN = rN (G * ((y2D : K21) * G)⁻¹ ^ 2) * (rN ((y2D : K21) ^ 2 * G) * PN) := by
          rw [← mul_assoc, ← map_mul]
          have h1 : G * ((y2D : K21) * G)⁻¹ ^ 2 * ((y2D : K21) ^ 2 * G) = 1 := by field_simp
          rw [h1, map_one, one_mul]
      _ = rN G * (rN (((y2D : K21) * G)⁻¹) * Y2) ^ 2 := by rw [eN', map_mul, map_pow]; ring

/-- **The classes `κ_t` are trivial.** -/
theorem kappa_rel (k : Fin 2) (t : Fin 15) : ∏ s, gK k s ^ κK t s = 1 := by
  have hbits : ∀ (t : Fin 15) (s : Fin 82), κK t s = (KappaData.aK.getD t []).getD s 0 := by
    decide +kernel
  obtain ⟨hb, hl, h1, h2⟩ := KappaData.ck_shape t t.isLt
  have hg : zkE (FurioLombardo.M1.gensL.getD (t + 1) []) ≠ 0 := by
    have h := gO_ne_zero (t + 1) (by omega)
    intro h0
    exact h (Subtype.ext h0)
  simp only [hbits t]
  exact prod_gK_eq_one_of_checks k h1 h2 hb hl (KappaData.ck_PL t t.isLt) (KappaData.ck_PN t t.isLt)
    (KappaData.ck_SL t t.isLt) (KappaData.ck_SN t t.isLt) hg

end FurioLombardo.Discharge.SelmerBasis.Kappa
