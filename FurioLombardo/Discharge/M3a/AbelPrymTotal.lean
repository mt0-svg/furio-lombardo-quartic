import FurioLombardo.Discharge.M3a.AbelPrymExists
import FurioLombardo.Discharge.M3a.AbelPrymCheck2
import FurioLombardo.Discharge.M3a.AbelPrymKnown

/-!
# The concrete Abel-Prym map never takes its fallback value (WP4 of the M3a discharge)

For both twists and every point `x` of `D_δ(K21)` (Bruin's quadrics `Mmat`, `δ = δ k`), the swapped
point has a certificate (`cert_exists_fRev`), so `phiRev x` is the class of Bruin's divisor
(`phiRev_eq_cls`): the value `1` of `AbelPrym.bruinPhi` at points without certificate is never
used over K21. The hypotheses of `AbelPrym.cert_exists`:

* `fRev k` has no root in K21 (`fRev_no_root`): a root would make `d k` a square, by
  `β² - d = fRev γ`;
* `-δ det M1 = c k` is not a square (`lc_not_isSquare`);
* `(r, s) ≠ 0` (`rs_ne_zero`): Bruin's three conics have no common zero over K21
  (`no_common_zero`, certificate `D_j R_j⁴ = Σ_i (D_j a_(j,i)) Q_(i+1)` of AbelPrymCheck2.lean).
-/

open Polynomial Matrix
open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.M1.Vendor.NetOfConics
open FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M3a

namespace FurioLombardo.Discharge.M3a.Bruin

open FurioLombardo.Discharge.M3a.AbelPrym (Cert swapPt phiRev bruinPhi)

theorem qev_Qc (i : Fin 3) (p : Fin 3 → K21) :
    qev (fun m => zkE (QcL i m)) p = Qform i p := rfl

/-- **Bruin's three conics have no common zero over K21.** -/
theorem no_common_zero (p : Fin 3 → K21) (h : ∀ i, Qform i p = 0) : p = 0 := by
  funext j
  have hsum : ∑ i : Fin 3, qev (fun m => zkE (cfL j i m)) p * qev (fun m => zkE (QcL i m)) p =
      0 := by
    simp [qev_Qc, h]
  simp only [qev_mul_qev] at hsum
  rw [Finset.sum_comm] at hsum
  have hc : ∀ μ, ∑ i : Fin 3, conv (fun m => zkE (cfL j i m)) (fun m => zkE (QcL i m)) μ =
      if μ = tgt j then (cfDenN j : K21) else 0 := fun μ => by
    have e := evK_eq_zero_of_check _ _ (ck_cf j μ)
    simp only [cfChk, evK_sub, evK_add, evK_convKE, evK_int, aE, QE, evK_lin] at e
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e ⊢
    split_ifs at e ⊢ <;> push_cast at e <;> linear_combination e
  simp_rw [← Finset.sum_mul, hc, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at hsum
  have hm : m4 p (tgt j) = p j ^ 4 := by fin_cases j <;> rfl
  rw [hm] at hsum
  have hD : (cfDenN j : K21) ≠ 0 := Nat.cast_ne_zero.mpr (ck_cfDen j)
  exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp ((mul_eq_zero.mp hsum).resolve_left hD)

/-- Every point of `D_δ(K21)` has `(r, s) ≠ 0`. -/
theorem rs_ne_zero {δ' : K21} (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ') :
    x.r ≠ 0 ∨ x.s ≠ 0 := by
  by_contra hc
  push Not at hc
  apply x.ne_zero
  apply no_common_zero
  intro i
  rw [← Mmat_quad]
  fin_cases i
  · simpa [hc.1] using x.eq1
  · simpa [hc.1] using x.eq2
  · simpa [hc.2] using x.eq3

/-- `fRev k` has no root in K21. -/
theorem fRev_no_root (k : Fin 2) (u : K21) : (fRev k).eval u ≠ 0 := by
  intro h0
  have h := congrArg (Polynomial.eval u) (β_sq_sub k)
  simp only [eval_sub, eval_pow, eval_C, eval_mul, h0, zero_mul, sub_eq_zero] at h
  exact d_not_isSquare k ⟨(β k).eval u, by rw [← h, pow_two]⟩

/-- **A certificate at every point of `D_δ(K21)`**, for the swapped construction of `phiRev`. -/
theorem cert_exists_fRev (k : Fin 2) (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    Nonempty (Cert (Mmat 2) (Mmat 1) (Mmat 0) (δ k) (fRev k) (swapPt x)) := by
  have hrs : (swapPt x).r ≠ 0 ∨ (swapPt x).s ≠ 0 := by
    rw [AbelPrym.swapPt_r, AbelPrym.swapPt_s]; exact (rs_ne_zero x).symm
  exact AbelPrym.cert_exists (Mmat_symm 2) (Mmat_symm 1) (Mmat_symm 0) two_ne_zero (δ_ne_zero k)
    (fRev_eq_det_swap k) (lc_not_isSquare k) (fRev_no_root k) (swapPt x) hrs

/-- **`phiRev` is the class of Bruin's divisor at every point of `D_δ(K21)`**: the fallback value
`1` is never used. -/
theorem phiRev_eq_cls (k : Fin 2) (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    ∃ c : Cert (Mmat 2) (Mmat 1) (Mmat 0) (δ k) (fRev k) (swapPt x),
      phiRev (Mmat 0) (Mmat 1) (Mmat 2) (δ k) (fRev k) x = c.cls := by
  obtain ⟨c⟩ := cert_exists_fRev k x
  exact ⟨c, AbelPrym.phiRev_eq_of_cert c⟩

end FurioLombardo.Discharge.M3a.Bruin
