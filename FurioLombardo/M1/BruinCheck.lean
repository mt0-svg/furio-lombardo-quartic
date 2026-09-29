import FurioLombardo.M1.Conics
import FurioLombardo.M1.Gens
import FurioLombardo.M1.DataBruin

/-!
# The Bruin data of `C` over `K21`, checked by the kernel

* `qC i m`: coefficient of monomial `m` (on x², xy, xz, y², yz, z²) of the conic `Q_(i+1)`.
* `bruin_O`: `Q1 Q3 - Q2² = cB F` in `𝓞 K21` (15 coefficient identities, `ck_bruin`).
* `coeffs_dJ_qC`: the coefficients of `∂J/∂x_l`, `J` the Jacobian cubic of the net (`ck_dJ`).
* `sum_N_six`: `N M = cS I` for the six matrix `M` (rows `Q1, Q2, Q3, ∂J/∂x, ∂J/∂y, ∂J/∂z`), with
  `cS = 2^13 7^13 pi3^12 pi439^12` (`ck_N`, `ck_cS`).
-/

namespace FurioLombardo.M1

open Kron Vendor.NetOfConics NumberField

/-- zk coordinates of the coefficient `m` of `Q_(i+1)`. -/
def qcA (i m : ℕ) : List ℤ := (qcL.getD i []).getD m []

/-- zk coordinates of the coefficient `m` of `∂J/∂x_l`. -/
def dJA (l m : ℕ) : List ℤ := (dJL.getD l []).getD m []

/-- zk coordinates of `N i j`. -/
def nA (i j : ℕ) : List ℤ := (nL.getD i []).getD j []

/-- zk coordinates of the six matrix. -/
def sixA (r m : ℕ) : List ℤ := if r < 3 then qcA r m else dJA (r - 3) m

/-- The conics as expressions. -/
def qKE : Fin 3 → Fin 6 → KE := fun i m => .lin (qcA i m)

/-- The conics over `𝓞 K21`. -/
noncomputable def qC : Fin 3 → Fin 6 → 𝓞 K21 := fun i m => zkO (qcA i m)

/-- `cB` in `𝓞 K21`. -/
noncomputable def cBO : 𝓞 K21 := zkO cBL

/-! ## Kernel checks -/

/-- Coefficient `μ` of `Q1 Q3 - Q2² - cB F`. -/
def bruinKE (μ : Fin 15) : KE :=
  .sub (.sub (convKE (qKE 0) (qKE 2) μ) (convKE (qKE 1) (qKE 1) μ)) (.mul (.lin cBL) (.int (fcoef μ)))

theorem ck_bruin : (List.finRange 15).all (fun μ => checkK 1024 (bruinKE μ)) = true := by
  decide +kernel

theorem ck_dJ : (List.finRange 3).all (fun l => (List.finRange 6).all fun m =>
    checkK 1024 (.sub (coeffsKE (dJKE qKE l) m) (.lin (dJA l m)))) = true := by
  decide +kernel

/-- `cS = 2^13 7^13 pi3^12 pi439^12` as an expression. -/
def cSKE : KE :=
  .mul (.mul (.mul ((KE.int 2).pow 13) ((KE.int 7).pow 13)) ((gE 16).pow 12)) ((gE 17).pow 12)

theorem ck_cS : checkK 8192 (.sub (.lin cSL) cSKE) = true := by decide +kernel

/-- Entry `(i, j)` of `N M - cS I`. -/
def nsixKE (i j : Fin 6) : KE :=
  .sub (KE.sum ((List.finRange 6).map fun k => .mul (.lin (nA i k)) (.lin (sixA k j))))
    (if i = j then .lin cSL else .int 0)

theorem ck_N : (List.finRange 6).all (fun i => (List.finRange 6).all fun j =>
    checkK 1024 (nsixKE i j)) = true := by
  decide +kernel

/-! ## Consequences in `𝓞 K21` -/

theorem coe_qev {c : Fin 6 → 𝓞 K21} {R : Fin 3 → 𝓞 K21} :
    ((qev c R : 𝓞 K21) : K21) = qev (fun m => (c m : K21)) (fun j => (R j : K21)) := by
  simp [qev]

theorem map_qev {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (c : Fin 6 → A)
    (R : Fin 3 → A) : φ (qev c R) = qev (fun m => φ (c m)) (fun j => φ (R j)) := by
  simp [qev]

/-- **Bruin identity** `Q1 Q3 - Q2² = cB F`. -/
theorem bruin_O (R : Fin 3 → 𝓞 K21) :
    qev (qC 0) R * qev (qC 2) R - qev (qC 1) R ^ 2 = cBO * FurioLombardo.F (R 0) (R 1) (R 2) := by
  apply RingOfIntegers.coe_injective
  have hc : ∀ μ, conv (fun m => zkE (qcA 0 m)) (fun m => zkE (qcA 2 m)) μ -
      conv (fun m => zkE (qcA 1 m)) (fun m => zkE (qcA 1 m)) μ - zkE cBL * (fcoef μ : K21) = 0 := by
    intro μ
    have h := evK_eq_zero_of_check 1024 _
      (List.all_eq_true.mp ck_bruin μ (List.mem_finRange μ))
    simpa [bruinKE, evK_convKE, qKE] using h
  have hF : ((FurioLombardo.F (R 0) (R 1) (R 2) : 𝓞 K21) : K21) =
      FurioLombardo.F ((R 0 : 𝓞 K21) : K21) (R 1 : K21) (R 2 : K21) := by
    simp only [FurioLombardo.F, map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp only [map_sub, map_mul, map_pow, coe_qev, hF]
  rw [sq, qev_mul_qev, qev_mul_qev, F_eq_sum (fun j => (R j : K21))]
  simp only [qC, coe_zkO, cBO, Finset.mul_sum, ← Finset.sum_sub_distrib, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun μ _ => ?_
  linear_combination (m4 (fun j => (R j : K21)) μ) * hc μ

/-- The coefficients of `∂J/∂x_l` for the net `Q1, Q2, Q3`. -/
theorem coeffs_dJ_qC (l : Fin 3) (m : Fin 6) : coeffs (dJ qC l) m = zkO (dJA l m) := by
  apply RingOfIntegers.coe_injective
  have h1 := congrFun (coeffs_dJ_map (algebraMap (𝓞 K21) K21) qC l) m
  have h2 := evK_eq_of_check 1024 _ _
    (List.all_eq_true.mp (List.all_eq_true.mp ck_dJ l (List.mem_finRange l)) m (List.mem_finRange m))
  rw [evK_coeffsKE_dJKE] at h2
  change (algebraMap (𝓞 K21) K21) (coeffs (dJ qC l) m) = zkE (dJA l m)
  rw [← h1]
  exact h2

theorem cSO_eq : zkO cSL = 2 ^ 13 * 7 ^ 13 * gO 16 ^ 12 * gO 17 ^ 12 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check 8192 _ _ ck_cS
  simp only [cSKE, evK_mul, evK_pow, evK_int, evK_lin, evK_gE] at h
  simp only [coe_zkO, map_mul, map_pow, map_ofNat]
  rw [h]
  push_cast
  ring

/-- `N M = cS I`. -/
theorem sum_N_six (i j : Fin 6) :
    ∑ k : Fin 6, zkO (nA i k) * zkO (sixA k j) = if i = j then zkO cSL else 0 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_zero_of_check 1024 _
    (List.all_eq_true.mp (List.all_eq_true.mp ck_N i (List.mem_finRange i)) j (List.mem_finRange j))
  rw [nsixKE, evK_sub, evK_sum, List.map_map] at h
  rw [map_sum]
  simp only [map_mul, coe_zkO]
  rw [Fin.sum_univ_def]
  split_ifs with hij
  · rw [if_pos hij] at h
    exact sub_eq_zero.mp h
  · rw [if_neg hij, evK_int, Int.cast_zero, sub_zero] at h
    exact h

end FurioLombardo.M1
