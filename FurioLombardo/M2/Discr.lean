import FurioLombardo.M2.Norm
import FurioLombardo.M2.DiscrData

/-!
# An upper bound on the discriminant of K21 (lane M2)

`abs_discr_K21_le : |disc K21| ≤ 2^22 7^27` (PARI: `disc K21 = -2^22 7^27`), from
`exists_mul_discr_K21 : ∃ q, q^2 disc K21 = -2^22 7^27`; also `disc K21 ∣ 2^22 7^27` and
`disc K21 < 0`. Data and kernel checks: `FurioLombardo.M2.DiscrData` (code/field/discriminant_bound.gp).

* `β = fZ'(θ)` has characteristic polynomial `χ = X^21 + chiB` (kernel check `chi_beta`) and
  `MB θ = HB(β)` (kernel check `H_beta`), so `ℚ⟮β⟯ = K21`, the minimal polynomial of `β` is `χ`
  and `N(β) = -χ(0)`. Mathlib's `Algebra.discr_powerBasis_eq_norm` gives
  `discr (1, θ, ..., θ^20) = N(β)` (the sign is `(-1)^(21·20/2) = 1`).
* `e_j = Σ_k hA_j[k] w_k ∈ 𝓞 K21` equals `hW_j(θ)/DD` (kernel check `hA_combo`), and the matrix
  `P` of the `e_j` in the power basis is upper triangular (`hW_tri`) with determinant
  `diagP / DD^21` (`hW_diag`). So `discr e = (diagP / DD^21)^2 N(β) = -2^22 7^27` (`diag_num`).
* Writing `e = b Q` with `b` an integral basis of `𝓞 K21` and `Q` an integer matrix,
  `discr e = det(Q)^2 disc K21`. As `det Q` is a nonzero integer, `|disc K21| ≤ 2^22 7^27`.
-/

namespace FurioLombardo.M2.Discr

open Polynomial NumberField IntermediateField Matrix FurioLombardo.M2

/-! ## Evaluation of coefficient lists as sums -/

theorem evalZ_eq_sum_range {R : Type*} [CommRing R] (t : R) :
    ∀ (l : List ℤ) (m : ℕ), l.length ≤ m →
      evalZ t l = ∑ i ∈ Finset.range m, (l.getD i 0 : R) * t ^ i
  | [], m, _ => by simp
  | a :: l, m, h => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp at h; omega⟩
    have ih := evalZ_eq_sum_range t l k (by simp at h; omega)
    rw [Finset.sum_range_succ', evalZ_cons, ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem evalZ_eq_sum {R : Type*} [CommRing R] (t : R) (l : List ℤ) (hl : l.length ≤ 21) :
    evalZ t l = ∑ i : Fin 21, (l.getD i 0 : R) * t ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (l.getD i 0 : R) * t ^ i)]
  exact evalZ_eq_sum_range t l 21 hl

theorem prod_range_eq_list {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∀ m : ℕ, ∏ i ∈ Finset.range m, g i = ((List.range m).map g).prod
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, prod_range_eq_list g m, List.range_succ, List.map_append,
      List.prod_append]
    simp

/-! ## The norm of `β = fZ'(θ)` -/

/-- `fZ'(θ)` in K21. -/
noncomputable def βK : K21 := evalZ (AdjoinRoot.root fQ : K21) fdL

theorem one_mul_βK : ((1 : ℤ) : K21) * βK = evalZ (AdjoinRoot.root fQ : K21) fdL := by
  rw [Int.cast_one, one_mul]; rfl

theorem βK_root : βK ^ 21 + evalZ βK chiB = 0 := by
  have key := evalZ_homogL (AdjoinRoot.root fQ : K21) βK fLow fdL 1
    (root_fLow _ evalZ_root_fL) one_mul_βK (chiB ++ [1])
  rw [evalZ_eq_zero_of_forall _ _ ((allZero_iff _).mp chi_beta), mul_zero, evalZ_append,
    chiB_len.1] at key
  simp only [evalZ_cons, evalZ_nil, mul_zero, add_zero, Int.cast_one, mul_one, one_pow,
    one_mul] at key
  linear_combination -key

theorem βK_H : evalZ βK HB = (MB : K21) * AdjoinRoot.root fQ := by
  have key := evalZ_homogL (AdjoinRoot.root fQ : K21) βK fLow fdL 1
    (root_fLow _ evalZ_root_fL) one_mul_βK HB
  simp only [Int.cast_one, one_pow, one_mul] at key
  have h := evalZ_eq_zero_of_forall (AdjoinRoot.root fQ : K21) _ ((allZero_iff _).mp H_beta)
  rw [evalZ_addZ] at h
  simp only [evalZ_cons, evalZ_nil, mul_zero, add_zero, Int.cast_zero, zero_add,
    Int.cast_neg] at h
  linear_combination h - key

theorem evalZ_mem (S : IntermediateField ℚ K21) (y : K21) (hy : y ∈ S) :
    ∀ l : List ℤ, evalZ y l ∈ S
  | [] => by rw [evalZ_nil]; exact S.zero_mem
  | a :: l => by
    rw [evalZ_cons]
    exact S.add_mem (intCast_mem S a) (S.mul_mem hy (evalZ_mem S y hy l))

theorem adjoin_βK_eq_top : ℚ⟮βK⟯ = ⊤ := by
  have hMB : (MB : K21) ≠ 0 := by exact_mod_cast MB_ne_zero
  have hroot : AdjoinRoot.root fQ ∈ ℚ⟮βK⟯ := by
    have hmem := evalZ_mem ℚ⟮βK⟯ _ (mem_adjoin_simple_self ℚ βK) HB
    rw [βK_H] at hmem
    have := IntermediateField.mul_mem _ (IntermediateField.inv_mem _ (intCast_mem _ MB)) hmem
    rwa [← mul_assoc, inv_mul_cancel₀ hMB, one_mul] at this
  have htop : ℚ⟮AdjoinRoot.root fQ⟯ = (⊤ : IntermediateField ℚ K21) := adjoin_root_eq_top fQ
  rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
  exact hroot

theorem natDegree_minpoly_βK : (minpoly ℚ βK).natDegree = 21 := by
  have hint : IsIntegral ℚ βK := Algebra.IsIntegral.isIntegral _
  rw [← adjoin.finrank hint, adjoin_βK_eq_top, IntermediateField.finrank_top', finrank_K21]

theorem minpoly_βK : minpoly ℚ βK = toPoly ℚ (chiB ++ [1]) := by
  have hint : IsIntegral ℚ βK := Algebra.IsIntegral.isIntegral _
  have hmon := monic_toPoly (R := ℚ) (chiB ++ [1]) (by simp)
  have haev : aeval βK (toPoly ℚ (chiB ++ [1])) = 0 := by
    rw [aeval_toPoly, evalZ_append, chiB_len.1]
    simp only [evalZ_cons, evalZ_nil, mul_zero, add_zero, Int.cast_one, mul_one]
    linear_combination βK_root
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon.1
    (minpoly.dvd ℚ _ haev) ?_).symm
  rw [hmon.2, natDegree_minpoly_βK]
  simp [chiB_len.1]

theorem norm_βK : Algebra.norm ℚ βK = -((chiB.getD 0 0 : ℤ) : ℚ) := by
  rw [norm_eq_of_natDegree _ natDegree_minpoly_βK, minpoly_βK, coeff_toPoly,
    List.getD_append _ _ _ _ (by rw [chiB_len.1]; norm_num)]

/-! ## The discriminant of the power basis -/

/-- The power basis `1, θ, ..., θ^20` of K21 as a family. -/
noncomputable def pw : Fin 21 → K21 := fun i => AdjoinRoot.root fQ ^ (i : ℕ)

theorem aeval_derivative_fQ :
    aeval (AdjoinRoot.root fQ : K21) (derivative fQ) = βK := by
  show aeval (AdjoinRoot.root fQ : K21) (derivative (fZ.map (Int.castRingHom ℚ))) = βK
  rw [derivative_map, ← algebraMap_int_eq, aeval_map_algebraMap]
  exact aeval_derivative_fZ_eq _

theorem powerBasis_dim_fQ : (AdjoinRoot.powerBasis fQ_ne_zero).dim = 21 := by
  rw [AdjoinRoot.powerBasis_dim, fQ_natDegree]

theorem discr_pw : Algebra.discr ℚ pw = Algebra.norm ℚ βK := by
  have hpw : pw = (AdjoinRoot.powerBasis fQ_ne_zero).basis ∘ (finCongr powerBasis_dim_fQ).symm := by
    funext i
    rw [Function.comp_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rfl
  have h1 : Algebra.discr ℚ pw = Algebra.discr ℚ (AdjoinRoot.powerBasis fQ_ne_zero).basis := by
    rw [hpw]; exact Algebra.discr_reindex ℚ _ (finCongr powerBasis_dim_fQ)
  have h2 : Algebra.discr ℚ (AdjoinRoot.powerBasis fQ_ne_zero).basis = (-1) ^ (21 * (21 - 1) / 2) *
      Algebra.norm ℚ
        (aeval (AdjoinRoot.root fQ : K21) (minpoly ℚ (AdjoinRoot.root fQ : K21)).derivative) := by
    have := Algebra.discr_powerBasis_eq_norm ℚ (AdjoinRoot.powerBasis fQ_ne_zero)
    rw [finrank_K21, AdjoinRoot.powerBasis_gen] at this
    exact this
  rw [h1, h2, minpoly_root, aeval_derivative_fQ]
  norm_num

/-! ## The triangular family -/

/-- The matrix of the family `hW_j(θ) / DD` in the power basis. -/
noncomputable def Pm : Matrix (Fin 21) (Fin 21) ℚ :=
  fun i j => (((hW.getD j []).getD i 0 : ℤ) : ℚ) / (DD : ℚ)

theorem Pm_blockTriangular : Pm.IsUpperTriangular := by
  intro i j hij
  have hij' : (j : ℕ) < i := hij
  simp only [Pm]
  rw [hW_tri i i.2 j hij', Int.cast_zero, zero_div]

theorem det_Pm : Pm.det = (diagP : ℚ) / (DD : ℚ) ^ 21 := by
  rw [Matrix.det_of_isUpperTriangular Pm_blockTriangular]
  simp only [Pm]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  refine (Fin.prod_univ_eq_prod_range (fun i => (((hW.getD i []).getD i 0 : ℤ) : ℚ)) 21).trans ?_
  rw [prod_range_eq_list, ← hW_diag, Int.cast_list_prod, List.map_map]
  rfl

/-- The triangular family `e_j = Σ_k hA_j[k] w_k` in `𝓞 K21`. -/
noncomputable def eF (j : Fin 21) : 𝓞 K21 := elt (hA.getD j [])

theorem coe_eF (j : Fin 21) :
    ((eF j : 𝓞 K21) : K21) = evalZ (AdjoinRoot.root fQ : K21) (hW.getD j []) / (DD : K21) := by
  have h := evalZ_eq_zero_of_forall (AdjoinRoot.root fQ : K21) _
    ((allZero_iff _).mp (hA_combo j j.2))
  rw [evalZ_addZ, evalZ_smulZ, comboK_eq] at h
  change eltK (hA.getD j []) = _
  unfold eltK
  congr 1
  push_cast at h
  linear_combination h

theorem pw_vecMul : pw ᵥ* Pm.map (algebraMap ℚ K21) = fun j => ((eF j : 𝓞 K21) : K21) := by
  funext j
  rw [coe_eF, evalZ_eq_sum _ _ (hW_len j j.2).le, Finset.sum_div]
  simp only [vecMul, dotProduct, pw, Pm, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_div₀, map_intCast, map_intCast]
  ring

theorem discr_eF : Algebra.discr ℚ (fun j => ((eF j : 𝓞 K21) : K21)) = -(2 ^ 22 * 7 ^ 27) := by
  have h := Algebra.discr_of_matrix_vecMul pw Pm
  rw [pw_vecMul, discr_pw, norm_βK, det_Pm] at h
  rw [h]
  have hDD : (DD : ℚ) ^ 42 ≠ 0 := pow_ne_zero _ (by exact_mod_cast DD_pos.1.ne')
  have hq : (diagP : ℚ) ^ 2 * ((chiB.getD 0 0 : ℤ) : ℚ) = (DD : ℚ) ^ 42 * (2 ^ 22 * 7 ^ 27) := by
    exact_mod_cast diag_num
  calc ((diagP : ℚ) / (DD : ℚ) ^ 21) ^ 2 * -((chiB.getD 0 0 : ℤ) : ℚ)
      = -((diagP : ℚ) ^ 2 * ((chiB.getD 0 0 : ℤ) : ℚ)) / (DD : ℚ) ^ 42 := by ring
    _ = -((DD : ℚ) ^ 42 * (2 ^ 22 * 7 ^ 27)) / (DD : ℚ) ^ 42 := by rw [hq]
    _ = -(2 ^ 22 * 7 ^ 27) := by rw [neg_div, mul_div_cancel_left₀ _ hDD]

/-! ## Comparison with an integral basis -/

theorem card_chooseBasisIndex : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K21)) = 21 := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_O]

/-- The index set of Mathlib's integral basis of `𝓞 K21`, identified with `Fin 21`. -/
noncomputable def idxEquiv : Module.Free.ChooseBasisIndex ℤ (𝓞 K21) ≃ Fin 21 :=
  Fintype.equivFinOfCardEq card_chooseBasisIndex

/-- The matrix of the family `e_j` in Mathlib's integral basis of `𝓞 K21`. -/
noncomputable def Qm : Matrix (Fin 21) (Fin 21) ℤ :=
  fun i j => (RingOfIntegers.basis K21).repr (eF j) (idxEquiv.symm i)

theorem integralBasis_vecMul :
    (⇑(integralBasis K21) ∘ ⇑idxEquiv.symm) ᵥ* (Qm.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ K21) =
      fun j => ((eF j : 𝓞 K21) : K21) := by
  funext j
  rw [← (integralBasis K21).sum_repr ((eF j : 𝓞 K21) : K21), ← Equiv.sum_comp idxEquiv.symm]
  simp only [vecMul, dotProduct, Function.comp_apply, Matrix.map_apply, Qm,
    RingOfIntegers.coe_eq_algebraMap, integralBasis_repr_apply, Algebra.smul_def, map_intCast,
    eq_intCast]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end FurioLombardo.M2.Discr

namespace FurioLombardo.M2

open NumberField Matrix Discr

/-- `q^2 disc K21 = -2^22 7^27` for an integer `q` (the determinant of the family `e_j` in an
integral basis of `𝓞 K21`). -/
theorem exists_mul_discr_K21 : ∃ q : ℤ, q ^ 2 * NumberField.discr K21 = -(2 ^ 22 * 7 ^ 27) := by
  have hib : Algebra.discr ℚ (⇑(integralBasis K21) ∘ ⇑idxEquiv.symm) = (discr K21 : ℚ) := by
    rw [coe_discr]; exact Algebra.discr_reindex ℚ (integralBasis K21) idxEquiv
  have h1 := Algebra.discr_of_matrix_vecMul (⇑(integralBasis K21) ∘ ⇑idxEquiv.symm)
    (Qm.map (Int.cast : ℤ → ℚ))
  rw [integralBasis_vecMul, hib, discr_eF] at h1
  have hdet : (Qm.map (Int.cast : ℤ → ℚ)).det = (Qm.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det Qm).symm
  rw [hdet] at h1
  refine ⟨Qm.det, ?_⟩
  exact_mod_cast h1.symm

/-- `|disc K21| ≤ 2^22 7^27`. -/
theorem abs_discr_K21_le : |NumberField.discr K21| ≤ 2 ^ 22 * 7 ^ 27 := by
  obtain ⟨q, hq⟩ := exists_mul_discr_K21
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  have h1 : 1 ≤ q ^ 2 := by
    have h : 0 < q ^ 2 := by positivity
    exact h
  calc |NumberField.discr K21| ≤ q ^ 2 * |NumberField.discr K21| :=
        le_mul_of_one_le_left (abs_nonneg _) h1
    _ = |q ^ 2 * NumberField.discr K21| := by rw [abs_mul, abs_of_nonneg (sq_nonneg q)]
    _ = 2 ^ 22 * 7 ^ 27 := by rw [hq]; norm_num

end FurioLombardo.M2

namespace FurioLombardo.M2

open NumberField

/-- `disc K21` divides `2^22 7^27`. -/
theorem discr_K21_dvd : NumberField.discr K21 ∣ 2 ^ 22 * 7 ^ 27 := by
  obtain ⟨q, hq⟩ := exists_mul_discr_K21
  exact ⟨-q ^ 2, by linear_combination hq⟩

/-- `disc K21 < 0`. -/
theorem discr_K21_neg : NumberField.discr K21 < 0 := by
  obtain ⟨q, hq⟩ := exists_mul_discr_K21
  by_contra h
  have h0 : 0 ≤ q ^ 2 * NumberField.discr K21 := mul_nonneg (sq_nonneg q) (not_lt.mp h)
  rw [hq] at h0
  norm_num at h0

end FurioLombardo.M2
