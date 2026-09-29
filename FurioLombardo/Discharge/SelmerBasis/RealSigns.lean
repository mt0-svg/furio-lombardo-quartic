import FurioLombardo.Discharge.SelmerBasis.AssemblyData
import FurioLombardo.Discharge.SelmerBasis.RealCoord
import FurioLombardo.Discharge.SelmerBasis.RealSignCheckL
import FurioLombardo.Discharge.SelmerBasis.RealSignCheckM
import FurioLombardo.Discharge.SelmerBasis.RealSignCheckN
import FurioLombardo.Discharge.SelmerBasis.RealSignCheckI0
import FurioLombardo.Discharge.SelmerBasis.RealSignCheckI1
import FurioLombardo.Discharge.SelmerBasis.TowerFacts

/-!
# The sign data at the real places 5 and 6 (twist 0)

`Sg k s j` is the sign bit of `Pgen s` at the root `j` (increasing order) of `fRev 0` at `realEmb k`, read
from `Assembly.SgRows` (code/selmer-assembly/assembly_data.gp; computed numerically, proved right by `signOK`).

* `signOK`: the table is right (`SignOK k (Sg k)`), through `hS_of_signs` (RealCoord.lean): the square roots
  `u = sAl √σ(ε)`, `u' = sEb √σ(ε)`, `v = sV √τ'(eN)` (`τ' = extendHom σ u'`) with the sign conditions of
  `hS_of_signs`, and the sign of every generator at the four real embeddings of the tower from the kernel
  certificates of RealSignCheck*.lean (data code/selmer-local-conditions/local_data_real.gp, 548 certificates);
* `CR k`: the matrix of `coordCond_place` for this table, and `CR_eq`: its rows are `Assembly.RealRows k`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.RealRoots

open Polynomial FurioLombardo.M1 FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis
  RealSignData

/-- The sign bits. -/
def Sg (k : Fin 2) : Fin 82 → Fin 4 → ZMod 2 :=
  fun s j => if ((Assembly.SgRows k).getD s 0).testBit j then 1 else 0

theorem signBit_of_tBit {k : Fin 2} {s : Fin 82} {j : Fin 4} {x : ℝ} (h : 0 < (tBit k s j : ℝ) * x) :
    SignBit x (Sg k s j) := by
  unfold tBit at h
  unfold Sg SignBit
  by_cases hb : ((Assembly.SgRows k).getD s 0).testBit j = true
  · rw [if_pos hb] at h ⊢
    push_cast at h
    exact Or.inl ⟨by linarith, rfl⟩
  · rw [if_neg hb] at h ⊢
    push_cast at h
    exact Or.inr ⟨by linarith, rfl⟩

theorem Sg_eq_zero {k : Fin 2} {s : Fin 82} {j : Fin 4} (h : tBit k s j = 1) : Sg k s j = 0 := by
  unfold tBit at h
  unfold Sg
  by_cases hb : ((Assembly.SgRows k).getD s 0).testBit j = true
  · rw [if_pos hb] at h
    exact absurd h (by decide)
  · rw [if_neg hb]

theorem ckL_all (k : Fin 2) (i : ℕ) (hi : i < 29) : ckLf k i = true := by
  fin_cases k
  · exact ck_L0 i (Nat.zero_le _) hi
  · exact ck_L1 i (Nat.zero_le _) hi

theorem ckM_all (k : Fin 2) (j : ℕ) (hj : j < 53) : ckMf k j = true := by
  fin_cases k
  · exact ck_M0 j (Nat.zero_le _) hj
  · exact ck_M1 j (Nat.zero_le _) hj

theorem ckN_all (k : Fin 2) (j : ℕ) (hj : j < 53) : ckNf k j = true := by
  fin_cases k
  · exact ck_N0 j (Nat.zero_le _) hj
  · exact ck_N1 j (Nat.zero_le _) hj

theorem idN_all (j : ℕ) (hj : j < 53) : idNf j = true := by
  rcases Nat.lt_or_ge j 27 with h | h
  · exact id_N0 j (Nat.zero_le _) h
  · exact id_N1 j h hj

/-- The bits of the table at a generator of `L42` (`i < 29`) and of `N84` (`j < 53`). -/
theorem bitsL (k : Fin 2) (i : ℕ) (hi : i < 29) :
    tBit k i (hIdx k 0) = 1 ∧ tBit k i (hIdx k 1) = 1 ∧
      tBit k i (qIdx k 1) = (if posLk k i then tBit k i (qIdx k 0) else -tBit k i (qIdx k 0)) := by
  have h := ck_B k
  simp only [ckBf, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨(h.1 i hi).1.1, (h.1 i hi).1.2, (h.1 i hi).2⟩

theorem bitsN (k : Fin 2) (j : ℕ) (hj : j < 53) :
    tBit k (29 + j) (qIdx k 0) = 1 ∧ tBit k (29 + j) (qIdx k 1) = 1 ∧
      tBit k (29 + j) (hIdx k 1) =
        (if posMTk k j then tBit k (29 + j) (hIdx k 0) else -tBit k (29 + j) (hIdx k 0)) := by
  have h := ck_B k
  simp only [ckBf, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨(h.2 j hj).1.1, (h.2 j hj).1.2, (h.2 j hj).2⟩

theorem reM (z w : L42) : (z * w).re = z.re * w.re + epsK * z.im * w.im := rfl

theorem imM (z w : L42) : (z * w).im = z.re * w.im + z.im * w.re + 0 * z.im * w.im := rfl

/-- `M = A² - eN B'²` for `gensN j`. -/
theorem normN_eq (j : ℕ) (hj : j < 53) :
    (mkN (SUnitData.gN.getD j [])).re * (mkN (SUnitData.gN.getD j [])).re -
      eN * ((mkN (SUnitData.gN.getD j [])).im * (mkN (SUnitData.gN.getD j [])).im) =
      (⟨zkE (mN0.getD j []), zkE (mN1.getD j [])⟩ : L42) := by
  have h := idN_all j hj
  simp only [idNf, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩ := h
  have e0 := evK_eq_of_check _ _ _ h0
  have e1 := evK_eq_of_check _ _ _ h1
  simp only [m0E, m1E, evK_lin, evK_sub, evK_add, evK_mul, evK_int] at e0 e1
  ext
  · simp only [QuadraticAlgebra.re_sub, reM, imM]
    simp only [mkN, eN, eaK, ebK, epsK_eq]
    rw [e0]
    simp only [gNl]
    push_cast
    ring
  · simp only [QuadraticAlgebra.im_sub, reM, imM]
    simp only [mkN, eN, eaK, ebK, epsK_eq]
    rw [e1]
    simp only [gNl]
    push_cast
    ring

/-- **The sign table is right.** -/
theorem signOK (k : Fin 2) : SignOK k (Sg k) := by
  have hT := ck_T k
  simp only [ckTf, Bool.and_eq_true, beq_iff_eq] at hT
  obtain ⟨⟨⟨⟨⟨hA1, hE1⟩, hV1⟩, hAl⟩, hEb⟩, hBe⟩ := hT
  have hA1' : (sAlk k : ℝ) * sAlk k = 1 := by exact_mod_cast hA1
  have hE1' : (sEbk k : ℝ) * sEbk k = 1 := by exact_mod_cast hE1
  have hV1' : (sVk k : ℝ) * sVk k = 1 := by exact_mod_cast hV1
  set σ := realEmb (Fin.castSucc k) with hσ
  have hr : 0 < sqrtEps (Fin.castSucc k) := Real.sqrt_pos.mpr (realEmb_epsK_pos _)
  -- u
  set u : ℝ := (sAlk k : ℝ) * sqrtEps (Fin.castSucc k) with hu_def
  have hu : u * u = σ epsK := by
    rw [hu_def, show (sAlk k : ℝ) * sqrtEps (Fin.castSucc k) * ((sAlk k : ℝ) * sqrtEps (Fin.castSucc k)) =
      ((sAlk k : ℝ) * sAlk k) * (sqrtEps (Fin.castSucc k) * sqrtEps (Fin.castSucc k)) by ring, hA1', one_mul,
      sqrtEps_mul]
  have hsu : 0 < (sAlk k : ℝ) * u := by
    rw [hu_def, ← mul_assoc, hA1', one_mul]; exact hr
  have hux : u * σ alphaR.im < 0 := by
    have h := elemAt_sign hAl
    push_cast at h
    have hd : (0 : ℝ) < (SUnitData.alphaDen : ℝ) := by norm_num [SUnitData.alphaDen]
    show u * σ (zkE (SUnitData.alphaL.getD 1 []) / (SUnitData.alphaDen : K21)) < 0
    rw [map_div₀, map_natCast,
      show u * (σ (zkE (SUnitData.alphaL.getD 1 [])) / (SUnitData.alphaDen : ℝ)) =
        -((-(sAlk k : ℝ) * σ (zkE (SUnitData.alphaL.getD 1 []))) * sqrtEps (Fin.castSucc k)) /
          (SUnitData.alphaDen : ℝ) by rw [hu_def]; ring]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos h hr)) hd
  -- u'
  set u' : ℝ := (sEbk k : ℝ) * sqrtEps (Fin.castSucc k) with hu'_def
  have hu' : u' * u' = σ epsK := by
    rw [hu'_def, show (sEbk k : ℝ) * sqrtEps (Fin.castSucc k) * ((sEbk k : ℝ) * sqrtEps (Fin.castSucc k)) =
      ((sEbk k : ℝ) * sEbk k) * (sqrtEps (Fin.castSucc k) * sqrtEps (Fin.castSucc k)) by ring, hE1', one_mul,
      sqrtEps_mul]
  have hsu' : 0 < (sEbk k : ℝ) * u' := by
    rw [hu'_def, ← mul_assoc, hE1', one_mul]; exact hr
  set τ' := extendHom σ u' hu' with hτ'
  have heN : 0 < τ' eN := by
    have h := sgn_extend σ u' hu' eN 1 (Or.inr ⟨?_, ?_⟩)
    · simpa using h
    · have h1 : eN.re * eN.re - epsK * (eN.im * eN.im) = mK := by
        show eaK / 2 * (eaK / 2) - epsK * (ebK / 2 * (ebK / 2)) = mK
        linear_combination ea_sq_sub / 4
      rw [h1]
      exact realEmb_m_neg _
    · have h := elemAt_sign hEb
      show 0 < 1 * (u' * σ (zkE ebL / 2))
      rw [map_div₀, map_ofNat,
        show 1 * (u' * (σ (zkE ebL) / 2)) = ((sEbk k : ℝ) * σ (zkE ebL)) * sqrtEps (Fin.castSucc k) / 2 by
          rw [hu'_def]; ring]
      exact div_pos (mul_pos h hr) two_pos
  -- v
  set v : ℝ := (sVk k : ℝ) * Real.sqrt (τ' eN) with hv_def
  have hq := Real.sqrt_pos.mpr heN
  have hv : v * v = τ' eN := by
    rw [hv_def, show (sVk k : ℝ) * Real.sqrt (τ' eN) * ((sVk k : ℝ) * Real.sqrt (τ' eN)) =
      ((sVk k : ℝ) * sVk k) * (Real.sqrt (τ' eN) * Real.sqrt (τ' eN)) by ring, hV1', one_mul,
      Real.mul_self_sqrt heN.le]
  have hsv : 0 < (sVk k : ℝ) * v := by
    rw [hv_def, ← mul_assoc, hV1', one_mul]; exact hq
  have hvy : v * τ' betaR.im < 0 := by
    have hb := certL_sound hu' hsu' hE1 (zkE_normE id_Beta) hBe
    push_cast at hb
    have hd : (0 : ℝ) < (SUnitData.betaDen : ℝ) := by norm_num [SUnitData.betaDen]
    have he : τ' betaR.im = τ' (⟨zkE (SUnitData.betaN.getD 2 []), zkE (SUnitData.betaN.getD 3 [])⟩ : L42) /
        (SUnitData.betaDen : ℝ) := by
      rw [hτ', extendHom_apply, extendHom_apply]
      show σ (zkE (SUnitData.betaN.getD 2 []) / (SUnitData.betaDen : K21)) +
          σ (zkE (SUnitData.betaN.getD 3 []) / (SUnitData.betaDen : K21)) * u' = _
      rw [map_div₀, map_div₀, map_natCast]
      ring
    rw [he, show v * (τ' (⟨zkE (SUnitData.betaN.getD 2 []), zkE (SUnitData.betaN.getD 3 [])⟩ : L42) /
        (SUnitData.betaDen : ℝ)) = -((-(sVk k : ℝ) *
          τ' (⟨zkE (SUnitData.betaN.getD 2 []), zkE (SUnitData.betaN.getD 3 [])⟩ : L42)) *
          Real.sqrt (τ' eN)) / (SUnitData.betaDen : ℝ) by rw [hv_def]; ring]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hb hq)) hd
  refine hS_of_signs k (Sg k) (TowerFacts.aeval_alphaR_q 0) (TowerFacts.aeval_betaR_h 0)
    TowerFacts.Pgen_alphaR_left TowerFacts.Pgen_alphaR_right TowerFacts.Pgen_betaR_left
    TowerFacts.Pgen_betaR_right hu hux hu' hv hvy ?_ ?_ ?_ ?_
  · -- gensL at the roots of q
    intro i b
    have hc := ckL_all k i i.2
    unfold ckLf at hc
    have hn := zkE_normE (id_L i (Nat.zero_le _) i.2)
    obtain ⟨-, -, hb1⟩ := bitsL k i i.2
    fin_cases b
    · have h := certL_sound hu hsu hA1 hn hc
      simp only [embQ, if_pos rfl]
      exact signBit_of_tBit h
    · have h := certL_sound_neg hu hsu hA1 hn hc
      simp only [embQ, show ((1 : Fin 2) = 0) = False by decide, if_false]
      apply signBit_of_tBit
      show 0 < (tBit k i (qIdx k 1) : ℝ) * _
      rw [hb1]
      exact h
  · -- gensL at the roots of h
    intro i b
    obtain ⟨h0, h1, -⟩ := bitsL k i i.2
    fin_cases b
    · exact Sg_eq_zero h0
    · exact Sg_eq_zero h1
  · -- gensN at the roots of q
    intro j b
    obtain ⟨h0, h1, -⟩ := bitsN k j j.2
    fin_cases b
    · exact Sg_eq_zero h0
    · exact Sg_eq_zero h1
  · -- gensN at the roots of h
    intro j b
    have hM := normN_eq j j.2
    have hcM := ckM_all k j j.2
    unfold ckMf at hcM
    have hcN := ckN_all k j j.2
    unfold ckNf at hcN
    have hid := idN_all j j.2
    simp only [idNf, Bool.and_eq_true] at hid
    obtain ⟨⟨⟨⟨-, -⟩, hnM⟩, hnA⟩, hnB⟩ := hid
    have hMs := certL_sound hu' hsu' hE1 (zkE_normE hnM) hcM
    obtain ⟨-, -, hb1⟩ := bitsN k j j.2
    have hx : gensN j = mkN (SUnitData.gN.getD j []) := rfl
    -- the sign of `extendHom τ' w (gensN j)` from the norm `M` and one coordinate
    have key : ∀ (w : ℝ) (hw : w * w = τ' eN) (t : ℝ),
        (0 < τ' (⟨zkE (mN0.getD j []), zkE (mN1.getD j [])⟩ : L42) ∧
            0 < t * τ' (mkN (SUnitData.gN.getD j [])).re) ∨
          (τ' (⟨zkE (mN0.getD j []), zkE (mN1.getD j [])⟩ : L42) < 0 ∧
            0 < t * (w * τ' (mkN (SUnitData.gN.getD j [])).im)) →
        0 < t * extendHom τ' w hw (gensN j) := by
      intro w hw t h
      apply sgn_extend τ' w hw
      rw [hx, normN_eq j j.2]
      exact h
    have him : τ' (mkN (SUnitData.gN.getD j [])).im =
        2 * τ' (⟨zkE (gNl j 2), zkE (gNl j 3)⟩ : L42) := by
      rw [hτ', extendHom_apply, extendHom_apply]
      show σ (2 * zkE (gNl j 2)) + σ (2 * zkE (gNl j 3)) * u' = _
      rw [map_mul, map_mul, map_ofNat]
      ring
    have hre : (mkN (SUnitData.gN.getD j [])).re = (⟨zkE (gNl j 0), zkE (gNl j 1)⟩ : L42) := rfl
    cases hp : posMTk k j with
    | true =>
      rw [hp, if_pos rfl] at hMs
      rw [hp, if_pos rfl] at hcN
      rw [hp, if_pos rfl] at hb1
      push_cast at hMs
      rw [one_mul] at hMs
      have hA := certL_sound hu' hsu' hE1 (zkE_normE hnA) hcN
      fin_cases b
      · simp only [embH, if_pos rfl]
        apply signBit_of_tBit
        refine key v hv _ (Or.inl ⟨hMs, ?_⟩)
        rw [hre]; exact hA
      · simp only [embH, show ((1 : Fin 2) = 0) = False by decide, if_false]
        apply signBit_of_tBit
        refine key (-v) (neg_mul_self_eq hv) _ (Or.inl ⟨hMs, ?_⟩)
        show 0 < (tBit k (29 + j) (hIdx k 1) : ℝ) * _
        rw [hb1, hre]; exact hA
    | false =>
      simp only [hp, Bool.false_eq_true, if_false] at hMs hcN hb1
      push_cast at hMs
      have hMn : τ' (⟨zkE (mN0.getD j []), zkE (mN1.getD j [])⟩ : L42) < 0 := by linarith
      have hB := certL_sound hu' hsu' hE1 (zkE_normE hnB) hcN
      push_cast at hB
      set Y := τ' (⟨zkE (gNl j 2), zkE (gNl j 3)⟩ : L42)
      set t0 : ℝ := (tBit k (29 + j) (hIdx k 0) : ℝ)
      fin_cases b
      · simp only [embH, if_pos rfl]
        apply signBit_of_tBit
        refine key v hv _ (Or.inr ⟨hMn, ?_⟩)
        show 0 < t0 * (v * τ' (mkN (SUnitData.gN.getD j [])).im)
        rw [him, show t0 * (v * (2 * Y)) = 2 * ((t0 * sVk k * Y) * ((sVk k : ℝ) * v)) by
          linear_combination (-2 * t0 * v * Y) * hV1']
        exact mul_pos two_pos (mul_pos hB hsv)
      · simp only [embH, show ((1 : Fin 2) = 0) = False by decide, if_false]
        apply signBit_of_tBit
        refine key (-v) (neg_mul_self_eq hv) _ (Or.inr ⟨hMn, ?_⟩)
        show 0 < (tBit k (29 + j) (hIdx k 1) : ℝ) * _
        rw [hb1, him]
        push_cast
        rw [show -t0 * (-v * (2 * Y)) = 2 * ((t0 * sVk k * Y) * ((sVk k : ℝ) * v)) by
          linear_combination (-2 * t0 * v * Y) * hV1']
        exact mul_pos two_pos (mul_pos hB hsv)

/-- The two rows at place `k + 5`. -/
def CR (k : Fin 2) : Matrix (Fin 2) (Fin 82) (ZMod 2) :=
  Matrix.of ![fun s => Sg k s 0 + Sg k s 3, fun s => Sg k s 1 + Sg k s 2]

theorem CR_eq0 : ∀ k : Fin 2, ∀ s : Fin 82,
    CR k 0 s = bitv 82 ((Assembly.RealRows k).getD 0 0) s := by
  decide +kernel

theorem CR_eq1 : ∀ k : Fin 2, ∀ s : Fin 82,
    CR k 1 s = bitv 82 ((Assembly.RealRows k).getD 1 0) s := by
  decide +kernel

theorem CR_eq (k r : Fin 2) (s : Fin 82) : CR k r s = bitv 82 ((Assembly.RealRows k).getD r 0) s := by
  fin_cases r
  · exact CR_eq0 k s
  · exact CR_eq1 k s

end FurioLombardo.Discharge.SelmerBasis.RealRoots
