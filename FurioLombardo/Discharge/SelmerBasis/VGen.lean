import FurioLombardo.Discharge.SelmerBasis.PlaceUCert
import FurioLombardo.Discharge.SelmerBasis.PointGen
import FurioLombardo.Discharge.SelmerBasis.PlaceWRows

/-!
# Generic facts for the place `v`: two components of different types

At `v` the local algebra `K_v[T]/(fRev k)^σ` is `F1 × F2` with `F1 = CF σ E` (Eisenstein, the root of
`q`) and `F2 = UF σ E` (unramified over `F1`, the root of `h`), so `G = F1ˣ × F2ˣ` and a row of `G / G²`
has `n1 + n2` bits, `F1` at bits `0 .. n1 - 1` and `F2` at bits `n1 .. n1 + n2 - 1`.

* `bP`: the basis of `G / G²` from bases of the two components;
* `isSquare_mul_rowsP`: squares in `G` from squares at the two components;
* `indep_rowsP`: independence in `G` from independence at the two components;
* `hcert_rel_of_bits`: the `F₂` identity of `relAtV_of_coords` from one xor identity of bitmasks;
* `bitv_val_eq_ite`: `(bitv n a i).val` is the bit `i` of `a`;
* `PtData.aeval_alphaR_U'`, `PtData.aeval_betaR_U'`: the values `Λ² U(α)`, `Λ² U(β)` from `okT`
  alone (the points at `v` exist already, lane SelmerSpan's `Dpt`; no Hensel data).
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3b
  FurioLombardo.Discharge.SelmerBasis.Tower

/-- The basis of `F1ˣ × F2ˣ`: `b1 i` at position `i`, `b2 i` at position `n1 + i`. -/
noncomputable def bP {F1 F2 : Type*} [Field F1] [Field F2] {n1 n2 : ℕ} (b1 : Fin n1 → F1)
    (b2 : Fin n2 → F2) (hb1 : ∀ i, b1 i ≠ 0) (hb2 : ∀ i, b2 i ≠ 0) : Fin (n1 + n2) → F1ˣ × F2ˣ :=
  Fin.append (fun i => (Units.mk0 (b1 i) (hb1 i), 1)) (fun i => (1, Units.mk0 (b2 i) (hb2 i)))

/-- **Squares in `F1ˣ × F2ˣ` from squares at the two components.** -/
theorem isSquare_mul_rowsP {F1 F2 : Type*} [Field F1] [Field F2] {n1 n2 : ℕ} (b1 : Fin n1 → F1)
    (b2 : Fin n2 → F2) (hb1 : ∀ i, b1 i ≠ 0) (hb2 : ∀ i, b2 i ≠ 0) (x : F1ˣ × F2ˣ) (A : ℕ)
    (h1 : IsSquare ((x.1 : F1) * ∏ i : Fin n1, b1 i ^ (bitv n1 A i).val))
    (h2 : IsSquare ((x.2 : F2) * ∏ i : Fin n2, b2 i ^ (bitv n2 (A >>> n1) i).val)) :
    IsSquare (x * ∏ l : Fin (n1 + n2), bP b1 b2 hb1 hb2 l ^ (bitv (n1 + n2) A l).val) := by
  -- Split the product over Fin (n1 + n2) using Fin.prod_univ_add
  rw [Fin.prod_univ_add (fun l : Fin (n1 + n2) => bP b1 b2 hb1 hb2 l ^ (bitv (n1 + n2) A l).val)]
  -- Simplify each bP term using its definition
  have hbP_castAdd (i : Fin n1) : bP b1 b2 hb1 hb2 (Fin.castAdd n2 i) = (Units.mk0 (b1 i) (hb1 i), 1) := by
    simp [bP]
  have hbP_natAdd (i : Fin n2) : bP b1 b2 hb1 hb2 (Fin.natAdd n1 i) = (1, Units.mk0 (b2 i) (hb2 i)) := by
    simp [bP]
  -- Simplify the bitv values
  have hbitv_castAdd (i : Fin n1) : (bitv (n1 + n2) A (Fin.castAdd n2 i)).val = (bitv n1 A i).val := by
    simp [bitv]
  have hbitv_natAdd (i : Fin n2) : (bitv (n1 + n2) A (Fin.natAdd n1 i)).val = (bitv n2 (A >>> n1) i).val := by
    simp [bitv]
  simp_rw [hbP_castAdd, hbP_natAdd, hbitv_castAdd, hbitv_natAdd]
  -- Define the two product subterms with explicit types
  set P1 : F1ˣ × F2ˣ := ∏ i : Fin n1, ((Units.mk0 (b1 i) (hb1 i) : F1ˣ), (1 : F2ˣ)) ^ (bitv n1 A i).val
  set P2 : F1ˣ × F2ˣ := ∏ i : Fin n2, ((1 : F1ˣ), (Units.mk0 (b2 i) (hb2 i) : F2ˣ)) ^ (bitv n2 (A >>> n1) i).val
  -- Compute components of P1 and P2
  have hP1_fst : P1.1 = ∏ i : Fin n1, (Units.mk0 (b1 i) (hb1 i)) ^ (bitv n1 A i).val := by
    simp [P1, Prod.fst_prod]
  have hP1_snd : P1.2 = 1 := by
    simp [P1, Prod.snd_prod]
  have hP2_fst : P2.1 = 1 := by
    simp [P2, Prod.fst_prod]
  have hP2_snd : P2.2 = ∏ i : Fin n2, (Units.mk0 (b2 i) (hb2 i)) ^ (bitv n2 (A >>> n1) i).val := by
    simp [P2, Prod.snd_prod]
  -- Compute components of x * (P1 * P2)
  have h_fst : (x * (P1 * P2)).1 = x.1 * P1.1 := by
    simp [Prod.fst_mul, hP2_fst]
  have h_snd : (x * (P1 * P2)).2 = x.2 * P2.2 := by
    simp [Prod.snd_mul, hP1_snd]
  -- Relate the field values of the components to the given hypotheses
  have h_fst_val : ((x * (P1 * P2)).1 : F1) = (x.1 : F1) * ∏ i : Fin n1, (b1 i : F1) ^ (bitv n1 A i).val := by
    simp [h_fst, hP1_fst, Units.val_pow_eq_pow_val, Units.val_mk0]
  have h_snd_val : ((x * (P1 * P2)).2 : F2) = (x.2 : F2) * ∏ i : Fin n2, (b2 i : F2) ^ (bitv n2 (A >>> n1) i).val := by
    simp [h_snd, hP2_snd, Units.val_pow_eq_pow_val, Units.val_mk0]
  -- From h1 and h2, the field values are squares in F1 and F2 respectively
  -- Lift to units using the helper lemma
  have h_sq_fst_val : IsSquare (((x * (P1 * P2)).1 : F1)) := by
    rw [h_fst_val]
    exact h1
  have h_sq_snd_val : IsSquare (((x * (P1 * P2)).2 : F2)) := by
    rw [h_snd_val]
    exact h2
  -- Lift to units: if a unit's value is a square in the field, the unit is a square
  have h_sq_fst_unit : IsSquare ((x * (P1 * P2)).1 : F1ˣ) := by
    rcases h_sq_fst_val with ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hzero
      have : ((x * (P1 * P2)).1 : F1) = 0 := by rw [hr, hzero, zero_mul]
      exact Units.ne_zero ((x * (P1 * P2)).1) this
    refine ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    calc
      (((x * (P1 * P2)).1 : F1ˣ) : F1) = r * r := hr
      _ = ((Units.mk0 r hr0 : F1ˣ) : F1) * ((Units.mk0 r hr0 : F1ˣ) : F1) := by simp [Units.val_mk0]
      _ = (((Units.mk0 r hr0 : F1ˣ) * (Units.mk0 r hr0 : F1ˣ) : F1ˣ) : F1) := by simp [Units.val_mul]
  have h_sq_snd_unit : IsSquare ((x * (P1 * P2)).2 : F2ˣ) := by
    rcases h_sq_snd_val with ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hzero
      have : ((x * (P1 * P2)).2 : F2) = 0 := by rw [hr, hzero, zero_mul]
      exact Units.ne_zero ((x * (P1 * P2)).2) this
    refine ⟨Units.mk0 r hr0, ?_⟩
    apply Units.ext
    calc
      (((x * (P1 * P2)).2 : F2ˣ) : F2) = r * r := hr
      _ = ((Units.mk0 r hr0 : F2ˣ) : F2) * ((Units.mk0 r hr0 : F2ˣ) : F2) := by simp [Units.val_mk0]
      _ = (((Units.mk0 r hr0 : F2ˣ) * (Units.mk0 r hr0 : F2ˣ) : F2ˣ) : F2) := by simp [Units.val_mul]
  -- Combine: a pair is a square iff both components are squares
  rcases h_sq_fst_unit with ⟨u1, hu1⟩
  rcases h_sq_snd_unit with ⟨u2, hu2⟩
  refine ⟨(u1, u2), ?_⟩
  ext <;> simp [hu1, hu2]

/-- **Independence in `F1ˣ × F2ˣ` from independence at the two components.** -/
theorem indep_rowsP {F1 F2 : Type*} [Field F1] [Field F2] {n1 n2 : ℕ} (b1 : Fin n1 → F1)
    (b2 : Fin n2 → F2) (hb1 : ∀ i, b1 i ≠ 0) (hb2 : ∀ i, b2 i ≠ 0)
    (h1 : ∀ ε : Fin n1 → ZMod 2, IsSquare (∏ i, b1 i ^ (ε i).val) → ε = 0)
    (h2 : ∀ ε : Fin n2 → ZMod 2, IsSquare (∏ i, b2 i ^ (ε i).val) → ε = 0) :
    ∀ ε : Fin (n1 + n2) → ZMod 2, IsSquare (∏ l, bP b1 b2 hb1 hb2 l ^ (ε l).val) → ε = 0 := by
  intro ε h_sq
  let φ1 : (F1ˣ × F2ˣ) →* F1 :=
    (Units.coeHom F1).comp (MonoidHom.fst (F1ˣ) (F2ˣ))
  let φ2 : (F1ˣ × F2ˣ) →* F2 :=
    (Units.coeHom F2).comp (MonoidHom.snd (F1ˣ) (F2ˣ))
  have h_sq1 : IsSquare (φ1 (∏ l, bP b1 b2 hb1 hb2 l ^ (ε l).val)) :=
    IsSquare.map φ1 h_sq
  have h_sq2 : IsSquare (φ2 (∏ l, bP b1 b2 hb1 hb2 l ^ (ε l).val)) :=
    IsSquare.map φ2 h_sq
  have h_prod1 : φ1 (∏ l, bP b1 b2 hb1 hb2 l ^ (ε l).val) =
      ∏ l, φ1 (bP b1 b2 hb1 hb2 l ^ (ε l).val) := by
    rw [map_prod]
  have h_prod2 : φ2 (∏ l, bP b1 b2 hb1 hb2 l ^ (ε l).val) =
      ∏ l, φ2 (bP b1 b2 hb1 hb2 l ^ (ε l).val) := by
    rw [map_prod]
  have h_term1_castAdd (i : Fin n1) : φ1 (bP b1 b2 hb1 hb2 (Fin.castAdd n2 i)) = b1 i := by
    simp [φ1, bP, MonoidHom.coe_comp, Units.coeHom_apply]
  have h_term1_natAdd (j : Fin n2) : φ1 (bP b1 b2 hb1 hb2 (Fin.natAdd n1 j)) = 1 := by
    simp [φ1, bP, MonoidHom.coe_comp, Units.coeHom_apply]
  have h_term2_castAdd (i : Fin n1) : φ2 (bP b1 b2 hb1 hb2 (Fin.castAdd n2 i)) = 1 := by
    simp [φ2, bP, MonoidHom.coe_comp, Units.coeHom_apply]
  have h_term2_natAdd (j : Fin n2) : φ2 (bP b1 b2 hb1 hb2 (Fin.natAdd n1 j)) = b2 j := by
    simp [φ2, bP, MonoidHom.coe_comp, Units.coeHom_apply]
  have h_split1 : ∏ l : Fin (n1 + n2), φ1 (bP b1 b2 hb1 hb2 l ^ (ε l).val) =
      (∏ i : Fin n1, b1 i ^ (ε (Fin.castAdd n2 i)).val) := by
    calc
      ∏ l : Fin (n1 + n2), φ1 (bP b1 b2 hb1 hb2 l ^ (ε l).val) =
          (∏ l : Fin (n1 + n2), φ1 (bP b1 b2 hb1 hb2 l) ^ (ε l).val) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        simp [map_pow]
      _ = (∏ i : Fin n1, φ1 (bP b1 b2 hb1 hb2 (Fin.castAdd n2 i)) ^ (ε (Fin.castAdd n2 i)).val) *
          (∏ j : Fin n2, φ1 (bP b1 b2 hb1 hb2 (Fin.natAdd n1 j)) ^ (ε (Fin.natAdd n1 j)).val) := by
        rw [Fin.prod_univ_add]
      _ = (∏ i : Fin n1, b1 i ^ (ε (Fin.castAdd n2 i)).val) *
          (∏ j : Fin n2, (1 : F1) ^ (ε (Fin.natAdd n1 j)).val) := by
        simp [h_term1_castAdd, h_term1_natAdd]
      _ = (∏ i : Fin n1, b1 i ^ (ε (Fin.castAdd n2 i)).val) * (∏ j : Fin n2, (1 : F1)) := by
        simp
      _ = (∏ i : Fin n1, b1 i ^ (ε (Fin.castAdd n2 i)).val) * 1 := by simp
      _ = ∏ i : Fin n1, b1 i ^ (ε (Fin.castAdd n2 i)).val := by simp
  have h_sq1' : IsSquare (∏ i : Fin n1, b1 i ^ (ε (Fin.castAdd n2 i)).val) := by
    rw [h_prod1] at h_sq1
    rw [h_split1] at h_sq1
    exact h_sq1
  have h_ε_castAdd : ε ∘ Fin.castAdd n2 = 0 := h1 (ε ∘ Fin.castAdd n2) h_sq1'
  have h_split2 : ∏ l : Fin (n1 + n2), φ2 (bP b1 b2 hb1 hb2 l ^ (ε l).val) =
      (∏ j : Fin n2, b2 j ^ (ε (Fin.natAdd n1 j)).val) := by
    calc
      ∏ l : Fin (n1 + n2), φ2 (bP b1 b2 hb1 hb2 l ^ (ε l).val) =
          (∏ l : Fin (n1 + n2), φ2 (bP b1 b2 hb1 hb2 l) ^ (ε l).val) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        simp [map_pow]
      _ = (∏ i : Fin n1, φ2 (bP b1 b2 hb1 hb2 (Fin.castAdd n2 i)) ^ (ε (Fin.castAdd n2 i)).val) *
          (∏ j : Fin n2, φ2 (bP b1 b2 hb1 hb2 (Fin.natAdd n1 j)) ^ (ε (Fin.natAdd n1 j)).val) := by
        rw [Fin.prod_univ_add]
      _ = (∏ i : Fin n1, (1 : F2) ^ (ε (Fin.castAdd n2 i)).val) *
          (∏ j : Fin n2, b2 j ^ (ε (Fin.natAdd n1 j)).val) := by
        simp [h_term2_castAdd, h_term2_natAdd]
      _ = (∏ i : Fin n1, (1 : F2)) * (∏ j : Fin n2, b2 j ^ (ε (Fin.natAdd n1 j)).val) := by
        simp
      _ = 1 * (∏ j : Fin n2, b2 j ^ (ε (Fin.natAdd n1 j)).val) := by simp
      _ = ∏ j : Fin n2, b2 j ^ (ε (Fin.natAdd n1 j)).val := by simp
  have h_sq2' : IsSquare (∏ j : Fin n2, b2 j ^ (ε (Fin.natAdd n1 j)).val) := by
    rw [h_prod2] at h_sq2
    rw [h_split2] at h_sq2
    exact h_sq2
  have h_ε_natAdd : ε ∘ Fin.natAdd n1 = 0 := h2 (ε ∘ Fin.natAdd n1) h_sq2'
  ext l
  exact Fin.addCases (fun i => by
    have := congr_fun h_ε_castAdd i
    simpa using this) (fun j => by
    have := congr_fun h_ε_natAdd j
    simpa using this) l

/-- `(bitv n a i).val` is the bit `i` of `a`. -/
theorem bitv_val_eq_ite (n a : ℕ) (i : Fin n) :
    (bitv n a i).val = if a.testBit i then 1 else 0 := by
  unfold bitv
  split_ifs <;> rfl

/-- **The `F₂` identity of `relAtV_of_coords` from bitmasks**: bit `s` of `βB j` is the parity of
`β j s`, bit `i` of `SBB j` the parity of `SB i j`, and the xor of the generator rows selected by
`βB j` and of the point rows selected by `SBB j` is the xor of the scalar rows selected by `cB j`. -/
theorem hcert_rel_of_bits {nb m r mκ : ℕ} (CgB AμB AκB : ℕ → ℕ) (β : Fin 4 → Fin m → ℕ)
    (SB : Matrix (Fin r) (Fin 4) ℤ) (βB SBB cB : Fin 4 → ℕ)
    (hβ : ∀ j s, ((β j s : ℕ) : ZMod 2) = bitv m (βB j) s)
    (hSB : ∀ i j, ((SB i j : ℤ) : ZMod 2) = bitv r (SBB j) i)
    (h : ∀ j, xorSel CgB m (βB j) ^^^ xorSel AμB r (SBB j) = xorSel AκB mκ (cB j)) :
    ∀ j, ∑ s, ((β j s : ℕ) : ZMod 2) • bitv nb (CgB s) + ∑ i, ((SB i j : ℤ) : ZMod 2) • bitv nb (AμB i) =
      ∑ l, bitv mκ (cB j) l • bitv nb (AκB l) := by
  intro j
  have hj := h j
  have hbitv := congrArg (bitv nb) hj
  rw [bitv_xor] at hbitv
  rw [bitv_xorSel, bitv_xorSel, bitv_xorSel] at hbitv
  have hsum1 : (∑ s : Fin m, bitv m (βB j) s • bitv nb (CgB s)) =
      (∑ s : Fin m, ((β j s : ℕ) : ZMod 2) • bitv nb (CgB s)) := by
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [← hβ j s]
  have hsum2 : (∑ i : Fin r, bitv r (SBB j) i • bitv nb (AμB i)) =
      (∑ i : Fin r, ((SB i j : ℤ) : ZMod 2) • bitv nb (AμB i)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← hSB i j]
  rw [hsum1, hsum2] at hbitv
  exact hbitv

/-- `Λ² U(α) = tL` from `okT`, `0 < d` and `d ∣ Λ²`. -/
theorem PtData.aeval_alphaR_U' {pt : PtData} (hd : 0 < pt.d) (hmL : pt.lamL ^ 2 % pt.d = 0)
    (hT : pt.okT = true) : (pt.lamL : L42) ^ 2 * aeval alphaR pt.U = mkL pt.tL := by
  simp only [PtData.okT, Bool.and_eq_true] at hT
  have h := aeval_pQ_of_checkL TowerFacts.alphaDen_ne_zero one_ne_zero (n := 2)
    (by simp [PtData.csL]) (by simp [PtData.csL, TowerChecks.tabA])
    (fun i hi => TowerFacts.tabA_spec i (by simp [PtData.csL] at hi; omega)) hT.1
  rw [PtData.pQ_csL (by omega) (Nat.dvd_of_mod_eq_zero hmL), map_mul, aeval_C, map_pow,
    map_natCast] at h
  rw [mkL_eq_evL]
  exact h

/-- `Λ² U(β) = tN` from `okT`, `0 < d` and `d ∣ Λ²`. -/
theorem PtData.aeval_betaR_U' {pt : PtData} (hd : 0 < pt.d) (hmN : pt.lamN ^ 2 % pt.d = 0)
    (hT : pt.okT = true) : (pt.lamN : N84) ^ 2 * aeval betaR pt.U = mkN pt.tN := by
  simp only [PtData.okT, Bool.and_eq_true] at hT
  have h := aeval_pQ_of_checkN TowerFacts.betaPowDen_ne_zero one_ne_zero (n := 2)
    (by simp [PtData.csN]) (by simp [PtData.csN, TowerChecks.tabB])
    (fun i hi => TowerFacts.tabB_spec i (by simp [PtData.csN] at hi; omega)) hT.2
  rw [PtData.pQ_csN (by omega) (Nat.dvd_of_mod_eq_zero hmN), map_mul, aeval_C, map_pow,
    map_natCast] at h
  rw [mkN_eq_evN]
  exact h

end FurioLombardo.Discharge.SelmerBasis
