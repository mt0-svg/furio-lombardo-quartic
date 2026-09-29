import FurioLombardo.Discharge.SelmerBasis.W7Model
import FurioLombardo.Discharge.SelmerBasis.AssemblyData
import FurioLombardo.Discharge.SelmerBasis.GlobalGens
import FurioLombardo.Discharge.SelmerBasis.LocalGlue
import FurioLombardo.Discharge.SelmerBasis.PointGen
import FurioLombardo.Discharge.SelmerBasis.VGen

/-!
# `CoordCond` at `w7` from the checked data (lane selmer-p7)

`Checks` gathers the statements of the W7Check files (W7Spec.lean) about data `tab, M, pts, pairs, cL, cN,
cK, Akap, Amu, Cg, QI, TI, QC, nQI`, with `pts.length = 4` and `2 ≤ M.N`. From them, in the model of
W7Model.lean (`G = (Fin 4 → K_w7ˣ) × F'ˣ`, basis `bW` of `G / G²`, 10 bits):

* `hAkap`, `hAmu`, `hCg`: the rows of the scalars `π, -1`, of the three points `D7 i` and of the 82 global
  generators, one certificate per component (`sqK`, `sqF`);
* `indepImage_w7_of`, `imageIn_w7_of` (with `Count.countBound_w7`);
* `coordCond_w7_of`: `CoordCond` at `w7` for the image of `μ` and the rows `Assembly.C7Rows`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.M3b FurioLombardo.Discharge
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin FurioLombardo.M3a.Genus2
  FurioLombardo.Discharge.SelmerBasis.GlobalK21
open FurioLombardo.M2.Special (al7)
open scoped FurioLombardo.Discharge.SelmerBasis.Adic

namespace FurioLombardo.Discharge.SelmerBasis.W7

instance goodSextic7 : GoodSextic ((fRev 1).map σ7) :=
  goodSextic_fRev_map σ7 1 (by rw [fRev_leadingCoeff]; exact Count.not_isSquare_c_w7)

/-! ## The checks -/

/-- The W7Check statements (W7Spec.lean), with `pts.length = 4` and `2 ≤ M.N`. -/
structure Checks (tab : List (List ℤ)) (tabK : List ℕ) (M : Model) (pts : List PtSq)
    (pairs : List PairData) (cL : List (KCert × KCert)) (cN : List (KCert × KCert × FCert))
    (cK : List FCert) (Akap Amu Cg QI TI QC : List ℕ) (nQI : ℕ) : Prop where
  tab_len : tab.length = 9
  tab_zero : tab.getD 0 [] = al7
  ck_tab : ∀ i, i < 8 → powOK tab (tabK.getD i 0) i = true
  ck_M : M.ok tab = true
  hN : 2 ≤ M.N
  pts_len : pts.length = 4
  ck_pt : ∀ i, i < 4 → (pts.getD i default).ok tab = true
  ck_pair : ∀ i, i < 3 → (pairs.getD i default).okU tab pts = true ∧
    (pairs.getD i default).toPt.okT = true ∧ (pairs.getD i default).okC tab M = true
  ck_L : ∀ s, s < 29 → okL tab M (cL.getD s default) s = true
  ck_N : ∀ s, s < 53 → okN tab M (cN.getD s default) s = true
  ck_K : ∀ i, i < 2 → (cK.getD i default).ok tab M.N M.E4U (kapXE i) (.int 0) = true
  kap_bits : ∀ i, i < 2 → Akap.getD i 0 = kapLow i + 256 * (cK.getD i default).bits
  mu_bits : ∀ i, i < 3 → Amu.getD i 0 = (pairs.getD i default).bits
  cgL_bits : ∀ s, s < 29 → Cg.getD s 0 = bitsL (cL.getD s default)
  cgN_bits : ∀ s, s < 53 → Cg.getD (29 + s) 0 = bitsN (cN.getD s default)
  annI : annOK 10 (fun l => Akap.getD l 0) 2 (fun q => QI.getD q 0) nQI = true
  leftInv : leftInvOK (fun q => dotRow 10 (fun i => Amu.getD i 0) (QI.getD q 0) 3) nQI 3
    (fun q => TI.getD q 0) = true
  annCk : annOK 10 (fun l => Akap.getD l 0) 2 (fun q => QC.getD q 0) 5 = true
  annCm : annOK 10 (fun i => Amu.getD i 0) 3 (fun q => QC.getD q 0) 5 = true
  c7_rows : ∀ q, q < 5 → dotRow 10 (fun s => Cg.getD s 0) (QC.getD q 0) 82 =
    Assembly.C7Rows.getD q 0

/-! ## Row arithmetic -/

theorem bitv2_mod (n : ℕ) : bitv 2 n = bitv 2 (n % 4) := by
  funext i
  have h : (n % 2 ^ 2).testBit i.val = n.testBit i.val := by
    rw [Nat.testBit_mod_two_pow]; simp [i.isLt]
  simp only [bitv]
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, h]

theorem bitv2_row (a : Fin 4 → ℕ) (a' : ℕ) (ha : ∀ c, a c < 4) (c : Fin 4) :
    bitv 2 ((a 0 + 4 * a 1 + 16 * a 2 + 64 * a 3 + 256 * a') >>> (2 * c.val)) = bitv 2 (a c) := by
  rw [bitv2_mod, bitv2_mod (a c), Nat.shiftRight_eq_div_pow]
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2; have h3 := ha 3
  congr 1
  fin_cases c <;> simp <;> omega

theorem bitv2_row' (a : Fin 4 → ℕ) (a' : ℕ) (ha : ∀ c, a c < 4) :
    bitv 2 ((a 0 + 4 * a 1 + 16 * a 2 + 64 * a 3 + 256 * a') >>> 8) = bitv 2 a' := by
  rw [Nat.shiftRight_eq_div_pow]
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2; have h3 := ha 3
  congr 1
  omega

theorem isSquare_row7 {F F' : Type*} [Field F] [Field F'] (b : Fin 2 → F) (b' : Fin 2 → F')
    (hb : ∀ i, b i ≠ 0) (hb' : ∀ i, b' i ≠ 0) (x : (Fin 4 → Fˣ) × F'ˣ) (a : Fin 4 → ℕ) (a' : ℕ)
    (ha : ∀ c, a c < 4)
    (h : ∀ c, IsSquare ((x.1 c : F) * ∏ i : Fin 2, b i ^ (bitv 2 (a c) i).val))
    (h' : IsSquare ((x.2 : F') * ∏ i : Fin 2, b' i ^ (bitv 2 a' i).val)) :
    IsSquare (x * ∏ l, b7 b b' hb hb' l ^
      (bitv 10 (a 0 + 4 * a 1 + 16 * a 2 + 64 * a 3 + 256 * a') l).val) :=
  isSquare_mul_rows7 b b' hb hb' x _ (fun c => by rw [bitv2_row a a' ha c]; exact h c)
    (by rw [bitv2_row' a a' ha]; exact h')

theorem KCert.bits_lt (c : KCert) : c.bits < 4 := by
  unfold KCert.bits; split_ifs <;> norm_num

theorem FCert.bits_lt (c : FCert) : c.bits < 4 := by
  unfold FCert.bits; split_ifs <;> norm_num

theorem isSquare_one_mul_bits0 {F : Type*} [Field F] (b : Fin 2 → F) :
    IsSquare ((1 : F) * ∏ i : Fin 2, b i ^ (bitv 2 0 i).val) := by
  simp [bitv]

/-! ## The basis and the component squares -/

variable {tab : List (List ℤ)} {M : Model}

/-- `π, -1` at `K_w7`. -/
noncomputable def bK : Fin 2 → K7 := ![π7, -1]

theorem bK_ne_zero : ∀ i, bK i ≠ 0 := by
  intro i; fin_cases i
  · exact unif7.ne_zero
  · simp [bK]

/-- `Z, -1` at `F'`. -/
noncomputable def bF7 (H : Hyp tab M) : Fin 2 → F7 H := ![Z7 H, -1]

theorem unifZ (H : Hyp tab M) : NormUnif (Z7 H) := qfE_normUnif unif7 (A4_norm H) (by simp)

theorem bF7_ne_zero (H : Hyp tab M) : ∀ i, bF7 H i ≠ 0 := by
  intro i; fin_cases i
  · exact (unifZ H).ne_zero
  · simp [bF7]

/-- The basis of `G / G²`. -/
noncomputable def bW (H : Hyp tab M) : Fin 10 → (Fin 4 → K7ˣ) × (F7 H)ˣ :=
  b7 bK (bF7 H) bK_ne_zero (bF7_ne_zero H)

theorem hind7 (H : Hyp tab M) : ∀ ε : Fin 10 → ZMod 2, IsSquare (∏ l, bW H l ^ (ε l).val) → ε = 0 :=
  indep_rows7 _ _ _ _ (indep_pi_u unif7 two7 ferm7 negOne7.1 negOne7.2)
    (indep_pi_u (unifZ H) (qf_norm_two two7) (qfE_fermat unif7 (A4_norm H) (by simp) ferm7)
      (u := -1) (by simp) (by
        rw [show (-1 : F7 H) ^ 171 = -1 by norm_num, neg_add_cancel, norm_zero]; exact one_pos))

theorem natCast_ne7 {lam : ℕ} (h : lam ≠ 0) : (lam : K7) ≠ 0 := by
  rw [← map_natCast σ7]; exact (_root_.map_ne_zero σ7).mpr (Nat.cast_ne_zero.mpr h)

theorem natCast_neF (H : Hyp tab M) {lam : ℕ} (h : lam ≠ 0) : (lam : F7 H) ≠ 0 := by
  rw [← map_natCast (algebraMap K7 (F7 H))]; exact (_root_.map_ne_zero _).mpr (natCast_ne7 h)

/-- **A component `K_w7` from a `KCert`.** -/
theorem sqK (H : Hyp tab M) {X : KE} {c : KCert} (hc : c.ok tab M.N X = true) {y : K7} {lam : ℕ}
    (hlam : lam ≠ 0) (hy : ‖(lam : K7) ^ 2 * y - σ7 (evK X)‖ ≤ δ7 M) :
    IsSquare (y * ∏ i : Fin 2, bK i ^ (bitv 2 c.bits i).val) := by
  have h := KCert.sound σ7 int7 unif7 two7 H.h0 H.hsq hc hy
  refine isSquare_of_sq_mul (natCast_ne7 hlam) ?_
  rw [← mul_assoc]; exact h

/-- **The component `F'` from an `FCert`.** -/
theorem sqF (H : Hyp tab M) {X Y : KE} {c : FCert} (hc : c.ok tab M.N M.E4U X Y = true) {y : F7 H}
    {lam : ℕ} (hlam : lam ≠ 0) {u v : K7} (hy : (lam : F7 H) ^ 2 * y = QF.mk K7 (A4 H) 0 u v)
    (hu : ‖u - σ7 (evK X)‖ ≤ δ7 M) (hv : ‖v - σ7 (evK Y)‖ ≤ δ7 M) :
    IsSquare (y * ∏ i : Fin 2, bF7 H i ^ (bitv 2 c.bits i).val) := by
  have h := FCert.sound σ7 int7 unif7 two7 H.h0 H.hsq (A4_norm H) (A4_near H) hc hu hv
  refine isSquare_of_sq_mul (natCast_neF H hlam) ?_
  rw [← mul_assoc, hy]; exact h

/-! ## Scalars -/

/-- `π`, `-1` as units of `K_w7`. -/
noncomputable def κ0 (l : Fin 2) : K7ˣ := Units.mk0 (bK l) (bK_ne_zero l)

theorem hspan7 (x : K7) (hx : x ≠ 0) :
    ∃ c : Fin 2 → ZMod 2, IsSquare (x * ∏ l, (κ0 l : K7) ^ (c l).val) := by
  obtain ⟨c, hc⟩ := sb_span_odd unif7 two7 ferm7 euler7 negOne7.1 negOne7.2 x hx
  exact ⟨c, by simpa only [κ0, Units.val_mk0, bK] using hc⟩

/-- The subgroup of the scalars. -/
noncomputable def Ksub (H : Hyp tab M) : Subgroup ((Fin 4 → K7ˣ) × (F7 H)ˣ) :=
  ((evG H).comp (Units.map (algebraMap K7 (AdjoinRoot ((fRev 1).map σ7))).toMonoidHom)).range

theorem hK (H : Hyp tab M) :
    ∀ x ∈ Ksub H, ∃ c : Fin 2 → ZMod 2, IsSquare (x * ∏ l, (evG H (Units.map
      (algebraMap K7 (AdjoinRoot ((fRev 1).map σ7))).toMonoidHom (κ0 l))) ^ (c l).val) :=
  hK_of_span (evG H) κ0 hspan7

/-- The scalars in `G`. -/
noncomputable def kapG (H : Hyp tab M) (l : Fin 2) : (Fin 4 → K7ˣ) × (F7 H)ˣ :=
  evG H (Units.map (algebraMap K7 (AdjoinRoot ((fRev 1).map σ7))).toMonoidHom (κ0 l))

theorem algebraMap_F7 (H : Hyp tab M) (t : K7) : algebraMap K7 (F7 H) t = QF.mk K7 (A4 H) 0 t 0 := by
  change algebraMap K7 (QuadraticAlgebra K7 (A4 H) 0) t = ⟨t, 0⟩
  exact QuadraticAlgebra.ext (QuadraticAlgebra.algebraMap_re (a := A4 H) (b := 0) t)
    (QuadraticAlgebra.algebraMap_im (a := A4 H) (b := 0) t)

/-- The bit pair of the scalar `l` at the four components `K_w7`. -/
def kl (l : Fin 2) : ℕ := if l.val = 0 then 1 else 2

theorem kapLow_row (l : Fin 2) (k : ℕ) :
    kapLow l + 256 * k = kl l + 4 * kl l + 16 * kl l + 64 * kl l + 256 * k := by
  fin_cases l <;> simp [kapLow, kl]

theorem hAkap {tabK : List ℕ} {pts : List PtSq} {pairs : List PairData} {cL : List (KCert × KCert)}
    {cN : List (KCert × KCert × FCert)} {cK : List FCert} {Akap Amu Cg QI TI QC : List ℕ} {nQI : ℕ}
    (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (H : Hyp tab M) (l : Fin 2) :
    IsSquare (kapG H l * ∏ i, bW H i ^ (bitv 10 (Akap.getD l 0) i).val) := by
  rw [C.kap_bits l l.isLt, kapLow_row]
  refine isSquare_row7 bK (bF7 H) bK_ne_zero (bF7_ne_zero H) (kapG H l) (fun _ => kl l)
    (cK.getD l default).bits (fun _ => by unfold kl; split_ifs <;> norm_num) (fun c => ?_) ?_
  · have hx : (((kapG H l).1 c : K7ˣ) : K7) = bK l := by
      rw [kapG, evG_fst]; exact ev4_algebraMap H c _
    rw [hx]
    have e1 : bitv 2 1 = ![1, 0] := by decide
    have e2 : bitv 2 2 = ![0, 1] := by decide
    have v1 : (1 : ZMod 2).val = 1 := rfl
    fin_cases l
    · refine ⟨π7, ?_⟩
      simp [bK, kl, e1, v1, Fin.prod_univ_two]
    · refine ⟨1, ?_⟩
      simp [bK, kl, e2, v1, Fin.prod_univ_two]
  · have hx : (((kapG H l).2 : (F7 H)ˣ) : F7 H) = QF.mk K7 (A4 H) 0 (bK l) 0 := by
      rw [kapG, evG_snd]
      exact (ev'_algebraMap H (κ0 l : K7)).trans (algebraMap_F7 H _)
    refine sqF H (C.ck_K l l.isLt) one_ne_zero (u := bK l) (v := 0) ?_ ?_ ?_
    · rw [hx, Nat.cast_one, one_pow, one_mul]
    · fin_cases l <;> simp [bK, kapXE]
    · simp

/-! ## The points -/

theorem pt_sq (H : Hyp tab M) {p : PtSq} (hp : p.ok tab = true) :
    ∃ y : K7, y ^ 2 = ((fRev 1).map σ7).eval (σ7 (zkE p.x)) ∧ y ≠ 0 := by
  obtain ⟨⟨y, hy⟩, hne⟩ := PtSq.sound σ7 int7 unif7 two7 H.h0 H.hsq hp
  refine ⟨y, ?_, ?_⟩
  · rw [Polynomial.eval_map, Polynomial.eval₂_hom, hy, sq]
  · rintro rfl
    exact hne ((map_eq_zero σ7).mp (by rw [hy, zero_mul]))

/-! ## The data -/

variable {tabK : List ℕ} {pts : List PtSq} {pairs : List PairData} {cL : List (KCert × KCert)}
  {cN : List (KCert × KCert × FCert)} {cK : List FCert} {Akap Amu Cg QI TI QC : List ℕ} {nQI : ℕ}

/-- The model hypotheses from the checks. -/
theorem Checks.hyp (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) : Hyp tab M :=
  ⟨C.tab_zero, fun i hi => powOK_sq (C.ck_tab i (by rw [C.tab_len] at hi; omega)), C.ck_M, C.hN⟩

/-- **The point `P_i1 + P_i2 - ∞` of the pair `i`**, with `μ = [U]`. -/
theorem exists_D7 (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (i : Fin 3) :
    ∃ (D : Jac ((fRev 1).map σ7))
      (hu : IsUnit (AdjoinRoot.mk ((fRev 1).map σ7) ((pairs.getD i default).toPt.U.map σ7))),
      muJ ((fRev 1).map σ7) D = QuotientGroup.mk hu.unit := by
  have hH := C.hyp
  have hU := (C.ck_pair i i.isLt).1
  simp only [PairData.okU, Bool.and_eq_true, decide_eq_true_eq] at hU
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, hdv⟩, cd1⟩, ud⟩, cP⟩, cR⟩ := hU
  rw [C.pts_len] at h1 h2
  obtain ⟨y1, hy1, hy1'⟩ := pt_sq hH (C.ck_pt _ h1)
  obtain ⟨y2, hy2, hy2'⟩ := pt_sq hH (C.ck_pt _ h2)
  have ed := evK_eq_of_check _ _ _ cd1
  rw [evK_mul, evK_alPw hH.h0 hH.hsq hdv] at ed
  simp only [evK_sub, evK_lin] at ed
  have eP := evK_eq_of_check _ _ _ cP
  have eR := evK_eq_of_check _ _ _ cR
  simp only [evK_sub, evK_add, evK_mul, evK_lin, evK_int, Int.cast_zero] at eP eR
  have hx : σ7 (zkE (pts.getD (pairs.getD i default).i1 default).x) ≠
      σ7 (zkE (pts.getD (pairs.getD i default).i2 default).x) := by
    intro hx
    have h0 : σ7 (zkE al7 ^ (pairs.getD i default).dv * zkE (pairs.getD i default).dW) = 0 := by
      rw [← ed, map_sub, hx, sub_self]
    rw [map_mul, map_pow] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact pow_ne_zero _ unif7.ne_zero h
    · have hn := norm_unit σ7 int7 unif7 ud
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
  have e_U : uTwo (σ7 (zkE (pts.getD (pairs.getD i default).i1 default).x))
      (σ7 (zkE (pts.getD (pairs.getD i default).i2 default).x)) =
      (pairs.getD i default).toPt.U.map σ7 := by
    simp only [PtData.U, PairData.toPt, SelmerSpan.quad, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Nat.cast_one, div_one, eP, eR, uTwo]
    simp only [map_sub, map_add, map_mul, map_zero]
    ring
  rw [← e_U]
  exact exists_jac_two _ hx hy1 hy2 hy1' hy2'

/-- The three points. -/
noncomputable def D7 (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (i : Fin 3) :
    Jac ((fRev 1).map σ7) :=
  (exists_D7 C i).choose

/-- Their `U(T)`. -/
noncomputable def U7 (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (i : Fin 3) :
    (AdjoinRoot ((fRev 1).map σ7))ˣ :=
  (exists_D7 C i).choose_spec.choose.unit

theorem muJ_D7 (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (i : Fin 3) :
    muJ ((fRev 1).map σ7) (D7 C i) = QuotientGroup.mk (U7 C i) :=
  (exists_D7 C i).choose_spec.choose_spec

theorem U7_coe (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (i : Fin 3) :
    (U7 C i : AdjoinRoot ((fRev 1).map σ7)) =
      AdjoinRoot.mk _ ((pairs.getD i default).toPt.U.map σ7) :=
  (exists_D7 C i).choose_spec.choose.unit_spec

/-! ## The rows of the points and of the generators -/

theorem hAmu (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (i : Fin 3) :
    IsSquare (evG C.hyp (U7 C i) * ∏ j, bW C.hyp j ^ (bitv 10 (Amu.getD i 0) j).val) := by
  have hU := (C.ck_pair i i.isLt).1
  simp only [PairData.okU, Bool.and_eq_true, decide_eq_true_eq] at hU
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlL, hlN⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hU
  have hT := (C.ck_pair i i.isLt).2.1
  have hC := (C.ck_pair i i.isLt).2.2
  simp only [PairData.okC, Bool.and_eq_true] at hC
  obtain ⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩ := hC
  have hL : ((pairs.getD i default).lamL : L42) ^ 2 * aeval alphaR (pairs.getD i default).toPt.U =
      mkL (pairs.getD i default).tL :=
    PtData.aeval_alphaR_U' (pt := (pairs.getD i default).toPt) one_pos (Nat.mod_one _) hT
  have hN : ((pairs.getD i default).lamN : N84) ^ 2 * aeval betaR (pairs.getD i default).toPt.U =
      mkN (pairs.getD i default).tN :=
    PtData.aeval_betaR_U' (pt := (pairs.getD i default).toPt) one_pos (Nat.mod_one _) hT
  obtain ⟨e0, e1, e2, e3⟩ := ev4_mk C.hyp (pairs.getD i default).toPt.U
  have e4 := ev'_mk C.hyp (pairs.getD i default).toPt.U
  have h0 : IsSquare (((evG C.hyp (U7 C i)).1 0 : K7) *
      ∏ j : Fin 2, bK j ^ (bitv 2 (pairs.getD i default).c0.bits j).val) := by
    rw [evG_fst, U7_coe, e0]
    refine sqK C.hyp c0 hlL.ne' ?_
    have h := congrArg (ιp C.hyp) hL
    rw [map_mul, map_pow, map_natCast, mkL_eq_evL] at h
    rw [h]; exact approxLp _ _
  have h1 : IsSquare (((evG C.hyp (U7 C i)).1 1 : K7) *
      ∏ j : Fin 2, bK j ^ (bitv 2 (pairs.getD i default).c1.bits j).val) := by
    rw [evG_fst, U7_coe, e1]
    refine sqK C.hyp c1 hlL.ne' ?_
    have h := congrArg (ιm C.hyp) hL
    rw [map_mul, map_pow, map_natCast, mkL_eq_evL] at h
    rw [h]; exact approxLm _ _
  have h2 : IsSquare (((evG C.hyp (U7 C i)).1 2 : K7) *
      ∏ j : Fin 2, bK j ^ (bitv 2 (pairs.getD i default).c2.bits j).val) := by
    rw [evG_fst, U7_coe, e2]
    refine sqK C.hyp c2 hlN.ne' ?_
    have h := congrArg (ιN C.hyp true) hN
    rw [map_mul, map_pow, map_natCast, mkN_eq_evN] at h
    rw [h]; exact approxN _ _ _
  have h3 : IsSquare (((evG C.hyp (U7 C i)).1 3 : K7) *
      ∏ j : Fin 2, bK j ^ (bitv 2 (pairs.getD i default).c3.bits j).val) := by
    rw [evG_fst, U7_coe, e3]
    refine sqK C.hyp c3 hlN.ne' ?_
    have h := congrArg (ιN C.hyp false) hN
    rw [map_mul, map_pow, map_natCast, mkN_eq_evN] at h
    rw [h]; exact approxN _ _ _
  have h4 : IsSquare (((evG C.hyp (U7 C i)).2 : F7 C.hyp) *
      ∏ j : Fin 2, bF7 C.hyp j ^ (bitv 2 (pairs.getD i default).c4.bits j).val) := by
    rw [evG_snd, U7_coe, e4]
    refine sqF C.hyp c4 hlN.ne' ?_ (approxLm C.hyp (ofN (pairs.getD i default).tN).1)
      (approxLm C.hyp (ofN (pairs.getD i default).tN).2)
    have h := congrArg (ι' C.hyp) hN
    rw [map_mul, map_pow, map_natCast, mkN_eq_evN, approx'] at h
    exact h
  rw [C.mu_bits i i.isLt]
  refine isSquare_row7 bK (bF7 C.hyp) bK_ne_zero (bF7_ne_zero C.hyp) (evG C.hyp (U7 C i))
    ![(pairs.getD i default).c0.bits, (pairs.getD i default).c1.bits, (pairs.getD i default).c2.bits,
      (pairs.getD i default).c3.bits] (pairs.getD i default).c4.bits
    (fun c => by fin_cases c <;> exact KCert.bits_lt _) (fun c => ?_) h4
  fin_cases c
  exacts [h0, h1, h2, h3]

theorem hCg (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) (s : Fin 82) :
    IsSquare (evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom (gKu 1 s)) *
      ∏ j, bW C.hyp j ^ (bitv 10 (Cg.getD s 0) j).val) := by
  have hg : ∀ s : Fin 82, (((Units.map (etaleMap σ7 (fRev 1)).toMonoidHom (gKu 1 s)) :
      (AdjoinRoot ((fRev 1).map σ7))ˣ) : AdjoinRoot ((fRev 1).map σ7)) =
      etaleMap σ7 (fRev 1) (AdjoinRoot.mk _ (Pgen s)) := fun s => by
    change etaleMap σ7 (fRev 1) (gKu 1 s : AdjoinRoot (fRev 1)) = _
    rw [gKu_coe]
  revert s
  show ∀ s : Fin (29 + 53), _
  intro s
  refine Fin.addCases (fun i => ?_) (fun j => ?_) s
  · obtain ⟨e0, e1, e2, e3⟩ := ev4_etale C.hyp (Pgen (Fin.castAdd 53 i))
    have e4 := ev'_etale C.hyp (Pgen (Fin.castAdd 53 i))
    have cc := C.ck_L i i.isLt
    simp only [okL, Bool.and_eq_true] at cc
    have h0 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.castAdd 53 i)))).1 0 : K7ˣ) : K7) *
        ∏ j : Fin 2, bK j ^ (bitv 2 (cL.getD i default).1.bits j).val) := by
      rw [evG_fst, hg, e0, Pgen_alphaR_left]
      refine sqK C.hyp cc.1 one_ne_zero ?_
      rw [Nat.cast_one, one_pow, one_mul]
      exact approxLp C.hyp (ofL (SUnitData.gL.getD i []))
    have h1 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.castAdd 53 i)))).1 1 : K7ˣ) : K7) *
        ∏ j : Fin 2, bK j ^ (bitv 2 (cL.getD i default).2.bits j).val) := by
      rw [evG_fst, hg, e1, Pgen_alphaR_left]
      refine sqK C.hyp cc.2 one_ne_zero ?_
      rw [Nat.cast_one, one_pow, one_mul]
      exact approxLm C.hyp (ofL (SUnitData.gL.getD i []))
    have h2 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.castAdd 53 i)))).1 2 : K7ˣ) : K7) * ∏ j : Fin 2, bK j ^ (bitv 2 0 j).val) := by
      rw [evG_fst, hg, e2, Pgen_betaR_left, map_one]; exact isSquare_one_mul_bits0 _
    have h3 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.castAdd 53 i)))).1 3 : K7ˣ) : K7) * ∏ j : Fin 2, bK j ^ (bitv 2 0 j).val) := by
      rw [evG_fst, hg, e3, Pgen_betaR_left, map_one]; exact isSquare_one_mul_bits0 _
    have h4 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.castAdd 53 i)))).2 : (F7 C.hyp)ˣ) : F7 C.hyp) *
        ∏ j : Fin 2, bF7 C.hyp j ^ (bitv 2 0 j).val) := by
      rw [evG_snd, hg, e4, Pgen_betaR_left, map_one]; exact isSquare_one_mul_bits0 _
    have hrow : Cg.getD (Fin.castAdd 53 i : ℕ) 0 = (cL.getD i default).1.bits +
        4 * (cL.getD i default).2.bits + 16 * 0 + 64 * 0 + 256 * 0 := by
      rw [Fin.val_castAdd, C.cgL_bits i i.isLt, bitsL]; ring
    rw [hrow]
    refine isSquare_row7 bK (bF7 C.hyp) bK_ne_zero (bF7_ne_zero C.hyp) _
      ![(cL.getD i default).1.bits, (cL.getD i default).2.bits, 0, 0] 0
      (fun c => by fin_cases c <;> first | exact KCert.bits_lt _ | norm_num) (fun c => ?_) h4
    fin_cases c
    exacts [h0, h1, h2, h3]
  · obtain ⟨e0, e1, e2, e3⟩ := ev4_etale C.hyp (Pgen (Fin.natAdd 29 j))
    have e4 := ev'_etale C.hyp (Pgen (Fin.natAdd 29 j))
    have cc := C.ck_N j j.isLt
    simp only [okN, Bool.and_eq_true] at cc
    obtain ⟨⟨k2, k3⟩, k4⟩ := cc
    have h0 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.natAdd 29 j)))).1 0 : K7ˣ) : K7) * ∏ j : Fin 2, bK j ^ (bitv 2 0 j).val) := by
      rw [evG_fst, hg, e0, Pgen_alphaR_right, map_one]; exact isSquare_one_mul_bits0 _
    have h1 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.natAdd 29 j)))).1 1 : K7ˣ) : K7) * ∏ j : Fin 2, bK j ^ (bitv 2 0 j).val) := by
      rw [evG_fst, hg, e1, Pgen_alphaR_right, map_one]; exact isSquare_one_mul_bits0 _
    have h2 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.natAdd 29 j)))).1 2 : K7ˣ) : K7) *
        ∏ j' : Fin 2, bK j' ^ (bitv 2 (cN.getD j default).1.bits j').val) := by
      rw [evG_fst, hg, e2, Pgen_betaR_right]
      refine sqK C.hyp k2 one_ne_zero ?_
      rw [Nat.cast_one, one_pow, one_mul]
      exact approxN C.hyp true (ofN (SUnitData.gN.getD j []))
    have h3 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.natAdd 29 j)))).1 3 : K7ˣ) : K7) *
        ∏ j' : Fin 2, bK j' ^ (bitv 2 (cN.getD j default).2.1.bits j').val) := by
      rw [evG_fst, hg, e3, Pgen_betaR_right]
      refine sqK C.hyp k3 one_ne_zero ?_
      rw [Nat.cast_one, one_pow, one_mul]
      exact approxN C.hyp false (ofN (SUnitData.gN.getD j []))
    have h4 : IsSquare ((((evG C.hyp (Units.map (etaleMap σ7 (fRev 1)).toMonoidHom
        (gKu 1 (Fin.natAdd 29 j)))).2 : (F7 C.hyp)ˣ) : F7 C.hyp) *
        ∏ j' : Fin 2, bF7 C.hyp j' ^ (bitv 2 (cN.getD j default).2.2.bits j').val) := by
      rw [evG_snd, hg, e4, Pgen_betaR_right]
      refine sqF C.hyp k4 one_ne_zero ?_ (approxLm C.hyp (ofN (SUnitData.gN.getD j [])).1)
        (approxLm C.hyp (ofN (SUnitData.gN.getD j [])).2)
      rw [Nat.cast_one, one_pow, one_mul]
      exact approx' C.hyp (ofN (SUnitData.gN.getD j []))
    have hrow : Cg.getD (Fin.natAdd 29 j : ℕ) 0 = 0 + 4 * 0 + 16 * (cN.getD j default).1.bits +
        64 * (cN.getD j default).2.1.bits + 256 * (cN.getD j default).2.2.bits := by
      rw [Fin.val_natAdd, C.cgN_bits j j.isLt, bitsN]; ring
    rw [hrow]
    refine isSquare_row7 bK (bF7 C.hyp) bK_ne_zero (bF7_ne_zero C.hyp) _
      ![0, 0, (cN.getD j default).1.bits, (cN.getD j default).2.1.bits] (cN.getD j default).2.2.bits
      (fun c => by fin_cases c <;> first | exact KCert.bits_lt _ | norm_num) (fun c => ?_) h4
    fin_cases c
    exacts [h0, h1, h2, h3]

/-! ## The local Props at `w7` -/

/-- **`IndepImage` at `w7`.** -/
theorem indepImage_w7_of (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) :
    IndepImage ((fRev 1).map σ7) (D7 C) :=
  indepImage_of_coords _ (D7 C) (U7 C) (muJ_D7 C) (evG C.hyp) (Ksub C.hyp) (fun c => ⟨c, rfl⟩)
    (bW C.hyp) (hind7 C.hyp) (kapG C.hyp) (fun l => ⟨κ0 l, rfl⟩) (hK C.hyp)
    (fun l => bitv 10 (Akap.getD l 0)) (hAkap C C.hyp) (fun i => bitv 10 (Amu.getD i 0)) (hAmu C)
    (hcert_indep_of_bits (fun l => Akap.getD l 0) (fun i => Amu.getD i 0) (fun q => QI.getD q 0)
      (fun q => TI.getD q 0) C.annI C.leftInv)

/-- **`ImageIn` at `w7`** for the closure of the three points. -/
theorem imageIn_w7_of (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) :
    ImageIn ((fRev 1).map σ7) (Subgroup.closure (Set.range fun i => muJ ((fRev 1).map σ7) (D7 C i))) :=
  imageIn_closure_of_count_indep _ (D7 C) Count.countBound_w7 (indepImage_w7_of C)

/-- **`CoordCond` at `w7`** for the image of `μ` and the rows `Assembly.C7Rows`. -/
theorem coordCond_w7_of (C : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI) :
    CoordCond σ7 (fRev 1) (gK 1) (muJ ((fRev 1).map σ7)).range
      (Matrix.of fun (i : Fin 5) (s : Fin 82) => bitv 82 (Assembly.C7Rows.getD i 0) s) := by
  have hC : (Matrix.of fun (i : Fin 5) (s : Fin 82) =>
      bitv 82 (dotRow 10 (fun s => Cg.getD s 0) (QC.getD i 0) 82) s) =
      Matrix.of fun (i : Fin 5) (s : Fin 82) => bitv 82 (Assembly.C7Rows.getD i 0) s := by
    ext i s
    simp only [Matrix.of_apply]
    rw [C.c7_rows i i.isLt]
  have h := coordCond_of_coords σ7 (fRev 1) (gKu 1) (D7 C) (U7 C) (muJ_D7 C) (evG C.hyp) (Ksub C.hyp)
    (fun c => ⟨c, rfl⟩) (bW C.hyp) (hind7 C.hyp) (kapG C.hyp) (fun l => ⟨κ0 l, rfl⟩) (hK C.hyp)
    (fun l => bitv 10 (Akap.getD l 0)) (hAkap C C.hyp) (fun i => bitv 10 (Amu.getD i 0)) (hAmu C)
    (fun s => bitv 10 (Cg.getD s 0)) (hCg C) _
    (hcert_coord_of_bits (fun l => Akap.getD l 0) (fun i => Amu.getD i 0) (fun s => Cg.getD s 0)
      (fun q => QC.getD q 0) C.annCk C.annCm)
  rw [hC] at h
  exact coordCond_range_of_imageIn σ7 (fRev 1) (gK 1) _ _ (imageIn_w7_of C) h

end FurioLombardo.Discharge.SelmerBasis.W7
