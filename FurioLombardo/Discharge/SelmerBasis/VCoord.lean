import FurioLombardo.Discharge.SelmerBasis.VCheckE
import FurioLombardo.Discharge.SelmerBasis.VCheckK
import FurioLombardo.Discharge.SelmerBasis.VCheckN1
import FurioLombardo.Discharge.SelmerBasis.VGlue
import FurioLombardo.Discharge.SelmerBasis.VCheckK0
import FurioLombardo.Discharge.SelmerBasis.VCheckK1
import FurioLombardo.Discharge.SelmerBasis.VCRT
import FurioLombardo.Discharge.SelmerBasis.VPlace
import FurioLombardo.Discharge.SelmerBasis.LocalGlue

/-!
# The place `v`: `CoordCond` and `RelAtV` for both twists (lane selmer-v)

`σ = M4Cert.σ : K21 →+* Kv` (`e = 3`, residue field `𝔽₂`). The model `E, M, S` of VData.lean is a
`WPlace` (`wplace`); `K_v[T]/(fRev_k)^σ ≅ F1 × F2` (`psiV`, VCRT.lean) with `F1 = CF σ E` (the root
`iL α` of `q`) and `F2 = UF σ E` (the root `iNv β` of `h`), and `evG k` is the units map onto
`G = F1ˣ × F2ˣ`, with the basis `bV` of `G / G²` (8 + 14 elements, `bP` of VGen.lean).

* rows (22 bits): `Akap` (the scalars `dyGen al l`), `AmuK` (lane SelmerSpan's points `Dpt k i`, exact
  `U`), `Cg` (the global generators), each from one square certificate per component (VCheck*.lean);
* `coordCond_v`: `coordCond_of_coords` with the forms `QCK k`, whose rows on the generators are the
  rows `Cv k` of VPlace.lean (`Cv_eq`);
* `relAtV_v`: `relAtV_of_coords` with the isomorphism `evG k` and the bitmasks `SBBK k`, `cBK k`
  (`hcert_rel_of_bits`).
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis.V

open Polynomial FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.M3b
  FurioLombardo.Discharge.SelmerSpan FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.SelmerBasis.GlobalK21

attribute [local instance] goodSextic_fRev_Kv

/-! ## The place -/

theorem al_eq : E.al = M2.Special.al1 := by decide

theorem e_eq : E.e = 3 := rfl

theorem wplace : WPlace σ E where
  int := int_v
  unif := by rw [al_eq]; exact normUnif_v
  two := by rw [e_eq, al_eq]; exact norm_two_v
  res := res_v
  ok := ck_E

instance instNoRoot : Fact (∀ r : Kv, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r) := ⟨wplace.noRoot⟩

instance instNoRootU : Fact (∀ r : CF σ E, r ^ 2 ≠ -1 + 1 * r) := ⟨noRoot_CF wplace⟩

/-- The Eisenstein component. -/
abbrev F1 : Type := CF σ E

/-- The unramified component. -/
abbrev F2 : Type := UF σ E

/-- `(K_v[T]/(fRev k)^σ)ˣ ≃* F1ˣ × F2ˣ`. -/
noncomputable abbrev evG (k : Fin 2) : (AdjoinRoot ((fRev k).map σ))ˣ ≃* F1ˣ × F2ˣ :=
  evV M S wplace ck_M ck_S k

theorem evG_fst_mk (k : Fin 2) (u : (AdjoinRoot ((fRev k).map σ))ˣ) (P : K21[X])
    (hu : (u : AdjoinRoot ((fRev k).map σ)) = AdjoinRoot.mk _ (P.map σ)) :
    (((evG k u).1 : F1ˣ) : F1) = iL σ E M ck_M (aeval alphaR P) := by
  rw [evG, evV_fst, hu, psiV_mk]

theorem evG_snd_mk (k : Fin 2) (u : (AdjoinRoot ((fRev k).map σ))ˣ) (P : K21[X])
    (hu : (u : AdjoinRoot ((fRev k).map σ)) = AdjoinRoot.mk _ (P.map σ)) :
    (((evG k u).2 : F2ˣ) : F2) = iNv σ E M wplace ck_M S ck_S (aeval betaR P) := by
  rw [evG, evV_snd, hu, psiV_mk]

theorem etaleMap_mk' (k : Fin 2) (P : K21[X]) :
    etaleMap σ (fRev k) (AdjoinRoot.mk (fRev k) P) = AdjoinRoot.mk ((fRev k).map σ) (P.map σ) := by
  rw [etaleMap, AdjoinRoot.map_mk]

/-! ## The basis of `G / G²` -/

/-- The number of bits of `F1`. -/
abbrev nb1 : ℕ := 2 * E.e + 2

/-- The number of bits of `F2`. -/
abbrev nb2 : ℕ := 2 * (2 * E.e) + 2

/-- The number of bits of a row. -/
abbrev nb : ℕ := nb1 + nb2

noncomputable def b1 : Fin nb1 → F1 := fun i => bF σ E i

noncomputable def b2 : Fin nb2 → F2 := fun i => bU (A := (-1 : F1)) (B := 1) (cY σ E) (2 * E.e) i

theorem b1_ne (i : Fin nb1) : b1 i ≠ 0 := bF_ne_zero wplace i

theorem b2_ne (i : Fin nb2) : b2 i ≠ 0 :=
  bU_ne_zero (qfE_normUnif wplace.unif wplace.norm_A wplace.norm_B)
    (qfE_res wplace.unif wplace.norm_A wplace.norm_B wplace.res) (by simp) (by simp) (by decide)
    (qfE_two wplace.unif wplace.norm_A wplace.norm_B wplace.two) i

/-- The basis of `G / G²`. -/
noncomputable def bV : Fin nb → F1ˣ × F2ˣ := bP b1 b2 b1_ne b2_ne

theorem hind : ∀ ε : Fin nb → ZMod 2, IsSquare (∏ i, bV i ^ (ε i).val) → ε = 0 :=
  indep_rowsP b1 b2 b1_ne b2_ne (bF_indep wplace (by decide))
    (bU_indep (qfE_normUnif wplace.unif wplace.norm_A wplace.norm_B)
      (qfE_res wplace.unif wplace.norm_A wplace.norm_B wplace.res) (by simp) (by simp) (by decide)
      (qfE_two wplace.unif wplace.norm_A wplace.norm_B wplace.two))

/-- **A row of `G` from its two components.** -/
theorem row_sqV (x : F1ˣ × F2ˣ) (A a1 a2 : ℕ) (h1b : A % 2 ^ nb1 = a1 % 2 ^ nb1)
    (h2b : (A >>> nb1) % 2 ^ nb2 = a2 % 2 ^ nb2) (h1 : IsSquare ((x.1 : F1) * Ba σ E a1))
    (h2 : IsSquare ((x.2 : F2) * BaU σ E a2)) :
    IsSquare (x * ∏ l, bV l ^ (bitv nb A l).val) := by
  refine isSquare_mul_rowsP b1 b2 b1_ne b2_ne x A ?_ ?_
  · have e1 : (∏ i : Fin nb1, b1 i ^ (bitv nb1 A i).val) = Ba σ E a1 := by
      rw [← bitv_mod_two_pow nb1 A, h1b, bitv_mod_two_pow]; rfl
    rw [e1]; exact h1
  · have e2 : (∏ i : Fin nb2, b2 i ^ (bitv nb2 (A >>> nb1) i).val) = BaU σ E a2 := by
      rw [← bitv_mod_two_pow nb2 (A >>> nb1), h2b, bitv_mod_two_pow]
      simp only [BaU, b2, bitv_val_eq_ite]
    rw [e2]; exact h2

/-! ## Squares at one component from a certificate -/

theorem natCast_ne_zero_F1 {n : ℕ} (hn : n ≠ 0) : (n : F1) ≠ 0 := by
  rw [← map_natCast (algebraMap Kv F1)]
  exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hn)

theorem natCast_ne_zero_F2 {n : ℕ} (hn : n ≠ 0) : (n : F2) ≠ 0 := by
  rw [← map_natCast (algebraMap F1 F2)]
  exact (_root_.map_ne_zero _).mpr (natCast_ne_zero_F1 hn)

/-- `F1`: `Λ² y = iL t` and a certificate for `t`. -/
theorem sqL {y : F1} {lam : ℕ} (hlam : lam ≠ 0) {t : List (List ℤ)} {cc : WCert}
    (hc : certOK E cc.n0 (X0L M (ofL t)) (X1L M (ofL t)) cc = true)
    (hy : (lam : F1) ^ 2 * y = iL σ E M ck_M (mkL t)) : IsSquare (y * Ba σ E cc.a) := by
  have h := certOK_isSquare wplace hc ((lam : F1) ^ 2 * y) (by
    rw [hy, mkL_eq_evL, iL_evL, sub_self, norm_zero]; positivity)
  refine isSquare_of_sq_mul (natCast_ne_zero_F1 hlam) ?_
  rwa [← mul_assoc]

/-- `F2`: `Λ² y = iNv t` and a certificate for the approximation `XNv` of `t`. -/
theorem sqN {y : F2} {lam : ℕ} (hlam : lam ≠ 0) {t : List (List ℤ)} {cc : UCert}
    (hc : certOKU E (2 * cc.n) (XNv E M S (ofN t)).1 (XNv E M S (ofN t)).2.1 (XNv E M S (ofN t)).2.2.1
      (XNv E M S (ofN t)).2.2.2 cc = true)
    (hn : cc.n ≤ S.n - E.e - S.j)
    (hy : (lam : F2) ^ 2 * y = iNv σ E M wplace ck_M S ck_S (mkN t)) :
    IsSquare (y * BaU σ E cc.a) := by
  have h := certOKU_isSquare wplace hc ((lam : F2) ^ 2 * y) (by
    rw [hy, mkN_eq_evN]
    exact (norm_iNv_evN_sub wplace ck_M ck_S (ofN t)).trans
      (pow_le_pow_of_le_one (norm_nonneg _) wplace.unif.norm_lt_one.le hn))
  refine isSquare_of_sq_mul (natCast_ne_zero_F2 hlam) ?_
  rwa [← mul_assoc]

theorem sq_one_Ba : IsSquare ((1 : F1) * Ba σ E 0) := by
  rw [Ba_zero, one_mul]; exact ⟨1, (mul_one 1).symm⟩

theorem BaU_zero : BaU σ E 0 = 1 := by
  simp [BaU]

theorem sq_one_BaU : IsSquare ((1 : F2) * BaU σ E 0) := by
  rw [BaU_zero, one_mul]; exact ⟨1, (mul_one 1).symm⟩

/-! ## The data per twist -/

def ptsK : Fin 2 → List PtData := ![K0.pts, K1.pts]
def cM1K : Fin 2 → List WCert := ![K0.cM1, K1.cM1]
def cM2K : Fin 2 → List UCert := ![K0.cM2, K1.cM2]
def AmuK : Fin 2 → List ℕ := ![K0.Amu, K1.Amu]
def QCK : Fin 2 → List ℕ := ![K0.QC, K1.QC]
def SBBK : Fin 2 → List ℕ := ![K0.SBB, K1.SBB]
def cBK : Fin 2 → List ℕ := ![K0.cB, K1.cB]

theorem ck_ptK (k : Fin 2) (i : Fin 7) : 0 < ((ptsK k).getD i default).d ∧
    ((ptsK k).getD i default).lamL ^ 2 % ((ptsK k).getD i default).d = 0 ∧
    ((ptsK k).getD i default).lamN ^ 2 % ((ptsK k).getD i default).d = 0 ∧
    ((ptsK k).getD i default).okT = true := by
  fin_cases k
  · exact K0.ck_pt i i.isLt
  · exact K1.ck_pt i i.isLt

theorem ck_MK (k : Fin 2) (i : Fin 7) :
    certOK E ((cM1K k).getD i default).n0 (X0L M (ofL ((ptsK k).getD i default).tL))
        (X1L M (ofL ((ptsK k).getD i default).tL)) ((cM1K k).getD i default) = true ∧
      certOKU E (2 * ((cM2K k).getD i default).n) (XNv E M S (ofN ((ptsK k).getD i default).tN)).1
        (XNv E M S (ofN ((ptsK k).getD i default).tN)).2.1
        (XNv E M S (ofN ((ptsK k).getD i default).tN)).2.2.1
        (XNv E M S (ofN ((ptsK k).getD i default).tN)).2.2.2 ((cM2K k).getD i default) = true := by
  fin_cases k
  · exact ⟨K0.ck_M1 i i.isLt, K0.ck_M2 i i.isLt⟩
  · exact ⟨K1.ck_M1 i i.isLt, K1.ck_M2 i i.isLt⟩

/-! ## Kernel facts on the data -/

theorem ak_bits : ∀ l : Fin 7, Akap.getD l 0 % 2 ^ nb1 = (cK1.getD l default).a % 2 ^ nb1 ∧
    (Akap.getD l 0 >>> nb1) % 2 ^ nb2 = (cK2.getD l default).a % 2 ^ nb2 := by
  decide +kernel

theorem mu_bits : ∀ (k : Fin 2) (i : Fin 7),
    (AmuK k).getD i 0 % 2 ^ nb1 = ((cM1K k).getD i default).a % 2 ^ nb1 ∧
      ((AmuK k).getD i 0 >>> nb1) % 2 ^ nb2 = ((cM2K k).getD i default).a % 2 ^ nb2 := by
  decide +kernel

theorem cgL_bits : ∀ i : Fin 29, Cg.getD i 0 % 2 ^ nb1 = (cL.getD i default).a % 2 ^ nb1 ∧
    (Cg.getD i 0 >>> nb1) % 2 ^ nb2 = 0 % 2 ^ nb2 := by
  decide +kernel

theorem cgN_bits : ∀ j : Fin 53, Cg.getD (29 + j) 0 % 2 ^ nb1 = 0 % 2 ^ nb1 ∧
    (Cg.getD (29 + j) 0 >>> nb1) % 2 ^ nb2 = (cN.getD j default).a % 2 ^ nb2 := by
  decide +kernel

theorem mu_n : ∀ (k : Fin 2) (i : Fin 7), ((cM2K k).getD i default).n ≤ S.n - E.e - S.j := by
  decide +kernel

theorem gN_n : ∀ j : Fin 53, (cN.getD j default).n ≤ S.n - E.e - S.j := by
  decide +kernel

/-! ## Rows -/

/-- The scalars `dyGen al l`. -/
noncomputable def kap0 (l : Fin 7) : Kvˣ :=
  Units.mk0 (dyGen (σ (zkE E.al)) l) (dyGen_ne_zero wplace.unif l)

/-- Their images in `G`. -/
noncomputable def kapG (k : Fin 2) (l : Fin 7) : F1ˣ × F2ˣ :=
  evG k (Units.map (algebraMap Kv (AdjoinRoot ((fRev k).map σ))).toMonoidHom (kap0 l))

theorem kapG_val (k : Fin 2) (l : Fin 7) :
    (((kapG k l).1 : F1ˣ) : F1) = toF σ E (evK (kapX E l)) (evK (.int 0)) ∧
      (((kapG k l).2 : F2ˣ) : F2) = toU σ E (kapX E l) (.int 0) (.int 0) (.int 0) := by
  have hl : (l : ℕ) < E.alPow.length := lt_of_lt_of_le l.isLt (by decide +kernel)
  have hx : toF σ E (evK (kapX E l)) (evK (.int 0)) = algebraMap Kv F1 (kap0 l : Kv) := by
    rw [toF_int_zero, evK_kapX wplace hl]; rfl
  have hpsi := psiV_algebraMap M S wplace ck_M ck_S k (kap0 l : Kv)
  refine ⟨?_, ?_⟩
  · rw [kapG, evG, evV_fst]
    exact (congrArg Prod.fst hpsi).trans hx.symm
  · rw [kapG, evG, evV_snd]
    refine (congrArg Prod.snd hpsi).trans ?_
    rw [algebraMap_Kv_UF, ← hx, toU, qf_mk_eq]
    simp [toF_eq]

theorem hAkap (k : Fin 2) (l : Fin 7) :
    IsSquare (kapG k l * ∏ i, bV i ^ (bitv nb (Akap.getD l 0) i).val) := by
  obtain ⟨b1e, b2e⟩ := ak_bits l
  obtain ⟨v1, v2⟩ := kapG_val k l
  refine row_sqV _ _ (cK1.getD l default).a (cK2.getD l default).a b1e b2e ?_ ?_
  · exact certOK_isSquare wplace (ck_K1 l l.isLt) _ (by rw [v1, sub_self, norm_zero]; positivity)
  · exact certOKU_isSquare wplace (ck_K2 l l.isLt) _ (by rw [v2, sub_self, norm_zero]; positivity)

/-! ## The points -/

/-- `U = X² + (P/d) X + R/d` with `P = (d/pM) pL`, `R = (d/rM) rL`. -/
theorem PtData.U_eq_quad (pt : PtData) {pL rL : List ℤ} {pM rM : ℕ} (hpM : 0 < pM) (hrM : 0 < rM)
    (hd : 0 < pt.d) (hpd : pt.d % pM = 0) (hrd : pt.d % rM = 0)
    (hP : pt.P = smulL ((pt.d / pM : ℕ) : ℤ) pL) (hR : pt.R = smulL ((pt.d / rM : ℕ) : ℤ) rL) :
    pt.U = quad (((pM : ℕ) : K21)⁻¹ * zkE pL) (((rM : ℕ) : K21)⁻¹ * zkE rL) := by
  have key : ∀ (L : List ℤ) (m : ℕ), 0 < m → pt.d % m = 0 →
      zkE (smulL ((pt.d / m : ℕ) : ℤ) L) / (pt.d : K21) = ((m : ℕ) : K21)⁻¹ * zkE L := by
    intro L m hm hdm
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hdm
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; omega
    rw [zkE_eq_dot, dot_smulL, ← zkE_eq_dot, hq, Nat.mul_div_cancel_left q hm]
    have hm' : (m : K21) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hq' : (q : K21) ≠ 0 := Nat.cast_ne_zero.mpr hq0
    push_cast
    field_simp
  rw [PtData.U, hP, hR, key pL pM hpM hpd, key rL rM hrM hrd]

/-- The points of the data are those of lane SelmerSpan, and `Λ ≠ 0`. -/
theorem pt_bits : ∀ (k : Fin 2) (i : Fin 7),
    0 < pMi k i ∧ 0 < rMi k i ∧ ((ptsK k).getD i default).d % pMi k i = 0 ∧
      ((ptsK k).getD i default).d % rMi k i = 0 ∧
      ((ptsK k).getD i default).P = smulL ((((ptsK k).getD i default).d / pMi k i : ℕ) : ℤ) (pLi k i) ∧
      ((ptsK k).getD i default).R = smulL ((((ptsK k).getD i default).d / rMi k i : ℕ) : ℤ) (rLi k i) ∧
      0 < ((ptsK k).getD i default).lamL ∧ 0 < ((ptsK k).getD i default).lamN := by
  decide +kernel

/-- `U(T)` for the point `Dv k i`. -/
noncomputable def Uu (k : Fin 2) (i : Fin 7) : (AdjoinRoot ((fRev k).map σ))ˣ := (isUnit_U k i).unit

theorem muJ_Dv (k : Fin 2) (i : Fin 7) :
    muJ ((fRev k).map σ) (Dv k i) = QuotientGroup.mk (Uu k i) := muJ_Dpt k i

/-- The `PtData` of a point has lane SelmerSpan's `U`. -/
theorem ptU_eq (k : Fin 2) (i : Fin 7) : ((ptsK k).getD i default).U.map σ = Uv k i := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := pt_bits k i
  rw [PtData.U_eq_quad _ h1 h2 (ck_ptK k i).1 h3 h4 h5 h6, quad_map]
  rfl

theorem Uu_coe (k : Fin 2) (i : Fin 7) :
    ((Uu k i : (AdjoinRoot ((fRev k).map σ))ˣ) : AdjoinRoot ((fRev k).map σ)) =
      AdjoinRoot.mk _ (((ptsK k).getD i default).U.map σ) := by
  rw [Uu, IsUnit.unit_spec, ptU_eq]

theorem hAmu (k : Fin 2) (i : Fin 7) :
    IsSquare (evG k (Uu k i) * ∏ j, bV j ^ (bitv nb ((AmuK k).getD i 0) j).val) := by
  obtain ⟨hd, hmL, hmN, hT⟩ := ck_ptK k i
  obtain ⟨c1, c2⟩ := ck_MK k i
  obtain ⟨b1e, b2e⟩ := mu_bits k i
  have hL := PtData.aeval_alphaR_U' hd hmL hT
  have hN := PtData.aeval_betaR_U' hd hmN hT
  obtain ⟨-, -, -, -, -, -, hlL, hlN⟩ := pt_bits k i
  refine row_sqV _ _ ((cM1K k).getD i default).a ((cM2K k).getD i default).a b1e b2e ?_ ?_
  · rw [evG_fst_mk k _ _ (Uu_coe k i)]
    refine sqL hlL.ne' c1 ?_
    rw [← hL, map_mul, map_pow, map_natCast]
  · rw [evG_snd_mk k _ _ (Uu_coe k i)]
    refine sqN hlN.ne' c2 (mu_n k i) ?_
    rw [← hN, map_mul, map_pow, map_natCast]

/-! ## The generators -/

theorem gK_coe (k : Fin 2) (s : Fin 82) :
    (((Units.map (etaleMap σ (fRev k)).toMonoidHom (gKu k s)) : (AdjoinRoot ((fRev k).map σ))ˣ) :
      AdjoinRoot ((fRev k).map σ)) = AdjoinRoot.mk _ ((Pgen s).map σ) := by
  change etaleMap σ (fRev k) (gKu k s : AdjoinRoot (fRev k)) = _
  rw [gKu_coe, etaleMap_mk']

theorem hCg (k : Fin 2) (s : Fin 82) :
    IsSquare (evG k (Units.map (etaleMap σ (fRev k)).toMonoidHom (gKu k s)) *
      ∏ j, bV j ^ (bitv nb (Cg.getD s 0) j).val) := by
  revert s
  show ∀ s : Fin (29 + 53), _
  intro s
  refine Fin.addCases (fun i => ?_) (fun j => ?_) s
  · obtain ⟨b1e, b2e⟩ := cgL_bits i
    refine row_sqV _ _ (cL.getD i default).a 0 b1e b2e ?_ ?_
    · rw [evG_fst_mk k _ _ (gK_coe k _), Pgen_alphaR_left]
      refine sqL one_ne_zero (ck_L i i.isLt) ?_
      rw [Nat.cast_one, one_pow, one_mul]; rfl
    · rw [evG_snd_mk k _ _ (gK_coe k _), Pgen_betaR_left, map_one]
      exact sq_one_BaU
  · obtain ⟨b1e, b2e⟩ := cgN_bits j
    refine row_sqV _ _ 0 (cN.getD j default).a b1e b2e ?_ ?_
    · rw [evG_fst_mk k _ _ (gK_coe k _), Pgen_alphaR_right, map_one]
      exact sq_one_Ba
    · rw [evG_snd_mk k _ _ (gK_coe k _), Pgen_betaR_right]
      refine sqN one_ne_zero (ck_N j j.isLt) (gN_n j) ?_
      rw [Nat.cast_one, one_pow, one_mul]; rfl

/-! ## Scalars -/

theorem hspan (x : Kv) (hx : x ≠ 0) :
    ∃ c : Fin 7 → ZMod 2, IsSquare (x * ∏ l, (kap0 l : Kv) ^ (c l).val) := by
  obtain ⟨c, hc⟩ := sb_span_dyadic wplace.unif (e := 3) (by norm_num) wplace.two wplace.res x hx
  refine ⟨c, ?_⟩
  simp only [kap0, Units.val_mk0]
  exact hc

/-- The subgroup of the scalars. -/
noncomputable def Ksub (k : Fin 2) : Subgroup (F1ˣ × F2ˣ) :=
  ((evG k).toMonoidHom.comp (Units.map (algebraMap Kv (AdjoinRoot ((fRev k).map σ))).toMonoidHom)).range

theorem hK (k : Fin 2) :
    ∀ x ∈ Ksub k, ∃ c : Fin 7 → ZMod 2, IsSquare (x * ∏ l, kapG k l ^ (c l).val) :=
  hK_of_span (evG k).toMonoidHom kap0 hspan

/-! ## F₂ certificates (kernel) -/

theorem annCk : ∀ k : Fin 2, annOK nb (fun l => Akap.getD l 0) 7 (fun q => (QCK k).getD q 0) 11 = true := by
  decide +kernel

theorem annCm : ∀ k : Fin 2,
    annOK nb (fun i => (AmuK k).getD i 0) 7 (fun q => (QCK k).getD q 0) 11 = true := by
  decide +kernel

theorem cv_rows : ∀ (k : Fin 2) (i : Fin 11),
    (CvRows k).getD i 0 = dotRow nb (fun s => Cg.getD s 0) ((QCK k).getD i 0) 82 := by
  decide +kernel

theorem Cv_eq (k : Fin 2) :
    Cv k = Matrix.of fun (i : Fin 11) (s : Fin 82) =>
      bitv 82 (dotRow nb (fun s => Cg.getD s 0) ((QCK k).getD i 0) 82) s := by
  ext i s
  simp only [Cv, Matrix.of_apply, cv_rows k i]

theorem rel_xor : ∀ (k : Fin 2) (j : Fin 4),
    xorSel (fun s => Cg.getD s 0) 82 ((βRows k).getD j 0) ^^^
        xorSel (fun i => (AmuK k).getD i 0) 7 ((SBBK k).getD j 0) =
      xorSel (fun l => Akap.getD l 0) 7 ((cBK k).getD j 0) := by
  decide +kernel

theorem SB_bits : ∀ (k : Fin 2) (i : Fin 7) (j : Fin 4),
    ((SBv k i j : ℤ) : ZMod 2) = bitv 7 ((SBBK k).getD j 0) i := by
  decide +kernel

theorem β_bits (k : Fin 2) (j : Fin 4) (s : Fin 82) :
    ((βK k j s : ℕ) : ZMod 2) = bitv 82 ((βRows k).getD j 0) s := by
  simp only [βK, bitv]
  split_ifs <;> simp

/-! ## The frozen statements of VPlace.lean -/

/-- **`CoordCond` at `v`.** Lemma 5.7 of the paper. -/
theorem coordCond_v (k : Fin 2) : CoordCond σ (fRev k) (gK k) (Wv k) (Cv k) := by
  rw [Cv_eq]
  exact coordCond_of_coords σ (fRev k) (gKu k) (Dv k) (Uu k) (muJ_Dv k) (evG k).toMonoidHom (Ksub k)
    (fun c => ⟨c, rfl⟩) bV hind (kapG k) (fun l => ⟨kap0 l, rfl⟩) (hK k)
    (fun l => bitv nb (Akap.getD l 0)) (hAkap k) (fun i => bitv nb ((AmuK k).getD i 0)) (hAmu k)
    (fun s => bitv nb (Cg.getD s 0)) (hCg k) _
    (hcert_coord_of_bits (fun l => Akap.getD l 0) (fun i => (AmuK k).getD i 0) (fun s => Cg.getD s 0)
      (fun q => (QCK k).getD q 0) (annCk k) (annCm k))

/-- **`RelAtV` at `v`.** -/
theorem relAtV_v (k : Fin 2) : RelAtV σ (fRev k) (gK k) (βK k) (Dv k) (SBv k) :=
  relAtV_of_coords σ (fRev k) (gKu k) (Dv k) (Uu k) (muJ_Dv k) (evG k) bV kap0
    (fun l => bitv nb (Akap.getD l 0)) (hAkap k) (fun i => bitv nb ((AmuK k).getD i 0)) (hAmu k)
    (fun s => bitv nb (Cg.getD s 0)) (hCg k) (βK k) (SBv k)
    (fun j l => bitv 7 ((cBK k).getD j 0) l)
    (hcert_rel_of_bits (fun s => Cg.getD s 0) (fun i => (AmuK k).getD i 0) (fun l => Akap.getD l 0)
      (βK k) (SBv k) (fun j => (βRows k).getD j 0) (fun j => (SBBK k).getD j 0)
      (fun j => (cBK k).getD j 0) (β_bits k) (SB_bits k) (rel_xor k))

end FurioLombardo.Discharge.SelmerBasis.V
