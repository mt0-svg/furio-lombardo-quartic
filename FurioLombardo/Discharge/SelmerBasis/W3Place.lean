import FurioLombardo.Discharge.SelmerBasis.W3CheckE
import FurioLombardo.Discharge.SelmerBasis.W3CheckK
import FurioLombardo.Discharge.SelmerBasis.W3CheckN
import FurioLombardo.Discharge.SelmerBasis.W3CheckK0
import FurioLombardo.Discharge.SelmerBasis.W3CheckK1
import FurioLombardo.Discharge.SelmerBasis.PointGen
import FurioLombardo.Discharge.SelmerBasis.PlaceWRows
import FurioLombardo.Discharge.SelmerBasis.GlobalGens
import FurioLombardo.Discharge.SelmerBasis.Count.AtW3

/-!
# The place w3: `IndepImage`, `ImageIn` and `CoordCond` for both twists (lane selmer-basis w-places)

`σw = adicCoe w3 : K21 →+* K_w3` (`e = 6`, residue field `𝔽₂`). The model `E, M, S` of W3Data.lean is a
`WPlace` (`wplace`); `K_w3[T]/(fRev_k)` maps to three copies of the component field `F = CF σw E`
(`ev3 k`: `T ↦ iL α`, `iN (+) β`, `iN (-) β`), and `evG k` to `G = Fin 3 → Fˣ`, with the basis `bG` of
`G / G²` (42 elements, 14 per component).

* `D3 k i`: the 14 points of `pts` (W3DataK<k>.lean, `PtData.exists_point`), `μ(D3 k i) = [U(T)]`;
* rows (42 bits): `Akap` (the scalars `dyGen al l`), `Amu` (the points), `Cg` (the global generators),
  each from one square certificate per component (W3Check*.lean);
* `indepImage_w3`: `indepImage_of_coords` with the rows `QI`, `T` (`hcert_indep_of_bits`);
* `imageIn_w3`: with `countBound_w3` (Count/AtW3.lean);
* `coordCond_w3`: `coordCond_of_coords` with the rows `QC` (`hcert_coord_of_bits`), `C3 k` the
  `21 × 82` matrix of the forms `QC` on the generator rows.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis.W3

open Polynomial NumberField FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.SelmerBasis.GlobalK21
open scoped FurioLombardo.Discharge.SelmerBasis.Adic

/-! ## The place -/

/-- The completion at `w3`. -/
abbrev Kw : Type := w3.adicCompletion K21

/-- `K21 → K_w3`. -/
noncomputable abbrev σw : K21 →+* Kw := adicCoe w3

theorem al_eq : E.al = M2.Special.al3 := by decide

theorem e_eq : E.e = 6 := rfl

theorem int_w3 (a : List ℤ) : ‖σw (zkE a)‖ ≤ 1 := by
  have h := primeOf_norm_le (hP := isPrime_of_absNorm_two absNorm_eltO_al3)
    (hα := elt_ne_zero_of_absNorm absNorm_eltO_al3 two_ne_zero) (x := zkE a) (n := 0)
    (a := eltO a) (b := 1) (b' := 1) (c' := 0) (by ring) (by simp [coe_elt])
  rw [zpow_zero] at h
  exact h

theorem wplace : WPlace σw E where
  int := int_w3
  unif := by rw [al_eq, ← coe_elt]; exact normUnif_w3
  two := by rw [e_eq, al_eq, ← coe_elt]; exact norm_two_w3
  res := res_w3
  ok := ck_E

instance instNoRoot : Fact (∀ r : Kw, r ^ 2 ≠ σw (zkE E.A) + σw (zkE E.B) * r) := ⟨wplace.noRoot⟩

/-- The component field. -/
abbrev F : Type := CF σw E

instance goodSextic_w3 (k : Fin 2) : GoodSextic ((fRev k).map σw) :=
  goodSextic_fRev_map σw k (by rw [fRev_leadingCoeff]; exact Count.not_isSquare_c_w3 k)

/-! ## The three components -/

/-- `T ↦ iL α`, `iN (+) β`, `iN (-) β`. -/
noncomputable def ev3 (k : Fin 2) : Fin 3 → (AdjoinRoot ((fRev k).map σw) →+* F) :=
  ![evAt σw (iL σw E M ck_M) (iL_comp_algebraMap ck_M) (fRev k) alphaR (aeval_alphaR_fRev k),
    evAt σw (iN σw E M wplace ck_M S ck_S true) (iN_comp_algebraMap wplace ck_M ck_S true) (fRev k)
      betaR (aeval_betaR_fRev k),
    evAt σw (iN σw E M wplace ck_M S ck_S false) (iN_comp_algebraMap wplace ck_M ck_S false) (fRev k)
      betaR (aeval_betaR_fRev k)]

/-- `(K_w3[T]/(fRev_k))ˣ → G`. -/
noncomputable def evG (k : Fin 2) : (AdjoinRoot ((fRev k).map σw))ˣ →* (Fin 3 → Fˣ) :=
  MonoidHom.pi fun c => Units.map (ev3 k c).toMonoidHom

/-- The number of bits of a row. -/
abbrev nb : ℕ := 3 * (2 * E.e + 2)

/-- The basis of `G / G²`. -/
noncomputable def bW : Fin nb → Fin 3 → Fˣ := bG (2 * E.e + 2) (bF σw E) (bF_ne_zero wplace)

/-! ## The data per twist -/

def ptsK : Fin 2 → List PtData := ![K0.pts, K1.pts]
def cMK : Fin 2 → Fin 3 → List WCert := ![![K0.cM1, K0.cM2, K0.cM3], ![K1.cM1, K1.cM2, K1.cM3]]
def AmuK : Fin 2 → List ℕ := ![K0.Amu, K1.Amu]
def QCK : Fin 2 → List ℕ := ![K0.QC, K1.QC]
def TK : Fin 2 → List ℕ := ![K0.T, K1.T]

theorem ck_ptK (k : Fin 2) (i : Fin 14) : ((ptsK k).getD i default).okD E = true ∧
    ((ptsK k).getD i default).okZ E (gW k) = true := by
  fin_cases k
  · exact ⟨(K0.ck_pt i i.isLt).1, (K0.ck_pt i i.isLt).2.1⟩
  · exact ⟨(K1.ck_pt i i.isLt).1, (K1.ck_pt i i.isLt).2.1⟩

/-! ## The points -/

theorem exists_D3 (k : Fin 2) (i : Fin 14) :
    ∃ (D : Jac ((fRev k).map σw))
      (hu : IsUnit (AdjoinRoot.mk ((fRev k).map σw) (((ptsK k).getD i default).U.map σw))),
      muJ ((fRev k).map σw) D = (QuotientGroup.mk hu.unit : H ((fRev k).map σw)) :=
  PtData.exists_point wplace k (ck_ptK k i).1 (ck_ptK k i).2

/-- **The 14 points of twist `k` at `w3`.** -/
noncomputable def D3 (k : Fin 2) (i : Fin 14) : Jac ((fRev k).map σw) := (exists_D3 k i).choose

/-- `U(T)` for the point `D3 k i`. -/
noncomputable def U3 (k : Fin 2) (i : Fin 14) : (AdjoinRoot ((fRev k).map σw))ˣ :=
  (exists_D3 k i).choose_spec.choose.unit

theorem muJ_D3 (k : Fin 2) (i : Fin 14) :
    muJ ((fRev k).map σw) (D3 k i) = QuotientGroup.mk (U3 k i) :=
  (exists_D3 k i).choose_spec.choose_spec

/-! ## Evaluation at the three components -/

theorem evG_coe (k : Fin 2) (u : (AdjoinRoot ((fRev k).map σw))ˣ) (c : Fin 3) :
    ((evG k u c : Fˣ) : F) = ev3 k c (u : AdjoinRoot ((fRev k).map σw)) := rfl

theorem ev3_algebraMap (k : Fin 2) (c : Fin 3) (x : Kw) :
    ev3 k c (algebraMap Kw (AdjoinRoot ((fRev k).map σw)) x) = algebraMap Kw F x := by
  fin_cases c
  · exact evAt_algebraMap σw _ (iL_comp_algebraMap ck_M) (fRev k) alphaR (aeval_alphaR_fRev k) x
  · exact evAt_algebraMap σw _ (iN_comp_algebraMap wplace ck_M ck_S true) (fRev k) betaR
      (aeval_betaR_fRev k) x
  · exact evAt_algebraMap σw _ (iN_comp_algebraMap wplace ck_M ck_S false) (fRev k) betaR
      (aeval_betaR_fRev k) x

theorem ev3_mk (k : Fin 2) (P : K21[X]) :
    ev3 k 0 (AdjoinRoot.mk _ (P.map σw)) = iL σw E M ck_M (aeval alphaR P) ∧
    ev3 k 1 (AdjoinRoot.mk _ (P.map σw)) = iN σw E M wplace ck_M S ck_S true (aeval betaR P) ∧
    ev3 k 2 (AdjoinRoot.mk _ (P.map σw)) = iN σw E M wplace ck_M S ck_S false (aeval betaR P) :=
  ⟨evAt_mk σw _ (iL_comp_algebraMap ck_M) (fRev k) alphaR (aeval_alphaR_fRev k) P,
    evAt_mk σw _ (iN_comp_algebraMap wplace ck_M ck_S true) (fRev k) betaR (aeval_betaR_fRev k) P,
    evAt_mk σw _ (iN_comp_algebraMap wplace ck_M ck_S false) (fRev k) betaR (aeval_betaR_fRev k) P⟩

theorem ev3_etale (k : Fin 2) (P : K21[X]) :
    ev3 k 0 (etaleMap σw (fRev k) (AdjoinRoot.mk _ P)) = iL σw E M ck_M (aeval alphaR P) ∧
    ev3 k 1 (etaleMap σw (fRev k) (AdjoinRoot.mk _ P)) =
      iN σw E M wplace ck_M S ck_S true (aeval betaR P) ∧
    ev3 k 2 (etaleMap σw (fRev k) (AdjoinRoot.mk _ P)) =
      iN σw E M wplace ck_M S ck_S false (aeval betaR P) :=
  ⟨evAt_etaleMap σw _ (iL_comp_algebraMap ck_M) (fRev k) alphaR (aeval_alphaR_fRev k) P,
    evAt_etaleMap σw _ (iN_comp_algebraMap wplace ck_M ck_S true) (fRev k) betaR (aeval_betaR_fRev k) P,
    evAt_etaleMap σw _ (iN_comp_algebraMap wplace ck_M ck_S false) (fRev k) betaR
      (aeval_betaR_fRev k) P⟩

/-! ## Squares at one component from a certificate -/

theorem natCast_ne_zero_F {n : ℕ} (hn : n ≠ 0) : (n : F) ≠ 0 := by
  rw [← map_natCast (algebraMap Kw F)]
  exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hn)

/-- Component 1: `Λ² y = iL t` and a certificate for `t`. -/
theorem sqL {y : F} {lam : ℕ} (hlam : lam ≠ 0) {t : List (List ℤ)} {cc : WCert}
    (hc : certOK E cc.n0 (X0L M (ofL t)) (X1L M (ofL t)) cc = true)
    (hy : (lam : F) ^ 2 * y = iL σw E M ck_M (mkL t)) : IsSquare (y * Ba σw E cc.a) := by
  have h := certOK_isSquare wplace hc ((lam : F) ^ 2 * y) (by
    rw [hy, mkL_eq_evL, iL_evL, sub_self, norm_zero]; positivity)
  refine isSquare_of_sq_mul (natCast_ne_zero_F hlam) ?_
  rwa [← mul_assoc]

/-- Components 2 and 3: `Λ² y = iN b t` and a certificate for the approximation of `t`. -/
theorem sqN (b : Bool) {y : F} {lam : ℕ} (hlam : lam ≠ 0) {t : List (List ℤ)} {cc : WCert}
    (hc : certOK E cc.n0 (X0N E M S (ofN t) b) (X1N E M S (ofN t) b) cc = true)
    (hn : cc.n0 ≤ S.n - E.e - S.j)
    (hy : (lam : F) ^ 2 * y = iN σw E M wplace ck_M S ck_S b (mkN t)) :
    IsSquare (y * Ba σw E cc.a) := by
  have h := certOK_isSquare wplace hc ((lam : F) ^ 2 * y) (by
    rw [hy, mkN_eq_evN]
    exact (norm_iN_evN_sub wplace ck_M ck_S b (ofN t)).trans
      (pow_le_pow_of_le_one (norm_nonneg _) wplace.unif.norm_lt_one.le hn))
  refine isSquare_of_sq_mul (natCast_ne_zero_F hlam) ?_
  rwa [← mul_assoc]

theorem sq_one_Ba : IsSquare ((1 : F) * Ba σw E 0) := by
  rw [Ba_zero, one_mul]; exact ⟨1, (mul_one 1).symm⟩

/-- **A row of `G` from its three components.** -/
theorem row_sq (x : Fin 3 → Fˣ) (A : ℕ) (a : Fin 3 → ℕ)
    (ha : ∀ c : Fin 3, (A >>> ((2 * E.e + 2) * c)) % 2 ^ (2 * E.e + 2) = a c % 2 ^ (2 * E.e + 2))
    (h : ∀ c, IsSquare ((x c : F) * Ba σw E (a c))) :
    IsSquare (x * ∏ l, bW l ^ (bitv nb A l).val) := by
  refine isSquare_mul_rows (hb := bF_ne_zero wplace) x A fun c => ?_
  have hc := h c
  rw [← Ba_mod, ← ha c, Ba_mod] at hc
  exact hc

/-! ## Rows: kernel facts -/

theorem ak_bits : ∀ (l : Fin 13) (c : Fin 3),
    (Akap.getD l 0 >>> ((2 * E.e + 2) * c)) % 2 ^ (2 * E.e + 2) =
      (cK.getD l default).a % 2 ^ (2 * E.e + 2) := by
  decide +kernel

theorem mu_bits : ∀ (k : Fin 2) (i : Fin 14) (c : Fin 3),
    ((AmuK k).getD i 0 >>> ((2 * E.e + 2) * c)) % 2 ^ (2 * E.e + 2) =
      ((cMK k c).getD i default).a % 2 ^ (2 * E.e + 2) := by
  decide +kernel

theorem cgL_bits : ∀ (i : Fin 29) (c : Fin 3),
    (Cg.getD i 0 >>> ((2 * E.e + 2) * c)) % 2 ^ (2 * E.e + 2) =
      (![(cL.getD i default).a, 0, 0] c) % 2 ^ (2 * E.e + 2) := by
  decide +kernel

theorem cgN_bits : ∀ (j : Fin 53) (c : Fin 3),
    (Cg.getD (29 + j) 0 >>> ((2 * E.e + 2) * c)) % 2 ^ (2 * E.e + 2) =
      (![0, (cN1.getD j default).a, (cN2.getD j default).a] c) % 2 ^ (2 * E.e + 2) := by
  decide +kernel

theorem mu_n0 : ∀ (k : Fin 2) (i : Fin 14),
    ((cMK k 1).getD i default).n0 ≤ S.n - E.e - S.j ∧
      ((cMK k 2).getD i default).n0 ≤ S.n - E.e - S.j := by
  decide +kernel

theorem gN_n0 : ∀ j : Fin 53,
    (cN1.getD j default).n0 ≤ S.n - E.e - S.j ∧ (cN2.getD j default).n0 ≤ S.n - E.e - S.j := by
  decide +kernel

theorem ck_MK (k : Fin 2) (i : Fin 14) :
    certOK E ((cMK k 0).getD i default).n0 (X0L M (ofL ((ptsK k).getD i default).tL))
        (X1L M (ofL ((ptsK k).getD i default).tL)) ((cMK k 0).getD i default) = true ∧
      certOK E ((cMK k 1).getD i default).n0 (X0N E M S (ofN ((ptsK k).getD i default).tN) true)
        (X1N E M S (ofN ((ptsK k).getD i default).tN) true) ((cMK k 1).getD i default) = true ∧
      certOK E ((cMK k 2).getD i default).n0 (X0N E M S (ofN ((ptsK k).getD i default).tN) false)
        (X1N E M S (ofN ((ptsK k).getD i default).tN) false) ((cMK k 2).getD i default) = true := by
  fin_cases k
  · exact ⟨K0.ck_M1 i i.isLt, K0.ck_M2 i i.isLt, K0.ck_M3 i i.isLt⟩
  · exact ⟨K1.ck_M1 i i.isLt, K1.ck_M2 i i.isLt, K1.ck_M3 i i.isLt⟩

theorem ck_ptT (k : Fin 2) (i : Fin 14) : ((ptsK k).getD i default).okT = true := by
  fin_cases k
  · exact (K0.ck_pt i i.isLt).2.2
  · exact (K1.ck_pt i i.isLt).2.2

/-! ## Rows -/

/-- The scalars `dyGen al l`. -/
noncomputable def kap0 (l : Fin 13) : Kwˣ :=
  Units.mk0 (dyGen (σw (zkE E.al)) l) (dyGen_ne_zero wplace.unif l)

/-- Their images in `G`. -/
noncomputable def kapG (k : Fin 2) (l : Fin 13) : Fin 3 → Fˣ :=
  evG k (Units.map (algebraMap Kw (AdjoinRoot ((fRev k).map σw))).toMonoidHom (kap0 l))

theorem hAkap (k : Fin 2) (l : Fin 13) :
    IsSquare (kapG k l * ∏ i, bW i ^ (bitv nb (Akap.getD l 0) i).val) := by
  refine row_sq _ _ (fun _ => (cK.getD l default).a) (ak_bits l) fun c => ?_
  have hx : ((kapG k l c : Fˣ) : F) = toF σw E (evK (kapX E l)) (evK (.int 0)) := by
    rw [toF_int_zero, evK_kapX wplace (lt_of_lt_of_le l.isLt (by decide +kernel : 13 ≤ E.alPow.length)),
      kapG, evG_coe]
    exact ev3_algebraMap k c _
  exact certOK_isSquare wplace (ck_K l l.isLt) _ (by rw [hx, sub_self, norm_zero]; positivity)

theorem hAmu (k : Fin 2) (i : Fin 14) :
    IsSquare (evG k (U3 k i) * ∏ j, bW j ^ (bitv nb ((AmuK k).getD i 0) j).val) := by
  have hD := (ck_ptK k i).1
  have hT := ck_ptT k i
  have hD' := hD
  simp only [PtData.okD, Bool.and_eq_true, decide_eq_true_eq] at hD'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hlL⟩, hlN⟩, -⟩, -⟩ := hD'
  have hU : ((U3 k i : (AdjoinRoot ((fRev k).map σw))ˣ) : AdjoinRoot ((fRev k).map σw)) =
      AdjoinRoot.mk _ (((ptsK k).getD i default).U.map σw) :=
    (exists_D3 k i).choose_spec.choose.unit_spec
  have hL := PtData.aeval_alphaR_U E hD hT
  have hN := PtData.aeval_betaR_U E hD hT
  obtain ⟨c1, c2, c3⟩ := ck_MK k i
  obtain ⟨n2, n3⟩ := mu_n0 k i
  obtain ⟨e1, e2, e3⟩ := ev3_mk k ((ptsK k).getD i default).U
  have h0 : IsSquare (((evG k (U3 k i) 0 : Fˣ) : F) * Ba σw E ((cMK k 0).getD i default).a) := by
    rw [evG_coe, hU, e1]
    refine sqL hlL.ne' c1 ?_
    rw [← hL, map_mul, map_pow, map_natCast]
  have h1 : IsSquare (((evG k (U3 k i) 1 : Fˣ) : F) * Ba σw E ((cMK k 1).getD i default).a) := by
    rw [evG_coe, hU, e2]
    refine sqN true hlN.ne' c2 n2 ?_
    rw [← hN, map_mul, map_pow, map_natCast]
  have h2 : IsSquare (((evG k (U3 k i) 2 : Fˣ) : F) * Ba σw E ((cMK k 2).getD i default).a) := by
    rw [evG_coe, hU, e3]
    refine sqN false hlN.ne' c3 n3 ?_
    rw [← hN, map_mul, map_pow, map_natCast]
  refine row_sq _ _ (fun c => ((cMK k c).getD i default).a) (mu_bits k i) fun c => ?_
  fin_cases c
  exacts [h0, h1, h2]

theorem hCg (k : Fin 2) (s : Fin 82) :
    IsSquare (evG k (Units.map (etaleMap σw (fRev k)).toMonoidHom (gKu k s)) *
      ∏ j, bW j ^ (bitv nb (Cg.getD s 0) j).val) := by
  have hg : ∀ s : Fin 82, (((Units.map (etaleMap σw (fRev k)).toMonoidHom (gKu k s)) :
      (AdjoinRoot ((fRev k).map σw))ˣ) : AdjoinRoot ((fRev k).map σw)) =
      etaleMap σw (fRev k) (AdjoinRoot.mk _ (Pgen s)) := fun s => by
    change etaleMap σw (fRev k) (gKu k s : AdjoinRoot (fRev k)) = _
    rw [gKu_coe]
  revert s
  show ∀ s : Fin (29 + 53), _
  intro s
  refine Fin.addCases (fun i => ?_) (fun j => ?_) s
  · obtain ⟨e1, e2, e3⟩ := ev3_etale k (Pgen (Fin.castAdd 53 i))
    have h0 : IsSquare ((((evG k (Units.map (etaleMap σw (fRev k)).toMonoidHom
        (gKu k (Fin.castAdd 53 i))) 0 : Fˣ)) : F) * Ba σw E (cL.getD i default).a) := by
      rw [evG_coe, hg, e1, Pgen_alphaR_left]
      refine sqL one_ne_zero (ck_L i i.isLt) ?_
      rw [Nat.cast_one, one_pow, one_mul]; rfl
    have h12 : ∀ b : Bool, iN σw E M wplace ck_M S ck_S b (aeval betaR (Pgen (Fin.castAdd 53 i))) = 1 :=
      fun b => by rw [Pgen_betaR_left, map_one]
    have h1 : IsSquare ((((evG k (Units.map (etaleMap σw (fRev k)).toMonoidHom
        (gKu k (Fin.castAdd 53 i))) 1 : Fˣ)) : F) * Ba σw E 0) := by
      rw [evG_coe, hg, e2, h12]; exact sq_one_Ba
    have h2 : IsSquare ((((evG k (Units.map (etaleMap σw (fRev k)).toMonoidHom
        (gKu k (Fin.castAdd 53 i))) 2 : Fˣ)) : F) * Ba σw E 0) := by
      rw [evG_coe, hg, e3, h12]; exact sq_one_Ba
    refine row_sq _ _ (fun c => ![(cL.getD i default).a, 0, 0] c) (cgL_bits i) fun c => ?_
    fin_cases c
    exacts [h0, h1, h2]
  · obtain ⟨e1, e2, e3⟩ := ev3_etale k (Pgen (Fin.natAdd 29 j))
    obtain ⟨n1, n2⟩ := gN_n0 j
    have h1 : IsSquare ((((evG k (Units.map (etaleMap σw (fRev k)).toMonoidHom
        (gKu k (Fin.natAdd 29 j))) 1 : Fˣ)) : F) * Ba σw E (cN1.getD j default).a) := by
      rw [evG_coe, hg, e2, Pgen_betaR_right]
      refine sqN true one_ne_zero (ck_N1 j j.isLt) n1 ?_
      rw [Nat.cast_one, one_pow, one_mul]; rfl
    have h2 : IsSquare ((((evG k (Units.map (etaleMap σw (fRev k)).toMonoidHom
        (gKu k (Fin.natAdd 29 j))) 2 : Fˣ)) : F) * Ba σw E (cN2.getD j default).a) := by
      rw [evG_coe, hg, e3, Pgen_betaR_right]
      refine sqN false one_ne_zero (ck_N2 j j.isLt) n2 ?_
      rw [Nat.cast_one, one_pow, one_mul]; rfl
    have h0 : IsSquare ((((evG k (Units.map (etaleMap σw (fRev k)).toMonoidHom
        (gKu k (Fin.natAdd 29 j))) 0 : Fˣ)) : F) * Ba σw E 0) := by
      rw [evG_coe, hg, e1, Pgen_alphaR_right, map_one]; exact sq_one_Ba
    refine row_sq _ _ (fun c => ![0, (cN1.getD j default).a, (cN2.getD j default).a] c)
      (cgN_bits j) fun c => ?_
    fin_cases c
    exacts [h0, h1, h2]

theorem hind : ∀ ε : Fin nb → ZMod 2, IsSquare (∏ i, bW i ^ (ε i).val) → ε = 0 :=
  indep_rows (bF_indep wplace (by decide +kernel))

theorem hspan (x : Kw) (hx : x ≠ 0) :
    ∃ c : Fin 13 → ZMod 2, IsSquare (x * ∏ l, (kap0 l : Kw) ^ (c l).val) := by
  obtain ⟨c, hc⟩ := sb_span_dyadic wplace.unif (e := 6) (by norm_num) wplace.two wplace.res x hx
  refine ⟨c, ?_⟩
  simp only [kap0, Units.val_mk0]
  exact hc

/-- The subgroup of the scalars. -/
noncomputable def Ksub (k : Fin 2) : Subgroup (Fin 3 → Fˣ) :=
  ((evG k).comp (Units.map (algebraMap Kw (AdjoinRoot ((fRev k).map σw))).toMonoidHom)).range

theorem hK (k : Fin 2) :
    ∀ x ∈ Ksub k, ∃ c : Fin 13 → ZMod 2, IsSquare (x * ∏ l, kapG k l ^ (c l).val) :=
  hK_of_span (evG k) kap0 hspan

/-! ## F2 certificates (kernel) -/

theorem annI : annOK nb (fun l => Akap.getD l 0) 13 (fun q => QI.getD q 0) 35 = true := by
  decide +kernel

theorem leftInv : ∀ k : Fin 2,
    leftInvOK (fun q => dotRow nb (fun i => (AmuK k).getD i 0) (QI.getD q 0) 14) 35 14
      (fun q => (TK k).getD q 0) = true := by
  decide +kernel

theorem annCk : ∀ k : Fin 2,
    annOK nb (fun l => Akap.getD l 0) 13 (fun q => (QCK k).getD q 0) 21 = true := by
  decide +kernel

theorem annCm : ∀ k : Fin 2,
    annOK nb (fun i => (AmuK k).getD i 0) 14 (fun q => (QCK k).getD q 0) 21 = true := by
  decide +kernel

/-! ## The local Props -/

/-- **`IndepImage` at `w3`.** -/
theorem indepImage_w3 (k : Fin 2) : IndepImage ((fRev k).map σw) (D3 k) :=
  indepImage_of_coords _ (D3 k) (U3 k) (muJ_D3 k) (evG k) (Ksub k) (fun c => ⟨c, rfl⟩) bW hind
    (kapG k) (fun l => ⟨kap0 l, rfl⟩) (hK k) (fun l => bitv nb (Akap.getD l 0)) (hAkap k)
    (fun i => bitv nb ((AmuK k).getD i 0)) (hAmu k)
    (hcert_indep_of_bits (fun l => Akap.getD l 0) (fun i => (AmuK k).getD i 0) (fun q => QI.getD q 0)
      (fun q => (TK k).getD q 0) annI (leftInv k))

/-- **`ImageIn` at `w3`.** -/
theorem imageIn_w3 (k : Fin 2) :
    ImageIn ((fRev k).map σw) (Subgroup.closure (Set.range fun i => muJ ((fRev k).map σw) (D3 k i))) :=
  imageIn_closure_of_count_indep _ (D3 k) (Count.countBound_w3 k) (indepImage_w3 k)

/-- The coordinate matrix at `w3`: the forms `QC` read on the generator rows. -/
def C3 (k : Fin 2) : Matrix (Fin 21) (Fin 82) (ZMod 2) :=
  Matrix.of fun i s => bitv 82 (dotRow nb (fun s => Cg.getD s 0) ((QCK k).getD i 0) 82) s

/-- **`CoordCond` at `w3`.** -/
theorem coordCond_w3 (k : Fin 2) :
    CoordCond σw (fRev k) (gK k)
      (Subgroup.closure (Set.range fun i => muJ ((fRev k).map σw) (D3 k i))) (C3 k) :=
  coordCond_of_coords σw (fRev k) (gKu k) (D3 k) (U3 k) (muJ_D3 k) (evG k) (Ksub k) (fun c => ⟨c, rfl⟩)
    bW hind (kapG k) (fun l => ⟨kap0 l, rfl⟩) (hK k) (fun l => bitv nb (Akap.getD l 0)) (hAkap k)
    (fun i => bitv nb ((AmuK k).getD i 0)) (hAmu k) (fun s => bitv nb (Cg.getD s 0)) (hCg k) (C3 k)
    (hcert_coord_of_bits (fun l => Akap.getD l 0) (fun i => (AmuK k).getD i 0) (fun s => Cg.getD s 0)
      (fun q => (QCK k).getD q 0) (annCk k) (annCm k))

end FurioLombardo.Discharge.SelmerBasis.W3
