import FurioLombardo.Discharge.SelmerBasis.AssemblyData
import FurioLombardo.Discharge.SelmerBasis.GlobalGens
import FurioLombardo.Discharge.SelmerBasis.AdicPlace
import FurioLombardo.Discharge.SelmerBasis.Echelon
import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.M3a.Concrete
import FurioLombardo.Discharge.SelmerBasis.Count.AtW2
import FurioLombardo.Discharge.SelmerBasis.W2Glue
import FurioLombardo.Discharge.SelmerBasis.W2CheckE
import FurioLombardo.Discharge.SelmerBasis.W2CheckK
import FurioLombardo.Discharge.SelmerBasis.W2CheckL
import FurioLombardo.Discharge.SelmerBasis.W2CheckN1
import FurioLombardo.Discharge.SelmerBasis.W2CheckN2
import FurioLombardo.Discharge.SelmerBasis.W2CheckK0
import FurioLombardo.Discharge.SelmerBasis.W2CheckK1

/-!
# The place w2: the frozen statements of the SelmerBasisK21 side (both twists)

`σw = adicCoe w2 : K21 →+* K_w2` (`e = 12`, residue field `𝔽₂`, three unramified quadratic components of
`K_w2[T]/(fRev k)`).

* `not_isSquare_c_w2`: the leading coefficient `c k` is not a square at `w2` (depth `2e = 24` for `k = 0`,
  odd depth 11 for `k = 1`), hence `GoodSextic` at `w2`;
* `coordCond_w2`: the local condition in coordinates on the global generators, with the image of `μ` itself as
  subgroup (so `ImageIn` is trivial) and the 39 rows `C2 k` of stage 6 of
  code/selmer-local-conditions/selmer_rows_twist<k>_w12.out (data `Assembly.C2Rows`).

`not_isSquare_c_w2` is
`Count.not_isSquare_c_w2` (Count/AtW2.lean). `coordCond_w2` is `W2G.coordCond_w2_range` (W2Glue.lean) for the data
`dataW2` of W2Data.lean, W2DataK0.lean, W2DataK1.lean: `facts` collects their kernel checks (W2Check*.lean and
the bit facts here, all by `decide +kernel`), and `cmat_rows` shows that the forms `QC` read on the generator
rows are the rows `C2Rows`, so `Cmat dataW2 k = C2 k`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.W2

open Polynomial FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.SelmerBasis
open scoped FurioLombardo.Discharge.SelmerBasis.Adic

/-- The completion at `w2`. -/
abbrev Kw : Type := w2.adicCompletion K21

/-- `K21 → K_w2`. -/
noncomputable abbrev σw : K21 →+* Kw := adicCoe w2

/-- `σ(c k)` is not a square at `w2`. -/
theorem not_isSquare_c_w2 (k : Fin 2) : ¬ IsSquare (σw (c k)) :=
  Count.not_isSquare_c_w2 k

instance goodSextic_w2 (k : Fin 2) : GoodSextic ((fRev k).map σw) :=
  goodSextic_fRev_map σw k (by rw [fRev_leadingCoeff]; exact not_isSquare_c_w2 k)

/-- The 39 rows at `w2`. -/
def C2 (k : Fin 2) : Matrix (Fin 39) (Fin 82) (ZMod 2) :=
  Matrix.of fun i s => bitv 82 ((Assembly.C2Rows k).getD i 0) s

/-! ## The data at `w2` and their kernel facts -/

theorem e_eq : E.e = 12 := rfl

theorem al_eq : E.al = M2.Special.al2 := rfl

/-- The model of W2Data.lean is a `WPlace`. -/
theorem wplace : WPlace σw E where
  int := W2G.int_w2
  unif := by rw [al_eq, ← coe_elt]; exact normUnif_w2
  two := by rw [e_eq, al_eq, ← coe_elt]; exact norm_two_w2
  res := res_w2
  ok := ck_E

/-- The data at `w2` (W2Data.lean, W2DataK0.lean, W2DataK1.lean). -/
def dataW2 : W2G.Data := ⟨E, SR, SU, cK, Akap, cL, cN1, cN2, Cg, 65, QI, ![K0.pts, K1.pts],
  ![![K0.cM1, K0.cM2, K0.cM3], ![K1.cM1, K1.cM2, K1.cM3]], ![K0.Amu, K1.Amu], ![K0.T, K1.T],
  ![K0.QC, K1.QC]⟩

theorem ak_bits : ∀ (l : Fin (2 * dataW2.E.e + 1)) (c : Fin 3),
    (dataW2.Akap.getD l 0 >>> ((2 * dataW2.E.e + 2) * c)) % 2 ^ (2 * dataW2.E.e + 2) =
      (dataW2.cK.getD l default).a % 2 ^ (2 * dataW2.E.e + 2) := by
  decide +kernel

theorem gL_n : ∀ s : Fin 29, (dataW2.cL.getD s default).n ≤ dataW2.SR.n - dataW2.E.e - dataW2.SR.j := by
  decide +kernel

theorem gN_n : ∀ s : Fin 53, (dataW2.cN1.getD s default).n ≤ dataW2.SU.n - dataW2.E.e - dataW2.SU.j ∧
    (dataW2.cN2.getD s default).n ≤ dataW2.SU.n - dataW2.E.e - dataW2.SU.j := by
  decide +kernel

theorem cgL_bits : ∀ (i : Fin 29) (c : Fin 3),
    (dataW2.Cg.getD i 0 >>> ((2 * dataW2.E.e + 2) * c)) % 2 ^ (2 * dataW2.E.e + 2) =
      (![(dataW2.cL.getD i default).a, 0, 0] c) % 2 ^ (2 * dataW2.E.e + 2) := by
  decide +kernel

theorem cgN_bits : ∀ (j : Fin 53) (c : Fin 3),
    (dataW2.Cg.getD (29 + j) 0 >>> ((2 * dataW2.E.e + 2) * c)) % 2 ^ (2 * dataW2.E.e + 2) =
      (![0, (dataW2.cN1.getD j default).a, (dataW2.cN2.getD j default).a] c) % 2 ^ (2 * dataW2.E.e + 2) := by
  decide +kernel

theorem mu_n : ∀ (k : Fin 2) (i : Fin 26),
    ((dataW2.cM k 0).getD i default).n ≤ dataW2.SR.n - dataW2.E.e - dataW2.SR.j ∧
    ((dataW2.cM k 1).getD i default).n ≤ dataW2.SU.n - dataW2.E.e - dataW2.SU.j ∧
    ((dataW2.cM k 2).getD i default).n ≤ dataW2.SU.n - dataW2.E.e - dataW2.SU.j := by
  decide +kernel

theorem mu_bits : ∀ (k : Fin 2) (i : Fin 26) (c : Fin 3),
    ((dataW2.Amu k).getD i 0 >>> ((2 * dataW2.E.e + 2) * c)) % 2 ^ (2 * dataW2.E.e + 2) =
      ((dataW2.cM k c).getD i default).a % 2 ^ (2 * dataW2.E.e + 2) := by
  decide +kernel

theorem ann_I : annOK (3 * (2 * dataW2.E.e + 2)) (fun l => dataW2.Akap.getD l 0) (2 * dataW2.E.e + 1)
    (fun q => dataW2.QI.getD q 0) dataW2.nQI = true := by
  decide +kernel

theorem left_inv : ∀ k : Fin 2, leftInvOK (fun q => dotRow (3 * (2 * dataW2.E.e + 2))
    (fun i => (dataW2.Amu k).getD i 0) (dataW2.QI.getD q 0) 26) dataW2.nQI 26
    (fun q => (dataW2.T k).getD q 0) = true := by
  decide +kernel

theorem ann_Ck : ∀ k : Fin 2, annOK (3 * (2 * dataW2.E.e + 2)) (fun l => dataW2.Akap.getD l 0)
    (2 * dataW2.E.e + 1) (fun q => (dataW2.QC k).getD q 0) 39 = true := by
  decide +kernel

theorem ann_Cm : ∀ k : Fin 2, annOK (3 * (2 * dataW2.E.e + 2)) (fun i => (dataW2.Amu k).getD i 0) 26
    (fun q => (dataW2.QC k).getD q 0) 39 = true := by
  decide +kernel

/-- **The kernel facts of the data at `w2`.** -/
theorem facts : W2G.Facts dataW2 where
  wp := wplace
  sr := ck_SR
  su := ck_SU
  lenK := by decide +kernel
  ckK := fun i hi => ck_K i hi
  akBits := ak_bits
  ckL := fun s hs => ck_L s hs
  ckN1 := fun s hs => ck_N1 s hs
  ckN2 := fun s hs => ck_N2 s hs
  gLn := gL_n
  gNn := gN_n
  cgLBits := cgL_bits
  cgNBits := cgN_bits
  ckPt := fun k i => by
    fin_cases k
    · exact K0.ck_pt i i.isLt
    · exact K1.ck_pt i i.isLt
  ckM := fun k i => by
    fin_cases k
    · exact ⟨K0.ck_M1 i i.isLt, K0.ck_M2 i i.isLt, K0.ck_M3 i i.isLt⟩
    · exact ⟨K1.ck_M1 i i.isLt, K1.ck_M2 i i.isLt, K1.ck_M3 i i.isLt⟩
  muN := mu_n
  muBits := mu_bits
  annI := ann_I
  leftInv := left_inv
  annCk := ann_Ck
  annCm := ann_Cm

/-- The forms `QC` read on the generator rows are the rows `C2Rows` (both twists). -/
theorem cmat_rows : ∀ (k : Fin 2) (i : Fin 39),
    dotRow (3 * (2 * dataW2.E.e + 2)) (fun s => dataW2.Cg.getD s 0) ((dataW2.QC k).getD i 0) 82 =
      (Assembly.C2Rows k).getD i 0 := by
  decide +kernel

theorem Cmat_eq (k : Fin 2) : W2G.Cmat dataW2 k = C2 k := by
  ext i s
  simp only [W2G.Cmat, C2, Matrix.of_apply, cmat_rows]

/-- **`CoordCond` at `w2`.** -/
theorem coordCond_w2 (k : Fin 2) :
    CoordCond σw (fRev k) (gK k) (muJ ((fRev k).map σw)).range (C2 k) := by
  rw [← Cmat_eq]
  exact W2G.coordCond_w2_range facts k

end FurioLombardo.Discharge.SelmerBasis.W2
