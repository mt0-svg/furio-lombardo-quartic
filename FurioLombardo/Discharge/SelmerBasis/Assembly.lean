import FurioLombardo.Discharge.SelmerBasis.AssemblyGen
import FurioLombardo.Discharge.SelmerBasis.VCoord
import FurioLombardo.Discharge.SelmerBasis.W2Place
import FurioLombardo.Discharge.SelmerBasis.W3Place
import FurioLombardo.Discharge.SelmerBasis.W7Place
import FurioLombardo.Discharge.SelmerBasis.RealSigns
import FurioLombardo.Discharge.SelmerBasis.Kappa
import FurioLombardo.Discharge.SelmerBasis.GlobalSpan
import FurioLombardo.Discharge.SelmerSpan.Basis

/-!
# Assembly of `SelmerBasisK21 k T_k.SB` (both twists)

`selmerBasis_of_interfaces` over the places of code/selmer-local-conditions/selmer_bound_subsets.out:

* twist 0: `v`, `w2`, `w3` and the real places 5, 6 (`P0`);
* twist 1: `v`, `w2`, `w3` and the place above 7 (`P1`).

At every place the subgroup is the image of `μ` itself (`imageIn_range`); the local statements with their own
subgroups pass to it by `coordCond_range`. The global span is `GlobalK21.globalSpan_gK`, the columns are
`V.βK k`, the relations `Kappa.κK` (`Kappa.kappa_rel`), and the relation at `v` is `V.relAtV_v`.

`hX` is one `kerSpanOK` certificate per twist on the stacked rows (`Assembly.stk0`, `stk1` of
AssemblyData.lean, code/selmer-assembly/assembly_data.gp): the 75 (76) rows have rank 63, and the 19 kernel
vectors are combinations of `β_0, ..., β_3, κ_1, ..., κ_15`.

Where the inputs are proved: `V.coordCond_v`, `V.relAtV_v` (VCoord.lean), `W2.coordCond_w2` (W2Place.lean),
`W3.coordCond_w3` (W3Place.lean), `W7.coordCond_w7` (W7Place.lean), `RealRoots.signOK` (RealSigns.lean),
`Kappa.kappa_rel` (Kappa.lean), `mem_span_of_stacked`, `exists_decomp_of_mem_span` (AssemblyGen.lean);
`GoodSextic` at `w2` and `w7` comes from `W2.not_isSquare_c_w2`, `W7.not_isSquare_c_w7`.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis.Assembly

open Polynomial FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.M3b
  FurioLombardo.Discharge.SelmerBasis
open scoped FurioLombardo.Discharge.SelmerBasis.Adic

attribute [local instance] goodSextic_fRev_Kv

/-! ## The span `W = β, κ` and the columns -/

/-- `β_0, ..., β_3, κ_1, ..., κ_15` as bit rows. -/
def Wl (k : Fin 2) : List ℕ := V.βRows k ++ kapRows

theorem hWβ : ∀ (k : Fin 2) (j : Fin 4) (s : Fin 82),
    bitv 82 ((Wl k).getD j 0) s = ((V.βK k j s : ℕ) : ZMod 2) := by
  decide +kernel

theorem hWκ : ∀ (k : Fin 2) (t : Fin 15) (s : Fin 82),
    bitv 82 ((Wl k).getD (4 + t) 0) s = ((Kappa.κK t s : ℕ) : ZMod 2) := by
  decide +kernel

/-! ## Twist 0: `v`, `w2`, `w3`, the real places 5 and 6 -/

/-- The places of twist 0. -/
inductive P0
  | v | w2 | w3 | r5 | r6
  deriving DecidableEq

instance : Fintype P0 :=
  ⟨⟨[P0.v, .w2, .w3, .r5, .r6], by decide⟩, fun x => by cases x <;> decide⟩

/-- The completions. -/
abbrev K0 : P0 → Type
  | .v => Kv
  | .w2 => W2.Kw
  | .w3 => W3.Kw
  | .r5 => ℝ
  | .r6 => ℝ

noncomputable instance instField0 : (w : P0) → Field (K0 w)
  | .v => inferInstanceAs (Field Kv)
  | .w2 => inferInstanceAs (Field W2.Kw)
  | .w3 => inferInstanceAs (Field W3.Kw)
  | .r5 => inferInstanceAs (Field ℝ)
  | .r6 => inferInstanceAs (Field ℝ)

/-- The embeddings. -/
noncomputable def φ0 : (w : P0) → (K21 →+* K0 w)
  | .v => σ
  | .w2 => W2.σw
  | .w3 => W3.σw
  | .r5 => realEmb (Fin.castSucc 0)
  | .r6 => realEmb (Fin.castSucc 1)

instance instGS0 : (w : P0) → GoodSextic ((fRev 0).map (φ0 w))
  | .v => goodSextic_fRev_Kv 0
  | .w2 => W2.goodSextic_w2 0
  | .w3 => W3.goodSextic_w3 0
  | .r5 => RealRoots.goodSextic_place 0
  | .r6 => RealRoots.goodSextic_place 1

/-- The number of rows. -/
def c0 : P0 → ℕ
  | .v => 11
  | .w2 => 39
  | .w3 => 21
  | .r5 => 2
  | .r6 => 2

/-- The rows. -/
def C0 : (w : P0) → Matrix (Fin (c0 w)) (Fin 82) (ZMod 2)
  | .v => V.Cv 0
  | .w2 => W2.C2 0
  | .w3 => W3.C3 0
  | .r5 => RealRoots.CR 0
  | .r6 => RealRoots.CR 1

/-- The rows as natural numbers. -/
def Rn0 : P0 → ℕ → ℕ
  | .v => fun r => (V.CvRows 0).getD r 0
  | .w2 => fun r => (C2Rows 0).getD r 0
  | .w3 => fun r => dotRow W3.nb (fun s => W3.Cg.getD s 0) ((W3.QCK 0).getD r 0) 82
  | .r5 => fun r => (RealRows 0).getD r 0
  | .r6 => fun r => (RealRows 1).getD r 0

theorem hC0 : ∀ (w : P0) (r : Fin (c0 w)) (s : Fin 82), C0 w r s = bitv 82 (Rn0 w r) s
  | .v, _, _ => rfl
  | .w2, _, _ => rfl
  | .w3, _, _ => rfl
  | .r5, r, s => RealRoots.CR_eq 0 r s
  | .r6, r, s => RealRoots.CR_eq 1 r s

/-- The place of the stacked row `i`. -/
def src0 (i : ℕ) : P0 :=
  if i < 11 then .v else if i < 50 then .w2 else if i < 71 then .w3 else if i < 73 then .r5 else .r6

/-- Its index at the place. -/
def row0 (i : ℕ) : ℕ :=
  if i < 11 then i else if i < 50 then i - 11 else if i < 71 then i - 50 else if i < 73 then i - 71 else i - 73

theorem hsrc0 : ∀ i < 75, row0 i < c0 (src0 i) ∧ stk0.getD i 0 = Rn0 (src0 i) (row0 i) := by
  decide +kernel

theorem ker0 : kerSpanOK (fun i => stk0.getD i 0) 75 82 (fun k => T0.getD k 0) (fun k => piv0.getD k 0) 63
    (fun l => (Wl 0).getD l 0) 19 (fun j => U0.getD j 0) = true := by
  decide +kernel

theorem hX0 (a : Fin 82 → ZMod 2) (ha : ∀ w, (C0 w).mulVec a = 0) :
    ∃ e : Fin 4 → ZMod 2, ∃ ε : Fin 15 → ZMod 2,
      a = ∑ j, e j • (fun s => (V.βK 0 j s : ZMod 2)) + ∑ t, ε t • (fun s => (Kappa.κK t s : ZMod 2)) :=
  exists_decomp_of_mem_span (V.βK 0) Kappa.κK (fun l => (Wl 0).getD l 0) (hWβ 0) (hWκ 0) a
    (mem_span_of_stacked C0 Rn0 hC0 src0 row0 hsrc0 ker0 a ha)

theorem hCoord0 : ∀ w : P0, CoordCond (φ0 w) (fRev 0) (gK 0) (muJ ((fRev 0).map (φ0 w))).range (C0 w)
  | .v => coordCond_range σ (fRev 0) (gK 0) (V.Cv 0) (V.coordCond_v 0) (V.imageIn_v 0)
  | .w2 => W2.coordCond_w2 0
  | .w3 => coordCond_range W3.σw (fRev 0) (gK 0) (W3.C3 0) (W3.coordCond_w3 0) (W3.imageIn_w3 0)
  | .r5 => coordCond_range (realEmb (Fin.castSucc 0)) (fRev 0) (gK 0) (RealRoots.CR 0)
      (RealRoots.coordCond_place 0 (RealRoots.Sg 0) (RealRoots.signOK 0)) (RealRoots.imageIn_place 0)
  | .r6 => coordCond_range (realEmb (Fin.castSucc 1)) (fRev 0) (gK 0) (RealRoots.CR 1)
      (RealRoots.coordCond_place 1 (RealRoots.Sg 1) (RealRoots.signOK 1)) (RealRoots.imageIn_place 1)

/-- **`SelmerBasisK21` for twist 0.** -/
theorem selmerBasis_0 : SelmerSpan.SelmerBasisK21 0 FurioLombardo.M4.T0.data.SB := by
  unfold SelmerSpan.SelmerBasisK21 SelmerSpan
  exact selmerBasis_of_interfaces (fRev 0) (gK 0) (GlobalK21.globalSpan_gK 0) K0 φ0
    (fun w => (muJ ((fRev 0).map (φ0 w))).range) (fun w => imageIn_range _) c0 C0 hCoord0 (V.βK 0)
    Kappa.κK (Kappa.kappa_rel 0) hX0 σ (V.Dv 0) (V.SBv 0) (V.relAtV_v 0)

/-! ## Twist 1: `v`, `w2`, `w3`, the place above 7 -/

/-- The places of twist 1. -/
inductive P1
  | v | w2 | w3 | p7
  deriving DecidableEq

instance : Fintype P1 :=
  ⟨⟨[P1.v, .w2, .w3, .p7], by decide⟩, fun x => by cases x <;> decide⟩

/-- The completions. -/
abbrev K1 : P1 → Type
  | .v => Kv
  | .w2 => W2.Kw
  | .w3 => W3.Kw
  | .p7 => W7.Kw

noncomputable instance instField1 : (w : P1) → Field (K1 w)
  | .v => inferInstanceAs (Field Kv)
  | .w2 => inferInstanceAs (Field W2.Kw)
  | .w3 => inferInstanceAs (Field W3.Kw)
  | .p7 => inferInstanceAs (Field W7.Kw)

/-- The embeddings. -/
noncomputable def φ1 : (w : P1) → (K21 →+* K1 w)
  | .v => σ
  | .w2 => W2.σw
  | .w3 => W3.σw
  | .p7 => W7.σw

instance instGS1 : (w : P1) → GoodSextic ((fRev 1).map (φ1 w))
  | .v => goodSextic_fRev_Kv 1
  | .w2 => W2.goodSextic_w2 1
  | .w3 => W3.goodSextic_w3 1
  | .p7 => W7.goodSextic_w7

/-- The number of rows. -/
def c1 : P1 → ℕ
  | .v => 11
  | .w2 => 39
  | .w3 => 21
  | .p7 => 5

/-- The rows. -/
def C1 : (w : P1) → Matrix (Fin (c1 w)) (Fin 82) (ZMod 2)
  | .v => V.Cv 1
  | .w2 => W2.C2 1
  | .w3 => W3.C3 1
  | .p7 => W7.C7

/-- The rows as natural numbers. -/
def Rn1 : P1 → ℕ → ℕ
  | .v => fun r => (V.CvRows 1).getD r 0
  | .w2 => fun r => (C2Rows 1).getD r 0
  | .w3 => fun r => dotRow W3.nb (fun s => W3.Cg.getD s 0) ((W3.QCK 1).getD r 0) 82
  | .p7 => fun r => C7Rows.getD r 0

theorem hC1 : ∀ (w : P1) (r : Fin (c1 w)) (s : Fin 82), C1 w r s = bitv 82 (Rn1 w r) s
  | .v, _, _ => rfl
  | .w2, _, _ => rfl
  | .w3, _, _ => rfl
  | .p7, _, _ => rfl

/-- The place of the stacked row `i`. -/
def src1 (i : ℕ) : P1 :=
  if i < 11 then .v else if i < 50 then .w2 else if i < 71 then .w3 else .p7

/-- Its index at the place. -/
def row1 (i : ℕ) : ℕ :=
  if i < 11 then i else if i < 50 then i - 11 else if i < 71 then i - 50 else i - 71

theorem hsrc1 : ∀ i < 76, row1 i < c1 (src1 i) ∧ stk1.getD i 0 = Rn1 (src1 i) (row1 i) := by
  decide +kernel

theorem ker1 : kerSpanOK (fun i => stk1.getD i 0) 76 82 (fun k => T1.getD k 0) (fun k => piv1.getD k 0) 63
    (fun l => (Wl 1).getD l 0) 19 (fun j => U1.getD j 0) = true := by
  decide +kernel

theorem hX1 (a : Fin 82 → ZMod 2) (ha : ∀ w, (C1 w).mulVec a = 0) :
    ∃ e : Fin 4 → ZMod 2, ∃ ε : Fin 15 → ZMod 2,
      a = ∑ j, e j • (fun s => (V.βK 1 j s : ZMod 2)) + ∑ t, ε t • (fun s => (Kappa.κK t s : ZMod 2)) :=
  exists_decomp_of_mem_span (V.βK 1) Kappa.κK (fun l => (Wl 1).getD l 0) (hWβ 1) (hWκ 1) a
    (mem_span_of_stacked C1 Rn1 hC1 src1 row1 hsrc1 ker1 a ha)

theorem hCoord1 : ∀ w : P1, CoordCond (φ1 w) (fRev 1) (gK 1) (muJ ((fRev 1).map (φ1 w))).range (C1 w)
  | .v => coordCond_range σ (fRev 1) (gK 1) (V.Cv 1) (V.coordCond_v 1) (V.imageIn_v 1)
  | .w2 => W2.coordCond_w2 1
  | .w3 => coordCond_range W3.σw (fRev 1) (gK 1) (W3.C3 1) (W3.coordCond_w3 1) (W3.imageIn_w3 1)
  | .p7 => W7.coordCond_w7

/-- **`SelmerBasisK21` for twist 1.** -/
theorem selmerBasis_1 : SelmerSpan.SelmerBasisK21 1 FurioLombardo.M4.T1.data.SB := by
  unfold SelmerSpan.SelmerBasisK21 SelmerSpan
  exact selmerBasis_of_interfaces (fRev 1) (gK 1) (GlobalK21.globalSpan_gK 1) K1 φ1
    (fun w => (muJ ((fRev 1).map (φ1 w))).range) (fun w => imageIn_range _) c1 C1 hCoord1 (V.βK 1)
    Kappa.κK (Kappa.kappa_rel 1) hX1 σ (V.Dv 1) (V.SBv 1) (V.relAtV_v 1)

end FurioLombardo.Discharge.SelmerBasis.Assembly
