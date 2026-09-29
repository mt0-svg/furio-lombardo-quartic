import FurioLombardo.Discharge.SelmerBasis.AssemblyData
import FurioLombardo.Discharge.SelmerBasis.GlobalGens
import FurioLombardo.Discharge.SelmerBasis.AdicPlace
import FurioLombardo.Discharge.SelmerBasis.Echelon
import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.M3a.Concrete
import FurioLombardo.Discharge.SelmerBasis.Count.At7
import FurioLombardo.Discharge.SelmerBasis.W7Glue
import FurioLombardo.Discharge.SelmerBasis.W7Check

/-!
# The place above 7: the frozen statements of the SelmerBasisK21 side (twist 1)

`σw = adicCoe w7 : K21 →+* K_w7` (`e = 7`, `f = 3`); only twist 1 needs this place
(code/selmer-local-conditions/selmer_bound_subsets.out).

* `not_isSquare_c_w7`: `c 1` is not a square at `w7` (odd valuation 7, Count/At7.lean), hence `GoodSextic`
  at `w7`;
* `coordCond_w7`: the local condition in coordinates with the image of `μ` as subgroup and the 5 rows `C7`
  of stage 6 of code/selmer-local-conditions/selmer_rows_twist1_w7.out (data `Assembly.C7Rows`).

`coordCond_w7` is `coordCond_w7_of` (W7Glue.lean) applied to the kernel checks of the w7 data (W7Check.lean).
-/

namespace FurioLombardo.Discharge.SelmerBasis.W7

open Polynomial FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.SelmerBasis
open scoped FurioLombardo.Discharge.SelmerBasis.Adic

/-- The completion at `w7`. -/
abbrev Kw : Type := w7.adicCompletion K21

/-- `K21 → K_w7`. -/
noncomputable abbrev σw : K21 →+* Kw := adicCoe w7

/-- `σ(c 1)` is not a square at `w7` (odd valuation 7, Count/At7.lean). -/
theorem not_isSquare_c_w7 : ¬ IsSquare (σw (c 1)) :=
  Count.not_isSquare_c_w7

instance goodSextic_w7 : GoodSextic ((fRev 1).map σw) :=
  goodSextic_fRev_map σw 1 (by rw [fRev_leadingCoeff]; exact not_isSquare_c_w7)

/-- The 5 rows at `w7`. -/
def C7 : Matrix (Fin 5) (Fin 82) (ZMod 2) :=
  Matrix.of fun i s => bitv 82 (Assembly.C7Rows.getD i 0) s

/-- The kernel checks of the w7 data, gathered for `coordCond_w7_of`. -/
theorem checks_w7 : Checks tab tabK M pts pairs cL cN cK Akap Amu Cg QI TI QC nQI where
  tab_len := tab_len
  tab_zero := tab_zero
  ck_tab := ck_tab
  ck_M := ck_M
  hN := by decide +kernel
  pts_len := by decide +kernel
  ck_pt := ck_pt
  ck_pair := ck_pair
  ck_L := ck_L
  ck_N := ck_N
  ck_K := ck_K
  kap_bits := kap_bits
  mu_bits := mu_bits
  cgL_bits := cgL_bits
  cgN_bits := cgN_bits
  annI := annI
  leftInv := leftInv
  annCk := annCk
  annCm := annCm
  c7_rows := c7_rows

/-- **`CoordCond` at `w7`.** -/
theorem coordCond_w7 : CoordCond σw (fRev 1) (gK 1) (muJ ((fRev 1).map σw)).range C7 :=
  coordCond_w7_of checks_w7

end FurioLombardo.Discharge.SelmerBasis.W7
