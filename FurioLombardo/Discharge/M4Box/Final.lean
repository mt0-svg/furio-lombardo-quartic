import Mathlib
import FurioLombardo.Discharge.M4Box.CentreData.Values0
import FurioLombardo.Discharge.M4Box.CentreData.Values1
import FurioLombardo.Discharge.M4Box.BoxData.Values0
import FurioLombardo.Discharge.M4Box.BoxData.Values1
import FurioLombardo.Discharge.M4Box.LiftLog
import FurioLombardo.Discharge.M4Box.WeakConsumer
import FurioLombardo.Discharge.M4Box.SelLoc
import FurioLombardo.Discharge.SelmerBasis.Assembly

/-!
# The frozen statement from the certificates (lane lean-m4box, assembly)

`onlyFourPoints_of_chartLog_weak` asks, for each twist `k`, the Selmer basis `SelmerBasisK21 k`, a
logarithm with `ChartLog k` and the eight fields of `M4RestKvW` at the points `SelmerSpan.Dpt k`, for the
Abel-Prym map `phiK k` and the known lifts. With lane M4's logarithm `lam k` and branch `lamD k`:

* `hBD`, `hBP`, `hCe` are the certificate theorems of DCertData, PhiCertData, CentreData;
* `hCL`, `hTQ` come from the per box statements `ConstCert`, `TailCert` of BoxData (`hConstLip_of_cert`,
  `hTailQuad_of_cert`), and so does the branch cover of `hLog` (`branchCover_of_cert`);
* `hKn` and `hLog` need `log φ(x) ∈ Λ` for the known lifts, which is `HLam` (`hLam_k`: the chart, the
  2-torsion `{0, T}` and the independence of the `D_i` modulo 2);
* `hSel` is the localisation of the Selmer basis at `v` (`hSel_of_selmerBasis`).

The Selmer bases `selmerBasis_k` come from SelmerBasis/Assembly.lean.
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.Analytic (hLam_of_chartFin)

namespace FurioLombardo.Discharge.M4Box

/-! ## `HLam` and the logarithms of the known lifts -/

/-- **`HLam` for lane M4's logarithm**: the logarithms of `J(K_v)` are the `ℤ_2`-span of the
`lam (D_i)`. -/
theorem hLam_k (k : Fin 2) : FurioLombardo.M4.HLam (lam k) (SelmerSpan.Dpt k) := by
  obtain ⟨T, hT⟩ := two_torsion_Kv k
  exact hLam_of_chartFin (DCertData.chartLog k).logChartFin hT
    (indepModTwo_of_mu (SelmerSpan.Dpt k) (SelmerSpan.indep_Dpt k))

theorem logPhi_mem (k : Fin 2) (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    logPhi σ (fRev k) (phiK k) (lam k) x ∈ latL (lam k) (SelmerSpan.Dpt k) :=
  (hLam_k k _).mp ⟨_, rfl⟩

/-! ## The per box statements and the Selmer bases -/

theorem constCert_0 : ∀ c ∈ FurioLombardo.M4.T0.data.constant, ConstCert 0 (IntModelKv.admM0 0) c :=
  BoxData.constCert_0

theorem tailCert_0 : ∀ b ∈ FurioLombardo.M4.T0.data.tails, TailCert 0 (IntModelKv.admM0 0) b :=
  BoxData.tailCert_0

theorem constCert_1 : ∀ c ∈ FurioLombardo.M4.T1.data.constant, ConstCert 1 (IntModelKv.admM0 1) c :=
  BoxData.constCert_1

theorem tailCert_1 : ∀ b ∈ FurioLombardo.M4.T1.data.tails, TailCert 1 (IntModelKv.admM0 1) b :=
  BoxData.tailCert_1

theorem selmerBasis_0 : SelmerSpan.SelmerBasisK21 0 FurioLombardo.M4.T0.data.SB :=
  SelmerBasis.Assembly.selmerBasis_0

theorem selmerBasis_1 : SelmerSpan.SelmerBasisK21 1 FurioLombardo.M4.T1.data.SB :=
  SelmerBasis.Assembly.selmerBasis_1

/-! ## `M4RestKvW` for the two twists -/

theorem m4RestKvW_0 : M4RestKvW 0 FurioLombardo.M4.T0.data (phiK 0) x0 x2 (lam 0) (SelmerSpan.Dpt 0) (lamD 0) where
  hBD := DCertData.hBD_0
  hBP := PhiCertData.hBP_0
  hCe := CentreData.hCe_0
  hCL := hConstLip_of_cert (IntModelKv.admM0 0) (lamInt_of 0 (DCertData.lamK_Dpt_le_one 0)) constCert_0
  hTQ := hTailQuad_of_cert FurioLombardo.M4.T0.checks (IntModelKv.admM0 0)
    (lamInt_of 0 (DCertData.lamK_Dpt_le_one 0)) tailCert_0
  hKn := hKnown_0 _ (logPhi_mem 0 x0) (logPhi_mem 0 x2)
  hSel := hSel_of_selmerBasis 0 selmerBasis_0
  hLog := hLog_of_cover 0 (branchCover_of_cert 0 (IntModelKv.admM0 0) FurioLombardo.M4.T0.checks hExcl_T0_Mmat
    constCert_0 tailCert_0) _ (logPhi_mem 0 x0)

theorem m4RestKvW_1 : M4RestKvW 1 FurioLombardo.M4.T1.data (phiK 1) x1 x3 (lam 1) (SelmerSpan.Dpt 1) (lamD 1) where
  hBD := DCertData.hBD_1
  hBP := PhiCertData.hBP_1
  hCe := CentreData.hCe_1
  hCL := hConstLip_of_cert (IntModelKv.admM0 1) (lamInt_of 1 (DCertData.lamK_Dpt_le_one 1)) constCert_1
  hTQ := hTailQuad_of_cert FurioLombardo.M4.T1.checks (IntModelKv.admM0 1)
    (lamInt_of 1 (DCertData.lamK_Dpt_le_one 1)) tailCert_1
  hKn := hKnown_1 _ (logPhi_mem 1 x1) (logPhi_mem 1 x3)
  hSel := hSel_of_selmerBasis 1 selmerBasis_1
  hLog := hLog_of_cover 1 (branchCover_of_cert 1 (IntModelKv.admM0 1) FurioLombardo.M4.T1.checks hExcl_T1_Mmat
    constCert_1 tailCert_1) _ (logPhi_mem 1 x1)

/-- **The frozen statement** `FurioLombardo.OnlyFourPoints`. -/
theorem onlyFourPoints : FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_of_chartLog_weak selmerBasis_0 selmerBasis_1
    ⟨lam 0, lamD 0, DCertData.chartLog 0, m4RestKvW_0⟩ ⟨lam 1, lamD 1, DCertData.chartLog 1, m4RestKvW_1⟩

end FurioLombardo.Discharge.M4Box
