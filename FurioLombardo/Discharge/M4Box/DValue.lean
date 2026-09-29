import Mathlib
import FurioLombardo.Discharge.M4Box.LogBound
import FurioLombardo.Discharge.M4Box.Amat
import FurioLombardo.Discharge.M4Log.IntModelKv
import FurioLombardo.Discharge.SelmerSpan.Dpt
import FurioLombardo.Discharge.KvArith.DChain
import FurioLombardo.Discharge.KvArith.ChartBranch

/-!
# The values `lamK k (D_i)` from the chain `2^J N D_i + E0` (lane lean-m4box)

`DptMum k i` is the Mumford pair of `SelmerSpan.Dpt k i` on `g = (fRev k)^σ`, `E0Mum k` the base pair
`[(X - a)², v0(X - a)]` of the chart. If the exact chain `drun ... (chainSteps J)` from `D_i` ends at
`R` with chart coordinates `t = R.chartT a` deep enough and `w = R.chartW a` on the branch of `v0`, then
`R` is the chart point `ψ(t / π^M0)` of `2^J N D_i` (`chart_eq_smul_Dpt`), so by the chart bound
`norm_lamK_chart_sub_le`:
`‖2^J N lamK(D_i) - Amat t‖ ≤ ‖π‖^(2D - M0 - 3)` (`lamK_Dpt_sub_le`).
The ball run that certifies the exact run and encloses `t`, `w` is the certificate layer (probe:
code/local-group/di_values_ball_run.sh, P = 600 bits, J = 35 to 53).
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith
open FurioLombardo.Discharge.M3a.Bruin (fRev goodSextic_fRev_Kv)

namespace FurioLombardo.Discharge.M4Box

/-! ## The pairs -/

/-- The Mumford pair `[U, V]` of `SelmerSpan.Dpt k i`. -/
noncomputable def DptMum (k : Fin 2) (i : Fin 7) : Mum Kv :=
  ⟨σ (SelmerSpan.rG k i), σ (SelmerSpan.pG k i),
    SelmerSpan.sqC (σ (SelmerSpan.pG k i)) (SelmerSpan.Z1v k i) (SelmerSpan.av k i),
    SelmerSpan.sqB (SelmerSpan.Z1v k i) (SelmerSpan.av k i)⟩

theorem DptMum_u (k : Fin 2) (i : Fin 7) : (DptMum k i).u = SelmerSpan.Uv k i := by
  unfold DptMum Mum.u SelmerSpan.Uv SelmerSpan.quad
  rfl

theorem DptMum_v (k : Fin 2) (i : Fin 7) : (DptMum k i).v = SelmerSpan.Vv k i := by
  unfold DptMum Mum.v SelmerSpan.Vv
  rfl

theorem DptMum_onCurve (k : Fin 2) (i : Fin 7) : (DptMum k i).OnCurve ((fRev k).map σ) := by
  rw [Mum.OnCurve, DptMum_u k i, DptMum_v k i]
  exact ⟨-SelmerSpan.Wv k i, by rw [← neg_sub, SelmerSpan.hw k i]; ring⟩

theorem DptMum_cls (k : Fin 2) (i : Fin 7) :
    (DptMum k i).cls ((fRev k).map σ) =
      ((Additive.toMul (SelmerSpan.Dpt k i) : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) := by
  rw [SelmerSpan.Dpt_mumford k i]
  unfold Mum.cls
  have h_u : (DptMum k i).u = SelmerSpan.quad (σ (SelmerSpan.pG k i)) (σ (SelmerSpan.rG k i)) := by
    rw [DptMum_u k i, SelmerSpan.Uv]
  apply mk0_mumford_eq
  · exact h_u
  · exact DptMum_v k i

/-- The base pair `[(X - a)², v0(X - a)]` of the chart of `baseKv k`. -/
noncomputable def E0Mum (k : Fin 2) : Mum Kv :=
  ⟨aK k ^ 2, -(2 * aK k), (baseKv k).toSetup.v0.coeff 0 - aK k * (baseKv k).toSetup.v0.coeff 1,
    (baseKv k).toSetup.v0.coeff 1⟩

theorem E0Mum_chartT (k : Fin 2) : (E0Mum k).chartT (aK k) = 0 := by
  funext j
  fin_cases j <;> simp [Mum.chartT, E0Mum] <;> ring

theorem E0Mum_chartW (k : Fin 2) : (E0Mum k).chartW (aK k) = (baseKv k).toSetup.v0 := by
  unfold E0Mum Mum.chartW
  simp [sub_add_cancel]
  have hdeg : (baseKv k).toSetup.v0.degree ≤ 1 := by
    have hlt := FurioLombardo.Vendor.Toolbox.G2Formal.Setup.degree_v0 (baseKv k).toSetup
    cases h : (baseKv k).toSetup.v0.degree with
    | bot => exact bot_le
    | coe n =>
      rw [h] at hlt
      have hn' : n < 2 := by
        -- hlt : (n : WithBot ℕ) < (2 : WithBot ℕ)
        -- we need n < 2 in ℕ
        exact WithBot.coe_lt_coe.mp hlt
      have hn'' : n ≤ 1 := by omega
      simpa using hn''
  rw [← Polynomial.eq_X_add_C_of_degree_le_one hdeg]

theorem E0Mum_onCurve (k : Fin 2) : (E0Mum k).OnCurve ((fRev k).map σ) := by
  let S := (baseKv k).toSetup
  have h_dvd : X ^ 2 ∣ S.f - S.v0 ^ 2 := FurioLombardo.Vendor.Toolbox.G2Formal.Setup.dvd_f_sub_v0 (S := S)
  have h_comp : (X - C (aK k)) ^ 2 ∣ S.f.comp (X - C (aK k)) - (S.v0.comp (X - C (aK k))) ^ 2 := by
    have h := (Polynomial.compRingHom (X - C (aK k))).map_dvd h_dvd
    simpa [Polynomial.coe_compRingHom_apply] using h
  have h_u : (E0Mum k).u = (X - C (aK k)) ^ 2 := by
    calc
      (E0Mum k).u = (FurioLombardo.Vendor.Toolbox.G2Formal.uT ((E0Mum k).chartT (aK k))).comp (X - C (aK k)) := by
        rw [Mum.u_eq_comp]
      _ = (FurioLombardo.Vendor.Toolbox.G2Formal.uT 0).comp (X - C (aK k)) := by rw [E0Mum_chartT]
      _ = (X ^ 2).comp (X - C (aK k)) := by simp [FurioLombardo.Vendor.Toolbox.G2Formal.uT]
      _ = (X - C (aK k)) ^ 2 := by
        simp
  have h_v : (E0Mum k).v = S.v0.comp (X - C (aK k)) := by
    calc
      (E0Mum k).v = ((E0Mum k).chartW (aK k)).comp (X - C (aK k)) := by rw [Mum.v_eq_comp]
      _ = S.v0.comp (X - C (aK k)) := by rw [E0Mum_chartW]
  rw [Mum.OnCurve, h_u, h_v]
  have hSf : S.f = fK k := rfl
  rw [hSf, hF k] at h_comp
  exact h_comp

theorem E0Mum_cls (k : Fin 2) :
    (E0Mum k).cls ((fRev k).map σ) = clsA ((fRev k).map σ) (aK k) 0 (baseKv k).toSetup.v0 := by
  have h := Mum.cls_eq_clsA (F := (fRev k).map σ) (aK k) (E0Mum k)
  rw [E0Mum_chartT, E0Mum_chartW] at h
  exact h

/-! ## The chart point of the chain end -/

theorem M0_eq_four_mul (k : Fin 2) : M0 k = 4 * IntModelKv.aa k := by
  fin_cases k <;> rfl

theorem intModel_b (k : Fin 2) : (IntModelKv.intModel k).b = bK k := by
  rfl

/-- **The chain end is the chart point of `2^J N D_i`.** -/
theorem chart_eq_smul_Dpt (k : Fin 2) (i : Fin 7) (J : ℕ) {R : Mum Kv}
    (hR : drun (fieldOps Kv) (Sext.ofPoly ((fRev k).map σ)) (DptMum k i) (E0Mum k) (chainSteps J)
      (DptMum k i) = some R)
    (ht : ∀ j, ‖R.chartT (aK k) j‖ ≤ ‖pv‖ ^ (M0 k + 4))
    (hres : resQ (R.chartT (aK k)) (R.chartW (aK k) +
      (baseKv k).toSetup.vPt (IntModelKv.admM0 k) (chartPt (M0 k) (R.chartT (aK k)) ht)) ≠ 0) :
    chart k (IntModelKv.admM0 k) (chartPt (M0 k) (R.chartT (aK k)) ht) =
      (2 ^ J * dN) • SelmerSpan.Dpt k i := by
  set a := aK k
  set t := R.chartT a
  set w := R.chartW a
  set h := IntModelKv.admM0 k
  obtain ⟨hR1, hR2⟩ := drun_chainSteps_cls ((fRev k).map σ) (DptMum_onCurve k i) (E0Mum_onCurve k) J hR
  rw [DptMum_cls k i] at hR2
  have hQ : clsA ((fRev k).map σ) a t w =
      ((Additive.toMul (SelmerSpan.Dpt k i) : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) ^ (2 ^ J * dN) *
      clsA ((fRev k).map σ) a 0 (baseKv k).toSetup.v0 := by
    rw [← Mum.cls_eq_clsA (F := (fRev k).map σ) a R, ← E0Mum_cls k, hR2]
  have h_psi := psi_chartPt (baseKv k) (hF k) h ht (Mum.chartW_degree a R)
    (Mum.dvd_chart (hF k) hR1) hres hQ
  apply Additive.toMul.injective
  apply Subtype.ext
  simpa [toMul_nsmul, SubgroupClass.coe_pow] using h_psi

theorem resQ_chain_ne_zero_aux1 (k : Fin 2) (M : ℕ)
    (hM : M = 4 * IntModelKv.aa k)
    (hA : (baseKv k).toSetup.Adm M) {t : Fin 2 → Kv} {w : Kv[X]}
    (ht : ∀ j, ‖t j‖ ≤ ‖pv‖ ^ (M + 4))
    (ht0 : ‖t 0‖ ≤ ‖pv‖ ^ (7 + IntModelKv.aa k))
    (ht1 : ‖t 1‖ ≤ ‖pv‖ ^ (7 + 2 * IntModelKv.aa k))
    (hw0 : ‖w.coeff 0 - bK k‖ < ‖2 * bK k‖)
    (hw1 : ‖w.coeff 1‖ * ‖pv‖ ^ IntModelKv.aa k ≤ ‖bK k‖) :
    resQ t (w + (baseKv k).toSetup.vPt hA (chartPt M t ht)) ≠ 0 := by
  subst hM
  have hm : 7 ≤ 7 := le_refl 7
  have h_adm_eq : hA = M4Log.Model.adm_of_intModel (IntModelKv.intModel k) := Subsingleton.elim _ _
  rw [h_adm_eq]
  simpa [intModel_b k] using
    resQ_branch_ne_zero (baseKv k) (IntModelKv.intModel k) ht hm ht0 ht1 hw0 hw1

/-- The branch condition of the chain end gives the `hres` of `chart_eq_smul_Dpt`
(`resQ_branch_ne_zero` at the integral model `IntModelKv.intModel k`, `M0 k = 4 aa k`). -/
theorem resQ_chain_ne_zero (k : Fin 2) {t : Fin 2 → Kv} {w : Kv[X]}
    (ht : ∀ j, ‖t j‖ ≤ ‖pv‖ ^ (M0 k + 4))
    (ht0 : ‖t 0‖ ≤ ‖pv‖ ^ (7 + IntModelKv.aa k)) (ht1 : ‖t 1‖ ≤ ‖pv‖ ^ (7 + 2 * IntModelKv.aa k))
    (hw0 : ‖w.coeff 0 - bK k‖ < ‖2 * bK k‖) (hw1 : ‖w.coeff 1‖ * ‖pv‖ ^ IntModelKv.aa k ≤ ‖bK k‖) :
    resQ t (w + (baseKv k).toSetup.vPt (IntModelKv.admM0 k) (chartPt (M0 k) t ht)) ≠ 0 := by
  exact resQ_chain_ne_zero_aux1 k (M0 k) (M0_eq_four_mul k)
    (IntModelKv.admM0 k) ht ht0 ht1 hw0 hw1

/-- **The value of `lamK` at `D_i` from the chain end.** -/
theorem lamK_Dpt_sub_le (k : Fin 2) (i : Fin 7) (J : ℕ) {R : Mum Kv}
    (hR : drun (fieldOps Kv) (Sext.ofPoly ((fRev k).map σ)) (DptMum k i) (E0Mum k) (chainSteps J)
      (DptMum k i) = some R)
    {Dd : ℕ} (hDd : M0 k + 4 ≤ Dd) (hDd7 : 7 + 2 * IntModelKv.aa k ≤ Dd)
    (ht : ∀ j, ‖R.chartT (aK k) j‖ ≤ ‖pv‖ ^ Dd)
    (hw0 : ‖(R.chartW (aK k)).coeff 0 - bK k‖ < ‖2 * bK k‖)
    (hw1 : ‖(R.chartW (aK k)).coeff 1‖ * ‖pv‖ ^ IntModelKv.aa k ≤ ‖bK k‖) (j : Fin 2) :
    ‖((2 ^ J * dN : ℕ) : Kv) * lamK k (SelmerSpan.Dpt k i) j - (Amat k *ᵥ R.chartT (aK k)) j‖ ≤
      ‖pv‖ ^ (2 * Dd - M0 k - 3) := by
  set h := IntModelKv.admM0 k
  have norm_pv_le_one' : ‖pv‖ ≤ 1 := norm_pv_le_one
  have ht4 : ∀ j, ‖R.chartT (aK k) j‖ ≤ ‖pv‖ ^ (M0 k + 4) := by
    intro j
    refine (ht j).trans ?_
    have : M0 k + 4 ≤ Dd := hDd
    exact pow_le_pow_of_le_one (norm_nonneg _) norm_pv_le_one' this
  have ht0 : ‖R.chartT (aK k) 0‖ ≤ ‖pv‖ ^ (7 + IntModelKv.aa k) := by
    refine (ht 0).trans ?_
    have : 7 + IntModelKv.aa k ≤ Dd := by
      have : 7 + 2 * IntModelKv.aa k ≤ Dd := hDd7
      omega
    exact pow_le_pow_of_le_one (norm_nonneg _) norm_pv_le_one' this
  have ht1 : ‖R.chartT (aK k) 1‖ ≤ ‖pv‖ ^ (7 + 2 * IntModelKv.aa k) := by
    refine (ht 1).trans ?_
    exact pow_le_pow_of_le_one (norm_nonneg _) norm_pv_le_one' hDd7
  have hres : resQ (R.chartT (aK k)) (R.chartW (aK k) +
      (baseKv k).toSetup.vPt (IntModelKv.admM0 k) (chartPt (M0 k) (R.chartT (aK k)) ht4)) ≠ 0 :=
    resQ_chain_ne_zero k ht4 ht0 ht1 hw0 hw1
  set z := chartPt (M0 k) (R.chartT (aK k)) ht4
  have hchart : chart k h z = (2 ^ J * dN) • SelmerSpan.Dpt k i :=
    chart_eq_smul_Dpt k i J hR ht4 hres
  have hlam : lamK k (chart k h z) j = ((2 ^ J * dN : ℕ) : Kv) * lamK k (SelmerSpan.Dpt k i) j := by
    rw [hchart, map_nsmul]
    simp [Pi.smul_apply, nsmul_eq_mul]
  have htK : tK k h z = R.chartT (aK k) := by
    dsimp [tK, z]
    rw [tPt_chartPt (baseKv k) (M0 k) (R.chartT (aK k)) ht4]
  have ht' : ∀ i, ‖tK k h z i‖ ≤ ‖pv‖ ^ Dd := by
    intro i
    rw [htK]
    exact ht i
  have hbound := norm_lamK_chart_sub_le k h (fun i j => norm_Amat_le_one k i j) z hDd ht' j
  rw [hlam, htK] at hbound
  exact hbound

end FurioLombardo.Discharge.M4Box
