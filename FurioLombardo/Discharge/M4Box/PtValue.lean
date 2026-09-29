import Mathlib
import FurioLombardo.Discharge.M4Box.DFinal
import FurioLombardo.Discharge.M3a.AbelPrymKnown
import FurioLombardo.Discharge.M3a.CertMap

/-!
# The value certificate of `lamK k X` for a point given by a Mumford pair (lane lean-m4box)

`lamK_Dpt_of_cert` with `D_i` replaced by any `X` of `A(K_v)` with a pair `P` on the curve of class `X`
and a ball of `P`: `chart_eq_smul`, `lamK_sub_le`, `lamK_of_cert`. For the four known lifts `x_0, x_1,
x_2, x_3` the pair of `φ(x_i)` is M3a's `(apUp i, apVp i)` (`phiRev_x0`, ...) mapped by `σ`: `phiMum i`,
its ball `phiBall` from the `σ` images of its coefficients, and `hBallPhi_of_values`, the analogue of
`hBallD_of_values` for the two values bounded by `HBallPhi`.
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith
open FurioLombardo.Discharge.M3a.Bruin

namespace FurioLombardo.Discharge.M4Box

/-! ## The chain from any pair -/

/-- **The chain end is the chart point of `2^J N X`.** -/
theorem chart_eq_smul (k : Fin 2) {P : Mum Kv} {X : Additive (Jac ((fRev k).map σ))}
    (hP : P.OnCurve ((fRev k).map σ))
    (hPc : P.cls ((fRev k).map σ) = ((Additive.toMul X : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)))
    (J : ℕ) {R : Mum Kv}
    (hR : drun (fieldOps Kv) (Sext.ofPoly ((fRev k).map σ)) P (E0Mum k) (chainSteps J) P = some R)
    (ht : ∀ j, ‖R.chartT (aK k) j‖ ≤ ‖pv‖ ^ (M0 k + 4))
    (hres : resQ (R.chartT (aK k)) (R.chartW (aK k) +
      (baseKv k).toSetup.vPt (IntModelKv.admM0 k) (chartPt (M0 k) (R.chartT (aK k)) ht)) ≠ 0) :
    chart k (IntModelKv.admM0 k) (chartPt (M0 k) (R.chartT (aK k)) ht) = (2 ^ J * dN) • X := by
  set a := aK k
  set t := R.chartT a
  set w := R.chartW a
  set h := IntModelKv.admM0 k
  obtain ⟨hR1, hR2⟩ := drun_chainSteps_cls ((fRev k).map σ) hP (E0Mum_onCurve k) J hR
  rw [hPc] at hR2
  have hQ : clsA ((fRev k).map σ) a t w =
      ((Additive.toMul X : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) ^ (2 ^ J * dN) *
      clsA ((fRev k).map σ) a 0 (baseKv k).toSetup.v0 := by
    rw [← Mum.cls_eq_clsA (F := (fRev k).map σ) a R, ← E0Mum_cls k, hR2]
  have h_psi := psi_chartPt (baseKv k) (hF k) h ht (Mum.chartW_degree a R)
    (Mum.dvd_chart (hF k) hR1) hres hQ
  apply Additive.toMul.injective
  apply Subtype.ext
  simpa [toMul_nsmul, SubgroupClass.coe_pow] using h_psi

/-- **The value of `lamK` at `X` from the chain end.** -/
theorem lamK_sub_le (k : Fin 2) {P : Mum Kv} {X : Additive (Jac ((fRev k).map σ))}
    (hP : P.OnCurve ((fRev k).map σ))
    (hPc : P.cls ((fRev k).map σ) = ((Additive.toMul X : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)))
    (J : ℕ) {R : Mum Kv}
    (hR : drun (fieldOps Kv) (Sext.ofPoly ((fRev k).map σ)) P (E0Mum k) (chainSteps J) P = some R)
    {Dd : ℕ} (hDd : M0 k + 4 ≤ Dd) (hDd7 : 7 + 2 * IntModelKv.aa k ≤ Dd)
    (ht : ∀ j, ‖R.chartT (aK k) j‖ ≤ ‖pv‖ ^ Dd)
    (hw0 : ‖(R.chartW (aK k)).coeff 0 - bK k‖ < ‖2 * bK k‖)
    (hw1 : ‖(R.chartW (aK k)).coeff 1‖ * ‖pv‖ ^ IntModelKv.aa k ≤ ‖bK k‖) (j : Fin 2) :
    ‖((2 ^ J * dN : ℕ) : Kv) * lamK k X j - (Amat k *ᵥ R.chartT (aK k)) j‖ ≤
      ‖pv‖ ^ (2 * Dd - M0 k - 3) := by
  set h := IntModelKv.admM0 k
  have norm_pv_le_one' : ‖pv‖ ≤ 1 := norm_pv_le_one
  have ht4 : ∀ j, ‖R.chartT (aK k) j‖ ≤ ‖pv‖ ^ (M0 k + 4) := fun j =>
    (ht j).trans (pow_le_pow_of_le_one (norm_nonneg _) norm_pv_le_one' hDd)
  have ht0 : ‖R.chartT (aK k) 0‖ ≤ ‖pv‖ ^ (7 + IntModelKv.aa k) :=
    (ht 0).trans (pow_le_pow_of_le_one (norm_nonneg _) norm_pv_le_one' (by omega))
  have ht1 : ‖R.chartT (aK k) 1‖ ≤ ‖pv‖ ^ (7 + 2 * IntModelKv.aa k) :=
    (ht 1).trans (pow_le_pow_of_le_one (norm_nonneg _) norm_pv_le_one' hDd7)
  have hres : resQ (R.chartT (aK k)) (R.chartW (aK k) +
      (baseKv k).toSetup.vPt (IntModelKv.admM0 k) (chartPt (M0 k) (R.chartT (aK k)) ht4)) ≠ 0 :=
    resQ_chain_ne_zero k ht4 ht0 ht1 hw0 hw1
  set z := chartPt (M0 k) (R.chartT (aK k)) ht4
  have hchart : chart k h z = (2 ^ J * dN) • X := chart_eq_smul k hP hPc J hR ht4 hres
  have hlam : lamK k (chart k h z) j = ((2 ^ J * dN : ℕ) : Kv) * lamK k X j := by
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

/-- **The certificate of one point `X` with a ball `D` of a pair of class `X`.** -/
theorem lamK_of_cert (kk : Fin 2) {P : Mum Kv} {X : Additive (Jac ((fRev kk).map σ))}
    (hP : P.OnCurve ((fRev kk).map σ))
    (hPc : P.cls ((fRev kk).map σ) =
      ((Additive.toMul X : Jac ((fRev kk).map σ)) : Pic ((fRev kk).map σ)))
    {k : Ctx} (hk : k.Ok) {F g : Sext Ball} {b : Ball}
    {E D R : Mum Ball} {A : Mat2 Ball} {sB : N3} {eB J Dd : ℕ} {l : Fin 6 → ℤ} {q : ℕ}
    (hF : FvBall k kk = some F) (hg : gBall k F = some g) (hb : bKBall k kk g sB eB = some b)
    (hE : E0Ball k kk g b = some E) (hA : AmatBall k kk g b = some A)
    (hDm : Mum.Rel (fun x b => b.Mem x) P D)
    (hR : drun (ballOpsF k) g D E (chainSteps J) D = some R)
    (hfin : finalOK k A b kk (IntModelKv.aa kk) (M0 kk) R J Dd l q = true) (j : Fin 2) :
    ‖lamK kk X j‖ ≤ 1 ∧ ‖lamK kk X j - evZ (lTriple l j)‖ ≤ ‖pv‖ ^ (3 * q) := by
  have hFm := mem_FvBall hk hF
  have hgm := mem_gBall hk kk hFm hg
  have hbm := mem_bKBall hk kk hgm hb
  have hEm := mem_E0Ball hk kk hgm hbm hE
  have hAm := mem_AmatBall hk kk hgm hbm hA
  have hrel := Ops.Rel.drun (rel_ballOpsF hk) hgm hDm hEm (chainSteps J) hDm
  obtain ⟨Rx, hRx, hRR⟩ := hrel R hR
  have hs : Mum.Rel (fun x b => b.Mem x) (Mum.shift (fieldOps Kv) (aK kk) Rx) (shiftB k kk R) := by
    have h0 := Ops.Rel.shift (rel_ballOpsF hk) ((rel_ballOpsF hk).ofInt ((kk : ℕ) : ℤ)) hRR
    have e : (fieldOps Kv).ofInt ((kk : ℕ) : ℤ) = aK kk := by simp [fieldOps, aK]
    rw [e] at h0
    exact h0
  obtain ⟨hs0, hs1, hs2, hs3⟩ := hs
  simp only [finalOK, Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨⟨⟨⟨⟨⟨⟨hM, h7⟩, ht1⟩, ht0⟩, hw0⟩, hw1⟩, hl0⟩, hl1⟩ := hfin
  have ht : ∀ j, ‖Rx.chartT (aK kk) j‖ ≤ ‖pv‖ ^ Dd := by
    intro j
    rw [Mum.chartT_eq_shift]
    fin_cases j
    · exact Ball.norm_le_of_normLe hk hs1 ht1
    · exact Ball.norm_le_of_normLe hk hs0 ht0
  have hw0' : ‖(Rx.chartW (aK kk)).coeff 0 - bK kk‖ < ‖2 * bK kk‖ := by
    rw [chartW_coeff_zero_shift]
    exact Ball.norm_sub_lt_of_nearOK hk hs2 hbm hw0
  have hw1' : ‖(Rx.chartW (aK kk)).coeff 1‖ * ‖pv‖ ^ IntModelKv.aa kk ≤ ‖bK kk‖ := by
    rw [chartW_coeff_one_shift]
    exact Ball.norm_mul_le_of_normLeMul hk hs3 hbm hw1
  have hlam := lamK_sub_le kk hP hPc J hRx hM h7 ht hw0' hw1' j
  -- `j` stays a variable, as in `lamK_Dpt_of_cert`
  have hlj : lamCheck k A kk R J (2 * Dd - M0 kk - 3) j l q = true := by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · exact hl0
    · exact hl1
  obtain ⟨lb, hl, hok⟩ := lamCheck_eq_true hlj
  exact lamOK_sound hk (mem_lamBall hk kk hAm hRR j hlam hl) hok

/-! ## The pairs of `φ(x_i)` at the known lifts -/

/-- The pair `[U, V]` of `φ(x_i)` over `K_v`: M3a's `(apUp i, apVp i)` mapped by `σ`. -/
noncomputable def phiMum (i : ℕ) : Mum Kv :=
  ⟨σ ((apUdN i : K21)⁻¹ * zkE (apUL i 0)), σ ((apUdN i : K21)⁻¹ * zkE (apUL i 1)),
    σ ((apDN i : K21)⁻¹ * zkE (apVL i 0)), σ ((apDN i : K21)⁻¹ * zkE (apVL i 1))⟩

theorem phiMum_u {i : ℕ} (h : apUdN i ≠ 0) : (phiMum i).u = (apUp i).map σ := by
  have h' : (apUdN i : K21) ≠ 0 := by exact_mod_cast h
  ext n
  rcases n with (rfl|rfl|rfl|n)
  · unfold Mum.u phiMum apUp FurioLombardo.Discharge.M3a.pQ uL FurioLombardo.Discharge.M3a.pK
    simp [FurioLombardo.Discharge.M3a.pK_cons, FurioLombardo.Discharge.M3a.pK_nil, evK_int]
  · unfold Mum.u phiMum apUp FurioLombardo.Discharge.M3a.pQ uL FurioLombardo.Discharge.M3a.pK
    simp [FurioLombardo.Discharge.M3a.pK_cons, FurioLombardo.Discharge.M3a.pK_nil, evK_int]
  · unfold Mum.u phiMum apUp FurioLombardo.Discharge.M3a.pQ uL FurioLombardo.Discharge.M3a.pK
    simp [FurioLombardo.Discharge.M3a.pK_cons, FurioLombardo.Discharge.M3a.pK_nil, evK_int]
    field_simp [h']
  · unfold Mum.u phiMum apUp FurioLombardo.Discharge.M3a.pQ uL FurioLombardo.Discharge.M3a.pK
    simp [FurioLombardo.Discharge.M3a.pK_cons, FurioLombardo.Discharge.M3a.pK_nil, evK_int, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_add]

open FurioLombardo.Discharge.M3a in
theorem phiMum_v (i : ℕ) : (phiMum i).v = (apVp i).map σ := by
  unfold phiMum Mum.v apVp pQ vL
  simp only [pK_cons, pK_nil, evK_lin, mul_zero, add_zero,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, map_mul,
    C_mul]
  ring

/-- The pair of `φ(x)` from M3a's value of `φ(x)` at a known lift. -/
theorem phiMum_cls {k : Fin 2} (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) (i : Fin 4)
    (h : (phiK k x : Pic (fRev k)) =
      ClassGroup.mk0 (mumford0 (fRev k) (apUp_monic (ck_apNZ i).2.1).1.ne_zero (apVp i))) :
    (phiMum i).cls ((fRev k).map σ) =
      ((jacMap σ (fRev k) (phiK k x) : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) := by
  have hu := apUp_monic (ck_apNZ i).2.1
  change _ = picMap σ (fRev k) (phiK k x : Pic (fRev k))
  rw [h, picMap_mumford σ (fRev k) hu.1.ne_zero (hu.1.map σ).ne_zero, Mum.cls]
  exact mk0_mumford_eq _ _ (phiMum_u (ck_apNZ i).2.1) (phiMum_v i)

theorem phiMum_onCurve {k : Fin 2} (i : Fin 4) (h : apUp i ∣ apVp i ^ 2 - fRev k) :
    (phiMum i).OnCurve ((fRev k).map σ) := by
  rw [Mum.OnCurve, phiMum_u (ck_apNZ i).2.1, phiMum_v i, ← neg_sub, dvd_neg]
  have := Polynomial.map_dvd σ h
  simpa [Polynomial.map_sub, Polynomial.map_pow] using this

theorem mem_phiBall {k : Ctx} (hk : k.Ok) {i : ℕ} {d : Mum Ball} (h : phiBall k i = some d) :
    Mum.Rel (fun x b => b.Mem x) (phiMum i) d := by
  unfold phiBall at h
  obtain ⟨u0, hu0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u1, hu1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v0, hv0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v1, hv1, h⟩ := Option.bind_eq_some_iff.mp h
  have hd : d = ⟨u0, u1, v0, v1⟩ := by
    simpa using h.symm
  subst hd
  unfold phiMum
  exact ⟨mem_sigQ hk hu0, mem_sigQ hk hu1, mem_sigQ hk hv0, mem_sigQ hk hv1⟩

/-! ## From the values to `HBallPhi` -/

/-- **`HBallPhi` from the value bounds.** -/
theorem hBallPhi_of_values (kk : Fin 2) (D : FurioLombardo.M4.TwistData) (hI : LamInt kk)
    {Xa Xb : Additive (Jac ((fRev kk).map σ))}
    (ha : ∀ j, ‖lamK kk Xa j - evZ (lTriple D.la j)‖ ≤ ‖pv‖ ^ (3 * D.qa))
    (hb : ∀ j, ‖lamK kk Xb j - evZ (lTriple D.lb j)‖ ≤ ‖pv‖ ^ (3 * D.qb)) :
    FurioLombardo.M4.HBallPhi D (lam kk Xa) (lam kk Xb) := by
  constructor
  · apply dvdV_of_norm_toKv2_le
    intro j
    rw [map_sub, lam_toKv2 kk hI, Pi.sub_apply, toKv2_icast]
    exact ha j
  · apply dvdV_of_norm_toKv2_le
    intro j
    rw [map_sub, lam_toKv2 kk hI, Pi.sub_apply, toKv2_icast]
    exact hb j

end FurioLombardo.Discharge.M4Box
