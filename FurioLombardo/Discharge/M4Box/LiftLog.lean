import Mathlib
import FurioLombardo.Discharge.M3a.CertSmul
import FurioLombardo.Discharge.M4Box.Known
import FurioLombardo.Discharge.M4Box.BoxCert
import FurioLombardo.Discharge.M4Cert.Bridge
import FurioLombardo.M4.Cover

/-!
# The logarithm of a lift and the branch `lamD` (lane lean-m4box, `hLog`)

A lift `x` of twist `δ_k` lies over a point of `C(ℚ_2)` of disc `d = liftDisc x` and parameter
`X = liftPar x`, of twist `δ_k` (`liftTwist_Mmat`). Its image in `D_δ(K_v)` is a rescaling of a point
over `pKv d X` (`exists_smul_pKv`), which has the same value of `φ_v` (`phiRev_smul`). The box
certificates give a box of the branch table at `(d, X)` and a point on its branch there
(`branchCover_of_cert`), which is the rescaled image of `x` or its inverse. Hence `lamD d X` is
`± log φ(x) - log φ(x_a)` (`lamD_lift`), and `liftLog x = log φ(x) - log φ(x_a)`: the difference or
the sum lies in `satOf Λ (log φ(x_a)) b` (`hLog_of_cover`).
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M4Log FurioLombardo.M4
open FurioLombardo.Discharge.Analytic (satOf left_mem_satOf)
open FurioLombardo.Discharge.M3a (logPhi liftLog LogBranch)
open FurioLombardo.Discharge.M3a.AbelPrym (mapPt smulPt phiRev_smul)
open FurioLombardo.Discharge.M3a.Bruin (fRev Mmat δ phiK goodSextic_fRev_Kv)

namespace FurioLombardo.Discharge.M4Box

attribute [local instance] goodSextic_fRev_Kv

/-- Every parameter of twist `δ_k` has a box of the branch table and a point of `D_δ(K_v)` on its
branch over `pKv d X`. -/
def BranchCover (k : Fin 2) : Prop :=
  ∀ d ∈ [1, 2, 3, 4, 5], ∀ X : ℤ_[2], Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k) d X →
    ∃ e, boxAt k d X = some e ∧ ∃ y : DPtKv k, y.p = pKv d X ∧ BranchOK e y

/-- **`BranchCover` from the box certificates**: a parameter of twist `δ_k` lies in a box of the
covering (`TwistChecks.cover`), not an excluded one (`HExcl`), and the certificate of its constant
or tail box gives the point on the branch (`ArcChart`). -/
theorem branchCover_of_cert (k : Fin 2) (h : AdmM0 k) {D : TwistData} (hD : TwistChecks D)
    (hEx : HExcl D (Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k)))
    (hC : ∀ c ∈ D.constant, ConstCert k h c) (hT : ∀ t ∈ D.tails, TailCert k h t) :
    BranchCover k := by
  intro d hd X hX
  have hcover := hD.cover d hd
  obtain ⟨p, hp, hXp⟩ := cover_of_coverCheck (boxesOf D.excluded D.constant D.tails d) 12 hcover X
  rcases mem_boxesOf hp with (⟨e, he, hed, rfl⟩ | ⟨c, hc, hcd, rfl⟩ | ⟨t, ht, htd, rfl⟩)
  · -- excluded box
    have hcontra := hEx e he X hXp
    rw [hed] at hcontra
    exact absurd hX hcontra
  · -- constant box
    obtain ⟨e, he, hed, hec, hes, D', hM0D', hineq, hA⟩ := hC c hc
    rcases hXp with ⟨y, hy⟩
    have hArc := hA y
    rcases hArc with ⟨x, x0, hxp, hxOK, hx0p, hx0OK, z, hz, hP⟩
    have hbox : boxAt k d X = some e := by
      apply boxAt_eq_of_mem he
      · rw [hed, hcd]
      · rw [hec, hes]
        exact ⟨y, hy⟩
    rw [hed, hcd] at hxp
    rw [← hy] at hxp
    refine ⟨e, hbox, x, hxp, hxOK⟩
  · -- tail box
    obtain ⟨e, he, hed, hec, hes, c0, c1, a1, aS, NS, hM0ineq, h3vmNS, h3vm2d1, hc1, hg, hA⟩ := hT t ht
    rcases hXp with ⟨y, hy⟩
    obtain ⟨_, _, _, _, _, _, _, hmod⟩ := hD.tailsOK t ht
    have hdvd : (2 : ℤ) ^ t.s ∣ (t.c : ℤ) - t.Xi := by
      have hzero : ((t.c : ℤ) - t.Xi) % (2 : ℤ) ^ t.s = 0 :=
        (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod)
      exact Int.dvd_iff_emod_eq_zero.mpr hzero
    rcases hdvd with ⟨m, hm⟩
    have hm_eq : (t.c : ℤ) = t.Xi + (2 : ℤ) ^ t.s * m := by
      linarith
    have hX_eq : X = (t.Xi : ℤ_[2]) + (2 : ℤ_[2]) ^ t.s * ((m : ℤ_[2]) + y) := by
      rw [hy]
      have hm_cast : (t.c : ℤ_[2]) = (t.Xi : ℤ_[2]) + ((2 : ℤ) ^ t.s : ℤ_[2]) * (m : ℤ_[2]) := by
        exact_mod_cast hm_eq
      rw [hm_cast]
      push_cast
      ring
    have hArc := hA ((m : ℤ_[2]) + y)
    rcases hArc with ⟨x, x0, hxp, hxOK, hx0p, hx0OK, z, hz, hP⟩
    have hbox : boxAt k d X = some e := by
      apply boxAt_eq_of_mem he
      · rw [hed, htd]
      · rw [hec, hes]
        exact ⟨y, hy⟩
    rw [hed, htd] at hxp
    rw [← hX_eq] at hxp
    refine ⟨e, hbox, x, hxp, hxOK⟩

/-! ## The lift over `pKv d X` -/

theorem discY_eq_of_F {d : ℕ} (hd : IsDisc d) {X Y : ℤ_[2]}
    (h : FurioLombardo.F (discPt d X Y 0) (discPt d X Y 1) (discPt d X Y 2) = 0) : discY d X = Y := by
  exact ((discY_spec hd X).2 Y h).symm

/-- The image in `D_δ(K_v)` of a lift is a rescaling of a point over `pKv d X`. -/
theorem exists_smul_pKv (k : Fin 2) (x : FurioLombardo.M3a.Route.Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    ∃ a : Kv, a ≠ 0 ∧ (mapPt σ x.1).p = a • pKv (liftDisc x) (liftPar x) := by
  have h := nonempty_discData (onC_Mmat (δ k)) x
  rw [liftDisc_eq x h, liftPar_eq x h]
  set D := Classical.choice h with hD_def
  have hD_hov : (x.1).Over D.a D.b D.c := D.hov
  have hD_hd : D.d ∈ [1, 2, 3, 4, 5] := D.hd
  have hD_hμ : D.μ ≠ 0 := D.hμ
  have hD_h0 : D.μ * (D.a : ℚ_[2]) = ((discPt D.d D.X D.Y 0 : ℤ_[2]) : ℚ_[2]) := D.h0
  have hD_h1 : D.μ * (D.b : ℚ_[2]) = ((discPt D.d D.X D.Y 1 : ℤ_[2]) : ℚ_[2]) := D.h1
  have hD_h2 : D.μ * (D.c : ℚ_[2]) = ((discPt D.d D.X D.Y 2 : ℤ_[2]) : ℚ_[2]) := D.h2
  have hF_onC : F D.a D.b D.c = 0 := onC_Mmat (δ k) x.1 D.a D.b D.c hD_hov
  -- Prove that F vanishes at discPt D.d D.X D.Y 0, discPt D.d D.X D.Y 1, discPt D.d D.X D.Y 2
  have hF_discY : F (discPt D.d D.X D.Y 0) (discPt D.d D.X D.Y 1) (discPt D.d D.X D.Y 2) = 0 := by
    apply F_eq_zero_of_coe
    calc
      F ((discPt D.d D.X D.Y 0 : ℤ_[2]) : ℚ_[2]) ((discPt D.d D.X D.Y 1 : ℤ_[2]) : ℚ_[2]) ((discPt D.d D.X D.Y 2 : ℤ_[2]) : ℚ_[2])
          = F (D.μ * (D.a : ℚ_[2])) (D.μ * (D.b : ℚ_[2])) (D.μ * (D.c : ℚ_[2])) := by
        simp [hD_h0, hD_h1, hD_h2]
      _ = D.μ ^ 4 * F (D.a : ℚ_[2]) (D.b : ℚ_[2]) (D.c : ℚ_[2]) := by rw [F_smul]
      _ = D.μ ^ 4 * ((F D.a D.b D.c : ℚ) : ℚ_[2]) := by rw [F_rat_cast]
      _ = D.μ ^ 4 * ((0 : ℚ) : ℚ_[2]) := by rw [hF_onC]
      _ = 0 := by simp
  have hdisc : IsDisc D.d := by
    simpa [IsDisc] using hD_hd
  have discY_eq : discY D.d D.X = D.Y := discY_eq_of_F hdisc hF_discY
  rcases hD_hov with ⟨t0, ht0_ne, hp_eq⟩
  rcases liftTwist_Mmat (δ k) x with ⟨hdisc_mem, hTwist⟩
  rcases hTwist with ⟨Y', hF', D', t, ht_ne, hD'_p⟩
  set a := σ t0 * (algebraMap ℚ_[2] Kv D.μ)⁻¹ with ha_def
  have ha_ne : a ≠ 0 := by
    rw [ha_def]
    refine mul_ne_zero ((map_ne_zero σ).mpr ht0_ne) (inv_ne_zero ((map_ne_zero (algebraMap ℚ_[2] Kv)).mpr hD_hμ))
  refine ⟨a, ha_ne, ?_⟩
  show (mapPt σ x.1).p = a • pKv D.d D.X
  ext i
  have h_coord : ((![D.a, D.b, D.c] i : ℚ) : ℚ_[2]) = (D.μ)⁻¹ * ((discPt D.d D.X D.Y i : ℤ_[2]) : ℚ_[2]) := by
    fin_cases i
    · simp; field_simp [hD_hμ]; rw [← hD_h0]; ring
    · simp; field_simp [hD_hμ]; rw [← hD_h1]; ring
    · simp; field_simp [hD_hμ]; rw [← hD_h2]; ring
  calc
    (mapPt σ x.1).p i = σ (x.1.p i) := rfl
    _ = σ ((t0 • ![algebraMap ℚ K21 D.a, algebraMap ℚ K21 D.b, algebraMap ℚ K21 D.c]) i) := by rw [hp_eq]
    _ = σ (t0 * (![algebraMap ℚ K21 D.a, algebraMap ℚ K21 D.b, algebraMap ℚ K21 D.c] i)) := rfl
    _ = σ t0 * σ (![algebraMap ℚ K21 D.a, algebraMap ℚ K21 D.b, algebraMap ℚ K21 D.c] i) := by rw [map_mul]
    _ = σ t0 * σ (algebraMap ℚ K21 (![D.a, D.b, D.c] i)) := by
      fin_cases i <;> simp
    _ = σ t0 * algebraMap ℚ_[2] Kv ((![D.a, D.b, D.c] i : ℚ) : ℚ_[2]) := by rw [σ_algebraMap]
    _ = σ t0 * algebraMap ℚ_[2] Kv ((D.μ)⁻¹ * ((discPt D.d D.X D.Y i : ℤ_[2]) : ℚ_[2])) := by rw [h_coord]
    _ = σ t0 * ((algebraMap ℚ_[2] Kv D.μ)⁻¹ * algebraMap ℚ_[2] Kv (((discPt D.d D.X D.Y i : ℤ_[2]) : ℚ_[2]))) := by
      simp [map_mul, map_inv₀]
    _ = σ t0 * (algebraMap ℚ_[2] Kv D.μ)⁻¹ * algebraMap ℚ_[2] Kv (((discPt D.d D.X D.Y i : ℤ_[2]) : ℚ_[2])) := by ring
    _ = σ t0 * (algebraMap ℚ_[2] Kv D.μ)⁻¹ * toKv (discPt D.d D.X D.Y i) := rfl
    _ = σ t0 * (algebraMap ℚ_[2] Kv D.μ)⁻¹ * toKv (discPt D.d D.X (discY D.d D.X) i) := by rw [discY_eq]
    _ = σ t0 * (algebraMap ℚ_[2] Kv D.μ)⁻¹ * pKv D.d D.X i := rfl
    _ = (a • pKv D.d D.X) i := by rw [ha_def, Pi.smul_apply, smul_eq_mul]

theorem lamPt_smul (k : Fin 2) (a : Kv) (ha : a ≠ 0) (y : DPtKv k) :
    lamPt k (smulPt a ha y) = lamPt k y := by
  unfold lamPt phiV
  rw [phiRev_smul]

/-- **`lamD` at a lift**: `± log φ(x) - log φ(x_a)`. -/
theorem lamD_lift (k : Fin 2) (hcov : BranchCover k)
    (x : FurioLombardo.M3a.Route.Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    lamD k (liftDisc x) (liftPar x) =
        logPhi σ (fRev k) (phiK k) (lam k) x.1 - logPhi σ (fRev k) (phiK k) (lam k) (xa k) ∨
      lamD k (liftDisc x) (liftPar x) =
        -logPhi σ (fRev k) (phiK k) (lam k) x.1 - logPhi σ (fRev k) (phiK k) (lam k) (xa k) := by
  obtain ⟨hd, htw⟩ := liftTwist_Mmat (δ k) x
  obtain ⟨e, he, y, hyp, hyb⟩ := hcov (liftDisc x) hd (liftPar x) htw
  obtain ⟨a, ha, hpa⟩ := exists_smul_pKv k x
  let y' := smulPt a⁻¹ (inv_ne_zero ha) (mapPt σ x.1)
  have hy'p : y'.p = pKv (liftDisc x) (liftPar x) := by
    dsimp [y', smulPt]
    rw [hpa]
    calc
      a⁻¹ • (a • pKv (liftDisc x) (liftPar x)) = (a⁻¹ * a) • pKv (liftDisc x) (liftPar x) := by
        rw [smul_smul]
      _ = 1 • pKv (liftDisc x) (liftPar x) := by
        field_simp [ha]
        simp
      _ = pKv (liftDisc x) (liftPar x) := by rw [one_smul]
  rcases eq_or_eq_neg_of_p_eq (σδ_ne_zero k) FurioLombardo.Discharge.M3a.Bruin.two_ne_zero_Kv y y' (by
    rw [hyp, hy'p]) with (⟨hr, hs⟩ | ⟨hr, hs⟩)
  · -- case y = y'
    left
    have hy_eq_y' : y = y' := DPoint.ext' (by rw [hyp, hy'p]) hr hs
    rw [lamD_eq he y hyp hyb, hy_eq_y']
    dsimp [y']
    rw [lamPt_smul k a⁻¹ (inv_ne_zero ha) (mapPt σ x.1)]
    rw [lamPt_mapPt k x.1]
  · -- case y = y'.inv
    right
    have hy_eq_inv_p : y.p = y'.inv.p :=
      calc
        y.p = pKv (liftDisc x) (liftPar x) := hyp
        _ = y'.p := hy'p.symm
        _ = y'.inv.p := by
          dsimp [y', DPoint.inv]
    have hy_eq_y_inv : y = y'.inv := DPoint.ext' hy_eq_inv_p hr hs
    rw [lamD_eq he y hyp hyb, hy_eq_y_inv]
    have h_inv_smul : y'.inv = smulPt a⁻¹ (inv_ne_zero ha) (mapPt σ x.1).inv := by
      dsimp [y']
      apply DPoint.ext'
      · rfl
      · simp [smulPt, DPoint.inv]
      · simp [smulPt, DPoint.inv]
    rw [h_inv_smul]
    rw [lamPt_smul k a⁻¹ (inv_ne_zero ha) (mapPt σ x.1).inv]
    rw [lamPt_mapPt_inv k x.1]

theorem liftLog_eq (k : Fin 2) (x : FurioLombardo.M3a.Route.Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    liftLog σ (fRev k) (phiK k) (xa k) (lam k) x =
      logPhi σ (fRev k) (phiK k) (lam k) x.1 - logPhi σ (fRev k) (phiK k) (lam k) (xa k) := by
  unfold liftLog
  rw [map_div (jacMap σ (fRev k)), ofMul_div, map_sub (lam k)]

/-- **`hLog` from the branch cover**, given `log φ(x_a) ∈ Λ`. -/
theorem hLog_of_cover (k : Fin 2) (hcov : BranchCover k) {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])}
    (b : Fin 6 → ℤ_[2]) (ha : logPhi σ (fRev k) (phiK k) (lam k) (xa k) ∈ Λ) :
    LogBranch (liftLog σ (fRev k) (phiK k) (xa k) (lam k))
      (satOf Λ (logPhi σ (fRev k) (phiK k) (lam k) (xa k)) b) (lamD k) liftDisc liftPar := by
  have hA := left_mem_satOf b ha
  intro x
  rw [liftLog_eq]
  rcases lamD_lift k hcov x with h | h
  · left
    rw [h, sub_self]
    exact Submodule.zero_mem _
  · right
    rw [h, show ∀ u v : Fin 6 → ℤ_[2], u - v + (-u - v) = -v - v by intro u v; abel]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ hA) hA

end FurioLombardo.Discharge.M4Box
