import Mathlib
import FurioLombardo.Discharge.M4Box.BoxTM

/-!
# The per box statements from a box run (lane lean-m4box, D9)

A successful `boxRun` (M4Box/Comp/BoxTM.lean) of a box `{c + 2^s Y}` is read through three carriers
(M4Box/BoxTM.lean): the computation on `tmOpsF`, the run on `PC` (truncated series with fixed
coefficients times functions on `boxH s`) that it encloses (`rel_tmOpsF`), and the run on `K_v` at each
`h ∈ boxH s` that the functions give (`rel_evalAt`). Stage by stage:

* `boxRunP_sound`: the point `p(h) = pKv d (c + h)`, the radicand and `Q2/δ` at `p(h)`;
* `boxLift_sound`: the square root `y(h)` on the branch (`EnclC.sqrt`, `nearOK`), the point `x(h)` of
  `D_δ(K_v)` over `p(h)` (`ptR`, `ptS`) and the pair of `φ_v(x(h))` (`boxPhi_field`, `phiV_eq_cls`);
* `boxEncl`: the pair `R` of `E0 - φ_v(x(0))` (a ball run on the constant coefficients) and the sum
  `Q(h) = φ_v(x(h)) + R`, of class `φ_v(x(h)) - φ_v(x(0)) + E0`, translated by `a = k`, with `Amat t`.

`constCert_of_run` and `tailCert_of_run` read the checks `constOK`, `tailOK` in the chart
(`chart_of_pair`) and give `ConstCert`, `TailCert`.
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith
open FurioLombardo.Discharge.M3a.Bruin (fRev Mmat δ dL)

namespace FurioLombardo.Discharge.M4Box

/-! ## Leaves -/

theorem ofKv_zero : ofKv 0 = 0 := by
  simpa [map_zero] using ofKv_toKv (0 : ℤ_[2])

/-- Every box of the branch tables has `e = 0`. -/
theorem branchTable_e {kk : Fin 2} {e : BranchBox} (he : e ∈ branchTable kk) : e.e = 0 := by
  fin_cases kk <;> revert e <;> decide

theorem Sym3.rel_cmap_self {A B : Type*} {R : A → B → Prop} {f : A → B} (hf : ∀ x, R x (f x))
    (m : Sym3 A) : Sym3.Rel R m (m.cmap f) := by
  simp only [Sym3.Rel, Sym3.cmap]
  exact ⟨hf m.a00, hf m.a01, hf m.a02, hf m.a11, hf m.a12, hf m.a22⟩

theorem Mum.rel_cmap_self {A B : Type*} {R : A → B → Prop} {f : A → B} (hf : ∀ x, R x (f x))
    (m : Mum A) : Mum.Rel R m (m.cmap f) := by
  exact ⟨hf _, hf _, hf _, hf _⟩

theorem Sext.rel_cmap_self {A B : Type*} {R : A → B → Prop} {f : A → B} (hf : ∀ x, R x (f x))
    (m : Sext A) : Sext.Rel R m (m.cmap f) := by
  simp only [Sext.Rel, Sext.cmap]
  exact ⟨hf _, hf _, hf _, hf _, hf _, hf _, hf _⟩

theorem Ops.Rel.mumNeg {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop} (h : Ops.Rel o p R)
    {D : Mum A} {D' : Mum B} (hD : Mum.Rel R D D') : Mum.Rel R (Mum.neg o D) (Mum.neg p D') := by
  obtain ⟨h0, h1, h2, h3⟩ := hD
  exact ⟨h0, h1, h.neg h2, h.neg h3⟩

/-- The pair `(u, -v)` is on the curve, of the inverse class. -/
theorem Mum.neg_field_spec {K : Type*} [Field K] (fp : K[X]) [GoodSextic fp] {D : Mum K}
    (hD : D.OnCurve fp) :
    (Mum.neg (fieldOps K) D).OnCurve fp ∧ (Mum.neg (fieldOps K) D).cls fp = (D.cls fp)⁻¹ := by
  have h_neg_u : (Mum.neg (fieldOps K) D).u = D.u := by
    simp [Mum.neg, Mum.u, fieldOps]
  have h_neg_v : (Mum.neg (fieldOps K) D).v = -D.v := by
    simp [Mum.neg, Mum.v, fieldOps]
    ring
  have h_neg_v_sq : (-D.v) ^ 2 = D.v ^ 2 := by
    simp
  have hD' : D.u ∣ D.v ^ 2 - fp := by
    have : D.v ^ 2 - fp = -(fp - D.v ^ 2) := by ring
    rw [this]
    exact dvd_neg.mpr hD
  have h_on_curve : (Mum.neg (fieldOps K) D).OnCurve fp := by
    rw [Mum.OnCurve]
    rw [h_neg_u, h_neg_v, h_neg_v_sq]
    exact hD
  have h_cls : (Mum.neg (fieldOps K) D).cls fp = (D.cls fp)⁻¹ := by
    rw [Mum.cls]
    rw [mk0_mumford_eq (Mum.neg (fieldOps K) D).u_monic.ne_zero D.u_monic.ne_zero h_neg_u h_neg_v]
    rw [Mum.cls]
    rw [mk0_mumford_neg_of_dvd fp D.u_monic.ne_zero hD']
  exact And.intro h_on_curve h_cls

/-- The first two coefficients of a Horner sum. -/
theorem horner_take_two (cs : List Kv) (h : Kv) :
    (fieldOps Kv).horner (cs.take 2) h = cs.getD 0 0 + h * cs.getD 1 0 := by
  rcases cs with (_ | ⟨a, (_ | ⟨b, cs⟩)⟩)
  · simp [fieldOps_horner_nil]
  · simp [fieldOps_horner_cons, fieldOps_horner_nil]
  · simp [fieldOps_horner_cons, fieldOps_horner_nil]

theorem forall₂_getD_mem {k : Ctx} (hk : k.Ok) {cs : List Kv} {bs : List Ball}
    (h : List.Forall₂ (fun x b => Ball.Mem b x) cs bs) (i : ℕ) :
    (bs.getD i (Ball.ofInt k 0)).Mem (cs.getD i 0) := by
  induction h generalizing i with
  | nil =>
      simpa using Ball.mem_ofInt hk 0
  | cons hab h ih =>
      cases i with
      | zero => simpa using hab
      | succ i => simpa [List.getD_cons_succ] using ih i

/-- `Amat` is integral: a bound on `S` bounds `Amat S`. -/
theorem norm_Amat_mulVec_le (kk : Fin 2) {S : Fin 2 → Kv} {a : ℕ} (hS : ∀ i, ‖S i‖ ≤ ‖pv‖ ^ a)
    (i : Fin 2) : ‖(Amat kk *ᵥ S) i‖ ≤ ‖pv‖ ^ a := by
  have h_expand : (Amat kk *ᵥ S) i = (Amat kk i 0) * (S 0) + (Amat kk i 1) * (S 1) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h_expand]
  have h0 : ‖(Amat kk i 0) * (S 0)‖ ≤ ‖pv‖ ^ a := by
    calc
      ‖(Amat kk i 0) * (S 0)‖ ≤ ‖Amat kk i 0‖ * ‖S 0‖ := norm_mul_le _ _
      _ ≤ ‖S 0‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_Amat_le_one kk i 0)
      _ ≤ ‖pv‖ ^ a := hS 0
  have h1 : ‖(Amat kk i 1) * (S 1)‖ ≤ ‖pv‖ ^ a := by
    calc
      ‖(Amat kk i 1) * (S 1)‖ ≤ ‖Amat kk i 1‖ * ‖S 1‖ := norm_mul_le _ _
      _ ≤ ‖S 1‖ := mul_le_of_le_one_left (norm_nonneg _) (norm_Amat_le_one kk i 1)
      _ ≤ ‖pv‖ ^ a := hS 1
  calc
    ‖(Amat kk i 0) * (S 0) + (Amat kk i 1) * (S 1)‖ ≤
      max ‖(Amat kk i 0) * (S 0)‖ ‖(Amat kk i 1) * (S 1)‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max (‖pv‖ ^ a) (‖pv‖ ^ a) := max_le_max h0 h1
    _ = ‖pv‖ ^ a := by simp

/-- The ball of the tail check holds `2 (Amat c1)_j - g_j`. -/
theorem mem_tailG {kk : Fin 2} {T : TCtx} (hk : T.k.Ok) {Am : Mat2 Ball}
    (hA : Am.a00.Mem (Amat kk 0 0) ∧ Am.a01.Mem (Amat kk 0 1) ∧ Am.a10.Mem (Amat kk 1 0) ∧
      Am.a11.Mem (Amat kk 1 1))
    {Z : Mum TM} {c1 : Fin 2 → Kv} (h0 : (Z.u1.cs.getD 1 (TM.zeroB T)).Mem (c1 0))
    (h1 : (Z.u0.cs.getD 1 (TM.zeroB T)).Mem (c1 1)) (gl : Fin 6 → ℤ) (j : Fin 2) :
    (tailG T Am Z gl j).Mem (2 * (Amat kk *ᵥ c1) j - toKv2 (FurioLombardo.M4.icast gl) j) := by
  rcases hA with ⟨hA00, hA01, hA10, hA11⟩
  fin_cases j
  · -- j = 0
    simp only [tailG, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    refine Ball.mem_sub hk ?_ ?_
    · refine Ball.mem_mul hk ?_ ?_
      · simpa using Ball.mem_ofInt hk (2 : ℤ)
      · refine Ball.mem_add hk ?_ ?_
        · refine Ball.mem_mul hk hA00 h0
        · refine Ball.mem_mul hk hA01 h1
    · simpa [toKv2_icast gl 0] using Ball.mem_ofApprox hk (approx_evZ (lTriple gl 0) (T.k).P)
  · -- j = 1
    simp only [tailG, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    refine Ball.mem_sub hk ?_ ?_
    · refine Ball.mem_mul hk ?_ ?_
      · simpa using Ball.mem_ofInt hk (2 : ℤ)
      · refine Ball.mem_add hk ?_ ?_
        · refine Ball.mem_mul hk hA10 h0
        · refine Ball.mem_mul hk hA11 h1
    · simpa [toKv2_icast gl 1] using Ball.mem_ofApprox hk (approx_evZ (lTriple gl 1) (T.k).P)

/-! ## The first stage: the point, the radicand, `Q2/δ` -/

/-- The point over the box at `h`. -/
noncomputable def boxPt (B : BoxSpec) (h : Kv) : Fin 3 → Kv := pKv B.d ((B.c : ℤ_[2]) + ofKv h)

/-- **The first stage over the box**: the Taylor models of `boxRunP` enclose the point `p(h)`, the
radicand `Q1/δ` (or `Q3/δ`) and `Q2/δ` at `p(h)`. -/
theorem boxRunP_sound (kk : Fin 2) {k : Ctx} (hk : k.Ok) (n : ℕ) {B : BoxSpec} (hkk : B.kk = kk)
    (hd : IsDisc B.d) (hY : (2 : ℤ) ^ B.N ∣ G1 B.d B.c B.Y0) {P : (TM × TM × TM) × TM × TM}
    (hP : boxRunP (B.ctx k n) B = some P) :
    EnclF (B.ctx k n) (boxH B.s) P.1.1 (fun h => boxPt B h 0) ∧
      EnclF (B.ctx k n) (boxH B.s) P.1.2.1 (fun h => boxPt B h 1) ∧
      EnclF (B.ctx k n) (boxH B.s) P.1.2.2 (fun h => boxPt B h 2) ∧
      EnclF (B.ctx k n) (boxH B.s) P.2.1 (fun h =>
        (if B.e.wh then boxPt B h ⬝ᵥ ((Mmat 0).map σ *ᵥ boxPt B h)
          else boxPt B h ⬝ᵥ ((Mmat 2).map σ *ᵥ boxPt B h)) * (σ (δ kk))⁻¹) ∧
      EnclF (B.ctx k n) (boxH B.s) P.2.2 (fun h =>
        boxPt B h ⬝ᵥ ((Mmat 1).map σ *ᵥ boxPt B h) * (σ (δ kk))⁻¹) := by
  set T := B.ctx k n with hT
  set H := boxH B.s with hHdef
  have hkT : T.k.Ok := hk
  have hH : T.Dom H := boxH_dom k B n
  unfold boxRunP at hP
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hP
  obtain ⟨m0, hm0, m1, hm1, m2, hm2, dl, hdl, idl, hidl, Yt, hYt, rfl⟩ := hP
  rw [hkk] at hdl
  have hdl' := mem_dl hk kk hdl
  obtain ⟨-, hidl'⟩ := mem_inv_of hk hdl' hidl
  have hc := boxU_centre hk hd hY
  obtain ⟨csU, hU⟩ := EnclC.root (T := T) (H := H) hkT hH (Ball.mem_ofInt hk B.c)
    (by have := Ball.mem_ofInt hk 1; rw [Int.cast_one] at this; exact this) hc.2 hc.1 (boxU_spec hk hd hY B.s) hYt
  have hU' := EnclC.fresh hkT hU
  have r := rel_tmOpsF (T := T) hkT hH
  have hX := r.add (x := cstPC ((B.c : ℤ) : Kv)) (y := (([0, 1] : List Kv), (id : Kv → Kv)))
    (EnclC.cstPC (T := T) (H := H) hkT (Ball.mem_ofInt hk B.c)) (EnclC.var (H := H) hkT)
  have hM0 := Sym3.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2) (fun hx => EnclC.cstPC hkT hx)
    (mem_mBall hk 0 hm0)
  have hM1 := Sym3.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2) (fun hx => EnclC.cstPC hkT hx)
    (mem_mBall hk 1 hm1)
  have hM2 := Sym3.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2) (fun hx => EnclC.cstPC hkT hx)
    (mem_mBall hk 2 hm2)
  obtain ⟨hw, hq, hr⟩ := rel_boxP r B.d B.e.wh hM0 hM1 hM2 (idl := cstPC (σ (δ kk))⁻¹)
    (Y := (csU, boxU B.d B.c)) (EnclC.cstPC hkT hidl') hX hU'
  -- the functions at a point of the box
  have key : ∀ h ∈ H, _ := fun h hh =>
    rel_boxP (rel_evalAt (T := T) hh) B.d B.e.wh
      (m0 := Sym3.ofMatrix ((Mmat 0).map σ)) (m1 := Sym3.ofMatrix ((Mmat 1).map σ))
      (m2 := Sym3.ofMatrix ((Mmat 2).map σ))
      (Sym3.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
        (fun _ => rfl) _)
      (Sym3.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
        (fun _ => rfl) _)
      (Sym3.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
        (fun _ => rfl) _)
      (idl := (σ (δ kk))⁻¹) (X := ((B.c : ℤ) : Kv) + h) (Y := boxU B.d B.c h)
      (idl' := cstPC (σ (δ kk))⁻¹) (X' := (PC T H).add (cstPC ((B.c : ℤ) : Kv)) (([0, 1] : List Kv), (id : Kv → Kv)))
      (Y' := (csU, boxU B.d B.c)) rfl rfl rfl
  have hval : ∀ h ∈ H, boxP (fieldOps Kv) B.d B.e.wh (Sym3.ofMatrix ((Mmat 0).map σ))
      (Sym3.ofMatrix ((Mmat 1).map σ)) (Sym3.ofMatrix ((Mmat 2).map σ)) (σ (δ kk))⁻¹
      (((B.c : ℤ) : Kv) + h) (boxU B.d B.c h) =
      ((boxPt B h 0, boxPt B h 1, boxPt B h 2),
        (if B.e.wh then boxPt B h ⬝ᵥ ((Mmat 0).map σ *ᵥ boxPt B h)
          else boxPt B h ⬝ᵥ ((Mmat 2).map σ *ᵥ boxPt B h)) * (σ (δ kk))⁻¹,
        boxPt B h ⬝ᵥ ((Mmat 1).map σ *ᵥ boxPt B h) * (σ (δ kk))⁻¹) := by
    intro h hh
    have e : discPt B.d (((B.c : ℤ) : Kv) + h) (boxU B.d B.c h) = boxPt B h := by
      funext i; exact discPt_boxU hh i
    rw [boxP_field kk, e]
  have kv : ∀ h ∈ H, _ := fun h hh => by
    have := key h hh
    rw [hval h hh] at this
    exact this
  refine ⟨⟨_, EnclC.congr hw.1 fun h hh => (kv h hh).1.1⟩, ⟨_, EnclC.congr hw.2.1 fun h hh => (kv h hh).1.2.1⟩,
    ⟨_, EnclC.congr hw.2.2 fun h hh => (kv h hh).1.2.2⟩, ⟨_, EnclC.congr hq fun h hh => (kv h hh).2.1⟩,
    ⟨_, EnclC.congr hr fun h hh => (kv h hh).2.2⟩⟩

/-! ## The second stage: the lift and its pair -/

/-- **The second stage over the box**: the pair of `φ_v(x(h))`, `x(h)` the point over `p(h)` on the
branch, is enclosed. -/
theorem boxLift_sound (kk : Fin 2) {k : Ctx} (hk : k.Ok) (n : ℕ) {B : BoxSpec} (hkk : B.kk = kk)
    (hd : IsDisc B.d) (he0 : B.e.e = 0) (hY : (2 : ℤ) ^ B.N ∣ G1 B.d B.c B.Y0)
    {P : (TM × TM × TM) × TM × TM} (hP : boxRunP (B.ctx k n) B = some P) {yr : TM × Ball}
    (hyr : TM.sqrt (B.ctx k n) P.2.1 B.sR B.eR = some yr)
    (hnear : Ball.nearOK k yr.2 (Ball.ofApprox k B.e.rho k.P) = true)
    {m0 m1 m2 : Sym3 Ball} (hm0 : mBall k 0 = some m0) (hm1 : mBall k 1 = some m1)
    (hm2 : mBall k 2 = some m2) {dl : Ball} (hdl : sigQ k (dL B.kk) 1 = some dl) {m : Mum TM}
    (hm : boxPhi (tmOpsF (B.ctx k n)) B.e.wh B.prm (m0.cmap (TM.cst (B.ctx k n)))
      (m1.cmap (TM.cst (B.ctx k n))) (m2.cmap (TM.cst (B.ctx k n))) (TM.cst (B.ctx k n) dl) P.1 P.2.2
      (TM.fresh (B.ctx k n) yr.1) = some m) :
    ∃ mc : Mum (List Kv × (Kv → Kv)),
      Mum.Rel (fun cF M => EnclC (B.ctx k n) (boxH B.s) M cF.1 cF.2) mc m ∧
      ∀ h ∈ boxH B.s, ∃ x : DPtKv kk, x.p = boxPt B h ∧ BranchOK B.e x ∧
        (mc.cmap fun cF => cF.2 h).OnCurve ((fRev kk).map σ) ∧
        (mc.cmap fun cF => cF.2 h).cls ((fRev kk).map σ) =
          ((phiV kk x : Jac ((fRev kk).map σ)) : Pic ((fRev kk).map σ)) := by
  set T := B.ctx k n with hT
  set H := boxH B.s with hHdef
  have hkT : T.k.Ok := hk
  have hH : T.Dom H := boxH_dom k B n
  obtain ⟨⟨cw0, hw0⟩, ⟨cw1, hw1⟩, ⟨cw2, hw2⟩, ⟨cA, hA⟩, ⟨cq, hq⟩⟩ := boxRunP_sound kk hk n hkk hd hY hP
  obtain ⟨hex, ps, hps⟩ := EnclC.sqrt hkT hH hA hyr
  classical
  let r : Kv → Kv := fun h => if hh : h ∈ H then (hex h hh).choose else 0
  have hr : ∀ h ∈ H, r h ^ 2 = _ ∧ yr.2.Mem (r h) := fun h hh => by
    simp only [r, hh, dite_true]
    exact (hex h hh).choose_spec
  have hy := EnclC.fresh hkT (hps r hr)
  rw [hkk] at hdl
  have hdl' := mem_dl hk kk hdl
  have rT := rel_tmOpsF (T := T) hkT hH
  have hM0 := Sym3.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2)
    (fun hx => EnclC.cstPC hkT hx) (mem_mBall hk 0 hm0)
  have hM1 := Sym3.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2)
    (fun hx => EnclC.cstPC hkT hx) (mem_mBall hk 1 hm1)
  have hM2 := Sym3.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2)
    (fun hx => EnclC.cstPC hkT hx) (mem_mBall hk 2 hm2)
  obtain ⟨mc, hmc, hmcm⟩ := rel_boxPhi rT B.e.wh B.prm hM0 hM1 hM2 (dl := cstPC (σ (δ kk)))
    (EnclC.cstPC hkT hdl') (w := ((cw0, fun h => boxPt B h 0), (cw1, fun h => boxPt B h 1),
      (cw2, fun h => boxPt B h 2))) ⟨hw0, hw1, hw2⟩ (q := (cq, _)) hq (y := (ps, r)) hy m hm
  refine ⟨mc, hmcm, fun h hh => ?_⟩
  obtain ⟨mh, hmh, hmhc⟩ := rel_boxPhi (rel_evalAt (T := T) hh) B.e.wh B.prm
      (m0 := Sym3.ofMatrix ((Mmat 0).map σ)) (m1 := Sym3.ofMatrix ((Mmat 1).map σ))
      (m2 := Sym3.ofMatrix ((Mmat 2).map σ))
      (Sym3.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
        (fun _ => rfl) _)
      (Sym3.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
        (fun _ => rfl) _)
      (Sym3.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
        (fun _ => rfl) _)
      (dl := σ (δ kk)) (dl' := cstPC (σ (δ kk))) rfl
      (w := (boxPt B h 0, boxPt B h 1, boxPt B h 2)) (w' := ((cw0, fun h => boxPt B h 0),
        (cw1, fun h => boxPt B h 1), (cw2, fun h => boxPt B h 2))) ⟨rfl, rfl, rfl⟩
      (q := boxPt B h ⬝ᵥ ((Mmat 1).map σ *ᵥ boxPt B h) * (σ (δ kk))⁻¹) (q' := (cq, _)) rfl
      (y := r h) (y' := (ps, r)) rfl mc hmc
  have hcm : (mc.cmap fun cF => cF.2 h) = mh := by
    obtain ⟨e0, e1, e2, e3⟩ := hmhc
    cases mh
    simp only [Mum.cmap, e0, e1, e2, e3]
  rw [hcm]
  obtain ⟨hy0, hap⟩ := boxPhi_field hmh
  have hp : boxPt B h ≠ 0 := pKv_ne_zero hd ((B.c : ℤ_[2]) + ofKv h)
  have hF : FurioLombardo.F (boxPt B h 0) (boxPt B h 1) (boxPt B h 2) = 0 :=
    F_pKv hd ((B.c : ℤ_[2]) + ofKv h)
  have hrho := mem_rho hk (k := k) he0
  obtain ⟨hr2, hrm⟩ := hr h hh
  have hlt := norm_sub_lt_add_of_lt (Ball.norm_sub_lt_of_nearOK hk hrm hrho hnear)
  by_cases hwh : B.e.wh = true
  · simp only [hwh, ite_true] at hr2 hap
    refine ⟨ptR kk hp hF hy0 hr2, rfl, ?_, ?_⟩
    · simp only [BranchOK, hwh, ite_true]
      exact hlt
    · rw [← apInV_ptR kk hp hF hy0 hr2] at hap
      exact phiV_eq_cls kk _ hap
  · simp only [hwh, Bool.false_eq_true, ite_false] at hr2 hap
    refine ⟨ptS kk hp hF hy0 hr2, rfl, ?_, ?_⟩
    · simp only [BranchOK, hwh, Bool.false_eq_true, ite_false]
      exact hlt
    · rw [← apInV_ptS kk hp hF hy0 hr2] at hap
      exact phiV_eq_cls kk _ hap

/-! ## The third stage: the sum and the chart coordinates -/

/-- **The run over the box**: the Taylor models of `boxRun` enclose the translated pair `Q(h)` of class
`φ_v(x(h)) - φ_v(x(0)) + E0` and `Amat` of its chart coordinates. -/
theorem boxEncl (kk : Fin 2) {k : Ctx} (hk : k.Ok) (n : ℕ) {B : BoxSpec} (hkk : B.kk = kk)
    (hd : IsDisc B.d) (he0 : B.e.e = 0) (hY : (2 : ℤ) ^ B.N ∣ G1 B.d B.c B.Y0)
    {g : Sext Ball} {E : Mum Ball} {Am : Mat2 Ball}
    (hg : Sext.Rel (fun x b => b.Mem x) (Sext.ofPoly ((fRev kk).map σ)) g)
    (hE : Mum.Rel (fun x b => b.Mem x) (E0Mum kk) E)
    (hA : Am.a00.Mem (Amat kk 0 0) ∧ Am.a01.Mem (Amat kk 0 1) ∧ Am.a10.Mem (Amat kk 1 0) ∧
      Am.a11.Mem (Amat kk 1 1))
    {out : Mum TM × TM × TM} (hrun : boxRun (B.ctx k n) g E Am B = some out) :
    ∃ (Zc : Mum (List Kv × (Kv → Kv))) (A0 A1 : List Kv × (Kv → Kv)),
      Mum.Rel (fun cF M => EnclC (B.ctx k n) (boxH B.s) M cF.1 cF.2) Zc out.1 ∧
      EnclC (B.ctx k n) (boxH B.s) out.2.1 A0.1 A0.2 ∧ EnclC (B.ctx k n) (boxH B.s) out.2.2 A1.1 A1.2 ∧
      ∃ x0 : DPtKv kk, x0.p = boxPt B 0 ∧ BranchOK B.e x0 ∧
      ∀ h ∈ boxH B.s, ∃ x : DPtKv kk, x.p = boxPt B h ∧ BranchOK B.e x ∧
        ∃ Q : Mum Kv, Q.OnCurve ((fRev kk).map σ) ∧
          Q.cls ((fRev kk).map σ) = ((phiV kk x : Jac ((fRev kk).map σ)) : Pic ((fRev kk).map σ)) *
            ((phiV kk x0 : Jac ((fRev kk).map σ)) : Pic ((fRev kk).map σ))⁻¹ *
              (E0Mum kk).cls ((fRev kk).map σ) ∧
          Mum.shift (fieldOps Kv) (aK kk) Q = Zc.cmap (fun cF => cF.2 h) ∧
          A0.2 h = Amat kk 0 0 * Zc.u1.2 h + Amat kk 0 1 * Zc.u0.2 h ∧
          A1.2 h = Amat kk 1 0 * Zc.u1.2 h + Amat kk 1 1 * Zc.u0.2 h := by
  set T := B.ctx k n with hT
  set H := boxH B.s with hHdef
  have hkT : T.k.Ok := hk
  have hH : T.Dom H := boxH_dom k B n
  have h0H : (0 : Kv) ∈ H := zero_mem_boxH B.s
  unfold boxRun at hrun
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨m0, hm0, m1, hm1, m2, hm2, dl, hdl, P, hP, yr, hyr, hrun⟩ := hrun
  split_ifs at hrun with hnear
  simp only [Option.bind_eq_some_iff] at hrun
  obtain ⟨m, hm, R, hR, hrun⟩ := hrun
  obtain ⟨mc, hmcm, hlift⟩ := boxLift_sound kk hk n hkk hd he0 hY hP hyr hnear hm0 hm1 hm2 hdl hm
  obtain ⟨x0, hx0p, hx0b, hon0, hcls0⟩ := hlift 0 h0H
  -- the pair `R` of `E0 - φ_v(x(0))`
  have hhead : Mum.Rel (fun x b => b.Mem x) (mc.cmap fun cF => cF.2 0)
      (m.cmap fun M => M.cs.headD (TM.zeroB T)) := by
    obtain ⟨e0, e1, e2, e3⟩ := hmcm
    exact ⟨EnclC.mem_headD hkT e0 h0H, EnclC.mem_headD hkT e1 h0H, EnclC.mem_headD hkT e2 h0H,
      EnclC.mem_headD hkT e3 h0H⟩
  obtain ⟨Rx, hRx, hRxR⟩ := Ops.Rel.cantorAdd (rel_ballOpsF hk) hg hE
    (Ops.Rel.mumNeg (rel_ballOpsF hk) hhead) R hR
  obtain ⟨hnon, hncls⟩ := Mum.neg_field_spec ((fRev kk).map σ) hon0
  obtain ⟨hRon, hRcls⟩ := cantorAdd_spec ((fRev kk).map σ) (E0Mum_onCurve kk) hnon hRx
  -- the sum on `PC`
  have rT := rel_tmOpsF (T := T) hkT hH
  have hgc := Sext.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2)
    (fun hx => EnclC.cstPC hkT hx) hg
  have hRc := Mum.rel_cmap (S := fun (cF : List Kv × (Kv → Kv)) M => EnclC T H M cF.1 cF.2)
    (fun hx => EnclC.cstPC hkT hx) hRxR
  obtain ⟨oc, hoc, hocR⟩ := rel_boxChart rT hgc (a := (PC T H).ofInt B.kk) (rT.ofInt B.kk)
    (Am := Mat2.cmap cstPC ⟨Amat kk 0 0, Amat kk 0 1, Amat kk 1 0, Amat kk 1 1⟩)
    ⟨EnclC.cstPC hkT hA.1, EnclC.cstPC hkT hA.2.1, EnclC.cstPC hkT hA.2.2.1,
      EnclC.cstPC hkT hA.2.2.2⟩ hmcm hRc out hrun
  obtain ⟨hZ, hA0, hA1⟩ := hocR
  refine ⟨oc.1, oc.2.1, oc.2.2, hZ, hA0, hA1, x0, hx0p, hx0b, fun h hh => ?_⟩
  obtain ⟨x, hxp, hxb, hon, hcls⟩ := hlift h hh
  refine ⟨x, hxp, hxb, ?_⟩
  obtain ⟨oh, hoh, hohc⟩ := rel_boxChart (rel_evalAt (T := T) hh)
    (f := Sext.ofPoly ((fRev kk).map σ))
    (Sext.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
      (fun _ => rfl) _)
    ((rel_evalAt (T := T) hh).ofInt B.kk)
    (Am := ⟨Amat kk 0 0, Amat kk 0 1, Amat kk 1 0, Amat kk 1 1⟩) ⟨rfl, rfl, rfl, rfl⟩
    (m := mc.cmap fun cF => cF.2 h) ⟨rfl, rfl, rfl, rfl⟩
    (Mum.rel_cmap_self (R := fun x (cF : List Kv × (Kv → Kv)) => cF.2 h = x) (f := cstPC)
      (fun _ => rfl) Rx) oc hoc
  obtain ⟨Q, hQ, hsh, ha0, ha1⟩ := boxChart_field hoh
  obtain ⟨hQon, hQcls⟩ := cantorAdd_spec ((fRev kk).map σ) hon hRon hQ
  have ha : (fieldOps Kv).ofInt (B.kk : ℤ) = aK kk := by
    simp [fieldOps, aK, hkk]
  obtain ⟨⟨z0, z1, z2, z3⟩, e1, e2⟩ := hohc
  refine ⟨Q, hQon, ?_, ?_, ?_, ?_⟩
  · rw [← hQcls, hcls, ← hRcls, hncls, hcls0, ← mul_assoc, mul_right_comm]
  · rw [← ha, ← hsh]
    cases oh with
    | mk Z rest =>
      cases Z
      simp only [Mum.cmap] at z0 z1 z2 z3 ⊢
      rw [z0, z1, z2, z3]
  · rw [e1, ha0, z1, z0]
  · rw [e2, ha1, z1, z0]

/-! ## The per box statements -/

theorem Amat_mulVec_vec2 (kk : Fin 2) (a b : Kv) :
    (Amat kk *ᵥ ![a, b]) 0 = Amat kk 0 0 * a + Amat kk 0 1 * b ∧
      (Amat kk *ᵥ ![a, b]) 1 = Amat kk 1 0 * a + Amat kk 1 1 * b := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **`ConstCert` from a box run** and its check. -/
theorem constCert_of_run (kk : Fin 2) {c : FurioLombardo.M4.CBox} {e : BranchBox}
    (he : e ∈ branchTable kk) (hed : e.disc = c.disc) (hec : e.c = c.c) (hes : e.s = c.s)
    {k : Ctx} (hk : k.Ok) (n : ℕ) {B : BoxSpec} (hkk : B.kk = kk) (hBd : B.d = c.disc)
    (hBc : B.c = (c.c : ℤ)) (hBs : B.s = c.s) (hBe : B.e = e) (hd : IsDisc c.disc)
    (hY : (2 : ℤ) ^ B.N ∣ G1 B.d B.c B.Y0)
    {g : Sext Ball} {E : Mum Ball} {Am : Mat2 Ball}
    (hg : Sext.Rel (fun x b => b.Mem x) (Sext.ofPoly ((fRev kk).map σ)) g)
    (hE : Mum.Rel (fun x b => b.Mem x) (E0Mum kk) E)
    (hA : Am.a00.Mem (Amat kk 0 0) ∧ Am.a01.Mem (Amat kk 0 1) ∧ Am.a10.Mem (Amat kk 1 0) ∧
      Am.a11.Mem (Amat kk 1 1))
    {b : Ball} (hb : b.Mem (bK kk)) {out : Mum TM × TM × TM}
    (hrun : boxRun (B.ctx k n) g E Am B = some out) {D : ℕ}
    (hD2 : 3 * (c.vM / 3 + c.s) + M0 kk + 3 ≤ 2 * D)
    (hok : constOK (B.ctx k n) b (IntModelKv.aa kk) (M0 kk) D (3 * (c.vM / 3 + c.s)) out = true) :
    ConstCert kk (IntModelKv.admM0 kk) c := by
  set T := B.ctx k n with hT
  have hkT : T.k.Ok := hk
  have hH : T.Dom (boxH B.s) := boxH_dom k B n
  have he0 : B.e.e = 0 := by rw [hBe]; exact branchTable_e he
  obtain ⟨Zc, A0, A1, hZ, hA0, hA1, x0, hx0p, hx0b, hall⟩ :=
    boxEncl kk hk n hkk (hBd ▸ hd) he0 hY hg hE hA hrun
  simp only [constOK, chartOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hM, h7⟩, ht1⟩, ht0⟩, hw0⟩, hw1⟩, hn0⟩, hn1⟩ := hok
  obtain ⟨hZ0, hZ1, hZ2, hZ3⟩ := hZ
  refine ⟨e, he, hed, hec, hes, D, hM, hD2, fun Y => ?_⟩
  have hh : toKv (2 ^ B.s * Y) ∈ boxH B.s := toKv_mem_boxH _ _
  obtain ⟨x, hxp, hxb, Q, hQon, hQcls, hsh, hA0h, hA1h⟩ := hall _ hh
  have mem : ∀ {M : TM} {cF : List Kv × (Kv → Kv)}, EnclC T (boxH B.s) M cF.1 cF.2 →
      (TM.ball T M).Mem (cF.2 (toKv (2 ^ B.s * Y))) := fun hM =>
    Encl.mem_ball hkT hH (EnclF.encl ⟨_, hM⟩) hh
  have ht : ∀ j, ‖Q.chartT (aK kk) j‖ ≤ ‖pv‖ ^ D := by
    intro j
    rw [Mum.chartT_eq_shift, hsh]
    fin_cases j
    · exact Ball.norm_le_of_normLe hk (mem hZ1) ht1
    · exact Ball.norm_le_of_normLe hk (mem hZ0) ht0
  have hw0' : ‖(Q.chartW (aK kk)).coeff 0 - bK kk‖ < ‖2 * bK kk‖ := by
    rw [chartW_coeff_zero_shift, hsh]
    exact Ball.norm_sub_lt_of_nearOK hk (mem hZ2) hb hw0
  have hw1' : ‖(Q.chartW (aK kk)).coeff 1‖ * ‖pv‖ ^ IntModelKv.aa kk ≤ ‖bK kk‖ := by
    rw [chartW_coeff_one_shift, hsh]
    exact Ball.norm_mul_le_of_normLeMul hk (mem hZ3) hb hw1
  have hQc : Q.cls ((fRev kk).map σ) =
      ((Additive.toMul (Additive.ofMul (phiV kk x) - Additive.ofMul (phiV kk x0)) :
        Jac ((fRev kk).map σ)) : Pic ((fRev kk).map σ)) * (E0Mum kk).cls ((fRev kk).map σ) := by
    rw [hQcls, toMul_sub, toMul_ofMul, toMul_ofMul, Subgroup.coe_div, div_eq_mul_inv]
  obtain ⟨z, hz, htz⟩ := chart_of_pair kk hQon hQc hM h7 ht hw0' hw1'
  have hofs : ofKv (toKv (2 ^ B.s * Y)) = 2 ^ B.s * Y := ofKv_toKv _
  refine ⟨x, x0, ?_, hBe ▸ hxb, ?_, hBe ▸ hx0b, z, hz, ?_⟩
  · rw [hxp, boxPt, hofs, hBd, hBc, hBs, hed]
    push_cast
    rfl
  · rw [hx0p, boxPt, ofKv_zero, add_zero, hBd, hBc, hed]
    push_cast
    rfl
  · rw [htz, Mum.chartT_eq_shift, hsh]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · fin_cases i
      · exact Ball.norm_le_of_normLe hk (mem hZ1) ht1
      · exact Ball.norm_le_of_normLe hk (mem hZ0) ht0
    · obtain ⟨e0, e1⟩ := Amat_mulVec_vec2 kk (Zc.u1.2 (toKv (2 ^ B.s * Y))) (Zc.u0.2 (toKv (2 ^ B.s * Y)))
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · simp only [Mum.cmap]
        rw [e0, ← hA0h]
        exact Ball.norm_le_of_normLe hk (mem hA0) hn0
      · simp only [Mum.cmap]
        rw [e1, ← hA1h]
        exact Ball.norm_le_of_normLe hk (mem hA1) hn1

/-- **`TailCert` from a box run** and its check. -/
theorem tailCert_of_run (kk : Fin 2) {t : FurioLombardo.M4.TBox} {e : BranchBox}
    (he : e ∈ branchTable kk) (hed : e.disc = t.disc) (hec : e.c = t.c) (hes : e.s = t.s)
    {k : Ctx} (hk : k.Ok) (n : ℕ) {B : BoxSpec} (hkk : B.kk = kk) (hBd : B.d = t.disc)
    (hBc : B.c = t.Xi) (hBs : B.s = t.s) (hBe : B.e = e) (hd : IsDisc t.disc)
    (hY : (2 : ℤ) ^ B.N ∣ G1 B.d B.c B.Y0)
    {g : Sext Ball} {E : Mum Ball} {Am : Mat2 Ball}
    (hg : Sext.Rel (fun x b => b.Mem x) (Sext.ofPoly ((fRev kk).map σ)) g)
    (hE : Mum.Rel (fun x b => b.Mem x) (E0Mum kk) E)
    (hA : Am.a00.Mem (Amat kk 0 0) ∧ Am.a01.Mem (Amat kk 0 1) ∧ Am.a10.Mem (Amat kk 1 0) ∧
      Am.a11.Mem (Amat kk 1 1))
    {b : Ball} (hb : b.Mem (bK kk)) {out : Mum TM × TM × TM}
    (hrun : boxRun (B.ctx k n) g E Am B = some out) {D a1 aS : ℕ}
    (h1 : M0 kk + 4 ≤ 3 * t.s + min a1 (3 * t.s + aS)) (h2 : 3 * (t.vM / 3) ≤ 3 * t.s0 + aS)
    (h3 : 3 * (t.vM / 3) + M0 kk + 3 ≤ 3 * t.s0 + 2 * min a1 (3 * t.s + aS))
    (hok : tailOK (B.ctx k n) b Am (IntModelKv.aa kk) (M0 kk) D a1 aS t.q t.g out = true) :
    TailCert kk (IntModelKv.admM0 kk) t := by
  set T := B.ctx k n with hT
  have hkT : T.k.Ok := hk
  have hH : T.Dom (boxH B.s) := boxH_dom k B n
  have he0 : B.e.e = 0 := by rw [hBe]; exact branchTable_e he
  obtain ⟨Zc, A0, A1, hZ, -, -, x0, hx0p, hx0b, hall⟩ :=
    boxEncl kk hk n hkk (hBd ▸ hd) he0 hY hg hE hA hrun
  simp only [tailOK, chartOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hM, h7⟩, ht1⟩, ht0⟩, hw0⟩, hw1⟩, hn⟩, hc10⟩, hc11⟩, hS1⟩, hS0⟩, hg0⟩, hg1⟩ := hok
  obtain ⟨hZ0, hZ1, hZ2, hZ3⟩ := hZ
  set c0 : Fin 2 → Kv := ![Zc.u1.1.getD 0 0, Zc.u0.1.getD 0 0] with hc0
  set c1 : Fin 2 → Kv := ![Zc.u1.1.getD 1 0, Zc.u0.1.getD 1 0] with hc1
  have hm1 : (out.1.u1.cs.getD 1 (TM.zeroB T)).Mem (c1 0) := forall₂_getD_mem hk hZ1.1 1
  have hm0 : (out.1.u0.cs.getD 1 (TM.zeroB T)).Mem (c1 1) := forall₂_getD_mem hk hZ0.1 1
  refine ⟨e, he, hed, hec, hes, c0, c1, a1, aS, aS, h1, h2, h3, fun i => ?_, fun i => ?_, fun Y => ?_⟩
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exact Ball.norm_le_of_normLe hk hm1 hc10
    · exact Ball.norm_le_of_normLe hk hm0 hc11
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exact Ball.norm_le_of_normLe hk (mem_tailG hkT hA hm1 hm0 t.g 0) hg0
    · exact Ball.norm_le_of_normLe hk (mem_tailG hkT hA hm1 hm0 t.g 1) hg1
  have hh : toKv (2 ^ B.s * Y) ∈ boxH B.s := toKv_mem_boxH _ _
  obtain ⟨x, hxp, hxb, Q, hQon, hQcls, hsh, -, -⟩ := hall _ hh
  have mem : ∀ {M : TM} {cF : List Kv × (Kv → Kv)}, EnclC T (boxH B.s) M cF.1 cF.2 →
      (TM.ball T M).Mem (cF.2 (toKv (2 ^ B.s * Y))) := fun hM =>
    Encl.mem_ball hkT hH (EnclF.encl ⟨_, hM⟩) hh
  have ht : ∀ j, ‖Q.chartT (aK kk) j‖ ≤ ‖pv‖ ^ D := by
    intro j
    rw [Mum.chartT_eq_shift, hsh]
    fin_cases j
    · exact Ball.norm_le_of_normLe hk (mem hZ1) ht1
    · exact Ball.norm_le_of_normLe hk (mem hZ0) ht0
  have hw0' : ‖(Q.chartW (aK kk)).coeff 0 - bK kk‖ < ‖2 * bK kk‖ := by
    rw [chartW_coeff_zero_shift, hsh]
    exact Ball.norm_sub_lt_of_nearOK hk (mem hZ2) hb hw0
  have hw1' : ‖(Q.chartW (aK kk)).coeff 1‖ * ‖pv‖ ^ IntModelKv.aa kk ≤ ‖bK kk‖ := by
    rw [chartW_coeff_one_shift, hsh]
    exact Ball.norm_mul_le_of_normLeMul hk (mem hZ3) hb hw1
  have hQc : Q.cls ((fRev kk).map σ) =
      ((Additive.toMul (Additive.ofMul (phiV kk x) - Additive.ofMul (phiV kk x0)) :
        Jac ((fRev kk).map σ)) : Pic ((fRev kk).map σ)) * (E0Mum kk).cls ((fRev kk).map σ) := by
    rw [hQcls, toMul_sub, toMul_ofMul, toMul_ofMul, Subgroup.coe_div, div_eq_mul_inv]
  obtain ⟨z, hz, htz⟩ := chart_of_pair kk hQon hQc hM h7 ht hw0' hw1'
  have hofs : ofKv (toKv (2 ^ B.s * Y)) = 2 ^ B.s * Y := ofKv_toKv _
  have hj : 2 ≤ T.n + 1 := by omega
  obtain ⟨q1, hq1, e1⟩ := EnclC.split hkT hH hZ1 hj hh
  obtain ⟨q0, hq0, e0⟩ := EnclC.split hkT hH hZ0 hj hh
  rw [horner_take_two] at e1 e0
  refine ⟨x, x0, ?_, hBe ▸ hxb, ?_, hBe ▸ hx0b, z, hz, ?_⟩
  · rw [hxp, boxPt, hofs, hBd, hBc, hBs, hed]
  · rw [hx0p, boxPt, ofKv_zero, add_zero, hBd, hBc, hed]
  · refine ⟨![q1, q0], ?_, fun i => ?_, fun i => ?_⟩
    · rw [htz, Mum.chartT_eq_shift, hsh]
      funext i
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · simp only [Mum.cmap, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc0, hc1]
        rw [e1, hBs]
      · simp only [Mum.cmap, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, hc0, hc1]
        rw [e0, hBs]
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · exact Ball.norm_le_of_normLe hk hq1 hS1
      · exact Ball.norm_le_of_normLe hk hq0 hS0
    · refine norm_Amat_mulVec_le kk (fun j => ?_) i
      obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      · exact Ball.norm_le_of_normLe hk hq1 hS1
      · exact Ball.norm_le_of_normLe hk hq0 hS0

end FurioLombardo.Discharge.M4Box
