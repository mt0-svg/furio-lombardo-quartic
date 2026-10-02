import Mathlib
import FurioLombardo.Discharge.M4Box.Chain
import FurioLombardo.Discharge.M3a.ConcreteKv

/-!
# The route of lane M3a with the box inputs in the weak form

Copies of the M3a level of lane M4's chain where the fields `hAC : HAntiConst`, `hAT : HAntiTail`
are replaced by `hCL : HConstLip`, `hTQ : HTailQuad` (Weak.lean), all other fields unchanged, and
the data check `TailsFour D` (Chain.lean) is added next to `TwistChecks D`:

* `coverIII_knownZero_of_M4_w` (Plug.lean);
* `M4InputsW`, `inputs_of_M4_w`, `twistRoute_of_M4_w` (Assembly.lean);
* `M4RestW`, `M4RestW.toM4InputsW`, `twistRoute_fRev_w`, `TwistInputsW`,
  `twistRoute_of_twistInputsW` (ConcreteRoute.lean);
* `M4RestKvW`, `M4RestKvW.toM4RestW`, `TwistInputsKvW`, `twistInputs_of_KvW`, `T0_twistRoute_KvW`,
  `T1_twistRoute_KvW`, `onlyFourPoints_KvW` (ConcreteKv.lean).
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.Analytic (satOf isSatOf_satOf saturated_satOf left_mem_satOf
  right_mem_satOf IndepModTwo LogChartFin hLam_of_chartFin two_torsion_of_localTwoTorsion
  logKernelTorsion_of_chart logChart_of_fin)
open FurioLombardo.Discharge.M3a

namespace FurioLombardo.Discharge.M4Box

section Plug

variable {k : Type} [Field k] [Algebra ℚ k] {kv : Type} [Field kv]

/-- `CoverIII` and `KnownZero` of M3a from `cover_lifts_w`. Proposition 7.6 of the paper. -/
theorem coverIII_knownZero_of_M4_w {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k}
    {Pa Pb : ℚ × ℚ × ℚ} {D : FurioLombardo.M4.TwistData} (hD : FurioLombardo.M4.TwistChecks D)
    (hg4 : TailsFour D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    {y : Lift M1 M2 M3 δ → Fin 6 → ℤ_[2]}
    (hBD : FurioLombardo.M4.HBallD D ℓ) (hBP : FurioLombardo.M4.HBallPhi D a b)
    (hCe : FurioLombardo.M4.HCentre D lamD) (hCL : HConstLip D lamD) (hTQ : HTailQuad D lamD)
    (hKn : FurioLombardo.M4.HKnown D (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) lamD)
    (hEx : FurioLombardo.M4.HExcl D Twist)
    (hDisc : LiftDisc y (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) lamD Twist disc par)
    (hTail : TailGood Pa Pb D disc par) :
    CoverIII (Submodule.span ℤ_[2] (Set.range ℓ)) (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b)
        (FurioLombardo.M4.Wset D.W) y ∧
      KnownZero (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) y (fun x => GoodLift Pa Pb x.1) := by
  obtain ⟨h3, h0⟩ := cover_lifts_w hD hg4 (Λ := Submodule.span ℤ_[2] (Set.range ℓ))
    (S := satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) rfl hBD hBP (isSatOf_satOf _ a b) hCe hCL
    hTQ hKn hEx hDisc
  exact ⟨fun x => h3 x, fun x hx => hTail x (h0 x hx)⟩

end Plug

section Assembly

variable {k : Type} [Field k] [Algebra ℚ k] {kv : Type} [Field kv]

/-- `M4Inputs` with `hCL : HConstLip`, `hTQ : HTailQuad` in place of `hAC`, `hAT`. -/
structure M4InputsW (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) (Pa Pb : ℚ × ℚ × ℚ)
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    (D : FurioLombardo.M4.TwistData) (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2])
    (Twist : ℕ → ℤ_[2] → Prop) (disc : Lift M1 M2 M3 δ → ℕ) (par : Lift M1 M2 M3 δ → ℤ_[2]) :
    Prop where
  hLam : FurioLombardo.M4.HLam lam Dpt
  hBD : FurioLombardo.M4.HBallD D (fun i => lam (Dpt i))
  hBP : FurioLombardo.M4.HBallPhi D (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)
  hCe : FurioLombardo.M4.HCentre D lamD
  hCL : HConstLip D lamD
  hTQ : HTailQuad D lamD
  hKn : FurioLombardo.M4.HKnown D
    (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)) lamD
  hEx : FurioLombardo.M4.HExcl D Twist
  hSel : FurioLombardo.M4.HSelLoc (iotaA σ f) Dpt D
  hDisc : LiftDisc (liftLog σ f φ xa lam)
    (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)) lamD Twist disc par
  hTail : TailGood Pa Pb D disc par

/-- `inputs_of_M4` from `M4InputsW` and `TailsFour D`. -/
theorem inputs_of_M4_w (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (hD : FurioLombardo.M4.TwistChecks D) (hg4 : TailsFour D) (hQ : QuarterFrom D)
    (hG : GlobalLocal σ f hq hqf hdeg lam)
    (hM : M4InputsW σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par) :
    Inputs σ f hq hqf hdeg M1 M2 M3 δ Pa Pb φ xa xb lam (latL lam Dpt)
      (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb))
      (FurioLombardo.M4.Wset D.W) := by
  have ha : logPhi σ f φ lam xa ∈ latL lam Dpt := (hM.hLam _).mp ⟨_, rfl⟩
  have hb : logPhi σ f φ lam xb ∈ latL lam Dpt := (hM.hLam _).mp ⟨_, rfl⟩
  obtain ⟨h3, h0⟩ := coverIII_knownZero_of_M4_w (Pa := Pa) (Pb := Pb) hD hg4 hM.hBD hM.hBP hM.hCe
    hM.hCL hM.hTQ hM.hKn hM.hEx hM.hDisc hM.hTail
  exact
    { xtKernel := hG.xtKernel
      selmerInjective := hG.selmerInjective
      localTwoTorsion := hG.localTwoTorsion
      logKernelTorsion := hG.logKernelTorsion
      logRange := logRange_of_hLam lam Dpt hM.hLam
      saturated := saturated_satOf _ _ _
      mem_a := left_mem_satOf _ ha
      mem_b := right_mem_satOf _ hb
      selmerW := selmerW_of_M4 (iotaA σ f) lam Dpt hD hM.hLam hM.hBD hM.hBP hM.hSel
      quarter := hQ hM.hBD hM.hBP ha hb
      coverIII := h3
      knownZero := h0 }

/-- `twistRoute_of_M4` from `M4InputsW` and `TailsFour D`. -/
theorem twistRoute_of_M4_w (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (hD : FurioLombardo.M4.TwistChecks D) (hg4 : TailsFour D) (hQ : QuarterFrom D)
    (hG : GlobalLocal σ f hq hqf hdeg lam)
    (hM : M4InputsW σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par) :
    TwistRoute M1 M2 M3 δ Pa Pb :=
  ⟨kv, inferInstance, σ, f, inferInstance, inferInstance, q, hq, hqf, hdeg, φ, xa, xb, lam, _, _, _,
    inputs_of_M4_w σ f hq hqf hdeg φ xa xb lam Dpt hD hg4 hQ hG hM⟩

end Assembly

section Fine

variable {k : Type} [Field k] [Algebra ℚ k] {kv : Type} [Field kv]

/-- `M4Rest` with `hCL : HConstLip`, `hTQ : HTailQuad` in place of `hAC`, `hAT`. -/
structure M4RestW (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) (Pa Pb : ℚ × ℚ × ℚ)
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    (D : FurioLombardo.M4.TwistData) (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2])
    (Twist : ℕ → ℤ_[2] → Prop) (disc : Lift M1 M2 M3 δ → ℕ) (par : Lift M1 M2 M3 δ → ℤ_[2]) :
    Prop where
  hBD : FurioLombardo.M4.HBallD D (fun i => lam (Dpt i))
  hBP : FurioLombardo.M4.HBallPhi D (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)
  hCe : FurioLombardo.M4.HCentre D lamD
  hCL : HConstLip D lamD
  hTQ : HTailQuad D lamD
  hKn : FurioLombardo.M4.HKnown D
    (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)) lamD
  hEx : FurioLombardo.M4.HExcl D Twist
  hSel : FurioLombardo.M4.HSelLoc (iotaA σ f) Dpt D
  hDisc : LiftDisc (liftLog σ f φ xa lam)
    (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)) lamD Twist disc par
  hTail : TailGood Pa Pb D disc par

/-- `M4InputsW` from `M4RestW` and `HLam`. -/
theorem M4RestW.toM4InputsW {σ : k →+* kv} {f : k[X]} [GoodSextic f] [GoodSextic (f.map σ)]
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint k M1 M2 M3 δ → Jac f} {xa xb : DPoint k M1 M2 M3 δ}
    {lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])} {Dpt : Fin 7 → Additive (Jac (f.map σ))}
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (h : M4RestW σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par)
    (hLam : FurioLombardo.M4.HLam lam Dpt) :
    M4InputsW σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par :=
  ⟨hLam, h.hBD, h.hBP, h.hCe, h.hCL, h.hTQ, h.hKn, h.hEx, h.hSel, h.hDisc, h.hTail⟩

end Fine

section Bruin

open FurioLombardo.M1 FurioLombardo.Discharge.M3a.Bruin

/-- `Bruin.twistRoute_fRev` from `M4RestW` and `TailsFour D`. -/
theorem twistRoute_fRev_w {kv : Type} [Field kv] (σ : K21 →+* kv) (k : Fin 2)
    [GoodSextic ((fRev k).map σ)] (hloc : LocalFacts σ k) (hPS : PoonenSchaefer (fRev k))
    {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k))
    (xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k))
    (lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map σ)))
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → ℕ}
    {par : Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → ℤ_[2]}
    (hD : FurioLombardo.M4.TwistChecks D) (hg4 : TailsFour D) (hQ : QuarterFrom D)
    {L : Matrix (Fin 4) (Fin 7) ℤ}
    (hL : ∀ a b : Fin 4, (2 : ℤ) ∣ (L * D.SB) a b - if a = b then 1 else 0)
    (hspan : ∃ g : Fin 4 → H (fRev k), SelmerSpan (fRev k) g ∧
      ∀ j, Hmap σ (fRev k) (g j) = ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ D.SB i j)
    (hind : ∀ c : Fin 7 → ℤ,
      ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i)
    (hchart : LogChartFin lam)
    (hM : M4RestW σ (fRev k) (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb φ xa xb lam Dpt D lamD Twist
      disc par) :
    TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb := by
  obtain ⟨hK2, hInd⟩ := selmer_and_indep σ (fRev k) Dpt hL hspan hind
  have hL1 : LocalTwoTorsion ((fRev k).map σ)
      (jacMap σ (fRev k) (Tpt (fRev k) (q_monic k) (q_dvd_fRev k) (q_natDegree k))) :=
    localTwoTorsion_of_L1Inputs σ (fRev k) (q_monic k) (q_dvd_fRev k) (q_natDegree k)
      (l1Inputs σ k hloc.irr hloc.nsq)
  have hLam : FurioLombardo.M4.HLam lam Dpt :=
    hLam_of_chartFin hchart (two_torsion_of_localTwoTorsion hL1) hInd
  exact twistRoute_of_M4_w σ (fRev k) (q_monic k) (q_dvd_fRev k) (q_natDegree k) φ xa xb lam Dpt hD
    hg4 hQ ⟨xtKernel_fRev k hPS, hK2, hL1, logKernelTorsion_of_chart (logChart_of_fin hchart)⟩
    (hM.toM4InputsW hLam)

/-- `Bruin.TwistInputs` with `M4RestW` in place of `M4Rest`. -/
def TwistInputsW (k : Fin 2) (D : FurioLombardo.M4.TwistData) (Pa Pb : ℚ × ℚ × ℚ)
    (φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k))
    (xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) : Prop :=
  ∃ (kv : Type) (_ : Field kv) (σ : K21 →+* kv) (_ : GoodSextic ((fRev k).map σ))
    (lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map σ))) (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2])
    (Twist : ℕ → ℤ_[2] → Prop) (disc : Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → ℕ)
    (par : Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → ℤ_[2]),
    LocalFacts σ k ∧ PoonenSchaefer (fRev k) ∧
    (∃ g : Fin 4 → H (fRev k), SelmerSpan (fRev k) g ∧
      ∀ j, Hmap σ (fRev k) (g j) = ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ D.SB i j) ∧
    (∀ c : Fin 7 → ℤ,
      ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i) ∧
    LogChartFin lam ∧
    M4RestW σ (fRev k) (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb φ xa xb lam Dpt D lamD Twist disc par

theorem twistRoute_of_twistInputsW {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    {Pa Pb : ℚ × ℚ × ℚ} {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    (hD : FurioLombardo.M4.TwistChecks D) (hg4 : TailsFour D) (hQ : QuarterFrom D)
    {L : Matrix (Fin 4) (Fin 7) ℤ}
    (hL : ∀ a b : Fin 4, (2 : ℤ) ∣ (L * D.SB) a b - if a = b then 1 else 0)
    (h : TwistInputsW k D Pa Pb φ xa xb) : TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb := by
  obtain ⟨kv, _, σ, _, lam, Dpt, lamD, Twist, disc, par, hloc, hPS, hspan, hind, hchart, hM⟩ := h
  exact twistRoute_fRev_w σ k hloc hPS φ xa xb lam Dpt hD hg4 hQ hL hspan hind hchart hM

end Bruin

section Kv

open FurioLombardo.M1 FurioLombardo.Discharge.M3a.Bruin
open FurioLombardo.Discharge.M4Cert (Kv liftDisc liftPar liftTwist_Mmat hExcl_T0_Mmat hExcl_T1_Mmat
  tailGood_T0_Mmat tailGood_T1_Mmat)

attribute [local instance] goodSextic_fRev_Kv

/-- `Bruin.M4RestKv` with `hCL : HConstLip`, `hTQ : HTailQuad` in place of `hAC`, `hAT`. -/
structure M4RestKvW (k : Fin 2) (D : FurioLombardo.M4.TwistData)
    (φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k))
    (xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k))
    (lam : Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)) →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)))
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop where
  hBD : FurioLombardo.M4.HBallD D (fun i => lam (Dpt i))
  hBP : FurioLombardo.M4.HBallPhi D (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xa)
    (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xb)
  hCe : FurioLombardo.M4.HCentre D lamD
  hCL : HConstLip D lamD
  hTQ : HTailQuad D lamD
  hKn : FurioLombardo.M4.HKnown D
    (satOf (latL lam Dpt) (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xa)
      (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xb)) lamD
  hSel : FurioLombardo.M4.HSelLoc (iotaA FurioLombardo.Discharge.M4Cert.σ (fRev k)) Dpt D
  hLog : LogBranch (liftLog FurioLombardo.Discharge.M4Cert.σ (fRev k) φ xa lam)
    (satOf (latL lam Dpt) (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xa)
      (logPhi FurioLombardo.Discharge.M4Cert.σ (fRev k) φ lam xb)) lamD liftDisc liftPar

/-- `M4RestW` from `M4RestKvW`, given `HExcl` and `TailGood` for the twist. -/
theorem M4RestKvW.toM4RestW {k : Fin 2} {D : FurioLombardo.M4.TwistData} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    {lam : Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)) →+ (Fin 6 → ℤ_[2])}
    {Dpt : Fin 7 → Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ))}
    {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]} (h : M4RestKvW k D φ xa xb lam Dpt lamD)
    (hEx : FurioLombardo.M4.HExcl D
      (FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k)))
    (hTail : TailGood Pa Pb D (liftDisc (M1 := Mmat 0) (M2 := Mmat 1) (M3 := Mmat 2) (δ := δ k))
      liftPar) :
    M4RestW FurioLombardo.Discharge.M4Cert.σ (fRev k) (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb φ xa
      xb lam Dpt D lamD (FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k))
      liftDisc liftPar :=
  { hBD := h.hBD
    hBP := h.hBP
    hCe := h.hCe
    hCL := h.hCL
    hTQ := h.hTQ
    hKn := h.hKn
    hEx := hEx
    hSel := h.hSel
    hDisc := fun x => ⟨(liftTwist_Mmat (δ k) x).1, (liftTwist_Mmat (δ k) x).2, h.hLog x⟩
    hTail := hTail }

/-- `Bruin.TwistInputsKv` with `M4RestKvW` in place of `M4RestKv`. -/
def TwistInputsKvW (k : Fin 2) (D : FurioLombardo.M4.TwistData)
    (φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k))
    (xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) : Prop :=
  ∃ (lam : Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)) →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map FurioLombardo.Discharge.M4Cert.σ)))
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]),
    (∃ g : Fin 4 → H (fRev k), SelmerSpan (fRev k) g ∧
      ∀ j, Hmap FurioLombardo.Discharge.M4Cert.σ (fRev k) (g j) =
        ∏ i, muJ ((fRev k).map FurioLombardo.Discharge.M4Cert.σ) (Additive.toMul (Dpt i)) ^
          D.SB i j) ∧
    (∀ c : Fin 7 → ℤ,
      ∏ i, muJ ((fRev k).map FurioLombardo.Discharge.M4Cert.σ) (Additive.toMul (Dpt i)) ^ c i = 1 →
        ∀ i, (2 : ℤ) ∣ c i) ∧
    LogChartFin lam ∧ M4RestKvW k D φ xa xb lam Dpt lamD

/-- `TwistInputsW` from `TwistInputsKvW`, given `HExcl` and `TailGood` for the twist. -/
theorem twistInputs_of_KvW {k : Fin 2} {D : FurioLombardo.M4.TwistData} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    (hEx : FurioLombardo.M4.HExcl D
      (FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k)))
    (hTail : TailGood Pa Pb D (liftDisc (M1 := Mmat 0) (M2 := Mmat 1) (M3 := Mmat 2) (δ := δ k))
      liftPar)
    (h : TwistInputsKvW k D φ xa xb) : TwistInputsW k D Pa Pb φ xa xb := by
  obtain ⟨lam, Dpt, lamD, hspan, hind, hchart, hM⟩ := h
  exact ⟨Kv, inferInstance, FurioLombardo.Discharge.M4Cert.σ, inferInstance, lam, Dpt, lamD,
    FurioLombardo.Discharge.M4Cert.Twist (Mmat 0) (Mmat 1) (Mmat 2) (δ k), liftDisc, liftPar,
    localFacts_Kv k, poonenSchaefer_fRev k, hspan, hind, hchart, hM.toM4RestW hEx hTail⟩

/-- **The route of the twist δ0 at `K_v`, box inputs in the weak form.** -/
theorem T0_twistRoute_KvW {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 → Jac (fRev 0)}
    (h : TwistInputsKvW 0 FurioLombardo.M4.T0.data φ x0 x2) :
    TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) δ0 (0, 0, 1) (2, 0, 1) :=
  twistRoute_of_twistInputsW FurioLombardo.M4.T0.checks T0_tailsFour
    (fun hBD hBP ha hb => Q0.quarter hBD hBP ha hb) FurioLombardo.M4.T0.hSBL
    (twistInputs_of_KvW hExcl_T0_Mmat tailGood_T0_Mmat h)

/-- **The route of the twist δ1 at `K_v`, box inputs in the weak form.** -/
theorem T1_twistRoute_KvW {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1 → Jac (fRev 1)}
    (h : TwistInputsKvW 1 FurioLombardo.M4.T1.data φ x1 x3) :
    TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) δ1 (1, 1, 1) (-1, 0, 1) :=
  twistRoute_of_twistInputsW FurioLombardo.M4.T1.checks T1_tailsFour
    (fun hBD hBP ha hb => Q1.quarter hBD hBP ha hb) FurioLombardo.M4.T1.hSBL
    (twistInputs_of_KvW hExcl_T1_Mmat tailGood_T1_Mmat h)

/-- **The frozen statement from the inputs at `K_v`, box inputs in the weak form.** -/
theorem onlyFourPoints_KvW (hdesc : Descent K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 δ1)
    (φ0 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 → Jac (fRev 0))
    (φ1 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1 → Jac (fRev 1))
    (h0 : TwistInputsKvW 0 FurioLombardo.M4.T0.data φ0 x0 x2)
    (h1 : TwistInputsKvW 1 FurioLombardo.M4.T1.data φ1 x1 x3) : FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_of_route hdesc (T0_twistRoute_KvW h0) (T1_twistRoute_KvW h1)

end Kv

end FurioLombardo.Discharge.M4Box
