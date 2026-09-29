import Mathlib
import FurioLombardo.Discharge.M3a.Plug
import FurioLombardo.Discharge.M3a.QuarterInst

/-!
# The route of lane M3a for one twist from lane M4's hypotheses

`inputs_of_M4` builds the bundle `FurioLombardo.M3a.Route.Inputs` of one twist from

* `GlobalLocal`: the global inputs (K1) `XTKernel`, (K2) `SelmerInjective` and the local inputs
  (L1) `LocalTwoTorsion`, (L2) `LogKernelTorsion` (not provided by lane M4);
* `M4Inputs`: lane M4's named hypotheses (lean/FurioLombardo/M4/Hypotheses.lean) for the
  logarithm `lam`, the local divisors `Dpt` and the data `D`, together with the disc map of the
  lifts (`LiftDisc`, M4's `HDisc` for the lifts) and the link `TailGood` between the tail centres
  of `D` and the two known points;
* the kernel checked data `TwistChecks D` and the lattice fact `Quarter` in the form proved by
  `Q0.quarter`, `Q1.quarter` (`FurioLombardo.Discharge.M3a.QuarterInst`).

The lattices are `Λ = span (lam D_i)`, `S = satOf Λ a b`, `W = Wset D.W`. `twistRoute_of_M4`
packs the result as `TwistRoute`; `T0.twistRoute`, `T1.twistRoute` specialise to the two twists.
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.Analytic (satOf saturated_satOf left_mem_satOf right_mem_satOf)

namespace FurioLombardo.Discharge.M3a

section Assembly

variable {k : Type} [Field k] [Algebra ℚ k] {kv : Type} [Field kv]

/-- The inputs of M3a's route not provided by lane M4: (K1), (K2), (L1), (L2). -/
structure GlobalLocal (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) : Prop where
  xtKernel : XTKernel f
  selmerInjective : SelmerInjective σ f
  localTwoTorsion : LocalTwoTorsion (f.map σ) (jacMap σ f (Tpt f hq hqf hdeg))
  logKernelTorsion : LogKernelTorsion (f.map σ) lam

/-- `Λ = span (lam D_i)`. -/
noncomputable abbrev latL {kv : Type} [Field kv] {g : kv[X]} [GoodSextic g]
    (lam : Additive (Jac g) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac g)) :
    Submodule ℤ_[2] (Fin 6 → ℤ_[2]) :=
  Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))

/-- The logarithm of the localisation of `φ(x)`. -/
noncomputable abbrev logPhi (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} (φ : DPoint k M1 M2 M3 δ → Jac f)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (x : DPoint k M1 M2 M3 δ) :
    Fin 6 → ℤ_[2] :=
  lam (Additive.ofMul (jacMap σ f (φ x)))

/-- Lane M4's named hypotheses for one twist (with `S = satOf Λ a b`), the disc map of the lifts
and the link between the tail centres and the known points. -/
structure M4Inputs (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
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
  hAC : FurioLombardo.M4.HAntiConst D lamD
  hAT : FurioLombardo.M4.HAntiTail D lamD
  hKn : FurioLombardo.M4.HKnown D
    (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)) lamD
  hEx : FurioLombardo.M4.HExcl D Twist
  hSel : FurioLombardo.M4.HSelLoc (iotaA σ f) Dpt D
  hDisc : LiftDisc (liftLog σ f φ xa lam)
    (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb)) lamD Twist disc par
  hTail : TailGood Pa Pb D disc par

/-- The form in which `Q0.quarter`, `Q1.quarter` prove `Quarter` for the data `D`. -/
def QuarterFrom (D : FurioLombardo.M4.TwistData) : Prop :=
  ∀ {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]}, FurioLombardo.M4.HBallD D ℓ →
    FurioLombardo.M4.HBallPhi D a b → a ∈ Submodule.span ℤ_[2] (Set.range ℓ) →
    b ∈ Submodule.span ℤ_[2] (Set.range ℓ) →
    Quarter (Submodule.span ℤ_[2] (Set.range ℓ)) (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b)
      a b

/-- **The bundle `Inputs` of one twist from lane M4.** -/
theorem inputs_of_M4 (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (hD : FurioLombardo.M4.TwistChecks D) (hQ : QuarterFrom D)
    (hG : GlobalLocal σ f hq hqf hdeg lam)
    (hM : M4Inputs σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par) :
    Inputs σ f hq hqf hdeg M1 M2 M3 δ Pa Pb φ xa xb lam (latL lam Dpt)
      (satOf (latL lam Dpt) (logPhi σ f φ lam xa) (logPhi σ f φ lam xb))
      (FurioLombardo.M4.Wset D.W) := by
  have ha : logPhi σ f φ lam xa ∈ latL lam Dpt := (hM.hLam _).mp ⟨_, rfl⟩
  have hb : logPhi σ f φ lam xb ∈ latL lam Dpt := (hM.hLam _).mp ⟨_, rfl⟩
  obtain ⟨h3, h0⟩ := coverIII_knownZero_of_M4 (Pa := Pa) (Pb := Pb) hD hM.hBD hM.hBP hM.hCe hM.hAC
    hM.hAT hM.hKn hM.hEx hM.hDisc hM.hTail
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

/-- **The route of one twist from lane M4.** -/
theorem twistRoute_of_M4 (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (hD : FurioLombardo.M4.TwistChecks D) (hQ : QuarterFrom D)
    (hG : GlobalLocal σ f hq hqf hdeg lam)
    (hM : M4Inputs σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par) :
    TwistRoute M1 M2 M3 δ Pa Pb :=
  ⟨kv, inferInstance, σ, f, inferInstance, inferInstance, q, hq, hqf, hdeg, φ, xa, xb, lam, _, _, _,
    inputs_of_M4 σ f hq hqf hdeg φ xa xb lam Dpt hD hQ hG hM⟩

/-- **The route of the twist δ0 from lane M4** (data `FurioLombardo.M4.T0.data`). -/
theorem T0.twistRoute (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (hG : GlobalLocal σ f hq hqf hdeg lam)
    (hM : M4Inputs σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt FurioLombardo.M4.T0.data lamD Twist disc
      par) :
    TwistRoute M1 M2 M3 δ Pa Pb :=
  twistRoute_of_M4 σ f hq hqf hdeg φ xa xb lam Dpt FurioLombardo.M4.T0.checks
    (fun hBD hBP ha hb => Q0.quarter hBD hBP ha hb) hG hM

/-- **The route of the twist δ1 from lane M4** (data `FurioLombardo.M4.T1.data`). -/
theorem T1.twistRoute (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (hG : GlobalLocal σ f hq hqf hdeg lam)
    (hM : M4Inputs σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt FurioLombardo.M4.T1.data lamD Twist disc
      par) :
    TwistRoute M1 M2 M3 δ Pa Pb :=
  twistRoute_of_M4 σ f hq hqf hdeg φ xa xb lam Dpt FurioLombardo.M4.T1.checks
    (fun hBD hBP ha hb => Q1.quarter hBD hBP ha hb) hG hM

end Assembly

end FurioLombardo.Discharge.M3a
