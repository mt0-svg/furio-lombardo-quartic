import Mathlib
import FurioLombardo.M4.Instances
import FurioLombardo.M3a.Route
import FurioLombardo.Discharge.Analytic.ModTwo

/-!
# The routes of lanes M3a and M4 with the analytic inputs on the lattice replaced

Lane M3a (`FurioLombardo.M3a.Route.onlyFourPoints_of_route`) asks, for each twist, the inputs `LogKernelTorsion`,
`LogRange`, `Saturated`, `mem_a`, `mem_b` about the logarithm `lam` and the submodules `Λ`, `S`. With
`Λ := span (lam D_i)` and `S := satOf Λ a b` (FurioLombardo.Discharge.Analytic.Saturation) all five follow from
`LogChartFin lam` (the logarithm is a chart near the origin on a subgroup of finite index), `IndepModTwo Dpt` (the
seven local points are independent modulo 2) and the input `LocalTwoTorsion` that the route already has
(FurioLombardo.Discharge.Analytic.LogChart, ModTwo): `InputsA`, `inputs_of_inputsA`, `TwistRouteA`,
`onlyFourPoints_of_routeA`.

Lane M4 (`FurioLombardo.M4.T0.twist_local`, `T1.twist_local`) asks `HLam` and `HSat`; with `S := satOf Λ a b` they
follow from `LogChart lam` and `GenModTwo Dpt` (`T0.twist_local_gen`, `T1.twist_local_gen`); from `LogChartFin`,
the local 2-power torsion (L1), `2 T = 0` and `IndepModTwo` follow `HLam`, `HSat` and `HKer` (`T0.twist_local`,
`T1.twist_local`).
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.Analytic

/-- `Λ = span (lam D_i)`, the lattice of the route. -/
noncomputable abbrev spanD {B : Type*} [AddCommGroup B] (lam : B →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → B) :
    Submodule ℤ_[2] (Fin 6 → ℤ_[2]) :=
  Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))

section M3a

/-- Lane M3a's `LocalTwoTorsion` (L1) in additive form: an element of `A(k_v)[2]` is `0` or `T_v`. -/
theorem two_torsion_of_localTwoTorsion {kv : Type*} [Field kv] {g : kv[X]} [GoodSextic g] {Tv : Jac g}
    (h : LocalTwoTorsion g Tv) (b : Additive (Jac g)) (hb : (2 : ℕ) • b = 0) :
    b = 0 ∨ b = Additive.ofMul Tv := by
  have h2 : (Additive.toMul b) ^ (2 ^ 1) = 1 := by
    rw [pow_one, ← toMul_nsmul, hb, toMul_zero]
  rcases h (Additive.toMul b) ⟨1, h2⟩ with h1 | h1
  · left
    rw [← ofMul_toMul b, h1, ofMul_one]
  · right
    rw [← ofMul_toMul b, h1]

variable {k : Type*} [Field k] [Algebra ℚ k]

/-- The inputs of `FurioLombardo.M3a.Route.Inputs` with `Λ := span (lam D_i)` and `S := satOf Λ a b`, where the
analytic fields `logKernelTorsion`, `logRange`, `saturated`, `mem_a`, `mem_b` are replaced by `LogChartFin lam` and
`IndepModTwo Dpt`. -/
structure InputsA {kv : Type*} [Field kv] (σ : k →+* kv) (f : k[X]) [GoodSextic f]
    [GoodSextic (f.map σ)] {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) (Pa Pb : ℚ × ℚ × ℚ)
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    (W : Set (Fin 6 → ℤ_[2])) : Prop where
  xtKernel : XTKernel f
  selmerInjective : SelmerInjective σ f
  localTwoTorsion : LocalTwoTorsion (f.map σ) (jacMap σ f (Tpt f hq hqf hdeg))
  logChart : LogChartFin lam
  indepModTwo : IndepModTwo Dpt
  selmerW : SelmerW (iotaA σ f) lam W
  quarter : Quarter (spanD lam Dpt)
    (satOf (spanD lam Dpt) (lam (Additive.ofMul (jacMap σ f (φ xa))))
      (lam (Additive.ofMul (jacMap σ f (φ xb)))))
    (lam (Additive.ofMul (jacMap σ f (φ xa)))) (lam (Additive.ofMul (jacMap σ f (φ xb))))
  coverIII : CoverIII (spanD lam Dpt)
    (satOf (spanD lam Dpt) (lam (Additive.ofMul (jacMap σ f (φ xa))))
      (lam (Additive.ofMul (jacMap σ f (φ xb))))) W
    (fun x : Lift M1 M2 M3 δ => lam (Additive.ofMul (jacMap σ f (φ x.1 / φ xa))))
  knownZero : KnownZero
    (satOf (spanD lam Dpt) (lam (Additive.ofMul (jacMap σ f (φ xa))))
      (lam (Additive.ofMul (jacMap σ f (φ xb)))))
    (fun x : Lift M1 M2 M3 δ => lam (Additive.ofMul (jacMap σ f (φ x.1 / φ xa))))
    (fun x => GoodLift Pa Pb x.1)

/-- `InputsA` gives the inputs of lane M3a, with `Λ := span (lam D_i)` and `S := satOf Λ a b`. -/
theorem inputs_of_inputsA {kv : Type*} [Field kv] {σ : k →+* kv} {f : k[X]} [GoodSextic f]
    [GoodSextic (f.map σ)] {q : k[X]} {hq : q.Monic} {hqf : q ∣ f} {hdeg : q.natDegree = 2}
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint k M1 M2 M3 δ → Jac f} {xa xb : DPoint k M1 M2 M3 δ}
    {lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])} {Dpt : Fin 7 → Additive (Jac (f.map σ))}
    {W : Set (Fin 6 → ℤ_[2])}
    (h : InputsA σ f hq hqf hdeg M1 M2 M3 δ Pa Pb φ xa xb lam Dpt W) :
    Inputs σ f hq hqf hdeg M1 M2 M3 δ Pa Pb φ xa xb lam (spanD lam Dpt)
      (satOf (spanD lam Dpt) (lam (Additive.ofMul (jacMap σ f (φ xa))))
        (lam (Additive.ofMul (jacMap σ f (φ xb))))) W := by
  have hT : ∀ b : Additive (Jac (f.map σ)), (2 : ℕ) • b = 0 → b = 0 ∨ b = Additive.ofMul (jacMap σ f (Tpt f hq hqf hdeg)) :=
    two_torsion_of_localTwoTorsion h.localTwoTorsion
  have hLam : FurioLombardo.M4.HLam lam Dpt := hLam_of_chartFin h.logChart hT h.indepModTwo
  exact
    { xtKernel := h.xtKernel
      selmerInjective := h.selmerInjective
      localTwoTorsion := h.localTwoTorsion
      logKernelTorsion := logKernelTorsion_of_chart (logChart_of_fin h.logChart)
      logRange := logRange_of_hLam hLam
      saturated := saturated_satOf _ _ _
      mem_a := left_mem_satOf _ (mem_span_of_hLam hLam _)
      mem_b := right_mem_satOf _ (mem_span_of_hLam hLam _)
      selmerW := h.selmerW
      quarter := h.quarter
      coverIII := h.coverIII
      knownZero := h.knownZero }

/-- `FurioLombardo.M3a.Route.TwistRoute` with the analytic inputs on the lattice replaced by `LogChartFin` and
`IndepModTwo`: some completion, sextic, quadratic factor, Abel-Prym map, known lifts, logarithm, seven local points and
Selmer representatives satisfy `InputsA`. -/
def TwistRouteA (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) (Pa Pb : ℚ × ℚ × ℚ) : Prop :=
  ∃ (kv : Type) (_ : Field kv) (σ : k →+* kv) (f : k[X]) (_ : GoodSextic f)
    (_ : GoodSextic (f.map σ)) (q : k[X]) (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    (W : Set (Fin 6 → ℤ_[2])),
    InputsA σ f hq hqf hdeg M1 M2 M3 δ Pa Pb φ xa xb lam Dpt W

theorem twistRoute_of_routeA {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (h : TwistRouteA M1 M2 M3 δ Pa Pb) : TwistRoute M1 M2 M3 δ Pa Pb := by
  obtain ⟨kv, hkv, σ, f, hf, hfv, q, hq, hqf, hdeg, φ, xa, xb, lam, Dpt, W, hin⟩ := h
  exact ⟨kv, hkv, σ, f, hf, hfv, q, hq, hqf, hdeg, φ, xa, xb, lam, spanD lam Dpt, _, W, inputs_of_inputsA hin⟩

/-- **Lane M3a's top theorem with the lattice inputs discharged**: `OnlyFourPoints` from the descent and,
for each twist, `TwistRouteA` (no `LogKernelTorsion`, `LogRange`, `Saturated`, `mem_a`, `mem_b`; instead
`LogChartFin` and `IndepModTwo`). -/
theorem onlyFourPoints_of_routeA {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ0 δ1 : k}
    (hdesc : Descent k M1 M2 M3 δ0 δ1) (h0 : TwistRouteA M1 M2 M3 δ0 (0, 0, 1) (2, 0, 1))
    (h1 : TwistRouteA M1 M2 M3 δ1 (1, 1, 1) (-1, 0, 1)) : FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_of_route hdesc (twistRoute_of_routeA h0) (twistRoute_of_routeA h1)

end M3a

section M4

open FurioLombardo.M4

/-- **Lane M4 for the twist δ0, with `HLam` and `HSat` discharged**, first form: `S := satOf Λ a b` and `HLam` from
`LogChart lam` and `GenModTwo Dpt`. The other inputs are those of `FurioLombardo.M4.T0.twist_local`. -/
theorem T0.twist_local_gen {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hChart : LogChart lam) (hGen : GenModTwo Dpt) (hBD : HBallD M4.T0.data (fun i => lam (Dpt i)))
    (hBP : HBallPhi M4.T0.data (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre M4.T0.data lamD) (hAC : HAntiConst M4.T0.data lamD) (hAT : HAntiTail M4.T0.data lamD)
    (hKn : HKnown M4.T0.data (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) lamD)
    (hEx : HExcl M4.T0.data Twist)
    (hDi : HDisc ι lam (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) φ xa disc par lamD Twist)
    (hloc : HLocInj ι) (hker : HKer ι lam T) (hSel : HSelLoc ι Dpt M4.T0.data) (x : Dk) :
    ∃ t ∈ M4.T0.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) :=
  M4.T0.twist_local ι lam T Dpt _ φ xa xb lamD Twist disc par (hLam_of_chart hChart hGen) hBD hBP
    (hSat_satOf _ _ _) hCe hAC hAT hKn hEx hDi hloc hker hSel x

/-- **Lane M4 for the twist δ1, with `HLam` and `HSat` discharged**, first form (as `T0.twist_local_gen`). -/
theorem T1.twist_local_gen {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hChart : LogChart lam) (hGen : GenModTwo Dpt) (hBD : HBallD M4.T1.data (fun i => lam (Dpt i)))
    (hBP : HBallPhi M4.T1.data (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre M4.T1.data lamD) (hAC : HAntiConst M4.T1.data lamD) (hAT : HAntiTail M4.T1.data lamD)
    (hKn : HKnown M4.T1.data (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) lamD)
    (hEx : HExcl M4.T1.data Twist)
    (hDi : HDisc ι lam (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) φ xa disc par lamD Twist)
    (hloc : HLocInj ι) (hker : HKer ι lam T) (hSel : HSelLoc ι Dpt M4.T1.data) (x : Dk) :
    ∃ t ∈ M4.T1.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) :=
  M4.T1.twist_local ι lam T Dpt _ φ xa xb lamD Twist disc par (hLam_of_chart hChart hGen) hBD hBP
    (hSat_satOf _ _ _) hCe hAC hAT hKn hEx hDi hloc hker hSel x

/-- **Lane M4 for the twist δ0, with `HLam` and `HSat` discharged**: `S := satOf Λ a b`; `HLam` and `HKer` from the
finite index chart `LogChartFin lam`, the local 2-power torsion `hL1` ((L1): `A(k_v)[2^∞] = {0, T}`), `2 T = 0` and
the independence certificate `IndepModTwo Dpt`. The other inputs are those of `FurioLombardo.M4.T0.twist_local`. -/
theorem T0.twist_local {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hChart : LogChartFin lam) (hL1 : ∀ b : B, (∃ k : ℕ, (2 ^ k : ℕ) • b = 0) → b = 0 ∨ b = ι T)
    (hT2 : (2 : ℕ) • T = 0) (hInd : IndepModTwo Dpt)
    (hBD : HBallD M4.T0.data (fun i => lam (Dpt i)))
    (hBP : HBallPhi M4.T0.data (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre M4.T0.data lamD) (hAC : HAntiConst M4.T0.data lamD) (hAT : HAntiTail M4.T0.data lamD)
    (hKn : HKnown M4.T0.data (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) lamD)
    (hEx : HExcl M4.T0.data Twist)
    (hDi : HDisc ι lam (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) φ xa disc par lamD Twist)
    (hloc : HLocInj ι) (hSel : HSelLoc ι Dpt M4.T0.data) (x : Dk) :
    ∃ t ∈ M4.T0.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) :=
  M4.T0.twist_local ι lam T Dpt _ φ xa xb lamD Twist disc par
    (hLam_of_chartFin hChart (fun b hb => hL1 b ⟨1, by simpa using hb⟩) hInd) hBD hBP
    (hSat_satOf _ _ _) hCe hAC hAT hKn hEx hDi hloc (hKer_of_chart (logChart_of_fin hChart) hL1 hT2) hSel x

/-- **Lane M4 for the twist δ1, with `HLam` and `HSat` discharged** (as `T0.twist_local`). -/
theorem T1.twist_local {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hChart : LogChartFin lam) (hL1 : ∀ b : B, (∃ k : ℕ, (2 ^ k : ℕ) • b = 0) → b = 0 ∨ b = ι T)
    (hT2 : (2 : ℕ) • T = 0) (hInd : IndepModTwo Dpt)
    (hBD : HBallD M4.T1.data (fun i => lam (Dpt i)))
    (hBP : HBallPhi M4.T1.data (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre M4.T1.data lamD) (hAC : HAntiConst M4.T1.data lamD) (hAT : HAntiTail M4.T1.data lamD)
    (hKn : HKnown M4.T1.data (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) lamD)
    (hEx : HExcl M4.T1.data Twist)
    (hDi : HDisc ι lam (satOf (spanD lam Dpt) (lam (ι (φ xa))) (lam (ι (φ xb)))) φ xa disc par lamD Twist)
    (hloc : HLocInj ι) (hSel : HSelLoc ι Dpt M4.T1.data) (x : Dk) :
    ∃ t ∈ M4.T1.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) :=
  M4.T1.twist_local ι lam T Dpt _ φ xa xb lamD Twist disc par
    (hLam_of_chartFin hChart (fun b hb => hL1 b ⟨1, by simpa using hb⟩) hInd) hBD hBP
    (hSat_satOf _ _ _) hCe hAC hAT hKn hEx hDi hloc (hKer_of_chart (logChart_of_fin hChart) hL1 hT2) hSel x

end M4

end FurioLombardo.Discharge.Analytic
