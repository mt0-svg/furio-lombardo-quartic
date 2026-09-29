import Mathlib
import FurioLombardo.M3a.Route
import FurioLombardo.M4.Instances
import FurioLombardo.Discharge.Analytic.Saturation

/-!
# Lane M4's local chain plugged into the route of lane M3a

`FurioLombardo.M3a.Route.TwistRoute` asks, for one twist, a completion `σ : k → k_v`, the reversed
Prym sextic `f`, the Abel-Prym map `φ`, the known lifts, a logarithm `lam`, lattices `Λ`, `S` and a
set `W` with the fields of `FurioLombardo.M3a.Route.Inputs`. This file takes `Λ`, `S`, `W` from
lane M4's data and derives the lattice and covering fields from lane M4's named hypotheses
(lean/FurioLombardo/M4/Hypotheses.lean):

* `Λ = span (lam D_i)` (M4's `HGen` holds by definition), `S = satOf Λ a b` (the saturation of
  `span {a, b}` in `Λ`, `FurioLombardo.Discharge.Analytic.satOf`, so M4's `HSat` holds by
  definition), `W = Wset D.W`;
* `logRange_of_hLam` (`LogRange` from `HLam`);
* `selmerW_of_M4` (`SelmerW` from `HSelLoc`, through M4's `hW_of_selLoc`);
* `coverIII_knownZero_of_M4` (`CoverIII` and `KnownZero` from M4's `cover_lifts`, given the disc
  map of the lifts, `LiftDisc`, and the link `TailGood` between the tail centres and the known
  points).

The whole bundle for one twist is `FurioLombardo.Discharge.M3a.inputs_of_M4` (Assembly.lean).
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.Analytic (satOf isSatOf_satOf saturated_satOf left_mem_satOf
  right_mem_satOf mem_satOf)

namespace FurioLombardo.Discharge.M3a

section Lattice

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

/-- M3a's `LogRange` from M4's `HLam`, with `Λ` the span of the logarithms of the local divisors. -/
theorem logRange_of_hLam {B : Type*} [AddCommGroup B] (lam : B →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → B) (hLam : FurioLombardo.M4.HLam lam Dpt) :
    LogRange lam (Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))) :=
  fun l => (hLam l).symm

theorem condIII_iff {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {W : Set (Fin 6 → ℤ_[2])}
    {y : Fin 6 → ℤ_[2]} : FurioLombardo.M3a.CondIII Λ S W y ↔ FurioLombardo.M4.CondIII Λ S W y :=
  Iff.rfl

end Lattice

section Plug

variable {k : Type} [Field k] [Algebra ℚ k] {kv : Type} [Field kv]

/-- The logarithm of the localisation of `φ(x) - φ(x_a)` at a lift `x` (the family `y` of M3a's
`CoverIII` and `KnownZero`). -/
noncomputable def liftLog (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} (φ : DPoint k M1 M2 M3 δ → Jac f)
    (xa : DPoint k M1 M2 M3 δ) (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2]))
    (x : Lift M1 M2 M3 δ) : Fin 6 → ℤ_[2] :=
  lam (Additive.ofMul (jacMap σ f (φ x.1 / φ xa)))

/-- The disc map of the lifts, lane M4's `HDisc` for `Dk = Lift M1 M2 M3 δ`: every lift lies over a
point of `C(Q_2)` of twist δ with disc `disc x` and parameter `par x`, and its logarithm is, modulo
`S`, plus or minus the analytic branch `lamD` there. -/
def LiftDisc {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} (y : Lift M1 M2 M3 δ → Fin 6 → ℤ_[2])
    (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2])
    (Twist : ℕ → ℤ_[2] → Prop) (disc : Lift M1 M2 M3 δ → ℕ) (par : Lift M1 M2 M3 δ → ℤ_[2]) :
    Prop :=
  ∀ x, disc x ∈ [1, 2, 3, 4, 5] ∧ Twist (disc x) (par x) ∧
    (y x - lamD (disc x) (par x) ∈ S ∨ y x + lamD (disc x) (par x) ∈ S)

/-- A lift whose disc and parameter are those of a tail centre (a known lift of lane M4's data) lies
over one of the two known points `Pa`, `Pb`. -/
def TailGood {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} (Pa Pb : ℚ × ℚ × ℚ)
    (D : FurioLombardo.M4.TwistData) (disc : Lift M1 M2 M3 δ → ℕ) (par : Lift M1 M2 M3 δ → ℤ_[2]) :
    Prop :=
  ∀ x : Lift M1 M2 M3 δ, (∃ t ∈ D.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2])) →
    GoodLift Pa Pb x.1

/-- `CoverIII` and `KnownZero` of M3a from lane M4's `cover_lifts`. -/
theorem coverIII_knownZero_of_M4 {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k}
    {Pa Pb : ℚ × ℚ × ℚ} {D : FurioLombardo.M4.TwistData} (hD : FurioLombardo.M4.TwistChecks D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    {y : Lift M1 M2 M3 δ → Fin 6 → ℤ_[2]}
    (hBD : FurioLombardo.M4.HBallD D ℓ) (hBP : FurioLombardo.M4.HBallPhi D a b)
    (hCe : FurioLombardo.M4.HCentre D lamD) (hAC : FurioLombardo.M4.HAntiConst D lamD)
    (hAT : FurioLombardo.M4.HAntiTail D lamD)
    (hKn : FurioLombardo.M4.HKnown D (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) lamD)
    (hEx : FurioLombardo.M4.HExcl D Twist)
    (hDisc : LiftDisc y (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) lamD Twist disc par)
    (hTail : TailGood Pa Pb D disc par) :
    CoverIII (Submodule.span ℤ_[2] (Set.range ℓ)) (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b)
        (FurioLombardo.M4.Wset D.W) y ∧
      KnownZero (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) y (fun x => GoodLift Pa Pb x.1) := by
  obtain ⟨h3, h0⟩ := FurioLombardo.M4.cover_lifts hD (Λ := Submodule.span ℤ_[2] (Set.range ℓ))
    (S := satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) rfl hBD hBP (isSatOf_satOf _ a b) hCe hAC
    hAT hKn hEx hDisc
  exact ⟨fun x => h3 x, fun x hx => hTail x (h0 x hx)⟩

/-- `SelmerW` of M3a from lane M4's `HSelLoc`. -/
theorem selmerW_of_M4 {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → B) {D : FurioLombardo.M4.TwistData}
    (hD : FurioLombardo.M4.TwistChecks D) {a b : Fin 6 → ℤ_[2]}
    (hLam : FurioLombardo.M4.HLam lam Dpt) (hBD : FurioLombardo.M4.HBallD D (fun i => lam (Dpt i)))
    (hBP : FurioLombardo.M4.HBallPhi D a b) (hSel : FurioLombardo.M4.HSelLoc ι Dpt D) :
    SelmerW ι lam (FurioLombardo.M4.Wset D.W) := by
  obtain ⟨-, h4, -⟩ := FurioLombardo.M4.qchar_of_cert hD rfl hBD hBP (isSatOf_satOf _ a b)
  exact FurioLombardo.M4.hW_of_selLoc ι lam Dpt hD hLam hBD h4 hSel

end Plug

end FurioLombardo.Discharge.M3a
