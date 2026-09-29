import Mathlib
import FurioLombardo.Discharge.M3a.Assembly
import FurioLombardo.Discharge.M3a.SelmerK2
import FurioLombardo.Discharge.M3a.XTKernelK1
import FurioLombardo.Discharge.M3a.MuT

/-!
# The route of one twist from the finest inputs

`GlobalLocal` (Assembly.lean) bundles (K1), (K2), (L1), (L2). Here each of the first three is
replaced by what is left of it after the reductions of this directory:

* `K1Inputs f`: `PoonenSchaefer f` (proved for the sextics `fRev k`, `Bruin.poonenSchaefer_fRev`,
  K1Concrete.lean) and a non-square `d ∈ k` that is a square in `k[T]/(f)` (`xtKernel_of_sq`,
  XTKernelK1.lean);
* `K2Inputs σ f SB`: four classes `g_j ∈ H f` spanning the image of `μ` (`SelmerSpan`, the
  Selmer bound), their local images `∏ d_i^{SB i j}` in terms of seven independent classes `d_i`
  of `H (f^σ)` (`selmerInjective_of_SB`, SelmerK2.lean); the left inverse of `SB` modulo 2 is
  lane M4's kernel checked `hSBL`;
* `L1Inputs σ f q`: `f = q r` with `r^σ` irreducible over `k_v` and `(q^σ - r^σ)(T)` not in
  `k_v^× (L_v^×)²` (`localTwoTorsion_route_of_factors`, MuT.lean, WP1);
* (L2) `LogKernelTorsion` stays as it is (reduced by the analytic discharge lane to its chart
  statement).

`T0.twistRoute_fine`, `T1.twistRoute_fine`: `TwistRoute` of one twist from these, lane M4's
`M4Inputs`, and the kernel checked data of lane M4.
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.M3a

section Fine

variable {k : Type} [Field k] [Algebra ℚ k] {kv : Type} [Field kv]

/-- What is left of (K1). -/
structure K1Inputs (f : k[X]) [GoodSextic f] : Prop where
  ps : PoonenSchaefer f
  sq : ∃ d : k, ¬ IsSquare d ∧ ∃ ε : AdjoinRoot f, ε ^ 2 = algebraMap k (AdjoinRoot f) d

/-- What is left of (K2), for the matrix `SB` of the local images of the Selmer generators. -/
structure K2Inputs (σ : k →+* kv) (f : k[X]) [GoodSextic f] (SB : Matrix (Fin 7) (Fin 4) ℤ) :
    Prop where
  span : ∃ g : Fin 4 → H f, SelmerSpan f g ∧ ∃ d : Fin 7 → H (f.map σ),
    (∀ j, Hmap σ f (g j) = ∏ i, d i ^ SB i j) ∧
    ∀ c : Fin 7 → ℤ, ∏ i, d i ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i

/-- What is left of (L1). -/
structure L1Inputs (σ : k →+* kv) (f : k[X]) (q : k[X]) : Prop where
  fac : ∃ r : k[X], f = q * r ∧ Irreducible (r.map σ) ∧
    ∀ (c : kv) (y : AdjoinRoot (f.map σ)),
      AdjoinRoot.mk (f.map σ) (q.map σ - r.map σ) ≠ algebraMap kv (AdjoinRoot (f.map σ)) c * y ^ 2

omit [Algebra ℚ k] in
theorem xtKernel_of_K1Inputs {f : k[X]} [GoodSextic f] (h : K1Inputs f) : XTKernel f := by
  obtain ⟨d, hd, ε, hε⟩ := h.sq
  exact xtKernel_of_sq f h.ps d hd ε hε

omit [Algebra ℚ k] in
theorem selmerInjective_of_K2Inputs {σ : k →+* kv} {f : k[X]} [GoodSextic f]
    {SB : Matrix (Fin 7) (Fin 4) ℤ} {L : Matrix (Fin 4) (Fin 7) ℤ}
    (hL : ∀ a b : Fin 4, (2 : ℤ) ∣ (L * SB) a b - if a = b then 1 else 0) (h : K2Inputs σ f SB) :
    SelmerInjective σ f := by
  obtain ⟨g, hspan, d, hσ, hind⟩ := h.span
  exact selmerInjective_of_SB σ f g d SB L hspan hσ hind hL

omit [Algebra ℚ k] in
theorem localTwoTorsion_of_L1Inputs (σ : k →+* kv) (f : k[X]) [GoodSextic f]
    [GoodSextic (f.map σ)] {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (h : L1Inputs σ f q) : LocalTwoTorsion (f.map σ) (jacMap σ f (Tpt f hq hqf hdeg)) := by
  obtain ⟨r, hqr, hr, hsq⟩ := h.fac
  exact localTwoTorsion_route_of_factors σ f hq hqf hdeg hqr hr hsq

omit [Algebra ℚ k] in
/-- `GlobalLocal` from the finest inputs. -/
theorem globalLocal_of_fine (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) {SB : Matrix (Fin 7) (Fin 4) ℤ}
    {L : Matrix (Fin 4) (Fin 7) ℤ}
    (hL : ∀ a b : Fin 4, (2 : ℤ) ∣ (L * SB) a b - if a = b then 1 else 0)
    (h1 : K1Inputs f) (h2 : K2Inputs σ f SB) (hl1 : L1Inputs σ f q)
    (hl2 : LogKernelTorsion (f.map σ) lam) : GlobalLocal σ f hq hqf hdeg lam :=
  { xtKernel := xtKernel_of_K1Inputs h1
    selmerInjective := selmerInjective_of_K2Inputs hL h2
    localTwoTorsion := localTwoTorsion_of_L1Inputs σ f hq hqf hdeg hl1
    logKernelTorsion := hl2 }

/-- **The route of the twist δ0 from the finest inputs.** -/
theorem T0.twistRoute_fine (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (h1 : K1Inputs f) (h2 : K2Inputs σ f FurioLombardo.M4.T0.SB) (hl1 : L1Inputs σ f q)
    (hl2 : LogKernelTorsion (f.map σ) lam)
    (hM : M4Inputs σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt FurioLombardo.M4.T0.data lamD Twist disc
      par) :
    TwistRoute M1 M2 M3 δ Pa Pb :=
  T0.twistRoute σ f hq hqf hdeg φ xa xb lam Dpt
    (globalLocal_of_fine σ f hq hqf hdeg lam FurioLombardo.M4.T0.hSBL h1 h2 hl1 hl2) hM

/-- **The route of the twist δ1 from the finest inputs.** -/
theorem T1.twistRoute_fine (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (h1 : K1Inputs f) (h2 : K2Inputs σ f FurioLombardo.M4.T1.SB) (hl1 : L1Inputs σ f q)
    (hl2 : LogKernelTorsion (f.map σ) lam)
    (hM : M4Inputs σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt FurioLombardo.M4.T1.data lamD Twist disc
      par) :
    TwistRoute M1 M2 M3 δ Pa Pb :=
  T1.twistRoute σ f hq hqf hdeg φ xa xb lam Dpt
    (globalLocal_of_fine σ f hq hqf hdeg lam FurioLombardo.M4.T1.hSBL h1 h2 hl1 hl2) hM

end Fine

end FurioLombardo.Discharge.M3a
