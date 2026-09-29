import Mathlib
import FurioLombardo.Discharge.M3a.ConcreteInputs
import FurioLombardo.Discharge.Analytic.Route

/-!
# The route of lane M3a on the concrete sextics, with every proved input plugged in

For the twist `k : Fin 2` over K21 (WP2's `Bruin.Mmat`, `Bruin.δ k`, `Bruin.fRev k`, `Bruin.q k`):

* `indepModTwo_of_mu`: seven local points whose `x - T` images are independent in `H (f^σ)` are
  independent modulo `2 A(k_v)` (the analytic discharge lane's `IndepModTwo`). So the local
  certificate of (K2) (independence of the classes `μ_v(D_i)`) also gives `IndepModTwo`;
* `M4Rest`: lane M4's named hypotheses of `M4Inputs` (Assembly.lean) except `HLam`, which follows
  from the analytic lane's `LogChartFin lam`, (L1) and `IndepModTwo` (`hLam_of_chartFin`);
* `LocalFacts σ k`: the three local facts at `v` about `fRev k`: its leading coefficient is not a
  square in `k_v`, `h k` stays irreducible over `k_v`, and `(q - c h)(T)` is not in
  `k_v^× (L_v^×)²`;
* `Bruin.twistRoute_fRev`: lane M3a's `TwistRoute` for the twist `k` from `LocalFacts`,
  `PoonenSchaefer (fRev k)`, the Selmer bound `SelmerSpan` with the local images of
  its generators, the local independence of the `μ_v(D_i)`, `LogChartFin lam`, `M4Rest`, the kernel
  checked data `TwistChecks D` and the lattice fact `QuarterFrom D`, for any Abel-Prym map `φ`;
* `Bruin.T0.twistRoute_fRev`, `Bruin.T1.twistRoute_fRev`: with lane M4's data and the known lifts
  `x0`, `x2` (resp. `x1`, `x3`); `Bruin.onlyFourPoints_fRev`: the frozen statement from M1's descent
  for `Mmat` and the two twist inputs.

At `K_v` the local facts and `PoonenSchaefer (fRev k)` are theorems (`localFacts_Kv`, LocalFacts.lean;
`poonenSchaefer_fRev`, K1Concrete.lean), plugged in by `twistInputs_of_Kv` (ConcreteKv.lean) and, on the
route of the final theorem, by `twistInputs_of_KvW` (M4Box/ChainM3a.lean).
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.Analytic (IndepModTwo LogChartFin hLam_of_chartFin
  two_torsion_of_localTwoTorsion logKernelTorsion_of_chart logChart_of_fin satOf)

namespace FurioLombardo.Discharge.M3a

/-- **Independent `x - T` images give independence modulo 2.** If `∏ μ(D_i)^{c_i} = 1` in `H g`
forces every `c_i` to be even, then the `D_i` are independent modulo `2 A(k_v)`. -/
theorem indepModTwo_of_mu {kv : Type*} [Field kv] {g : kv[X]} [GoodSextic g]
    (Dpt : Fin 7 → Additive (Jac g))
    (h : ∀ c : Fin 7 → ℤ, ∏ i, muJ g (Additive.toMul (Dpt i)) ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i) :
    IndepModTwo Dpt := by
  rintro c ⟨b, hb⟩
  apply h c
  have key : Additive.ofMul (∏ i, muJ g (Additive.toMul (Dpt i)) ^ c i) =
      (muJ g).toAdditive (∑ i, c i • Dpt i) := by
    rw [ofMul_prod_zpow (fun i => muJ g (Additive.toMul (Dpt i))) c, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_zsmul (muJ g).toAdditive (c i) (Dpt i)).symm
  rw [hb, map_nsmul] at key
  have hsq : (muJ g).toAdditive b + (muJ g).toAdditive b = 0 := by
    change Additive.ofMul (muJ g (Additive.toMul b) * muJ g (Additive.toMul b)) = 0
    rw [← sq, H_sq_eq_one]
    rfl
  rw [two_nsmul, hsq] at key
  exact key

section Fine

variable {k : Type} [Field k] [Algebra ℚ k] {kv : Type} [Field kv]

/-- Lane M4's named hypotheses of `M4Inputs` except `HLam`. -/
structure M4Rest (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) (Pa Pb : ℚ × ℚ × ℚ)
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → Additive (Jac (f.map σ)))
    (D : FurioLombardo.M4.TwistData) (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2])
    (Twist : ℕ → ℤ_[2] → Prop) (disc : Lift M1 M2 M3 δ → ℕ) (par : Lift M1 M2 M3 δ → ℤ_[2]) :
    Prop where
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

/-- `M4Inputs` from `M4Rest` and `HLam`. -/
theorem M4Rest.toM4Inputs {σ : k →+* kv} {f : k[X]} [GoodSextic f] [GoodSextic (f.map σ)]
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint k M1 M2 M3 δ → Jac f} {xa xb : DPoint k M1 M2 M3 δ}
    {lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])} {Dpt : Fin 7 → Additive (Jac (f.map σ))}
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift M1 M2 M3 δ → ℕ} {par : Lift M1 M2 M3 δ → ℤ_[2]}
    (h : M4Rest σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par)
    (hLam : FurioLombardo.M4.HLam lam Dpt) :
    M4Inputs σ f M1 M2 M3 δ Pa Pb φ xa xb lam Dpt D lamD Twist disc par :=
  ⟨hLam, h.hBD, h.hBP, h.hCe, h.hAC, h.hAT, h.hKn, h.hEx, h.hSel, h.hDisc, h.hTail⟩

omit [Algebra ℚ k] in
/-- **(K2) and `IndepModTwo` from one local certificate.** The Selmer bound `SelmerSpan f g`, the
local images `Hmap σ f (g j) = ∏ μ_v(D_i)^{SB i j}`, the independence of the classes `μ_v(D_i)`
and a left inverse of `SB` modulo 2 give (K2) and the independence of the `D_i` modulo 2. -/
theorem selmer_and_indep (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    (Dpt : Fin 7 → Additive (Jac (f.map σ))) {SB : Matrix (Fin 7) (Fin 4) ℤ}
    {L : Matrix (Fin 4) (Fin 7) ℤ}
    (hL : ∀ a b : Fin 4, (2 : ℤ) ∣ (L * SB) a b - if a = b then 1 else 0)
    (hspan : ∃ g : Fin 4 → H f, SelmerSpan f g ∧
      ∀ j, Hmap σ f (g j) = ∏ i, muJ (f.map σ) (Additive.toMul (Dpt i)) ^ SB i j)
    (hind : ∀ c : Fin 7 → ℤ,
      ∏ i, muJ (f.map σ) (Additive.toMul (Dpt i)) ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i) :
    SelmerInjective σ f ∧ IndepModTwo Dpt := by
  obtain ⟨g, hg, hσ⟩ := hspan
  exact ⟨selmerInjective_of_K2Inputs hL ⟨⟨g, hg, _, hσ, hind⟩⟩, indepModTwo_of_mu Dpt hind⟩

end Fine

namespace Bruin

open FurioLombardo.M1

/-- The three local facts at `v` about the twist `k`. -/
structure LocalFacts {kv : Type} [Field kv] (σ : K21 →+* kv) (k : Fin 2) : Prop where
  lead : ¬ IsSquare (σ (fRev k).leadingCoeff)
  irr : Irreducible ((h k).map σ)
  nsq : ∀ (c' : kv) (y : AdjoinRoot ((fRev k).map σ)),
    AdjoinRoot.mk ((fRev k).map σ) ((q k).map σ - (C (c k) * h k).map σ) ≠
      algebraMap kv (AdjoinRoot ((fRev k).map σ)) c' * y ^ 2

/-- **The route of the twist `k` on the concrete sextic `fRev k`.** Hypotheses: the local
facts at `v`, `PoonenSchaefer (fRev k)`, the Selmer bound with the local images of its generators,
the independence of the `μ_v(D_i)`, the analytic lane's `LogChartFin lam` and lane M4's `M4Rest`,
for the data `D` (kernel checked `TwistChecks D`, lattice fact `QuarterFrom D`, left inverse `L` of
`D.SB` modulo 2) and any Abel-Prym map `φ`. -/
theorem twistRoute_fRev {kv : Type} [Field kv] (σ : K21 →+* kv) (k : Fin 2)
    [GoodSextic ((fRev k).map σ)] (hloc : LocalFacts σ k) (hPS : PoonenSchaefer (fRev k))
    {Pa Pb : ℚ × ℚ × ℚ}
    (φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k))
    (xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k))
    (lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]))
    (Dpt : Fin 7 → Additive (Jac ((fRev k).map σ)))
    {D : FurioLombardo.M4.TwistData} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → ℕ}
    {par : Lift (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → ℤ_[2]}
    (hD : FurioLombardo.M4.TwistChecks D) (hQ : QuarterFrom D) {L : Matrix (Fin 4) (Fin 7) ℤ}
    (hL : ∀ a b : Fin 4, (2 : ℤ) ∣ (L * D.SB) a b - if a = b then 1 else 0)
    (hspan : ∃ g : Fin 4 → H (fRev k), SelmerSpan (fRev k) g ∧
      ∀ j, Hmap σ (fRev k) (g j) = ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ D.SB i j)
    (hind : ∀ c : Fin 7 → ℤ,
      ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt i)) ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i)
    (hchart : LogChartFin lam)
    (hM : M4Rest σ (fRev k) (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb φ xa xb lam Dpt D lamD Twist
      disc par) :
    TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb := by
  obtain ⟨hK2, hInd⟩ := selmer_and_indep σ (fRev k) Dpt hL hspan hind
  have hL1 : LocalTwoTorsion ((fRev k).map σ)
      (jacMap σ (fRev k) (Tpt (fRev k) (q_monic k) (q_dvd_fRev k) (q_natDegree k))) :=
    localTwoTorsion_of_L1Inputs σ (fRev k) (q_monic k) (q_dvd_fRev k) (q_natDegree k)
      (l1Inputs σ k hloc.irr hloc.nsq)
  have hLam : FurioLombardo.M4.HLam lam Dpt :=
    hLam_of_chartFin hchart (two_torsion_of_localTwoTorsion hL1) hInd
  exact twistRoute_of_M4 σ (fRev k) (q_monic k) (q_dvd_fRev k) (q_natDegree k) φ xa xb lam Dpt hD
    hQ ⟨xtKernel_fRev k hPS, hK2, hL1, logKernelTorsion_of_chart (logChart_of_fin hchart)⟩
    (hM.toM4Inputs hLam)

/-- The hypotheses of `twistRoute_fRev` for the twist `k` with data `D`, Abel-Prym map `φ` and known
lifts `xa`, `xb`: some completion `σ : K21 → k_v` with the local facts, `PoonenSchaefer (fRev k)`, the
Selmer bound, the local points `D_i` with independent `x - T` images, a logarithm with `LogChartFin` and
lane M4's hypotheses. -/
def TwistInputs (k : Fin 2) (D : FurioLombardo.M4.TwistData) (Pa Pb : ℚ × ℚ × ℚ)
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
    M4Rest σ (fRev k) (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb φ xa xb lam Dpt D lamD Twist disc par

theorem twistRoute_of_twistInputs {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    {Pa Pb : ℚ × ℚ × ℚ} {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    (hD : FurioLombardo.M4.TwistChecks D) (hQ : QuarterFrom D) {L : Matrix (Fin 4) (Fin 7) ℤ}
    (hL : ∀ a b : Fin 4, (2 : ℤ) ∣ (L * D.SB) a b - if a = b then 1 else 0)
    (h : TwistInputs k D Pa Pb φ xa xb) : TwistRoute (Mmat 0) (Mmat 1) (Mmat 2) (δ k) Pa Pb := by
  obtain ⟨kv, _, σ, _, lam, Dpt, lamD, Twist, disc, par, hloc, hPS, hspan, hind, hchart, hM⟩ := h
  exact twistRoute_fRev σ k hloc hPS φ xa xb lam Dpt hD hQ hL hspan hind hchart hM

/-- **The frozen statement from the concrete inputs.** M1's descent for Bruin's quadrics (matrices
`Mmat`, twists `δ0`, `δ1`) and, for each twist, `TwistInputs` with lane M4's data and the known
lifts (`x0`, `x2` over `(0:0:1)`, `(2:0:1)`; `x1`, `x3` over `(1:1:1)`, `(-1:0:1)`) give
`FurioLombardo.OnlyFourPoints`, for any Abel-Prym maps `φ0`, `φ1` satisfying the inputs. -/
theorem onlyFourPoints_fRev (hdesc : Descent K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 δ1)
    (φ0 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 → Jac (fRev 0))
    (φ1 : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1 → Jac (fRev 1))
    (h0 : TwistInputs 0 FurioLombardo.M4.T0.data (0, 0, 1) (2, 0, 1) φ0 x0 x2)
    (h1 : TwistInputs 1 FurioLombardo.M4.T1.data (1, 1, 1) (-1, 0, 1) φ1 x1 x3) :
    FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_of_route hdesc
    (twistRoute_of_twistInputs FurioLombardo.M4.T0.checks
      (fun hBD hBP ha hb => Q0.quarter hBD hBP ha hb) FurioLombardo.M4.T0.hSBL h0)
    (twistRoute_of_twistInputs FurioLombardo.M4.T1.checks
      (fun hBD hBP ha hb => Q1.quarter hBD hBP ha hb) FurioLombardo.M4.T1.hSBL h1)

end Bruin

end FurioLombardo.Discharge.M3a
