import Mathlib
import FurioLombardo.Discharge.M4Log.BranchData
import FurioLombardo.Discharge.R7.Transfer
import FurioLombardo.Discharge.M3a.ConcretePhi

/-!
# Lane M4's logarithm at `v` through R7's chart: the definitions `lam`, `lamD` (lane lean-m4log)

For the twist `k : Fin 2` let `F = (fRev k)^σ` be the reversed Prym sextic over `K_v` and
`baseKv k` R7's base point datum (`f_k = F(X + a_k)`, `a_k = k`, `b_k² = f_k(0)`), with chart
`ψ z = [X² + t₀ X + t₁, v(t)] - E0`, `t = π^M z`, at an admissible exponent `M`
(R7/Psi.lean `Setup.Adm`, `Setup.psi`).

* `M0 k` (`8`, `0`) and the named statement `AdmM0 k`: `M0 k` is admissible (proved as
  `IntModelKv.admM0`, IntModelKv.lean).
* `Amat k = (1/b_k) [[a, 1 + a g₁], [1, g₁]]`, `g₁ = -f_k'(0) / (2 f_k(0))`: the linear part, in the
  chart coordinates `t`, of lane M4's logarithm `(∫ dx/y, ∫ x dx/y)` on the original model
  `y² = F_k(x)` (on the reversed model `(∫ -X dX/Y, ∫ -dX/Y)`, `x = 1/X`, `y = Y/X³`), summed over the
  two points of the chart divisor from the base point `(a_k, b_k)`.
* `lamK k : Jac(F) →+ K_v²`: on the chart ball, `lamK (ψ z) = π^(M0 + 4) Amat (logVal y)` for
  `z = π⁴ y` (`lamK_chart`), `logVal` the scaled logarithm of the integral formal group law of the chart;
  elsewhere by divisibility (R7's `exists_logChartFin_of_chart`, the index of `ψ(B1)`). With `logVal`
  normalized by `log(t) = t + O(t²)` this is `Amat · log_G(t)`, `G` the chart law. `lamK` does not
  depend on the square root `b_k` chosen by `bK` (changing `b_k` to `-b_k` negates both `ψ` and
  `Amat`).
* `LamInt k`: every value of `lamK k` lies in `O_v²` (named statement, proved by `lamInt_of`,
  LamInt.lean, from the bounds on the `lamK k (D_i)`), and
  `lam k = coordEquiv ∘ lamK k` (coordinates on `1, π, π²`, component `i`, slot `3 i + j`) when it
  holds, `0` otherwise (`lam_toKv2`).
* `lamD k d X = lam k (φ_v(x) - φ(x_a))`, the branch of lane M4: `x` is the point of `D_δ(K_v)` over
  the disc point `p = discPt d X Y` (`Y` a root of `F(discPt d X Y) = 0`, `pKv`) on the branch of the
  first box of `branchTable k` containing `X`: `|r - ρ_B| < |r + ρ_B|` (or the same with `s`), `ρ_B`
  the table's reference root; `φ_v` is Bruin's Abel-Prym map on the reversed model over `K_v`
  (`AbelPrym.phiRev`), `x_a = x0` (`k = 0`), `x1` (`k = 1`). `0` where no such point exists.
  `lamD_eq`: the value at any point on the branch.

The identification of `lam` with lane M4's analytic logarithm (formal Abel) is not used: the values
of `lam` at the points of lane M4's certificates are computed from the chart.
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.FormalGroup
open FurioLombardo.Discharge.M4Cert
open FurioLombardo.Discharge.M3a.Bruin (fRev Mmat δ phiK x0 x1 goodSextic_fRev_Kv)
open FurioLombardo.Discharge.R7 FurioLombardo.Discharge.R7.ConcreteKv

namespace FurioLombardo.Discharge.M4Log

attribute [local instance] goodSextic_fRev_Kv

/-! ## The chart at the explicit exponent -/

/-- The explicit admissible exponents: `8` for the twist `0`, `0` for the twist `1`. -/
def M0 : Fin 2 → ℕ := ![8, 0]

/-- **`M0 k` is admissible** for the chart of `baseKv k` (named statement; proved as
`IntModelKv.admM0`). -/
abbrev AdmM0 (k : Fin 2) : Prop := (baseKv k).toSetup.Adm (M0 k)

/-- The scaling `c = π⁴` of R7's ball `B1`. -/
noncomputable abbrev cB : OKv := pvO ^ (3 + 1)

/-- The integral formal group law of the chart at `M0 k`. -/
noncomputable abbrev fgl (k : Fin 2) (h : AdmM0 k) :
    FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw OKv (Fin 2) :=
  (baseKv k).toSetup.fglO h.good

/-- The chart homomorphism at `M0 k`. -/
noncomputable abbrev chart (k : Fin 2) (h : AdmM0 k) :
    (fgl k h).Points →+ Additive (Jac ((fRev k).map σ)) :=
  (baseKv k).toSetup.psi (hF k) h

/-- The scaled logarithm of the chart law at `y`, in `K_v²`. -/
noncomputable def logK (k : Fin 2) (h : AdmM0 k) (y : Fin 2 → OKv) : Fin 2 → Kv :=
  fun i => ((FurioLombardo.Vendor.Toolbox.FormalGroup.logVal (fgl k h) (unitBall Kv).subtype cB y i : OKv) : Kv)

/-! ## The normalization of lane M4 -/

/-- `g₁ = -f_k'(0) / (2 f_k(0))`, the coefficient of `s` in `(f_k(s) / f_k(0))^(-1/2)`. -/
noncomputable def g1K (k : Fin 2) : Kv := -(fK k).coeff 1 / (2 * (fK k).coeff 0)

/-- The linear part of lane M4's logarithm in the chart coordinates `(t₀, t₁)`: rows `λ₁, λ₂`. -/
noncomputable def Amat (k : Fin 2) : Matrix (Fin 2) (Fin 2) Kv :=
  (bK k)⁻¹ • !![aK k, 1 + aK k * g1K k; 1, g1K k]

/-! ## The logarithm `lamK` with values in `K_v²` -/

/-- R7's logarithmic chart at `M0 k`: a logarithm `lam` with `LogChartFin`, the subgroup
`H' = ψ(B1)` of finite index and `lam (ψ z) = [Jac : H'] • coordEquiv (logVal y)`. -/
theorem exists_chart (k : Fin 2) (h : AdmM0 k) :
    ∃ lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]), Analytic.LogChartFin lam ∧
      ∃ H' : AddSubgroup (Additive (Jac ((fRev k).map σ))),
        (H' : Set (Additive (Jac ((fRev k).map σ)))) =
          chart k h '' (B1 (fgl k h) cB : Set (fgl k h).Points) ∧
        H'.FiniteIndex ∧
        ∀ z ∈ B1 (fgl k h) cB, ∀ y : Fin 2 → OKv, (∀ j, (z j : OKv) = cB * y j) →
          lam (chart k h z) = H'.index • coordEquiv (FurioLombardo.Vendor.Toolbox.FormalGroup.logVal (fgl k h) (unitBall Kv).subtype cB y) :=
  exists_logChartFin_of_chart (fgl k h) (chart k h) ((baseKv k).toSetup.psi_injective (hF k) h)
    (FinIdx.hFinIdx_of_setupKv (baseKv k) _ (aK k) (hF k) h)

/-- R7's logarithm at `M0 k`. -/
noncomputable def lamR (k : Fin 2) (h : AdmM0 k) :
    Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]) :=
  (exists_chart k h).choose

/-- The subgroup `ψ(B1)`. -/
noncomputable def HR (k : Fin 2) (h : AdmM0 k) : AddSubgroup (Additive (Jac ((fRev k).map σ))) :=
  (exists_chart k h).choose_spec.2.choose

theorem lamR_chart (k : Fin 2) (h : AdmM0 k) :
    ∀ z ∈ B1 (fgl k h) cB, ∀ y : Fin 2 → OKv, (∀ j, (z j : OKv) = cB * y j) →
      lamR k h (chart k h z) =
        (HR k h).index • coordEquiv (FurioLombardo.Vendor.Toolbox.FormalGroup.logVal (fgl k h) (unitBall Kv).subtype cB y) :=
  (exists_chart k h).choose_spec.2.choose_spec.2.2

theorem index_HR_ne_zero (k : Fin 2) (h : AdmM0 k) : (HR k h).index ≠ 0 :=
  (exists_chart k h).choose_spec.2.choose_spec.2.1.index_ne_zero

/-- `ℤ_[2]⁶ → K_v²`, the inverse of `coordEquiv` followed by `O_v ⊂ K_v`. -/
noncomputable def toKv2 : (Fin 6 → ℤ_[2]) →+ (Fin 2 → Kv) :=
  (AddMonoidHom.compLeft (unitBall Kv).subtype.toAddMonoidHom (Fin 2)).comp
    (coordEquiv.symm : (Fin 6 → ℤ_[2]) ≃+ (Fin 2 → OKv)).toAddMonoidHom

theorem toKv2_coordEquiv (x : Fin 2 → OKv) : toKv2 (coordEquiv x) = fun i => (x i : Kv) := by
  funext i
  simp [toKv2]

theorem toKv2_injective : Function.Injective toKv2 := by
  intro a b hab
  apply coordEquiv.symm.injective
  funext i
  exact Subtype.ext (congrFun hab i)

/-- The matrix of `lamK` on the image of R7's logarithm: `[Jac : H']⁻¹ π^(M0 + 4) Amat`. -/
noncomputable def chartMat (k : Fin 2) (n : ℕ) : Matrix (Fin 2) (Fin 2) Kv :=
  ((n : Kv)⁻¹ * pv ^ (M0 k + 4)) • Amat k

/-- **Lane M4's logarithm through R7's chart**, with values in `K_v²` (`0` if `M0 k` is not
admissible). -/
noncomputable def lamK (k : Fin 2) : Additive (Jac ((fRev k).map σ)) →+ (Fin 2 → Kv) :=
  open Classical in
  if h : AdmM0 k then
    ((chartMat k (HR k h).index).mulVecLin.toAddMonoidHom).comp (toKv2.comp (lamR k h))
  else 0

/-- **The chart formula**: on the ball `B1`, `lamK (ψ z) = π^(M0 + 4) Amat (logVal y)` for
`z = π⁴ y`. -/
theorem lamK_chart (k : Fin 2) (h : AdmM0 k) (z : (fgl k h).Points) (hz : z ∈ B1 (fgl k h) cB)
    (y : Fin 2 → OKv) (hy : ∀ j, (z j : OKv) = cB * y j) :
    lamK k (chart k h z) = (pv ^ (M0 k + 4) • Amat k) *ᵥ logK k h y := by
  have hn : ((HR k h).index : Kv) ≠ 0 := Nat.cast_ne_zero.mpr (index_HR_ne_zero k h)
  rw [lamK, dite_eq_left_of_eq_true (eq_true h)]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    Matrix.mulVecLin_apply]
  rw [lamR_chart k h z hz y hy, map_nsmul, toKv2_coordEquiv, chartMat, Matrix.mulVec_smul,
    ← Nat.cast_smul_eq_nsmul Kv, Matrix.smul_mulVec, Matrix.smul_mulVec, smul_smul]
  congr 1
  field_simp

/-! ## Integrality and the logarithm `lam` -/

/-- **Every value of `lamK k` lies in `O_v²`** (named statement; proved by `lamInt_of`). -/
def LamInt (k : Fin 2) : Prop := ∀ b i, ‖lamK k b i‖ ≤ 1

/-- `lamK` with values in `O_v²`, under `LamInt`. -/
noncomputable def lamO (k : Fin 2) (hI : LamInt k) :
    Additive (Jac ((fRev k).map σ)) →+ (Fin 2 → OKv) where
  toFun b i := ⟨lamK k b i, mem_unitBall_iff.mpr (hI b i)⟩
  map_zero' := by
    funext i
    exact Subtype.ext (by simp)
  map_add' a b := by
    funext i
    exact Subtype.ext (by simp)

/-- **Lane M4's logarithm at `v`**, in the coordinates of `O_v²` on `1, π, π²` (`0` unless
`LamInt k`). -/
noncomputable def lam (k : Fin 2) : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]) :=
  open Classical in
  if hI : LamInt k then coordEquiv.toAddMonoidHom.comp (lamO k hI) else 0

theorem lam_toKv2 (k : Fin 2) (hI : LamInt k) (b : Additive (Jac ((fRev k).map σ))) :
    toKv2 (lam k b) = lamK k b := by
  rw [lam, dite_eq_left_of_eq_true (eq_true hI)]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [toKv2_coordEquiv]
  rfl

/-- **The chart formula for `lam`.** -/
theorem lam_chart (k : Fin 2) (h : AdmM0 k) (hI : LamInt k) (z : (fgl k h).Points)
    (hz : z ∈ B1 (fgl k h) cB) (y : Fin 2 → OKv) (hy : ∀ j, (z j : OKv) = cB * y j) :
    toKv2 (lam k (chart k h z)) = (pv ^ (M0 k + 4) • Amat k) *ᵥ logK k h y := by
  rw [lam_toKv2 k hI, lamK_chart k h z hz y hy]

/-! ## The analytic branch `lamD` -/

/-- A root `Y ∈ ℤ_[2]` of `F(discPt d X Y) = 0` (`0` if there is none). -/
noncomputable def discY (d : ℕ) (X : ℤ_[2]) : ℤ_[2] :=
  open Classical in
  if h : ∃ Y : ℤ_[2], FurioLombardo.F (discPt d X Y 0) (discPt d X Y 1) (discPt d X Y 2) = 0 then
    h.choose
  else 0

/-- The point of parameter `X` of the disc `d` of `C(ℚ_2)`, in `K_v³`. -/
noncomputable def pKv (d : ℕ) (X : ℤ_[2]) : Fin 3 → Kv := fun i => toKv (discPt d X (discY d X) i)

/-- The points of `D_δ(K_v)` for the twist `k`. -/
abbrev DPtKv (k : Fin 2) : Type :=
  DPoint Kv ((Mmat 0).map σ) ((Mmat 1).map σ) ((Mmat 2).map σ) (σ (δ k))

/-- Bruin's Abel-Prym map over `K_v`, on the reversed model. -/
noncomputable abbrev phiV (k : Fin 2) : DPtKv k → Jac ((fRev k).map σ) :=
  FurioLombardo.Discharge.M3a.AbelPrym.phiRev ((Mmat 0).map σ) ((Mmat 1).map σ) ((Mmat 2).map σ) (σ (δ k)) ((fRev k).map σ)

/-- The base lift `x_a` of the twist: `x0` for `k = 0`, `x1` for `k = 1`. -/
noncomputable def xa : (k : Fin 2) → DPoint FurioLombardo.M1.K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)
  | 0 => x0
  | 1 => x1

/-- The reference root of a box of the branch table. -/
noncomputable def rhoK (e : BranchBox) : Kv := evZ e.rho / pv ^ e.e

/-- The point `x` is on the branch of the box `e`. -/
def BranchOK {k : Fin 2} (e : BranchBox) (x : DPtKv k) : Prop :=
  if e.wh then ‖x.r - rhoK e‖ < ‖x.r + rhoK e‖ else ‖x.s - rhoK e‖ < ‖x.s + rhoK e‖

/-- The box of the branch table used at `(d, X)`: the first one of disc `d` containing `X`. -/
noncomputable def boxAt (k : Fin 2) (d : ℕ) (X : ℤ_[2]) : Option BranchBox :=
  open Classical in
  (branchTable k).find? fun e => e.disc == d && decide (FurioLombardo.M4.InBox X e.c e.s)

/-- The logarithm of `φ_v(x) - φ(x_a)`. -/
noncomputable def lamPt (k : Fin 2) (x : DPtKv k) : Fin 6 → ℤ_[2] :=
  lam k (Additive.ofMul (phiV k x) -
    Additive.ofMul (jacMap σ (fRev k) (phiK k (xa k))))

/-- **The analytic branch of lane M4**: `lam (φ_v(x) - φ(x_a))` at the point `x` of `D_δ(K_v)`
over `pKv d X` on the branch of the box of `(d, X)`; `0` if there is no box or no such point. -/
noncomputable def lamD (k : Fin 2) (d : ℕ) (X : ℤ_[2]) : Fin 6 → ℤ_[2] :=
  open Classical in
  match boxAt k d X with
  | none => 0
  | some e =>
    if h : ∃ x : DPtKv k, x.p = pKv d X ∧ BranchOK e x then lamPt k h.choose else 0

/-! ## The value of `lamD` at a point on the branch -/

/-- Two points of `D_δ` over the same point of `C` agree up to the covering involution. -/
theorem eq_or_eq_neg_of_p_eq {L : Type*} [Field L] {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {d : L}
    (hd : d ≠ 0) (h2 : (2 : L) ≠ 0) (x y : DPoint L M1 M2 M3 d) (h : x.p = y.p) :
    (x.r = y.r ∧ x.s = y.s) ∨ (x.r = -y.r ∧ x.s = -y.s) := by
  have e1 : d * x.r ^ 2 = d * y.r ^ 2 := by rw [← x.eq1, ← y.eq1, h]
  have e2 : d * (x.r * x.s) = d * (y.r * y.s) := by rw [← x.eq2, ← y.eq2, h]
  have e3 : d * x.s ^ 2 = d * y.s ^ 2 := by rw [← x.eq3, ← y.eq3, h]
  have h1 : x.r ^ 2 = y.r ^ 2 := mul_left_cancel₀ hd e1
  have hm : x.r * x.s = y.r * y.s := mul_left_cancel₀ hd e2
  have h3 : x.s ^ 2 = y.s ^ 2 := mul_left_cancel₀ hd e3
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with hr | hr <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h3 with hs | hs
  · exact Or.inl ⟨hr, hs⟩
  · -- `x.r = y.r`, `x.s = -y.s`: then `2 y.r y.s = 0`
    have h0 : y.r * y.s = 0 := by
      have : (2 : L) * (y.r * y.s) = 0 := by rw [hr, hs] at hm; linear_combination -hm
      exact (mul_eq_zero.mp this).resolve_left h2
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact Or.inr ⟨by rw [hr, h0, neg_zero], hs⟩
    · exact Or.inl ⟨hr, by rw [hs, h0, neg_zero]⟩
  · have h0 : y.r * y.s = 0 := by
      have : (2 : L) * (y.r * y.s) = 0 := by rw [hr, hs] at hm; linear_combination -hm
      exact (mul_eq_zero.mp this).resolve_left h2
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact Or.inl ⟨by rw [hr, h0, neg_zero], hs⟩
    · exact Or.inr ⟨hr, by rw [hs, h0, neg_zero]⟩
  · exact Or.inr ⟨hr, hs⟩

theorem DPoint.ext' {L : Type*} [Field L] {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {d : L}
    {x y : DPoint L M1 M2 M3 d} (hp : x.p = y.p) (hr : x.r = y.r) (hs : x.s = y.s) : x = y := by
  cases x; cases y
  simp only at hp hr hs
  subst hp hr hs
  rfl

theorem σδ_ne_zero (k : Fin 2) : σ (δ k) ≠ 0 :=
  (map_ne_zero σ).mpr (FurioLombardo.Discharge.M3a.Bruin.δ_ne_zero k)

/-- **A branch has at most one point over a given point of `C`.** -/
theorem branch_unique {k : Fin 2} {e : BranchBox} {x y : DPtKv k} (hp : x.p = y.p)
    (hx : BranchOK e x) (hy : BranchOK e y) : x = y := by
  rcases eq_or_eq_neg_of_p_eq (σδ_ne_zero k) FurioLombardo.Discharge.M3a.Bruin.two_ne_zero_Kv
    x y hp with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · exact DPoint.ext' hp hr hs
  · exfalso
    unfold BranchOK at hx hy
    split_ifs at hx hy
    · rw [hr, show -y.r - rhoK e = -(y.r + rhoK e) by ring,
        show -y.r + rhoK e = -(y.r - rhoK e) by ring, norm_neg, norm_neg] at hx
      exact lt_asymm hx hy
    · rw [hs, show -y.s - rhoK e = -(y.s + rhoK e) by ring,
        show -y.s + rhoK e = -(y.s - rhoK e) by ring, norm_neg, norm_neg] at hx
      exact lt_asymm hx hy

/-- **The value of `lamD` on the branch**: if `e` is the box of `(d, X)` and `x` a point of
`D_δ(K_v)` over `pKv d X` on the branch of `e`, then `lamD k d X = lam (φ_v(x) - φ(x_a))`. -/
theorem lamD_eq {k : Fin 2} {d : ℕ} {X : ℤ_[2]} {e : BranchBox} (he : boxAt k d X = some e)
    (x : DPtKv k) (hx : x.p = pKv d X) (hb : BranchOK e x) : lamD k d X = lamPt k x := by
  have hex : ∃ x : DPtKv k, x.p = pKv d X ∧ BranchOK e x := ⟨x, hx, hb⟩
  unfold lamD
  rw [he]
  simp only
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  congr 1
  exact branch_unique (hex.choose_spec.1.trans hx.symm) hex.choose_spec.2 hb

/-! ## The box of a parameter -/

/-- Two boxes of the table are disjoint (different discs, or incongruent centres). -/
def boxDisj (e e' : BranchBox) : Bool :=
  e.disc != e'.disc || e.c % 2 ^ min e.s e'.s != e'.c % 2 ^ min e.s e'.s

/-- The boxes of the branch table of the twist `k` are pairwise disjoint (a finite check). -/
def TableDisjoint (k : Fin 2) : Prop := (branchTable k).Pairwise fun e e' => boxDisj e e' = true

instance (k : Fin 2) : Decidable (TableDisjoint k) := by unfold TableDisjoint; infer_instance

theorem boxDisj_symm (e e' : BranchBox) : boxDisj e e' = boxDisj e' e := by
  unfold boxDisj
  rw [Nat.min_comm]
  cases h1 : (e.disc != e'.disc) <;> cases h2 : (e'.disc != e.disc) <;>
    cases h3 : (e.c % 2 ^ min e'.s e.s != e'.c % 2 ^ min e'.s e.s) <;>
    cases h4 : (e'.c % 2 ^ min e'.s e.s != e.c % 2 ^ min e'.s e.s) <;> simp_all [bne_iff_ne, ne_comm]

/-- A parameter in two boxes: the centres are congruent modulo `2 ^ min s s'`. -/
theorem mod_eq_of_inBox {X : ℤ_[2]} {c s c' s' : ℕ} (h : FurioLombardo.M4.InBox X c s)
    (h' : FurioLombardo.M4.InBox X c' s') : c % 2 ^ min s s' = c' % 2 ^ min s s' := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨y', hy'⟩ := h'
  have hd : (2 : ℤ_[2]) ^ min s s' ∣ (((c' : ℤ) - (c : ℤ) : ℤ) : ℤ_[2]) := by
    have e : (((c' : ℤ) - (c : ℤ) : ℤ) : ℤ_[2]) = 2 ^ s * y - 2 ^ s' * y' := by
      push_cast
      linear_combination hy - hy'
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow 2 (min_le_left s s')) y)
      (dvd_mul_of_dvd_left (pow_dvd_pow 2 (min_le_right s s')) y')
  rw [two_pow_dvd_intCast_iff] at hd
  have : c ≡ c' [MOD 2 ^ min s s'] := (Nat.modEq_iff_dvd).mpr (by exact_mod_cast hd)
  exact this

/-- **The box of `(d, X)`** is any box of the table of disc `d` containing `X`, when the boxes are
pairwise disjoint. -/
theorem boxAt_eq {k : Fin 2} (hD : TableDisjoint k) {e : BranchBox} (he : e ∈ branchTable k)
    {d : ℕ} {X : ℤ_[2]} (hd : e.disc = d) (hX : FurioLombardo.M4.InBox X e.c e.s) :
    boxAt k d X = some e := by
  classical
  have hp : ∀ e' : BranchBox, (e'.disc == d && decide (FurioLombardo.M4.InBox X e'.c e'.s)) = true ↔
      e'.disc = d ∧ FurioLombardo.M4.InBox X e'.c e'.s := fun e' => by simp
  unfold boxAt
  cases hf : (branchTable k).find? (fun e => e.disc == d && decide (FurioLombardo.M4.InBox X e.c e.s)) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hf
    exact hf e he (by rw [hp]; exact ⟨hd, hX⟩)
  | some e' =>
    congr 1
    have h0 := List.find?_some hf
    have h1 := (hp e').mp h0
    have hm := List.mem_of_find?_eq_some hf
    by_contra hne
    have : Std.Symm (fun e e' : BranchBox => boxDisj e e' = true) :=
      ⟨fun a b hab => by rw [boxDisj_symm]; exact hab⟩
    have hdisj := hD.forall hm he hne
    unfold boxDisj at hdisj
    rw [Bool.or_eq_true, bne_iff_ne, bne_iff_ne] at hdisj
    rcases hdisj with h2 | h2
    · exact h2 (h1.1.trans hd.symm)
    · exact h2 (mod_eq_of_inBox h1.2 hX)

/-- The boxes of each table are pairwise disjoint (kernel check on the generated table). -/
theorem tableDisjoint : ∀ k : Fin 2, TableDisjoint k := by
  intro k
  fin_cases k
  · decide +kernel
  · decide +kernel

/-- `boxAt_eq` for the generated tables. -/
theorem boxAt_eq_of_mem {k : Fin 2} {e : BranchBox} (he : e ∈ branchTable k) {d : ℕ} {X : ℤ_[2]}
    (hd : e.disc = d) (hX : FurioLombardo.M4.InBox X e.c e.s) : boxAt k d X = some e :=
  boxAt_eq (tableDisjoint k) he hd hX

end FurioLombardo.Discharge.M4Log
