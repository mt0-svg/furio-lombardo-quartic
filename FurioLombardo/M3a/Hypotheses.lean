import Mathlib
import FurioLombardo.M3a.XminusT
import FurioLombardo.M3a.TwoTorsion
import FurioLombardo.M3a.StollSat
import FurioLombardo.M3a.Sections

/-!
# Named hypotheses of the route (lane M3a)

Every input of the route (see the paper) that lane M3a does not prove is one of the
`Prop`s below. Setting, for one twist `δ`: `k` the global field (`K21`), `k_v` its completion at
the place `v` above 2, `σ : k →+* k_v`, `f` the reversed Prym sextic `f_δ^rev` over `k` (so that
`GoodSextic f` and `GoodSextic (f.map σ)` hold), `A(k) = Jac f`,
`A(k_v) = Jac (f.map σ)`, `ι = jacMap σ f`, `μ = muJ f`, `λ : A(k_v) → V = ℤ_[2]^6` the
logarithm (coordinates of lane M4), `Λ, S ⊆ V` the lattice `log A(k_v)` and its saturated
submodule, `W ⊆ V` the representatives of `ρ(σ_v(Sel²))`, `φ : D_δ(k) → A(k)` the Abel-Prym map
and `x_a, x_b` the two known lifts.

Global:

* `XTKernel f` (K1): the kernel of `μ = x - T` on `A(k)` is `2A(k)`;
* `SelmerInjective σ f` (K2): `μ(Q)` trivial at `v` implies `μ(Q)` trivial (localisation is
  injective on the image of `μ`, from `dim Sel² = 4` and the injectivity of `σ_v`);
* `SelmerW ι λ W`: every global logarithm is congruent modulo `2 log A(k_v)` to an element of `W`.

Local at `v`:

* `LocalTwoTorsion f Tv` (L1): the 2-power torsion of `A(k_v)` is `{0, T_v}`;
* `LogKernelTorsion λ` (L2): `λ` kills only torsion points;
* `LogRange λ Λ`: `Λ` is exactly the image of `λ`;
* `Saturated Λ S` (from lane M4's `HSat`), `λ(ι φ(x_a)), λ(ι φ(x_b)) ∈ S`;
* `Quarter Λ S a b` (L3): the elementary divisors of `span {a, b}` in `S` are `1, 4`: some
  `r ∈ Λ` has `4 r ∈ ℤa + ℤb` and `S ⊆ span {a, b, r}`.

Local at `v` (lane M4's `cover_iii` and the link between its analytic branch and `φ`):

* `CoverIII Λ S W y`: condition (iii) holds at `y(x) = λ(ι(φ(x) - φ(x_a)))` for every lift `x`
  (every point of `D_δ(k)` above a rational point of `C`, type `Lift`);
* `KnownZero S y Good`: `y(x) ∈ S` only for the lifts over the two known points.

The descent (lane M1): `FurioLombardo.M3a.Descent`.

For the two twists of the problem all of them are proved in the Discharge/ tree; the route of the
frozen statement is Discharge/M4Box/ChainM3a.lean, assembled in Discharge/M4Box/Final.lean.
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.M3a.Route

section Global

variable {k kv : Type*} [Field k] [Field kv]

/-- The localisation `ι : A(k) → A(k_v)`, additively. -/
noncomputable abbrev iotaA (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)] :
    Additive (Jac f) →+ Additive (Jac (f.map σ)) :=
  (jacMap σ f).toAdditive

/-- (K1) The kernel of the `x - T` map on `A(k)` is `2A(k)`. -/
def XTKernel (f : k[X]) [GoodSextic f] : Prop :=
  ∀ Q : Jac f, muJ f Q = 1 → ∃ R : Jac f, Q = R ^ 2

/-- (K2) The localisation `H f → H (f.map σ)` is injective on the image of `μ` on `A(k)`. -/
def SelmerInjective (σ : k →+* kv) (f : k[X]) [GoodSextic f] : Prop :=
  ∀ Q : Jac f, Hmap σ f (muJ f Q) = 1 → muJ f Q = 1

end Global

section Local

variable {kv : Type*} [Field kv]

/-- (L1) Every 2-power torsion point of `A(k_v)` is `0` or `T_v`. -/
def LocalTwoTorsion (f : kv[X]) [GoodSextic f] (Tv : Jac f) : Prop :=
  ∀ b : Jac f, (∃ n : ℕ, b ^ (2 ^ n) = 1) → b = 1 ∨ b = Tv

/-- (L2) The logarithm kills only torsion points. -/
def LogKernelTorsion {V : Type*} [AddCommGroup V] (f : kv[X]) [GoodSextic f]
    (lam : Additive (Jac f) →+ V) : Prop :=
  ∀ b : Additive (Jac f), lam b = 0 → ∃ n : ℕ, 0 < n ∧ n • b = 0

end Local

section Lattice

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

/-- `Λ` is the image of the logarithm `lam`. -/
def LogRange {B : Type*} [AddCommGroup B] (lam : B →+ V) (Λ : Submodule ℤ_[2] V) : Prop :=
  ∀ l : V, l ∈ Λ ↔ ∃ b : B, lam b = l

/-- Every global logarithm is congruent modulo `2 lam(B)` to an element of `W`. -/
def SelmerW {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B) (lam : B →+ V)
    (W : Set V) : Prop :=
  ∀ Q : A, ∃ w ∈ W, ∃ b : B, lam (ι Q) = w + (2 : ℕ) • lam b

/-- (L3) The lattice fact: some `r ∈ Λ` has `4 r = n a + m b` and `S ⊆ span {a, b, r}`. -/
def Quarter (Λ S : Submodule ℤ_[2] V) (a b : V) : Prop :=
  ∃ n m : ℤ, ∃ r ∈ Λ, (4 : ℤ_[2]) • r = n • a + m • b ∧ S ≤ Submodule.span ℤ_[2] {a, b, r}

/-- Condition (iii) at `y x` for every lift `x`. -/
def CoverIII {Dk : Type*} (Λ S : Submodule ℤ_[2] V) (W : Set V) (y : Dk → V) : Prop :=
  ∀ x : Dk, CondIII Λ S W (y x)

/-- (C2): `y x ∈ S` only when `x` is good (lies over a known point). -/
def KnownZero {Dk : Type*} (S : Submodule ℤ_[2] V) (y : Dk → V) (Good : Dk → Prop) : Prop :=
  ∀ x : Dk, y x ∈ S → Good x

end Lattice

section Twist

variable {k : Type*} [Field k] [Algebra ℚ k]

/-- The points of `D_δ(k)` above a rational point of `C` (its lifts). -/
def Lift (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) : Type _ :=
  {d : DPoint k M1 M2 M3 δ // ∃ x y z : ℚ, d.Over x y z}

/-- A lift `d ∈ D_δ(k)` is good if every rational point below it is `Pa` or `Pb`. -/
def GoodLift {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} (Pa Pb : ℚ × ℚ × ℚ)
    (d : DPoint k M1 M2 M3 δ) : Prop :=
  ∀ x y z : ℚ, d.Over x y z → FurioLombardo.SameProjPoint x y z Pa ∨
    FurioLombardo.SameProjPoint x y z Pb

/-- All inputs of the route for one twist `δ`, for given data: the completion `σ : k → k_v`,
the reversed Prym sextic `f` with its monic quadratic factor `q` (so `T = [⟨q, Y⟩]`), the
Abel-Prym map `φ`, the known lifts `xa`, `xb`, the logarithm `lam`, the lattice `Λ`, its
saturated submodule `S` and the Selmer representatives `W`. -/
structure Inputs {kv : Type*} [Field kv] (σ : k →+* kv) (f : k[X]) [GoodSextic f]
    [GoodSextic (f.map σ)] {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) (Pa Pb : ℚ × ℚ × ℚ)
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2]))
    (W : Set (Fin 6 → ℤ_[2])) : Prop where
  xtKernel : XTKernel f
  selmerInjective : SelmerInjective σ f
  localTwoTorsion : LocalTwoTorsion (f.map σ) (jacMap σ f (Tpt f hq hqf hdeg))
  logKernelTorsion : LogKernelTorsion (f.map σ) lam
  logRange : LogRange lam Λ
  saturated : Saturated Λ S
  mem_a : lam (Additive.ofMul (jacMap σ f (φ xa))) ∈ S
  mem_b : lam (Additive.ofMul (jacMap σ f (φ xb))) ∈ S
  selmerW : SelmerW (iotaA σ f) lam W
  quarter : Quarter Λ S (lam (Additive.ofMul (jacMap σ f (φ xa))))
    (lam (Additive.ofMul (jacMap σ f (φ xb))))
  coverIII : CoverIII Λ S W
    (fun x : Lift M1 M2 M3 δ => lam (Additive.ofMul (jacMap σ f (φ x.1 / φ xa))))
  knownZero : KnownZero S
    (fun x : Lift M1 M2 M3 δ => lam (Additive.ofMul (jacMap σ f (φ x.1 / φ xa))))
    (fun x => GoodLift Pa Pb x.1)

/-- The route for the twist `δ` with known points `Pa`, `Pb`: some
completion, reversed Prym sextic with a monic quadratic factor, Abel-Prym map, known lifts,
logarithm and lattices satisfy all the inputs. -/
def TwistRoute (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k) (δ : k) (Pa Pb : ℚ × ℚ × ℚ) : Prop :=
  ∃ (kv : Type) (_ : Field kv) (σ : k →+* kv) (f : k[X]) (_ : GoodSextic f)
    (_ : GoodSextic (f.map σ)) (q : k[X]) (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (φ : DPoint k M1 M2 M3 δ → Jac f) (xa xb : DPoint k M1 M2 M3 δ)
    (lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])) (Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2]))
    (W : Set (Fin 6 → ℤ_[2])),
    Inputs σ f hq hqf hdeg M1 M2 M3 δ Pa Pb φ xa xb lam Λ S W

end Twist

end FurioLombardo.M3a.Route
