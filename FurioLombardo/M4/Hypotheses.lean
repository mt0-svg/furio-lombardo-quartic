import Mathlib
import FurioLombardo.M4.Analytic

/-!
# The data of one twist, its finite checks, and the named hypotheses of lane M4

`TwistData` is the integer data of the certificates of one twist δ (instantiated for δ0 and δ1 in
`FurioLombardo.M4.Instances`), `TwistChecks` the finite facts about it proved by `decide +kernel`
(`FurioLombardo.M4.Checks`). The other inputs at `v` are named hypotheses (Props below), shared with lane M3a.
The analytic hypotheses come in two forms: `HSeries`, `HTail` (series form on a box, used by `cover_iii`) and
`HAntiConst`, `HAntiTail` (antiderivative form on the parent disc), from which the former are derived
(`hSeries_of_anti`, `hTail_of_anti` in `FurioLombardo.M4.Cover`).

The proof of the frozen statement proves the ones it needs for both twists in the Discharge/ tree
(assembled in Discharge/M4Box/Final.lean), with the analytic ones replaced by the weaker `HConstLip`,
`HTailQuad` (Discharge/M4Box/Weak.lean).
-/

namespace FurioLombardo.M4

/-- The integer data of the certificates of one twist δ (`FurioLombardo.M4.Data`). -/
structure TwistData where
  qD : Fin 7 → ℕ
  lD : Fin 7 → Fin 6 → ℤ
  qa : ℕ
  qb : ℕ
  la : Fin 6 → ℤ
  lb : Fin 6 → ℤ
  H : Matrix (Fin 6) (Fin 6) ℤ
  G : Matrix (Fin 6) (Fin 6) ℤ
  C : Matrix (Fin 6) (Fin 7) ℤ
  Cp : Matrix (Fin 7) (Fin 6) ℤ
  U : Matrix (Fin 6) (Fin 6) ℤ
  Ui : Matrix (Fin 6) (Fin 6) ℤ
  UG : Matrix (Fin 6) (Fin 6) ℤ
  Jab : ℕ
  Del : ℤ
  dl : ℕ
  r : ℕ
  sigE : Fin 2 → ℕ
  sigA : Fin 2 → ℤ
  sigB : Fin 2 → ℤ
  W : Fin 16 → Fin 6 → ℤ
  SB : Matrix (Fin 7) (Fin 4) ℤ
  excluded : List (ℕ × ℕ × ℕ)
  constant : List CBox
  tails : List TBox

/-- The finite checks on the data of one twist (all proved by `decide +kernel` in `FurioLombardo.M4.Checks`). -/
structure TwistChecks (D : TwistData) : Prop where
  cover : ∀ d ∈ [1, 2, 3, 4, 5], coverCheck (boxesOf D.excluded D.constant D.tails d) 12 0 0 = true
  hHG : D.H * D.G = (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ)
  hC : ∀ k j : Fin 6, (8 : ℤ) ∣ (∑ i, D.C k i * D.lD i j) - (if j = k then 4 else 0)
  hCp : ∀ j k : Fin 6, (4 : ℤ) ∣ D.H j k - ∑ i, D.lD i j * D.Cp i k
  hGl : ∀ (i : Fin 7) (j : Fin 6), (4 : ℤ) ∣ D.G.mulVec (D.lD i) j
  hUG : D.U * D.G = D.UG
  hid : D.H * D.Ui * D.UG = (4 * 1 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ)
  hGcol : ∀ j k : Fin 6, (4 : ℤ) ∣ (D.G * (D.H * D.Ui)) j k
  hDel : D.UG.mulVec D.la 0 * D.UG.mulVec D.lb 1 - D.UG.mulVec D.la 1 * D.UG.mulVec D.lb 0 = D.Del
  hdl : (2 : ℤ) ^ D.dl ∣ D.Del ∧ ¬ (2 : ℤ) ^ (D.dl + 1) ∣ D.Del
  hJab : ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ) ^ D.Jab ∣ D.UG.mulVec D.la o ∧ (2 : ℤ) ^ D.Jab ∣ D.UG.mulVec D.lb o
  hr : D.r + D.dl = min D.Jab (min D.qa D.qb) ∧ D.dl < min D.qa D.qb
  hsig : ∀ (j : Fin 2) (i : Fin 6), (2 : ℤ) ^ (D.r + D.sigE j + 2) ∣
    2 ^ D.sigE j * (D.H * D.Ui) i (Fin.castLE (by omega) j) - D.sigA j * D.la i - D.sigB j * D.lb i
  hsigq : ∀ j : Fin 2, D.r + D.sigE j + 2 ≤ D.qa ∧ D.r + D.sigE j + 2 ≤ D.qb
  hqD : ∀ i : Fin 7, 3 ≤ D.qD i
  centres : ∀ b ∈ D.constant, ClassOK D.UG D.W b.nu b.y ∧ b.nu + 3 ≤ b.q ∧ b.nu + 1 ≤ D.r ∧ b.vM % 3 = 0 ∧
    b.vM / 3 + b.s = b.nu + 3 ∧ 1 ≤ b.s
  centresMem : ∀ b ∈ D.constant, ∀ j : Fin 6, (4 : ℤ) ∣ D.G.mulVec b.y j
  tailsOK : ∀ b ∈ D.tails, ClassOK D.UG D.W b.nu b.g ∧ b.nu + 3 ≤ b.q ∧ b.nu + 1 ≤ D.r ∧ b.vM % 3 = 0 ∧
    1 ≤ b.s0 ∧ b.s0 ≤ b.s ∧ b.nu + 2 + b.s0 ≤ b.vM / 3 + b.s ∧ (b.c : ℤ) % 2 ^ b.s = b.Xi % 2 ^ b.s
  tailsVM : ∀ b ∈ D.tails, 3 ≤ b.vM
  hWc : ∀ (m : Fin 16) (o : Fin 6), D.W m o = ∑ i, selc D.SB m i * D.lD i o

/-! ## Named hypotheses

The analytic and structural inputs at `v` that are not checked here. `Λ` is `log A(k_v)` in the coordinates
`Fin 6 → ℤ_[2]` (O_v² on the basis 1, π, π²), `ℓ i = log D_i`, `a = log φ(x_a)`, `b = log φ(x_b)`,
`lam d X = log φ(x)` for the lift `x` on the chosen analytic branch over the point of parameter `X` of the disc `d`,
and `Twist d X` says that the point of parameter `X` of the disc `d` of `C(Q_2)` lifts to `D_δ(K_v)`. -/

/-- HGen: `log A(k_v)` is spanned by `log D_1, ..., log D_7` (the `D_i` generate `A(k_v)` modulo the kernel of the
logarithm). -/
def HGen (Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (ℓ : Fin 7 → Fin 6 → ℤ_[2]) : Prop :=
  Λ = Submodule.span ℤ_[2] (Set.range ℓ)

/-- HBallD: the certified balls of `log D_i` (code/earlier-computations/lattice_cert.gp). -/
def HBallD (D : TwistData) (ℓ : Fin 7 → Fin 6 → ℤ_[2]) : Prop :=
  ∀ i, DvdV (D.qD i) (ℓ i - icast (D.lD i))

/-- HBallPhi: the certified balls of `log φ(x_a)`, `log φ(x_b)` (code/earlier-computations/lattice_cert.gp). -/
def HBallPhi (D : TwistData) (a b : Fin 6 → ℤ_[2]) : Prop :=
  DvdV D.qa (a - icast D.la) ∧ DvdV D.qb (b - icast D.lb)

/-- HSat: `S = Ḡ_sat` is the saturation in `Λ` of the span of `log φ(x_a)` and `log φ(x_b)` (a definition of `S`). -/
def HSat (Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (a b : Fin 6 → ℤ_[2]) : Prop := IsSatOf Λ S a b

/-- HCentre: the certified balls of `λ` at the centres of the constant boxes (code/earlier-computations/centres_cert.gp). -/
def HCentre (D : TwistData) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ c ∈ D.constant, DvdV c.q (lam c.disc c.c - icast c.y)

/-- HSeries: on a constant box `{X = c + 2^s Y}`, `λ(c + 2^s Y) - λ(c) = Σ α_n Y^(n+1)` where the coefficient
`(n+1) α_n` of `Y^n` in `dλ/dY` has valuation at least `vM/3 + s + n` (the sup bound `|π|^vM` of `dλ/dX` on the parent
box of radius `2^-(s-1)`, and the antiderivative property on the open parent disc, KRZB Lemma 3.23). -/
def HSeries (D : TwistData) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ c ∈ D.constant, ∃ α : ℕ → Fin 6 → ℤ_[2],
    (∀ n : ℕ, DvdV (c.vM / 3 + c.s + n) (((n : ℤ_[2]) + 1) • α n)) ∧
    ∀ Y : ℤ_[2], HasSum (fun n => Y ^ (n + 1) • α n) (lam c.disc ((c.c : ℤ_[2]) + 2 ^ c.s * Y) - lam c.disc c.c)

/-- HTail: around the known lift of parameter `Xi`, `λ(Xi + 2^s0 Y) - λ(Xi) = Σ α_n Y^(n+1)` with the same kind of
bound (sup bound on the disc of radius `2^-(s0-1)`), whose linear coefficient is `α_0 = 2^(s0-1) g`, `g = 4 c_1`
in the certified ball of `4 c_1` (code/earlier-computations/pullback_known_lifts.gp, exact pullback identity). -/
def HTail (D : TwistData) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ t ∈ D.tails, ∃ g : Fin 6 → ℤ_[2], ∃ α : ℕ → Fin 6 → ℤ_[2],
    DvdV t.q (g - icast t.g) ∧ α 0 = (2 : ℤ_[2]) ^ (t.s0 - 1) • g ∧
    (∀ n : ℕ, DvdV (t.vM / 3 + t.s0 + n) (((n : ℤ_[2]) + 1) • α n)) ∧
    ∀ Y : ℤ_[2], HasSum (fun n => Y ^ (n + 1) • α n) (lam t.disc ((t.Xi : ℤ_[2]) + 2 ^ t.s0 * Y) - lam t.disc t.Xi)

/-- HKnown: `λ` at the known lifts lies in `S` (`λ(x_a) = 0`, `λ(x_b) = log φ(x_b) - log φ(x_a)`). -/
def HKnown (D : TwistData) (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ t ∈ D.tails, lam t.disc t.Xi ∈ S

/-- HExcl: an excluded box contains no point of twist δ (constant non-square class of `Q1/δ` or `Q3/δ` at `v`). -/
def HExcl (D : TwistData) (Twist : ℕ → ℤ_[2] → Prop) : Prop :=
  ∀ e ∈ D.excluded, ∀ X : ℤ_[2], InBox X e.2.1 e.2.2 → ¬ Twist e.1 X

/-- HAntiConst: on the open parent disc `|X - c| < 2^(-(s-1))` of every constant box `{c + 2^s Y}` (whose `ℚ_2`-points
are the box), `λ` is the antiderivative of a power series in `X - c` whose Gauss norm on the closed parent disc is
at most `|π|^vM = 2^(-vM/3)` (the certified sup bound of
`dλ/dX` on the parent box, and the antiderivative property on the open parent disc, KRZB Lemma 3.23). -/
def HAntiConst (D : TwistData) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ c ∈ D.constant, ∃ w : ℕ → Fin 6 → ℚ_[2], AntiderivOn (lam c.disc) (c.c : ℤ_[2]) (c.s - 1) (c.vM / 3) w

/-- HAntiTail: on the open disc `|X - Xi| < 2^(-(s0-1))` around the known lift of parameter `Xi`, `λ` is the
antiderivative of a power series `w` in `X - Xi` of Gauss norm at most `2^(-vM/3)` on the closed disc, whose constant term `w_0 = dλ/dX (Xi) = 2 c_1`
satisfies `2 w_0 = g` for a `g` in the certified ball of `4 c_1` (code/earlier-computations/pullback_known_lifts.gp, exact pullback identity). -/
def HAntiTail (D : TwistData) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ t ∈ D.tails, ∃ w : ℕ → Fin 6 → ℚ_[2], AntiderivOn (lam t.disc) (t.Xi : ℤ_[2]) (t.s0 - 1) (t.vM / 3) w ∧
    ∃ g : Fin 6 → ℤ_[2], DvdV t.q (g - icast t.g) ∧ ∀ i, 2 * w 0 i = ((g i : ℤ_[2]) : ℚ_[2])

/-- HLam: the image of the logarithm `lam : A(k_v) → V` is the `ℤ_[2]`-span of the logarithms of the local
divisors `D_1, ..., D_7` (`log` has kernel the torsion, `Λ = log A(k_v)` is a lattice, and the
`D_i` generate `A(k_v)` modulo `2A(k_v)`, Nakayama). -/
def HLam {B : Type*} [AddCommGroup B] (lam : B →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → B) : Prop :=
  ∀ y, (∃ b, lam b = y) ↔ y ∈ Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))

/-- HSelLoc: the localisation at `v` of every global point is, modulo `2A(k_v)`, the combination with coefficients
`selc SB m` of the local divisors for some `m` (the image of `A(k) → Sel² → A(k_v)/2A(k_v)` lies in `σ_v(Sel²)`,
spanned by the columns of `SB` in the basis `D_1, ..., D_7`). -/
def HSelLoc {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B) (Dpt : Fin 7 → B) (D : TwistData) :
    Prop :=
  ∀ Q : A, ∃ m : Fin 16, ∃ b : B, ι Q = ∑ i, selc D.SB m i • Dpt i + (2 : ℕ) • b

/-- HDisc: every `x : Dk` (in the application, the lifts to `D_δ(k)` of the rational points of `C` of twist δ, the
points the descent has to find) lies over a point of `C(Q_2)` of parameter `par x` in the disc
`disc x` which is of twist δ, and the logarithm of `φ(x) - φ(x_a)` is `±` the analytic branch `lamD` at that
parameter, modulo `S` (the two lifts differ by the covering involution, `φ ∘ ι = -φ`, and `log φ(x_a) ∈ S`). -/
def HDisc {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B) (lam : B →+ (Fin 6 → ℤ_[2]))
    (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (φ : Dk → A) (xa : Dk) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) : Prop :=
  ∀ x : Dk, disc x ∈ [1, 2, 3, 4, 5] ∧ Twist (disc x) (par x) ∧
    (lam (ι (φ x - φ xa)) - lamD (disc x) (par x) ∈ S ∨ lam (ι (φ x - φ xa)) + lamD (disc x) (par x) ∈ S)

/-- HLocInj: local injectivity of `A(k)/2A(k) → A(k_v)/2A(k_v)`; it follows from `σ_v` injective
(`FurioLombardo.M4.T0.sigma_injective`, `T1.sigma_injective`) by `hLocInj_of_sigma`. -/
def HLocInj {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B) : Prop :=
  ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q'

/-- HKer: a point of `A(k_v)` with zero logarithm is in `2A(k_v)` or in `π_v(T) + 2A(k_v)`, where `T` is the rational
2-torsion point (`ρ : A(k_v)/2A(k_v) → Λ/2Λ` has kernel `⟨π_v(T)⟩`), and `2T = 0`. -/
def HKer {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B) (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) :
    Prop :=
  (∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c) ∧ (2 : ℕ) • T = 0

end FurioLombardo.M4
