import Mathlib
import FurioLombardo.Statement
import FurioLombardo.M4.Stoll

/-!
# The abstract chain of the proof (lane M3a)

The group theoretic skeleton of the proof (see the paper), with every input a hypothesis.
The concrete objects (the Jacobian `A = Jac(F_δ)` over `k = K21` and `k_v`, the `x - T` map, the
Abel-Prym map) are plugged in by `FurioLombardo/M3a/Route.lean`.

* `hloc_of_xT` ((K1), (K2)): the kernel of the `x - T` map is `2A(k)`, its
  localisation is injective on the image of `A(k)`, and `μ_v` kills `2A(k_v)`; then a global
  point which is locally divisible by 2 is globally divisible by 2. This is the hypothesis `hloc`
  of `FurioLombardo.M4.stoll_log`.
* `hker_of_torsion` ((L1), (L2)): if the 2-power torsion of `A(k_v)` is `{0, T}` and
  the logarithm kills only torsion, then `ker log ⊆ 2A(k_v) ∪ (T + 2A(k_v))`: the hypothesis
  `hker` of `stoll_log`.
* `twist_conclusion`: Stoll's theorem at one place (`M4.stoll_log`) applied
  to the points `φ(x) - φ(x_a)` of the lifts `x ∈ D_δ(k)`.
* `DPoint`: the points of `D_δ : Q1 = δ r², Q2 = δ r s, Q3 = δ s²` over a field, the covering
  involution, and the relation "lies over a rational point".
* `onlyFourPoints_of_twists`: the descent and the conclusions for the two
  twists give `FurioLombardo.OnlyFourPoints`.
-/

open Matrix

namespace FurioLombardo.M3a

/-! ## Local injectivity from the `x - T` map -/

/-- (K1) and (K2): with `μ : A(k) → H`, `μ_v : A(k_v) → H_v` and `res : H → H_v`
compatible with the localisation `ι`, if `μ_v` kills `2A(k_v)` (the easy direction), the kernel of
`μ` is `2A(k)` (hypothesis `hkerμ`) and `res` is injective on the image of `μ` (hypothesis `hsel`,
the content of `dim Sel² = 4` and the injectivity of `σ_v`), then a global point whose
localisation is divisible by 2 is divisible by 2. -/
theorem hloc_of_xT {A B HA HB : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup HA]
    [AddCommGroup HB] (ι : A →+ B) (μ : A →+ HA) (μv : B →+ HB) (res : HA →+ HB)
    (hnat : ∀ Q : A, μv (ι Q) = res (μ Q)) (heasy : ∀ b : B, μv ((2 : ℕ) • b) = 0)
    (hkerμ : ∀ Q : A, μ Q = 0 → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hsel : ∀ Q : A, res (μ Q) = 0 → μ Q = 0) :
    ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q' := by
  rintro Q ⟨b, hb⟩
  apply hkerμ
  apply hsel
  rw [← hnat, hb, heasy]

/-! ## The kernel of the logarithm -/

/-- (L1) and (L2): if every 2-power torsion point of `B = A(k_v)` is `0` or `T_v`,
and `lam` kills only torsion points, then `lam b = 0` gives `b ∈ 2B` or `b ∈ T_v + 2B`. -/
theorem hker_of_torsion {B V : Type*} [AddCommGroup B] [AddCommGroup V] (lam : B →+ V) (Tv : B)
    (hL1 : ∀ b : B, (∃ n : ℕ, (2 ^ n : ℕ) • b = 0) → b = 0 ∨ b = Tv)
    (hL2 : ∀ b : B, lam b = 0 → ∃ n : ℕ, 0 < n ∧ n • b = 0) :
    ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = Tv + (2 : ℕ) • c := by
  intro b hb
  obtain ⟨n, hn, hnb⟩ := hL2 b hb
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨j, rfl⟩ := hm
  have h2 : (2 ^ a : ℕ) • ((2 * j + 1) • b) = 0 := by rw [← mul_nsmul']; exact hnb
  have hsplit : b = (2 * j + 1) • b + (2 : ℕ) • (-(j • b)) := by
    rw [add_nsmul, one_nsmul, mul_nsmul', smul_neg]; abel
  rcases hL1 _ ⟨a, h2⟩ with h | h
  · exact ⟨-(j • b), Or.inl (hsplit.trans (by rw [h, zero_add]))⟩
  · exact ⟨-(j • b), Or.inr (hsplit.trans (by rw [h]))⟩

/-! ## Stoll's theorem for one twist -/

/-- Stoll's theorem for one twist `δ`: `A = A(k)`, `B = A(k_v)`, `φ : D_δ(k) → A` the Abel-Prym
map, `x_a` a known lift. Hypotheses: `hloc`, `hker`, the conditions `hT`,
`hΓ`, `hW`, `hsat`, `htf`, `hkrull` of `M4.stoll_log` for the saturated group `Γ'` of (L3),
`hbox` (condition (iii) at every lift, from the covering by boxes) and `hzero` (a lift whose
`pr λ` vanishes is over a known point, (C2)). Conclusion: every lift is good. -/
theorem twist_conclusion {A B V M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]
    [AddCommGroup M] (ι : A →+ B) (lam : B →+ V) (pr : V →+ M) (T : A) (Γ : AddSubgroup A)
    (W : Set V) {Dk : Type*} (φ : Dk → A) (xa : Dk) (Good : Dk → Prop)
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hT : T ∈ Γ) (hΓ : ∀ γ ∈ Γ, pr (lam (ι γ)) = 0)
    (hW : ∀ Q : A, ∃ w ∈ W, ∃ b : B, lam (ι Q) = w + (2 : ℕ) • lam b)
    (hsat : ∀ Q : A, (∃ m : M, pr (lam (ι Q)) = (2 : ℕ) • m) →
      ∃ γ ∈ Γ, ∃ b : B, lam (ι Q) = lam (ι γ) + (2 : ℕ) • lam b)
    (htf : ∀ m : M, (2 : ℕ) • m = 0 → m = 0)
    (hkrull : ∀ m : M, (∀ n : ℕ, ∃ z : M, m = (2 ^ n : ℕ) • z) → m = 0)
    (hbox : ∀ x : Dk, ∀ (n : ℕ) (z : M) (w : V), (2 ^ n : ℕ) • z = pr (lam (ι (φ x - φ xa))) →
      w ∈ W → (∃ m : M, z - pr w = (2 : ℕ) • m) → ∃ m : M, z = (2 : ℕ) • m)
    (hzero : ∀ x : Dk, pr (lam (ι (φ x - φ xa))) = 0 → Good x) :
    ∀ x : Dk, Good x := fun x =>
  hzero x (FurioLombardo.M4.stoll_log ι lam pr T Γ W (φ x - φ xa) hloc hker hT hΓ hW hsat htf
    hkrull (hbox x))

/-! ## The étale double cover `D_δ` -/

/-- A point of `D_δ : Q1 = δ r², Q2 = δ r s, Q3 = δ s²` over a field `L`, where the ternary
quadratic forms `Q_i(p) = p ⬝ M_i p` are given by matrices `M_i`. -/
structure DPoint (L : Type*) [Field L] (M1 M2 M3 : Matrix (Fin 3) (Fin 3) L) (δ : L) where
  /-- the point `(x : y : z)` of `C` below -/
  p : Fin 3 → L
  /-- the coordinate `r` -/
  r : L
  /-- the coordinate `s` -/
  s : L
  ne_zero : p ≠ 0
  eq1 : p ⬝ᵥ (M1 *ᵥ p) = δ * r ^ 2
  eq2 : p ⬝ᵥ (M2 *ᵥ p) = δ * (r * s)
  eq3 : p ⬝ᵥ (M3 *ᵥ p) = δ * s ^ 2

namespace DPoint

variable {L : Type*} [Field L] {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

/-- The covering involution `ι : (p, r, s) ↦ (p, -r, -s)` of `D_δ` over `C`. -/
def inv (x : DPoint L M1 M2 M3 δ) : DPoint L M1 M2 M3 δ where
  p := x.p
  r := -x.r
  s := -x.s
  ne_zero := x.ne_zero
  eq1 := by rw [x.eq1, neg_sq]
  eq2 := by rw [x.eq2, neg_mul_neg]
  eq3 := by rw [x.eq3, neg_sq]

@[simp] theorem inv_inv (x : DPoint L M1 M2 M3 δ) : x.inv.inv = x := by
  cases x; simp [inv]

/-- `x` lies over the rational point `(a : b : c)` of `C`. -/
def Over [Algebra ℚ L] (x : DPoint L M1 M2 M3 δ) (a b c : ℚ) : Prop :=
  ∃ t : L, t ≠ 0 ∧ x.p = t • ![algebraMap ℚ L a, algebraMap ℚ L b, algebraMap ℚ L c]

theorem over_inv [Algebra ℚ L] (x : DPoint L M1 M2 M3 δ) (a b c : ℚ) :
    x.inv.Over a b c ↔ x.Over a b c := Iff.rfl

end DPoint

/-! ## The conclusion -/

/-- The descent (lane M1): every rational point of `C` lifts to `D_{δ0}(k)` or `D_{δ1}(k)`. -/
def Descent (k : Type*) [Field k] [Algebra ℚ k] (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k)
    (δ0 δ1 : k) : Prop :=
  ∀ x y z : ℚ, (x, y, z) ≠ (0, 0, 0) → FurioLombardo.F x y z = 0 →
    (∃ d : DPoint k M1 M2 M3 δ0, d.Over x y z) ∨ (∃ d : DPoint k M1 M2 M3 δ1, d.Over x y z)

/-- The conclusion of the route for the twist `δ`: every rational point with a lift to
`D_δ(k)` is one of the two known points `Pa`, `Pb` of that twist. -/
def TwistConclusion (k : Type*) [Field k] [Algebra ℚ k] (M1 M2 M3 : Matrix (Fin 3) (Fin 3) k)
    (δ : k) (Pa Pb : ℚ × ℚ × ℚ) : Prop :=
  ∀ (d : DPoint k M1 M2 M3 δ) (x y z : ℚ), d.Over x y z →
    FurioLombardo.SameProjPoint x y z Pa ∨ FurioLombardo.SameProjPoint x y z Pb

/-- The descent to the covers `D_δ` and the conclusions for the twists `δ0`
(known points `P0 = (0:0:1)`, `P2 = (2:0:1)`) and `δ1` (`P1 = (1:1:1)`, `P3 = (-1:0:1)`) give
the frozen statement `FurioLombardo.OnlyFourPoints`. -/
theorem onlyFourPoints_of_twists {k : Type*} [Field k] [Algebra ℚ k]
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ0 δ1 : k} (hdesc : Descent k M1 M2 M3 δ0 δ1)
    (h0 : TwistConclusion k M1 M2 M3 δ0 (0, 0, 1) (2, 0, 1))
    (h1 : TwistConclusion k M1 M2 M3 δ1 (1, 1, 1) (-1, 0, 1)) :
    FurioLombardo.OnlyFourPoints := by
  intro x y z hne hF
  rcases hdesc x y z hne hF with ⟨d, hd⟩ | ⟨d, hd⟩
  · rcases h0 d x y z hd with h | h
    · exact ⟨(0, 0, 1), by simp [FurioLombardo.listed], h⟩
    · exact ⟨(2, 0, 1), by simp [FurioLombardo.listed], h⟩
  · rcases h1 d x y z hd with h | h
    · exact ⟨(1, 1, 1), by simp [FurioLombardo.listed], h⟩
    · exact ⟨(-1, 0, 1), by simp [FurioLombardo.listed], h⟩

end FurioLombardo.M3a
