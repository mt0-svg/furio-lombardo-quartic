import Mathlib

/-!
# Definitions of lane M4 (the 2-adic certificates at the place v of K21 above 2 with e = 3)

Boxes of `ℤ_[2]` and the covering checker, the leading level and class modulo a saturated submodule (condition (iii)),
the projection test `QChar`, divisibility of vectors of `ℤ_[2]`, integer matrices acting on `ℤ_[2]`-vectors, the
saturation of a span, the box records of the data, and the class test at a centre.
-/

namespace FurioLombardo.M4




/-- `X` lies in the box `{X ≡ c mod 2^s}` of `ℤ_[2]`. -/
def InBox (X : ℤ_[2]) (c s : ℕ) : Prop := ∃ y : ℤ_[2], X = (c : ℤ_[2]) + 2 ^ s * y

/-- The box `b = (c', s')` contains the box `(c, s)`: `s' ≤ s` and `c ≡ c' mod 2^s'`. -/
def boxLe (b : ℕ × ℕ) (c s : ℕ) : Bool := decide (b.2 ≤ s) && (c % 2 ^ b.2 == b.1 % 2 ^ b.2)

/-- `coverCheck L fuel c s = true` certifies that every `X ≡ c mod 2^s` lies in a box of `L`
(the box is split into its two halves at most `fuel` times). -/
def coverCheck (L : List (ℕ × ℕ)) : ℕ → ℕ → ℕ → Bool
  | 0, c, s => L.any (fun b => boxLe b c s)
  | fuel + 1, c, s => L.any (fun b => boxLe b c s) ||
      (coverCheck L fuel c (s + 1) && coverCheck L fuel (c + 2 ^ s) (s + 1))

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

/-- `z ∈ S + 2^n Λ`. -/
def InSL (Λ S : Submodule ℤ_[2] V) (n : ℕ) (z : V) : Prop :=
  ∃ s ∈ S, ∃ l ∈ Λ, z = s + (2 : ℤ_[2]) ^ n • l

/-- `S` is a saturated submodule of `Λ` at 2: `S ≤ Λ`, and `x ∈ Λ`, `2x ∈ S` imply `x ∈ S`. -/
def Saturated (Λ S : Submodule ℤ_[2] V) : Prop :=
  S ≤ Λ ∧ ∀ x ∈ Λ, (2 : ℤ_[2]) • x ∈ S → x ∈ S

/-- Condition (iii) at `y`: if `y ≡ 2^n z mod S` with `z ∈ Λ`, and `z` is congruent
modulo `S + 2Λ` to an element of `W`, then `z ∈ S + 2Λ`. -/
def CondIII (Λ S : Submodule ℤ_[2] V) (W : Set V) (y : V) : Prop :=
  ∀ (n : ℕ) (z w : V), z ∈ Λ → w ∈ W → y - (2 : ℤ_[2]) ^ n • z ∈ S → InSL Λ S 1 (z - w) →
    InSL Λ S 1 z

/-- `y ∈ S + 2^ν z0 + 2^(ν+1) Λ` with `z0 ∈ Λ` whose class modulo `S + 2Λ` is neither `0` nor the class of
an element of `W` (leading level `ν`, leading class outside `pr(W)`). -/
def Leading (Λ S : Submodule ℤ_[2] V) (W : Set V) (ν : ℕ) (y : V) : Prop :=
  ∃ s0 ∈ S, ∃ z0 ∈ Λ, ∃ l ∈ Λ, y = s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l ∧
    ¬ InSL Λ S 1 z0 ∧ ∀ w ∈ W, ¬ InSL Λ S 1 (z0 - w)

/-- The projection `Q` (in the application an integer matrix, rows of `U G` outside the saturation rows)
detects `S + 2^n Λ` for `n ≤ r`: `S ≤ Λ`, and for `x ∈ Λ`, `x ∈ S + 2^n Λ` iff `2^(n+2)` divides every
coordinate of `Q x`. -/
def QChar (Λ S : Submodule ℤ_[2] V) {m : ℕ} (Q : V →ₗ[ℤ_[2]] (Fin m → ℤ_[2])) (r : ℕ) : Prop :=
  S ≤ Λ ∧ ∀ n ≤ r, ∀ x ∈ Λ, InSL Λ S n x ↔ ∀ i, (2 : ℤ_[2]) ^ (n + 2) ∣ Q x i

/-- Every coordinate of `x` is divisible by `2^B`. -/
def DvdV {d : ℕ} (B : ℕ) (x : Fin d → ℤ_[2]) : Prop := ∀ i, (2 : ℤ_[2]) ^ B ∣ x i

/-- The integer vector `c` as a vector of `ℤ_[2]`. -/
noncomputable def icast {n : ℕ} (c : Fin n → ℤ) : Fin n → ℤ_[2] := fun i => (c i : ℤ_[2])

/-- The integer matrix `A` acting on vectors of `ℤ_[2]`. -/
noncomputable def imv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ_[2]) : Fin m → ℤ_[2] :=
  (A.map (Int.cast : ℤ → ℤ_[2])).mulVec x

/-- `S` is the saturation in `Λ` of the span of `a` and `b`. -/
def IsSatOf {V : Type*} [AddCommGroup V] [Module ℤ_[2] V] (Λ S : Submodule ℤ_[2] V) (a b : V) : Prop :=
  ∀ x, x ∈ S ↔ x ∈ Λ ∧ ∃ m : ℕ, (2 : ℤ_[2]) ^ m • x ∈ Submodule.span ℤ_[2] {a, b}


/-- A constant box of the covering: parameter box `{X ≡ c mod 2^s}` of the disc `disc`, the certified leading
level `nu` of `pr λ` at the centre `X = c`, the sup bound exponent `vM` (in `v_π`), and the ball of `λ(c)`: every
coordinate of `λ(c) - y` is divisible by `2^q`. -/
structure CBox where
  disc : ℕ
  c : ℕ
  s : ℕ
  nu : ℕ
  vM : ℕ
  q : ℕ
  y : Fin 6 → ℤ

/-- A tail box `{X ≡ c mod 2^s}` of the disc `disc` around the known lift `x_i` of parameter `Xi` (`c ≡ Xi mod 2^s`),
with analyticity parameter `s0`, sup bound exponent `vM`, and the ball of `g = 4 c_1`: every coordinate of
`4 c_1 - g` is divisible by `2^q`; `nu` is the leading level of `pr g`. -/
structure TBox where
  disc : ℕ
  c : ℕ
  s : ℕ
  i : ℕ
  Xi : ℤ
  s0 : ℕ
  vM : ℕ
  q : ℕ
  nu : ℕ
  g : Fin 6 → ℤ

/-- The boxes `(c, s)` of the disc `d` in the covering of twist data `(ex, cb, tb)`. -/
def boxesOf (ex : List (ℕ × ℕ × ℕ)) (cb : List CBox) (tb : List TBox) (d : ℕ) : List (ℕ × ℕ) :=
  (ex.filter (fun e => e.1 == d)).map (fun e => (e.2.1, e.2.2)) ++
  (cb.filter (fun b => b.disc == d)).map (fun b => (b.c, b.s)) ++
  (tb.filter (fun b => b.disc == d)).map (fun b => (b.c, b.s))

/-- The class test at a centre with Q-values `UG y` (rows 2 to 5). -/
def ClassOK (UG : Matrix (Fin 6) (Fin 6) ℤ) (W : Fin 16 → Fin 6 → ℤ) (nu : ℕ) (y : Fin 6 → ℤ) : Prop :=
  (∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ) ^ (nu + 2) ∣ UG.mulVec y o) ∧
  (∃ o : Fin 6, 2 ≤ o.val ∧ ¬ (2 : ℤ) ^ (nu + 3) ∣ UG.mulVec y o) ∧
  (∀ m : Fin 16, ∃ o : Fin 6, 2 ≤ o.val ∧ ¬ (2 : ℤ) ^ (nu + 3) ∣ UG.mulVec y o - 2 ^ nu * UG.mulVec (W m) o)

/-- The projection on the rows 2 to 5 of the integer matrix `UG`. -/
noncomputable def projO (UG : Matrix (Fin 6) (Fin 6) ℤ) : (Fin 6 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin 4 → ℤ_[2]) :=
  LinearMap.funLeft ℤ_[2] ℤ_[2] (fun i : Fin 4 => (⟨i.val + 2, by omega⟩ : Fin 6)) ∘ₗ
    (UG.map (Int.cast : ℤ → ℤ_[2])).mulVecLin

/-- The set of the 16 representatives of `W`, as vectors of `ℤ_[2]`. -/
noncomputable def Wset (W : Fin 16 → Fin 6 → ℤ) : Set (Fin 6 → ℤ_[2]) := Set.range (fun m => icast (W m))

instance (UG : Matrix (Fin 6) (Fin 6) ℤ) (W : Fin 16 → Fin 6 → ℤ) (nu : ℕ) (y : Fin 6 → ℤ) :
    Decidable (ClassOK UG W nu y) := by unfold ClassOK; infer_instance

/-- The coefficient on the local divisor `D_i` of the representative number `m` of `W`: `∑ j, b_j(m) SB i j`, where
`b_j(m)` are the four binary digits of `m`, most significant first (code/covering/lattice_export.gp). -/
def selc (SB : Matrix (Fin 7) (Fin 4) ℤ) (m : Fin 16) (i : Fin 7) : ℤ :=
  ∑ j : Fin 4, (if Nat.testBit m.val (3 - j.val) then 1 else 0) * SB i j

end FurioLombardo.M4
