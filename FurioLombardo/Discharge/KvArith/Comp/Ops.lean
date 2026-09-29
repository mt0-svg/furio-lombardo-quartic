/-!
# Straight line programs over any arithmetic: the computational part (lane lean-kv-arith)

No Mathlib import. A program is a Lean function over `o : Ops A`; soundness (`Ops.Rel`, `fieldOps`,
`funOps` and the `_rel` lemmas) is in `KvArith/Ops.lean`.
-/

universe u v

namespace FurioLombardo.Discharge.KvArith

/-- The operations of a straight line program. -/
structure Ops (A : Type u) where
  /-- Sum. -/
  add : A → A → A
  /-- Difference. -/
  sub : A → A → A
  /-- Negation. -/
  neg : A → A
  /-- Product. -/
  mul : A → A → A
  /-- Partial inverse. -/
  inv : A → Option A
  /-- Integer constants. -/
  ofInt : Int → A

/-- The derivative in `y` of a bivariate integer polynomial (`hornerZ2` convention). -/
def derivY (cs : List (List Int)) : List (List Int) :=
  cs.map fun c => (c.drop 1).mapIdx fun i z => ((i + 1 : Nat) : Int) * z

section Programs

variable {A : Type u} (o : Ops A)

/-- `0`. -/
def Ops.zero : A := o.ofInt 0

/-- Horner evaluation `c₀ + x (c₁ + x (c₂ + ...))`. -/
def Ops.horner (cs : List A) (x : A) : A := cs.foldr (fun c acc => o.add c (o.mul x acc)) o.zero

/-- Horner evaluation of an integer coefficient list. -/
def Ops.hornerZ (cs : List Int) (x : A) : A :=
  cs.foldr (fun c acc => o.add (o.ofInt c) (o.mul x acc)) o.zero

/-- Evaluation of a bivariate integer polynomial `Σ_i (Σ_j c_ij y^j) x^i`. -/
def Ops.hornerZ2 (cs : List (List Int)) (x y : A) : A :=
  cs.foldr (fun c acc => o.add (o.hornerZ c y) (o.mul x acc)) o.zero

/-- Coefficientwise sum of list polynomials (the longer tail is kept). -/
def Ops.zipAdd : List A → List A → List A
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => o.add a b :: Ops.zipAdd p q

/-- Coefficientwise difference of list polynomials. -/
def Ops.zipSub : List A → List A → List A
  | [], q => q.map o.neg
  | a :: p, [] => a :: p
  | a :: p, b :: q => o.sub a b :: Ops.zipSub p q

/-- Product of list polynomials. -/
def Ops.conv : List A → List A → List A
  | [], _ => []
  | a :: p, q => o.zipAdd (q.map (o.mul a)) (o.zero :: Ops.conv p q)

/-- Product truncated to degree `n`. -/
def Ops.pmul (n : Nat) (p q : List A) : List A := (o.conv p q).take (n + 1)

/-- The formal inverse to order `n`: `d₀ = 1/g₀`, `d_j = -d₀ Σ_{1 ≤ i ≤ j} gᵢ d_{j-i}`. -/
def Ops.invSeries (n : Nat) (g : List A) : Option (List A) := do
  let d0 ← o.inv (g.headD o.zero)
  let step : List A → Nat → List A := fun ds j =>
    let s := ((List.range j).map fun i =>
      o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)).foldr o.add o.zero
    ds ++ [o.neg (o.mul s d0)]
  pure ((List.range' 1 n).foldl step [d0])

/-- The formal square root to order `n` from a root `p₀` of `a₀`:
`p_j = (a_j - Σ_{1 ≤ i ≤ j-1} pᵢ p_{j-i}) / (2 p₀)`. -/
def Ops.sqrtSeries (n : Nat) (a : List A) (p0 : A) : Option (List A) := do
  let i2 ← o.inv (o.add p0 p0)
  let step : List A → Nat → List A := fun ps j =>
    let s := ((List.range (j - 1)).map fun i =>
      o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero)).foldr o.add o.zero
    ps ++ [o.mul (o.sub (a.getD j o.zero) s) i2]
  pure ((List.range' 1 n).foldl step [p0])

/-- Truncated power series of degree `≤ n` over `o` (the inverse is `invSeries`). -/
def polyOps (n : Nat) : Ops (List A) where
  add := o.zipAdd
  sub := o.zipSub
  neg := List.map o.neg
  mul := o.pmul n
  inv := o.invSeries n
  ofInt z := [o.ofInt z]

/-- Pairs, operation by operation; the inverse succeeds when both succeed. -/
def Ops.prod {B : Type v} (p : Ops B) : Ops (A × B) where
  add x y := (o.add x.1 y.1, p.add x.2 y.2)
  sub x y := (o.sub x.1 y.1, p.sub x.2 y.2)
  neg x := (o.neg x.1, p.neg x.2)
  mul x y := (o.mul x.1 y.1, p.mul x.2 y.2)
  inv x := match o.inv x.1, p.inv x.2 with
    | some a, some b => some (a, b)
    | _, _ => none
  ofInt z := (o.ofInt z, p.ofInt z)

/-- Divided difference in `y` of an integer polynomial `Σ cⱼ yʲ`, `(p(a) - p(b)) / (a - b)`, by
`dd(c :: cs) = cs(a) + b dd(cs)`. -/
def Ops.ddZ : List Int → A → A → A
  | [], _, _ => o.zero
  | _ :: cs, a, b => o.add (o.hornerZ cs a) (o.mul b (Ops.ddZ cs a b))

/-- Divided difference in `y` of a bivariate integer polynomial (`hornerZ2` convention). -/
def Ops.ddZ2 (cs : List (List Int)) (x a b : A) : A :=
  cs.foldr (fun c acc => o.add (o.ddZ c a b) (o.mul x acc)) o.zero

/-- The formal root to order `n` of `F(t₀ + t₁ h, Y)` from a simple root `y₀` of `F(t₀, Y)`:
`y_k = -[h^k] F(t₀ + t₁ h, y₀ + ... + y_{k-1} h^(k-1)) / F_Y(t₀, y₀)`, on truncated series. -/
def Ops.rootSeries (n : Nat) (F : List (List Int)) (t0 t1 y0 : A) : Option (List A) := do
  let c ← o.inv (o.hornerZ2 (derivY F) t0 y0)
  let step : List A → Nat → List A := fun P k =>
    let r := (polyOps o n).hornerZ2 F [t0, t1] P
    P ++ [o.neg (o.mul (r.getD k o.zero) c)]
  pure ((List.range' 1 n).foldl step [y0])

end Programs

end FurioLombardo.Discharge.KvArith
