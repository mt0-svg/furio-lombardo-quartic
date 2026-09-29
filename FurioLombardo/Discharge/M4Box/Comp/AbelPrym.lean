import FurioLombardo.Discharge.KvArith.Comp.Cantor

/-!
# Bruin's Abel-Prym map as a straight line program: the computational part (lane lean-m4box, D4)

No Mathlib import. For three symmetric forms `N1, N2, N3` (the pencil `N1 + 2t N2 + t² N3`), `δ`, and a
point `(p, r, s)` of `D_δ : N1(p) = δ r², N2(p) = δ r s, N3(p) = δ s²`, `apPhi` computes the Mumford pair
`[U, V]` of Bruin's construction (lane M3a's `AbelPrym.Cert`, built by `Cert.ofEntry`):

* the rank check: the component `jN` of `(s² N1 - 2rs N2 + r² N3) p` is inverted;
* `T`: the cofactor vector of the `3 × 5` tangent matrix `J` (rows `W ↦ polarD i P W`) with the column
  `kd` dropped, a kernel vector of `J`;
* `a_i = quadD i T`, `a₃` inverted, `U = X² + (2 a₂ / a₃) X + a₁ / a₃`;
* `c`: the minor `l` of `(p, T_p)` (the entry `(l, 3)` of `⋆A`, a constant), inverted;
* `V = ((G A G)_{l3} mod U) / c`, with `(G A G)_{l3} = -δ Σ_a (N1 + 2t N2 + t² N3)_{la} (α_a + β_a t)`,
  `α_a = p_a T_r - T_a r`, `β_a = p_a T_s - T_a s`, a cubic in `t`.

The result is `none` exactly when one of the three inverses fails. Soundness over a field
(`apPhi_spec`) and the relational lemma (`apPhi_rel`) are in `M4Box/AbelPrymSpec.lean`.
-/

universe u

namespace FurioLombardo.Discharge.M4Box

open FurioLombardo.Discharge.KvArith

/-- A symmetric `3 × 3` matrix by its upper entries. -/
structure Sym3 (A : Type u) where
  /-- `(0, 0)` -/
  a00 : A
  /-- `(0, 1)` -/
  a01 : A
  /-- `(0, 2)` -/
  a02 : A
  /-- `(1, 1)` -/
  a11 : A
  /-- `(1, 2)` -/
  a12 : A
  /-- `(2, 2)` -/
  a22 : A

/-- A vector with five coordinates `(x, y, z, r, s)`. -/
structure Vec5 (A : Type u) where
  /-- `x` -/
  c0 : A
  /-- `y` -/
  c1 : A
  /-- `z` -/
  c2 : A
  /-- `r` -/
  c3 : A
  /-- `s` -/
  c4 : A

/-- The input of the Abel-Prym program: the forms, `δ`, and the point `(p, r, s)`. -/
structure APIn (A : Type u) where
  /-- first form -/
  n1 : Sym3 A
  /-- second form -/
  n2 : Sym3 A
  /-- third form -/
  n3 : Sym3 A
  /-- `δ` -/
  dl : A
  /-- `p₀` -/
  p0 : A
  /-- `p₁` -/
  p1 : A
  /-- `p₂` -/
  p2 : A
  /-- `r` -/
  r : A
  /-- `s` -/
  s : A

/-- The choices of the program: the dropped column `kd` of the tangent matrix, the minor `l` of
`(p, T_p)`, the component `jN` of the rank vector. -/
structure APPrm where
  /-- dropped column, `0` to `4` -/
  kd : Nat
  /-- minor, `0` to `2` -/
  l : Nat
  /-- rank component, `0` to `2` -/
  jN : Nat
  deriving DecidableEq, Repr

section Programs

variable {A : Type u} (o : Ops A)

/-- `m p`. -/
def Sym3.mulVec (m : Sym3 A) (p0 p1 p2 : A) : A × A × A :=
  (o.add (o.add (o.mul m.a00 p0) (o.mul m.a01 p1)) (o.mul m.a02 p2),
   o.add (o.add (o.mul m.a01 p0) (o.mul m.a11 p1)) (o.mul m.a12 p2),
   o.add (o.add (o.mul m.a02 p0) (o.mul m.a12 p1)) (o.mul m.a22 p2))

/-- `q ⬝ m q`. -/
def Sym3.quad (m : Sym3 A) (q0 q1 q2 : A) : A :=
  let w := Sym3.mulVec o m q0 q1 q2
  o.add (o.add (o.mul q0 w.1) (o.mul q1 w.2.1)) (o.mul q2 w.2.2)

/-- The `3 × 3` determinant, rows `(a, b, c)`, `(d, e, f)`, `(g, h, i)`. -/
def det3 (a b c d e f g h i : A) : A :=
  o.add (o.sub (o.mul a (o.sub (o.mul e i) (o.mul f h))) (o.mul b (o.sub (o.mul d i) (o.mul f g))))
    (o.mul c (o.sub (o.mul d h) (o.mul e g)))

/-- A coordinate of a `Vec5`. -/
def Vec5.get (v : Vec5 A) : Nat → A
  | 0 => v.c0
  | 1 => v.c1
  | 2 => v.c2
  | 3 => v.c3
  | _ => v.c4

/-- The minor of the three rows on the columns `a, b, c`. -/
def minor3 (J0 J1 J2 : Vec5 A) (a b c : Nat) : A :=
  det3 o (J0.get a) (J0.get b) (J0.get c) (J1.get a) (J1.get b) (J1.get c) (J2.get a) (J2.get b) (J2.get c)

/-- The cofactor kernel vector of the rows `J0, J1, J2` with the column `kd` dropped. -/
def kerVec (J0 J1 J2 : Vec5 A) (kd : Nat) : Vec5 A :=
  let m := minor3 o J0 J1 J2
  match kd with
  | 0 => ⟨o.zero, m 2 3 4, o.neg (m 1 3 4), m 1 2 4, o.neg (m 1 2 3)⟩
  | 1 => ⟨m 2 3 4, o.zero, o.neg (m 0 3 4), m 0 2 4, o.neg (m 0 2 3)⟩
  | 2 => ⟨m 1 3 4, o.neg (m 0 3 4), o.zero, m 0 1 4, o.neg (m 0 1 3)⟩
  | 3 => ⟨m 1 2 4, o.neg (m 0 2 4), m 0 1 4, o.zero, o.neg (m 0 1 2)⟩
  | _ => ⟨m 1 2 3, o.neg (m 0 2 3), m 0 1 3, o.neg (m 0 1 2), o.zero⟩

/-- The row `W ↦ polarD i P W` of the tangent matrix for the form `m`: `(2 m p, ρ, σ)`. -/
def tanRow (m : Sym3 A) (p0 p1 p2 ρ σ : A) : Vec5 A :=
  let w := Sym3.mulVec o m p0 p1 p2
  ⟨o.add w.1 w.1, o.add w.2.1 w.2.1, o.add w.2.2 w.2.2, ρ, σ⟩

/-- A component of a triple. -/
def trip (w : A × A × A) : Nat → A
  | 0 => w.1
  | 1 => w.2.1
  | _ => w.2.2

/-- The row `l` of a symmetric matrix. -/
def Sym3.row (m : Sym3 A) : Nat → A × A × A
  | 0 => (m.a00, m.a01, m.a02)
  | 1 => (m.a01, m.a11, m.a12)
  | _ => (m.a02, m.a12, m.a22)

/-- The minor `l` of `(p, q)`: `p₁q₂ - p₂q₁`, `p₂q₀ - p₀q₂`, `p₀q₁ - p₁q₀`. -/
def minor2 (p0 p1 p2 q0 q1 q2 : A) : Nat → A
  | 0 => o.sub (o.mul p1 q2) (o.mul p2 q1)
  | 1 => o.sub (o.mul p2 q0) (o.mul p0 q2)
  | _ => o.sub (o.mul p0 q1) (o.mul p1 q0)

/-- The rank vector `(s² N1 - 2rs N2 + r² N3) p`. -/
def apNv (x : APIn A) : A × A × A :=
  let rr := o.mul x.r x.r
  let ss := o.mul x.s x.s
  let rs := o.mul x.r x.s
  let w1 := Sym3.mulVec o x.n1 x.p0 x.p1 x.p2
  let w2 := Sym3.mulVec o x.n2 x.p0 x.p1 x.p2
  let w3 := Sym3.mulVec o x.n3 x.p0 x.p1 x.p2
  (o.add (o.sub (o.mul ss w1.1) (o.mul (o.add rs rs) w2.1)) (o.mul rr w3.1),
   o.add (o.sub (o.mul ss w1.2.1) (o.mul (o.add rs rs) w2.2.1)) (o.mul rr w3.2.1),
   o.add (o.sub (o.mul ss w1.2.2) (o.mul (o.add rs rs) w2.2.2)) (o.mul rr w3.2.2))

/-- The three rows of the tangent matrix. -/
def apJ0 (x : APIn A) : Vec5 A :=
  tanRow o x.n1 x.p0 x.p1 x.p2 (o.neg (o.add (o.mul x.dl x.r) (o.mul x.dl x.r))) o.zero

/-- The second row. -/
def apJ1 (x : APIn A) : Vec5 A :=
  tanRow o x.n2 x.p0 x.p1 x.p2 (o.neg (o.mul x.dl x.s)) (o.neg (o.mul x.dl x.r))

/-- The third row. -/
def apJ2 (x : APIn A) : Vec5 A :=
  tanRow o x.n3 x.p0 x.p1 x.p2 o.zero (o.neg (o.add (o.mul x.dl x.s) (o.mul x.dl x.s)))

/-- The tangent vector `T`. -/
def apT (x : APIn A) (kd : Nat) : Vec5 A := kerVec o (apJ0 o x) (apJ1 o x) (apJ2 o x) kd

/-- `a_i = quadD i T`. -/
def apA (x : APIn A) (T : Vec5 A) : A × A × A :=
  (o.sub (Sym3.quad o x.n1 T.c0 T.c1 T.c2) (o.mul x.dl (o.mul T.c3 T.c3)),
   o.sub (Sym3.quad o x.n2 T.c0 T.c1 T.c2) (o.mul x.dl (o.mul T.c3 T.c4)),
   o.sub (Sym3.quad o x.n3 T.c0 T.c1 T.c2) (o.mul x.dl (o.mul T.c4 T.c4)))

/-- The dot product of a triple with `(y₀, y₁, y₂)`. -/
def dot3 (m : A × A × A) (y0 y1 y2 : A) : A :=
  o.add (o.add (o.mul m.1 y0) (o.mul m.2.1 y1)) (o.mul m.2.2 y2)

/-- The coefficients `e₀, e₁, e₂, e₃` of `(G A G)_{l3}`. -/
def apE (x : APIn A) (T : Vec5 A) (l : Nat) : Quart A :=
  let al0 := o.sub (o.mul x.p0 T.c3) (o.mul T.c0 x.r)
  let al1 := o.sub (o.mul x.p1 T.c3) (o.mul T.c1 x.r)
  let al2 := o.sub (o.mul x.p2 T.c3) (o.mul T.c2 x.r)
  let be0 := o.sub (o.mul x.p0 T.c4) (o.mul T.c0 x.s)
  let be1 := o.sub (o.mul x.p1 T.c4) (o.mul T.c1 x.s)
  let be2 := o.sub (o.mul x.p2 T.c4) (o.mul T.c2 x.s)
  let m1 := Sym3.row x.n1 l
  let m2 := Sym3.row x.n2 l
  let m3 := Sym3.row x.n3 l
  let nd := o.neg x.dl
  ⟨o.mul nd (dot3 o m1 al0 al1 al2),
   o.mul nd (o.add (dot3 o m1 be0 be1 be2) (o.add (dot3 o m2 al0 al1 al2) (dot3 o m2 al0 al1 al2))),
   o.mul nd (o.add (o.add (dot3 o m2 be0 be1 be2) (dot3 o m2 be0 be1 be2)) (dot3 o m3 al0 al1 al2)),
   o.mul nd (dot3 o m3 be0 be1 be2)⟩

/-- **Bruin's Abel-Prym map**: the Mumford pair `[U, V]` at the point `x`. -/
def apPhi (prm : APPrm) (x : APIn A) : Option (Mum A) := do
  let _ ← o.inv (trip (apNv o x) prm.jN)
  let T := apT o x prm.kd
  let a := apA o x T
  let ia3 ← o.inv a.2.2
  let u1 := o.mul (o.add a.2.1 a.2.1) ia3
  let u0 := o.mul a.1 ia3
  let ic ← o.inv (minor2 o x.p0 x.p1 x.p2 T.c0 T.c1 T.c2 prm.l)
  let e := apE o x T prm.l
  let r1 := o.add (o.sub e.c1 (o.mul e.c2 u1)) (o.mul e.c3 (o.sub (o.mul u1 u1) u0))
  let r0 := o.add (o.sub e.c0 (o.mul e.c2 u0)) (o.mul e.c3 (o.mul u1 u0))
  pure ⟨u0, u1, o.mul r0 ic, o.mul r1 ic⟩

end Programs

end FurioLombardo.Discharge.M4Box
