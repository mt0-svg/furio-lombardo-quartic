/-!
# Ball arithmetic on natural triples modulo `2^P`: the computational part (lane lean-kv-arith, D1)

No Mathlib import, so that kernel checks (`decide +kernel`) load only this code. Meaning and soundness:
`KvArith/Ball.lean`. A ball `⟨c, e, r, v⟩` stands for `2^-e (evN c + pv^r O_v)`, `evN c = c₀ + c₁ pv +
c₂ pv²`, with `v` a lower bound for the valuation of `evN c`; triples are reduced modulo `m = 2^P`
(`Ctx`), so radii are capped at `3P`.

Cost design (timed probes code/formal-proof/ball_arith_kernel_bench.lean): the valuation `vN` of a triple costs more
kernel time than a product, so it is recomputed only where cancellation is expected (`Ball.sub`), by the
inverse and square root checks, and for constants; `Ball.add` keeps `min v_a v_b`, `Ball.mulRaw`
`v_a + v_b`, and `Ball.norm` returns at once on scale 0.
-/

namespace FurioLombardo.Discharge.KvArith

/-- Natural triples `(a₀, a₁, a₂)`, standing for `a₀ + a₁ pv + a₂ pv²`. -/
abbrev N3 := Nat × Nat × Nat

/-- The coefficients of the Eisenstein cubic `E = x³ + e2 x² + e1 x + e0` of `M4Cert.Kv`. -/
def E0N : Nat := 17325639337422721302482
/-- `e1`. -/
def E1N : Nat := 16418729904282180494548
/-- `e2`. -/
def E2N : Nat := 37469486047374096441064

/-- The working modulus `m = 2^P` and residues `neᵢ ≡ -eᵢ (mod m)`. -/
structure Ctx where
  /-- Number of bits kept. -/
  P : Nat
  /-- `2 ^ P`. -/
  m : Nat
  /-- `-e0 mod m`. -/
  ne0 : Nat
  /-- `-e1 mod m`. -/
  ne1 : Nat
  /-- `-e2 mod m`. -/
  ne2 : Nat

/-- The context of precision `P` bits. -/
def Ctx.ofP (P : Nat) : Ctx :=
  ⟨P, 2 ^ P, 2 ^ P - E0N % 2 ^ P, 2 ^ P - E1N % 2 ^ P, 2 ^ P - E2N % 2 ^ P⟩

/-- Reduction of the coordinates modulo `m`. -/
def redN (k : Ctx) (a : N3) : N3 := (a.1 % k.m, a.2.1 % k.m, a.2.2 % k.m)

/-- Sum modulo `m`. -/
def addN (k : Ctx) (a b : N3) : N3 :=
  ((a.1 + b.1) % k.m, (a.2.1 + b.2.1) % k.m, (a.2.2 + b.2.2) % k.m)

/-- Negation modulo `m`. -/
def negN (k : Ctx) (a : N3) : N3 :=
  ((k.m - a.1 % k.m) % k.m, (k.m - a.2.1 % k.m) % k.m, (k.m - a.2.2 % k.m) % k.m)

/-- Difference modulo `m`. -/
def subN (k : Ctx) (a b : N3) : N3 :=
  ((a.1 + (k.m - b.1 % k.m)) % k.m, (a.2.1 + (k.m - b.2.1 % k.m)) % k.m,
    (a.2.2 + (k.m - b.2.2 % k.m)) % k.m)

/-- Multiplication by a natural number modulo `m`. -/
def smulN (k : Ctx) (s : Nat) (a : N3) : N3 := (s * a.1 % k.m, s * a.2.1 % k.m, s * a.2.2 % k.m)

/-- Product modulo `m`, with `pv³ = -(e0 + e1 pv + e2 pv²)`. -/
def mulN (k : Ctx) (a b : N3) : N3 :=
  let c0 := a.1 * b.1
  let c1 := a.1 * b.2.1 + a.2.1 * b.1
  let c2 := a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1
  let c3 := (a.2.1 * b.2.2 + a.2.2 * b.2.1) % k.m
  let c4 := (a.2.2 * b.2.2) % k.m
  let d3 := (c3 + k.ne2 * c4) % k.m
  ((c0 + k.ne0 * d3) % k.m, (c1 + k.ne1 * d3 + k.ne0 * c4) % k.m,
    (c2 + k.ne2 * d3 + k.ne1 * c4) % k.m)

/-- `log₂ gcd(n, 2^P)`: a lower bound for the 2-adic valuation of `n`, exact when `2^P ∤ n`. -/
def v2 (k : Ctx) (n : Nat) : Nat := Nat.log2 (Nat.gcd n k.m)

/-- Lower bound for the valuation of `evN a`, exact when below `3P`. -/
def vN (k : Ctx) (a : N3) : Nat :=
  min (3 * v2 k a.1) (min (3 * v2 k a.2.1 + 1) (3 * v2 k a.2.2 + 2))

/-- A ball: centre, scale exponent, radius exponent, valuation bound of the centre. -/
structure Ball where
  /-- Centre. -/
  c : N3
  /-- Scale exponent. -/
  e : Nat
  /-- Radius exponent. -/
  r : Nat
  /-- Lower bound for the valuation of the centre. -/
  v : Nat
  deriving DecidableEq, Repr

namespace Ball

variable (k : Ctx)

/-- The exact ball of a triple. -/
def ofN (c : N3) : Ball := let c' := redN k c; ⟨c', 0, 3 * k.P, vN k c'⟩

/-- The exact ball of an integer. -/
def ofInt (z : Int) : Ball := let c : N3 := ((z % (k.m : Int)).toNat, 0, 0); ⟨c, 0, 3 * k.P, vN k c⟩

/-- The ball of the exact centre, with a recomputed valuation bound. -/
def exactN (b : Ball) : Ball := ⟨b.c, b.e, 3 * k.P, vN k b.c⟩

/-- Scale up by `2^j` (no change for `j = 0`). -/
def up (j : Nat) (b : Ball) : Ball :=
  if j = 0 then b else
    ⟨smulN k (2 ^ j) b.c, b.e + j, min (b.r + 3 * j) (3 * k.P), min (b.v + 3 * j) (3 * k.P)⟩

/-- Sum (valuation bound `min v_a v_b`). -/
def add (a b : Ball) : Ball :=
  let a' := a.up k (b.e - a.e)
  let b' := b.up k (a.e - b.e)
  ⟨addN k a'.c b'.c, a'.e, min (min a'.r b'.r) (3 * k.P), min (min a'.v b'.v) (3 * k.P)⟩

/-- Difference (valuation recomputed: cancellation). -/
def sub (a b : Ball) : Ball :=
  let a' := a.up k (b.e - a.e)
  let b' := b.up k (a.e - b.e)
  let c := subN k a'.c b'.c
  ⟨c, a'.e, min (min a'.r b'.r) (3 * k.P), vN k c⟩

/-- The same ball with the valuation bound of the centre recomputed. -/
def fresh (b : Ball) : Ball := ⟨b.c, b.e, b.r, vN k b.c⟩

/-- Negation. -/
def neg (b : Ball) : Ball := ⟨negN k b.c, b.e, min b.r (3 * k.P), min b.v (3 * k.P)⟩

/-- Product, not normalized. -/
def mulRaw (a b : Ball) : Ball :=
  ⟨mulN k a.c b.c, a.e + b.e, min (min (a.r + min b.v b.r) (a.v + b.r)) (3 * k.P),
    min (a.v + b.v) (3 * k.P)⟩

/-- Divide the centre by the largest `2^j` with `j ≤ e`, `3j ≤ r`, `2^j` dividing it. -/
def norm (b : Ball) : Ball :=
  if b.e = 0 then b else
    let j := min b.e (min (b.r / 3) (min (v2 k b.c.1) (min (v2 k b.c.2.1) (v2 k b.c.2.2))))
    if j = 0 then b else
      ⟨(b.c.1 / 2 ^ j, b.c.2.1 / 2 ^ j, b.c.2.2 / 2 ^ j), b.e - j, b.r - 3 * j, b.v - 3 * j⟩

/-- Product, normalized. -/
def mul (a b : Ball) : Ball := (mulRaw k a b).norm k

/-- Certified nonzero: the exact valuation of the centre is below the radius and below `3P`. -/
def nz (b : Ball) : Bool := decide (vN k b.c < b.r) && decide (vN k b.c < 3 * k.P)

/-- Newton's iteration for the inverse of an odd `o` modulo `m` (unverified). -/
def oddInvAux (m o : Nat) : Nat → Nat → Nat
  | 0, y => y
  | n + 1, y => oddInvAux m o n (y * (2 + m - o * y % m) % m)

/-- Candidate inverse of an odd number modulo `m` (unverified). -/
def oddInv (o : Nat) : Nat := oddInvAux k.m o (Nat.log2 k.P + 2) 1

/-- Candidate inverse of a triple (unverified): `(c, w)` with `evN c / 2^w ≈ 1 / evN a`, from the
adjugate of the multiplication matrix of `a` on `1, pv, pv²` and the odd part of its determinant. -/
def invCand (a : N3) : N3 × Nat :=
  let m := k.m
  let s : Nat → Nat → Nat := fun x y => (x + (m - y % m)) % m
  let c2 := mulN k a (0, 1, 0)
  let c3 := mulN k c2 (0, 1, 0)
  let C11 := s (c2.2.1 * c3.2.2) (c3.2.1 * c2.2.2)
  let C12 := s (c3.2.1 * a.2.2) (a.2.1 * c3.2.2)
  let C13 := s (a.2.1 * c2.2.2) (c2.2.1 * a.2.2)
  let det := (a.1 * C11 + c2.1 * C12 + c3.1 * C13) % m
  let w := v2 k det
  (smulN k (oddInv k (det / 2 ^ w)) (C11, C12, C13), w)

/-- Inverse: `none` unless the centre is certified nonzero; the candidate of `invCand` is checked
through the residual `c_a c - 2^(e + e')`. -/
def inv (b : Ball) : Option Ball :=
  let u := vN k b.c
  if u < b.r ∧ u < 3 * k.P then
    let cw := invCand k b.c
    let c0 := if b.e ≤ cw.2 then cw.1 else smulN k (2 ^ (b.e - cw.2)) cw.1
    let e' := cw.2 - b.e
    let d := subN k (mulN k b.c c0) ((2 ^ (b.e + e')) % k.m, 0, 0)
    let vc := vN k c0
    let r' := min (min (vN k d) (3 * k.P)) (vc + b.r)
    if u ≤ r' then some ⟨c0, e', r' - u, vc⟩ else none
  else none

/-- Square root near the root candidate `evN s / 2^es`: `none` unless Hensel's condition
`v(s² - 2^(2es) x) > 6 + 2 v(s)` is certified. -/
def sqrt (b : Ball) (s : N3) (es : Nat) : Option Ball :=
  if b.e ≤ 2 * es then
    let s' := redN k s
    let j := 2 * es - b.e
    let d := subN k (mulN k s' s') (smulN k (2 ^ j) b.c)
    let q := min (min (vN k d) (3 * k.P)) (3 * j + b.r)
    let vs := vN k s'
    if vs < 3 * k.P ∧ 2 * vs + 6 < q then some ⟨s', es, q - 3 - vs, vs⟩ else none
  else none

/-- Inclusion of balls (a certificate may store a coarser ball than the one computed): `b ⊆ b'`
when `e ≤ e'`, the centres agree to the radius `r' ≤ r` after scaling, and `v'` bounds the centre of `b'`. -/
def incl (b b' : Ball) : Bool :=
  let a := b.up k (b'.e - b.e)
  decide (b.e ≤ b'.e) && decide (b'.r ≤ a.r) &&
    decide (b'.r ≤ min (vN k (subN k a.c b'.c)) (3 * k.P)) && decide (b'.v ≤ vN k b'.c)

end Ball

/-- The natural triple of the residues of an integer triple modulo `m`. -/
def natOfT3 (k : Ctx) (t : Int × Int × Int) : N3 :=
  ((t.1 % (k.m : Int)).toNat, (t.2.1 % (k.m : Int)).toNat, (t.2.2 % (k.m : Int)).toNat)

/-- The integer triple of a natural triple. -/
def t3OfN (a : N3) : Int × Int × Int := ((a.1 : Int), (a.2.1 : Int), (a.2.2 : Int))

/-- The ball of a residue modulo `2^n` (`M4Cert.Approx`). -/
def Ball.ofApprox (k : Ctx) (t : Int × Int × Int) (n : Nat) : Ball :=
  let c := natOfT3 k t; ⟨c, 0, min (3 * n) (3 * k.P), vN k c⟩

end FurioLombardo.Discharge.KvArith
