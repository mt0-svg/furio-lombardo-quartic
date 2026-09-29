import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

/-!
# Kernel checkers of lane M2: generic definitions

Everything here is run by the kernel (`decide +kernel`) on literal data. The file imports only the
notations `ℕ`, `ℤ`: every function is defined on `ℕ` or `ℤ` with the core instances, so that the data files
load fast and the kernel reduces the core arithmetic directly. The ring-valued semantics
(`evalZ`, `evalN`, `evP`, `combo`) and the correctness lemmas live in `FurioLombardo.M2.Spec`.

* Integer coefficient lists (constant term first): `addZ`, `smulZ`, `mulZ`, `mulXZ`, `redZ`
  (reduction modulo a monic polynomial given by its lower coefficients), `homogL` (homogenized
  Horner evaluation, for characteristic polynomials of `W(θ)/D`), `digitsZ` (balanced digits in
  base `2^k`), `evalI` (Horner evaluation in `ℤ`, used at `2^k` for Kronecker checks).
* Packed polynomials modulo a prime `p`: a polynomial with coefficients in `[0, p)` and at most
  `n` coefficients is the natural number `Σ c_i Bw^i`, `Bw = 2^128`. The kernel multiplies such
  numbers with one GMP multiplication; slots never overflow for `p < 2^20` and at most 44 slots.
* Fixed width decoding of certificate records stored as one natural number (`decW`, `zz`).
-/

namespace FurioLombardo.M2

/-! ## Coefficient lists -/

/-- Horner evaluation in `ℤ` (kernel version of `evalZ`). -/
def evalI (t : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + t * evalI t l

/-- `Σ a_i b_i`. -/
def dotZ : List ℤ → List ℤ → ℤ
  | a :: l, b :: m => a * b + dotZ l m
  | _, _ => 0

/-- Coefficientwise sum. -/
def addZ : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addZ l m

/-- Scalar multiple. -/
def smulZ (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: l => c * a :: smulZ c l

/-- Product. -/
def mulZ : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: l, m => addZ (smulZ a m) (0 :: mulZ l m)

/-- `X * r` reduced once modulo the monic `X ^ gl.length + gl`: if `r` has length `gl.length`,
the top coefficient of `0 :: r` is folded back using `X ^ n = -gl`. -/
def mulXZ (gl r : List ℤ) : List ℤ :=
  if r.length = gl.length then addZ (0 :: r.dropLast) (smulZ (-(r.getLastD 0)) gl) else 0 :: r

/-- Reduction modulo the monic `X ^ gl.length + gl` (Horner scheme from the top). -/
def redZ (gl : List ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: l => addZ [a] (mulXZ gl (redZ gl l))

/-- `Σ_i c_i D^(n-i) W^i` for `cs = [c_0, ..., c_n]`, reduced modulo `X ^ gl.length + gl`. -/
def homogL (gl W : List ℤ) (D : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: cs => redZ gl (addZ [c * D ^ cs.length] (mulZ W (homogL gl W D cs)))

/-- Every coefficient is zero. -/
def allZero : List ℤ → Bool
  | [] => true
  | a :: l => a == 0 && allZero l

/-- Every coefficient is divisible by `p`. -/
def allDvd (p : ℤ) : List ℤ → Bool
  | [] => true
  | a :: l => a % p == 0 && allDvd p l

/-- The `n` balanced digits in base `2^k` of `N` (constant digit first). -/
def digitsZ (k : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n + 1, N => Int.bmod N (2 ^ k) :: digitsZ k n ((N - Int.bmod N (2 ^ k)) / ((2 ^ k : ℕ) : ℤ))

/-- `Σ c_i r^i mod p` by Horner (constant term first). -/
def hornerMod (p : ℤ) (r : ℤ) : List ℤ → ℤ
  | [] => 0
  | c :: l => (c + r * hornerMod p r l) % p

/-- Every entry has absolute value at most `b`. -/
def allBounded (b : ℕ) : List ℤ → Bool
  | [] => true
  | a :: l => (a.natAbs ≤ b) && allBounded b l

/-! ## Packed polynomials modulo `p` -/

/-- The slot base `2^128`. -/
def Bw : ℕ := 2 ^ 128

/-- `pack l = Σ l_i Bw^i`. -/
def pack : List ℕ → ℕ
  | [] => 0
  | a :: l => a + Bw * pack l

/-- The first `n` slots of `N`, each reduced modulo `p`, repacked. -/
def modSlots (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, N => N % Bw % p + Bw * modSlots p n (N / Bw)

/-- `Σ_j slot_j(H) * T_j` for the list `Ts = [T_0, T_1, ...]`. -/
def foldT : List ℕ → ℕ → ℕ
  | [], _ => 0
  | T :: Ts, H => H % Bw * T + foldT Ts (H / Bw)

/-- Product modulo `p` and a monic `g` of degree `d`, given the table `Ts` of
`X^(d+j) mod (g, p)`, `j < d - 1`: the low `d` slots of `N * M` plus the high slots folded
through the table, reduced modulo `p`. -/
def mulmod (p d : ℕ) (Ts : List ℕ) (N M : ℕ) : ℕ :=
  modSlots p d (N * M % Bw ^ d + foldT Ts (N * M / Bw ^ d))

/-- One reduction step modulo `p` and a monic `g` of degree `d` of a packed `H` with at most
`d + 1` slots, with `T0 = X^d mod (g, p)`. -/
def redOnce (p d T0 H : ℕ) : ℕ :=
  modSlots p d (H % Bw ^ d + H / Bw ^ d * T0)

/-- `X * N` modulo `p` and a monic `g` of degree `d`. -/
def mulX (p d T0 N : ℕ) : ℕ := redOnce p d T0 (N * Bw)

/-- `X^d mod (g, p)` for `g = X^d + Σ_{i<d} gl_i X^i`: the packed list of `-gl_i mod p`. -/
def negLow (p : ℕ) (gl : List ℤ) : ℕ := pack (gl.map fun c => ((-c) % (p : ℤ)).toNat)

/-- The table `[T, X T, X^2 T, ...]` (`n` entries) modulo `(g, p)`. -/
def mkTable (p d T0 : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, T => T :: mkTable p d T0 n (mulX p d T0 T)

/-- Binary digits, most significant first (`fuel` bounds the number of digits). -/
def bitsHigh : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else bitsHigh fuel (n / 2) ++ [n % 2 == 1]

/-- `X^e mod (g, p)`, packed, by left to right binary powering, for `g` monic of degree `d`,
`T0 = X^d mod (g, p)` and `Ts` the table of `mulmod`. -/
def powXT (p d T0 : ℕ) (Ts : List ℕ) (e : ℕ) : ℕ :=
  (bitsHigh 64 e).foldl (fun acc b =>
    let s := mulmod p d Ts acc acc
    if b then mulX p d T0 s else s) 1

/-- Product of packed polynomials, `n` slots kept after each product. -/
def prodP (p n : ℕ) : List ℕ → ℕ
  | [] => 1 % p
  | a :: l => modSlots p n (a * prodP p n l)

/-! ## Fixed width records -/

/-- `n` fields of `w` bits of `N`, least significant first, and the remaining high bits. -/
def decW (w : ℕ) : ℕ → ℕ → List ℕ × ℕ
  | 0, N => ([], N)
  | n + 1, N =>
    match decW w n (N / 2 ^ w) with
    | (l, r) => (N % 2 ^ w :: l, r)

/-- Zigzag decoding: `0, 1, 2, 3, 4, ... ↦ 0, -1, 1, -2, 2, ...`. -/
def zz (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n + 1) / 2 : ℕ) : ℤ)

end FurioLombardo.M2
