import FurioLombardo.M2.Global

/-!
# The per-prime certificate checker of lane M2

A certificate for an odd prime `p` not dividing `ResZ` is a record `PData`:

* `facs`: monic factors `L` of `fZ mod p` (coefficients in `[0, p)`, constant first), each with
  a generator certificate: coordinates `a`, `c` (on the integral basis `w_j = W_j(θ)/DD`) of
  `α` and of `c = p / α`, and for `deg L ≥ 2` a Bezout pair `sp`, `up` with
  `C sp + L up ≡ 1 mod p` (`C = DD c` as a polynomial in `θ`);
* `ss`: for `e = 1, ..., E` (with `p ^ (E + 1) > Bnd`), a packed `s_e` with
  `s_e (X^(p^e) - X) ≡ ∏_{deg L ∣ e} L mod (fZ, p)`.

`checkPrime p N` decodes the record from one natural number and runs every check. The soundness
theorem (`FurioLombardo.M2.checkPrime_sound`) says that a successful check makes every prime
ideal `P` above `p` with `p ^ f(P) ≤ Bnd` principal.
-/

namespace FurioLombardo.M2

/-- The class bound of lane M2: every prime ideal of norm at most `Bnd` has a certificate. It is
above Zimmert's Satz 2 value for K21 at `γ = 1/2, α = 1/12` (107991) and at `γ = 9/20` (100618). -/
def Bnd : ℕ := 120000

/-- The Kronecker exponent: polynomials are evaluated at `2 ^ kK`. -/
def kK : ℕ := 512

/-- `2 ^ kK` in `ℤ`, computed through `ℕ` (the kernel accelerates `Nat.pow` only). -/
def tK : ℤ := ((2 ^ kK : ℕ) : ℤ)

/-- A factor of `fZ mod p` with its generator certificate. -/
structure Fac where
  deg : ℕ
  L : List ℕ
  a : List ℤ
  c : List ℤ
  sp : List ℕ
  up : List ℕ
  deriving Inhabited

/-- The certificate for one prime. -/
structure PData where
  facs : List Fac
  ss : List (List ℕ)
  deriving Inhabited

/-! ## Decoding -/

/-- One factor: degree (8 bits), the `deg` lower coefficients of `L` (17 bits each), `a` (21
fields of 16 bits, zigzag), `c` (21 fields of 28 bits, zigzag), and for `deg ≥ 2` the `deg`
coefficients of `sp` and the 21 coefficients of `up` (17 bits each). -/
def decFac (N : ℕ) : Fac × ℕ :=
  match decW 8 1 N with
  | (dl, N1) =>
    match decW 17 (dl.headD 0) N1 with
    | (Llow, N2) =>
      match decW 16 21 N2 with
      | (al, N3) =>
        match decW 28 21 N3 with
        | (cl, N4) =>
          if dl.headD 0 = 1 then
            (⟨1, Llow ++ [1], al.map zz, cl.map zz, [], []⟩, N4)
          else
            match decW 17 (dl.headD 0) N4 with
            | (spl, N5) =>
              match decW 17 21 N5 with
              | (upl, N6) => (⟨dl.headD 0, Llow ++ [1], al.map zz, cl.map zz, spl, upl⟩, N6)

/-- `n` factors. -/
def decFacs : ℕ → ℕ → List Fac × ℕ
  | 0, N => ([], N)
  | n + 1, N =>
    match decFac N with
    | (fac, N1) =>
      match decFacs n N1 with
      | (l, N2) => (fac :: l, N2)

/-- `n` packed Bezout multipliers of 21 coefficients (17 bits each). -/
def decSS : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | n + 1, N =>
    match decW 17 21 N with
    | (s, N1) => s :: decSS n N1

/-- The record: number of factors (8 bits), `E` (8 bits), the factors, the `E` multipliers. -/
def decode (N : ℕ) : PData :=
  match decW 8 2 N with
  | (h, N1) =>
    match decFacs (h.headD 0) N1 with
    | (facs, N2) => ⟨facs, decSS (h.getD 1 0) N2⟩

/-! ## Checks -/

/-- `L` is monic of degree `deg ≥ 1` with coefficients in `[0, p)`. -/
def facOK (p : ℕ) (fac : Fac) : Bool :=
  1 ≤ fac.deg && fac.L.length == fac.deg + 1 && fac.L.getLast? == some 1 && fac.L.all (· < p)

/-- Degree one factor `L = X + l0`: `C(-l0) ≢ 0 mod p` and `(X + l0) C - C_20 fZ ≡ 0 mod p`. -/
def linCheck (p : ℕ) (L : List ℕ) (Cl : List ℤ) : Bool :=
  let l0 : ℤ := (L.headD 0 : ℕ)
  hornerMod p (-l0) Cl != 0 &&
    allDvd p (addZ (addZ (0 :: Cl) (smulZ l0 Cl)) (smulZ (-(Cl.getLastD 0)) fL))

/-- Factor of degree at least 2: `L C mod fZ ≡ 0 mod p` and `C sp + L up ≡ 1 mod p`. -/
def hiCheck (p : ℕ) (L : List ℕ) (Cl : List ℤ) (sp up : List ℕ) : Bool :=
  let Lz : List ℤ := L.map fun x : ℕ => (x : ℤ)
  allDvd p (redZ fLow (mulZ Lz Cl)) &&
    allDvd p (addZ (addZ (mulZ Cl (sp.map fun x : ℕ => (x : ℤ)))
      (mulZ Lz (up.map fun x : ℕ => (x : ℤ)))) [-1])

/-- The generator certificate of `(p, L(θ))`: `α c = p` by a Kronecker check (quotient digits
`Ql`), the coefficients `Cl` of `C = DD c` recovered from `C(2^kK)`, then `linCheck` or
`hiCheck`. -/
def genCheck (p : ℕ) (fac : Fac) : Bool :=
  fac.a.length == 21 && fac.c.length == 21 && allBounded (2 ^ 15) fac.a &&
    allBounded (2 ^ 27) fac.c &&
    (let Ak := dotZ fac.a omL
     let Ck := dotZ fac.c omL
     let Hv := Ak * Ck - (p : ℤ) * DD ^ 2
     let Qv := Hv / Fk
     let Ql := digitsZ kK 20 Qv
     let Cl := digitsZ kK 21 Ck
     Hv == Fk * Qv && evalI tK Ql == Qv && allBounded (2 ^ 425) Ql &&
       evalI tK Cl == Ck && allBounded (2 ^ 112) Cl &&
       (if fac.deg = 1 then linCheck p fac.L Cl else hiCheck p fac.L Cl fac.sp fac.up))

/-- Factor certificate for residue degree `e`: `s (X^(p^e) - X) ≡ ∏_{deg L ∣ e} L mod (fZ, p)`. -/
def facCheckE (p T0 : ℕ) (Ts : List ℕ) (facs : List Fac) (e : ℕ) (s : List ℕ) : Bool :=
  let sel := facs.filter fun fac => e % fac.deg == 0
  decide ((sel.map Fac.deg).sum ≤ 21) && decide (s.length ≤ 21) && s.all (· < p) &&
    mulmod p 21 Ts (pack s) (modSlots p 21 (powXT p 21 T0 Ts (p ^ e) + (p - 1) * Bw)) ==
      redOnce p 21 T0 (prodP p 22 (sel.map fun fac => pack fac.L))

/-- The factor certificates for `e = e0, e0 + 1, ...`. -/
def checkSS (p T0 : ℕ) (Ts : List ℕ) (facs : List Fac) : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | e, s :: ss => facCheckE p T0 Ts facs e s && checkSS p T0 Ts facs (e + 1) ss

/-- All checks for the prime `p`. -/
def checkData (p : ℕ) (d : PData) : Bool :=
  let T0 := negLow p fLow
  let Ts := mkTable p 21 T0 20 T0
  ResZ % (p : ℤ) != 0 && decide (3 ≤ p) && decide (p < 2 ^ 17) &&
    decide (Bnd < p ^ (d.ss.length + 1)) && d.facs.all (facOK p) &&
    checkSS p T0 Ts d.facs 1 d.ss && d.facs.all (genCheck p)

/-- The checker run by the kernel on the packed record `N`. -/
def checkPrime (p N : ℕ) : Bool := checkData p (decode N)

/-! ## Blocks of consecutive integers -/

/-- Every record of the list passes `checkPrime` (proved one record at a time). -/
def AllTrue : List (ℕ × ℕ) → Prop
  | [] => True
  | x :: l => checkPrime x.1 x.2 = true ∧ AllTrue l

/-- The primes up to 337 (every composite number up to `Bnd` has one of them as a factor). -/
def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337]

/-- The primes treated separately (`FurioLombardo.M2.Special`). -/
def isSpecial (n : ℕ) : Bool := n == 2 || n == 7 || n == 45613

/-- `n` has a proper factor in `smallPrimes`. -/
def hasSmallFactor (n : ℕ) : Bool := smallPrimes.any fun q => decide (q < n) && n % q == 0

/-- Every `n` in `[lo, lo + len)` is below 2, special, has a small factor, or is the next entry of
the increasing list `ps`, and `ps` is used up. -/
def coverCheck : ℕ → ℕ → List ℕ → Bool
  | _, 0, ps => ps.isEmpty
  | n, len + 1, [] => (decide (n < 2) || isSpecial n || hasSmallFactor n) && coverCheck (n + 1) len []
  | n, len + 1, q :: qs =>
    if q == n then coverCheck (n + 1) len qs
    else (decide (n < 2) || isSpecial n || hasSmallFactor n) && coverCheck (n + 1) len (q :: qs)

end FurioLombardo.M2
