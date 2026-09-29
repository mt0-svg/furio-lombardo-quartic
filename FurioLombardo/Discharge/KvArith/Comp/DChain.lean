import FurioLombardo.Discharge.KvArith.Comp.Cantor

/-!
# The chain of the D_i values: the computational part (lane lean-kv-arith)

No Mathlib import. From a pair `D`, a base pair `E0` and a start `R`, a list of step codes: `0` doubling,
`1` addition of `D`, `2` addition of `E0`, `3` addition of `-E0`. `dcoef` tracks the exponents `(m, e)` of
`[R] = [D]^m [E0]^e`. `chainSteps J` from `R = D`: `N D` by double-and-add (`N = 2^4 NM = 2882880`), `+ E0`,
then `J` rounds of (doubling, `- E0`), so `[R_J] = [D]^(2^J N) [E0]` (probe:
code/local-group/di_values_ball_run.sh). Soundness and the class statement: `KvArith/DChain.lean`.
-/

universe u

namespace FurioLombardo.Discharge.KvArith

section Programs

variable {A : Type u} (o : Ops A)

/-- One step of the chain. -/
def dstep (f : Sext A) (D E0 R : Mum A) : Nat → Option (Mum A)
  | 0 => cantorDbl o f R
  | 1 => cantorAdd o f R D
  | 2 => cantorAdd o f R E0
  | _ => cantorAdd o f R (Mum.neg o E0)

/-- The chain of steps `ss` from `R`. -/
def drun (f : Sext A) (D E0 : Mum A) : List Nat → Mum A → Option (Mum A)
  | [], R => some R
  | s :: ss, R => (dstep o f D E0 R s).bind (drun f D E0 ss)

end Programs

/-- The exponents after one step. -/
def dcoef1 (me : Int × Int) : Nat → Int × Int
  | 0 => (2 * me.1, 2 * me.2)
  | 1 => (me.1 + 1, me.2)
  | 2 => (me.1, me.2 + 1)
  | _ => (me.1, me.2 - 1)

/-- The exponents `(m, e)` of `[R] = [D]^m [E0]^e` after the steps `ss`. -/
def dcoef : List Nat → Int × Int → Int × Int
  | [], me => me
  | s :: ss, me => dcoef ss (dcoef1 me s)

/-- The multiple `N = 2^4 NM = 2882880` of the D_i values. -/
def dN : Nat := 2882880

/-- The bits of `dN` after the leading one. -/
def dNBits : List Nat := [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]

/-- The steps of `N D` by double-and-add from `D`. -/
def mulSteps : List Nat := dNBits.flatMap (fun b => if b = 1 then [0, 1] else [0])

/-- The J rounds of (doubling, `- E0`). -/
def tailSteps : Nat → List Nat
  | 0 => []
  | J + 1 => tailSteps J ++ [0, 3]

/-- The whole chain: `N D`, `+ E0`, then `J` rounds. -/
def chainSteps (J : Nat) : List Nat := mulSteps ++ [2] ++ tailSteps J

end FurioLombardo.Discharge.KvArith
