/- k1_bench.lean: kernel cost of the computational layer (`KvArith.Comp`, no Mathlib
import) under `decide +kernel`, at P = 200 bits (600 π-digits) and P = 1000 bits. Loops of n steps; each
theorem is one declaration, checked in order on one thread (`-j1`, `Elab.async false`), so the n-th
profiler line is the kernel time of the n-th theorem.
The inverse chain goes through `ballOps` (normalized balls): the raw `Ball.inv` on unnormalized balls lets
the scale grow and hits the 3P radius cap after 9 steps. Repeated doubling of a random pair (not on the
curve) loses about 24(k - 1) π-digits at step k (measured: 21, 17, 47, 71, 95, 119, 143) and fails at step 8, so the doubling chain has 6 steps. Run from lean/:
  lake env lean -j1 ../code/lean-kv-arith/k1_bench.lean -/
import FurioLombardo.Discharge.KvArith.Comp.TM
import FurioLombardo.Discharge.KvArith.Comp.Cantor
open FurioLombardo.Discharge.KvArith
set_option profiler true
set_option profiler.threshold 10
set_option maxRecDepth 1000000
set_option Elab.async false

def k2 : Ctx := Ctx.ofP 200
def k10 : Ctx := Ctx.ofP 1000
def bb (k : Ctx) (a b c : Nat) : Ball := Ball.ofN k (a, b, c)
def x0 (k : Ctx) : Ball := bb k 12345678901234567 98765432109876543 5555555555555555
-- (1) triple products: x ← x² + c
def loopN (k : Ctx) : Nat → N3 → N3
  | 0, x => x
  | n + 1, x => loopN k n (addN k (mulN k x x) (3, 5, 7))
-- (2) ball products: x ← x² + c (Ball.mul with normalization, Ball.add)
def loopB (k : Ctx) : Nat → Ball → Ball
  | 0, x => x
  | n + 1, x => loopB k n (Ball.add k (Ball.mul k x x) (bb k 3 5 7))
-- (3) ball inverses: x ← 1/(x + c)
def loopI (k : Ctx) : Nat → Ball → Option Ball
  | 0, x => some x
  | n + 1, x => ((ballOps k).inv (Ball.add k x (bb k 3 5 7))).bind (loopI k n)
-- (4) Taylor models of order 4 over pv^9 O: M ← M² + N
def TT (k : Ctx) : TCtx := ⟨k, 9, 4⟩
def M1 (k : Ctx) : TM := ⟨[bb k 3 5 7, bb k 1 2 3, bb k 11 0 5, bb k 2 2 2, bb k 9 9 1], TM.zeroB (TT k)⟩
def M2 (k : Ctx) : TM := ⟨[bb k 5 1 0, bb k 7 7 7, bb k 1 0 0, bb k 0 0 1, bb k 3 3 3], TM.zeroB (TT k)⟩
def loopT (k : Ctx) : Nat → TM → TM
  | 0, M => M
  | n + 1, M => loopT k n (TM.add (TT k) (TM.mul (TT k) M M) (M2 k))
-- (5) Cantor additions on balls: D ← D + E (not on a curve: the cost only)
def D1 (k : Ctx) : Mum Ball := ⟨bb k 3 1 0, bb k 5 0 1, bb k 7 2 2, bb k 1 1 1⟩
def D2 (k : Ctx) : Mum Ball := ⟨bb k 2 0 1, bb k 1 3 0, bb k 5 5 5, bb k 9 0 2⟩
def fS (k : Ctx) : Sext Ball := ⟨bb k 1 0 0, bb k 3 0 0, bb k 5 1 0, bb k 7 0 0, bb k 1 1 1, bb k 2 0 3, bb k 1 2 0⟩
def loopC (k : Ctx) : Nat → Mum Ball → Option (Mum Ball)
  | 0, D => some D
  | n + 1, D => (cantorAdd (ballOps k) (fS k) D (D2 k)).bind (loopC k n)
def loopD (k : Ctx) : Nat → Mum Ball → Option (Mum Ball)
  | 0, D => some D
  | n + 1, D => (cantorDbl (ballOps k) (fS k) D).bind (loopD k n)

theorem n200_1000 : (loopN k2 1000 (x0 k2).c).1 ≥ 0 := by decide +kernel
theorem b200_1000 : (loopB k2 1000 (x0 k2)).r ≥ 0 := by decide +kernel
theorem i200_100 : ((loopI k2 100 (x0 k2)).map (·.r)).isSome = true := by decide +kernel
theorem t200_20 : (loopT k2 20 (M1 k2)).R.r ≥ 0 := by decide +kernel
theorem t200_100 : (loopT k2 100 (M1 k2)).R.r ≥ 0 := by decide +kernel
theorem c200_20 : ((loopC k2 20 (D1 k2)).map (·.u0.r)).isSome = true := by decide +kernel
theorem d200_6 : ((loopD k2 6 (D1 k2)).map (·.u0.r)).isSome = true := by decide +kernel
theorem b1000_1000 : (loopB k10 1000 (x0 k10)).r ≥ 0 := by decide +kernel
theorem c1000_20 : ((loopC k10 20 (D1 k10)).map (·.u0.r)).isSome = true := by decide +kernel
theorem c1000_100 : ((loopC k10 100 (D1 k10)).map (·.u0.r)).isSome = true := by decide +kernel
