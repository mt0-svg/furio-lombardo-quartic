
/-! ## The chain -/

def oB : Ops Ball := ballOpsF k2
/-- Step codes: 0 doubling, 1 addition of `D`, 2 addition of `E0`, 3 addition of `-E0`. -/
def step (f : Sext Ball) (D E0 : Mum Ball) (R : Mum Ball) : Nat → Option (Mum Ball)
  | 0 => cantorDbl oB f R
  | 1 => cantorAdd oB f R D
  | 2 => cantorAdd oB f R E0
  | _ => cantorAdd oB f R (Mum.neg oB E0)
def run (f : Sext Ball) (D E0 : Mum Ball) : List Nat → Mum Ball → Option (Mum Ball)
  | [], R => some R
  | s :: ss, R => (step f D E0 R s).bind (run f D E0 ss)
/-- The bits of `N = 2^4 NM = 2882880` after the leading one. -/
def nBits : List Nat := [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0]
/-- From `D`: `N D` by double-and-add, `+ E0`, then `J` times (doubling, `- E0`). -/
def chainSteps (J : Nat) : List Nat :=
  nBits.flatMap (fun b => if b = 1 then [0, 1] else [0]) ++ [2] ++ (List.replicate J [0, 3]).flatten
