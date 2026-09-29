import FurioLombardo.Discharge.KvArith.Comp.DChain

/-!
# Splitting a chain run (lane lean-m4box)

`drun_append`: a run of the chain on `l₁ ++ l₂` is the run on `l₁` followed by the run on `l₂`. It sits
beside the program so that the generated certificate files cut their runs into chunks without importing
the soundness files.
-/

namespace FurioLombardo.Discharge.KvArith

universe u

theorem drun_append {A : Type u} (o : Ops A) (f : Sext A) (D E0 : Mum A) (l₁ l₂ : List Nat)
    (X : Mum A) : drun o f D E0 (l₁ ++ l₂) X = (drun o f D E0 l₁ X).bind (drun o f D E0 l₂) := by
  induction l₁ generalizing X with
  | nil =>
    simp [drun]
  | cons s ss ih =>
    simp only [List.cons_append, drun]
    rw [Option.bind_assoc]
    congr 1
    funext Y
    exact ih Y

end FurioLombardo.Discharge.KvArith
