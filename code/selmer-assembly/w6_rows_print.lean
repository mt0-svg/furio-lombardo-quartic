import FurioLombardo.Discharge.SelmerBasis.W3Place

/-! The rows of `W3.C3 k` (bit `s` of row `i` is entry `(i, s)`), printed for code/selmer-assembly/assembly_data.gp.
Run from lean/: `lake env lean ../code/selmer-assembly/w6_rows_print.lean`. -/

open FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.W3

#eval IO.println s!"W3ROWS = {[QCK 0, QCK 1].map fun q =>
  (List.range 21).map fun i => dotRow nb (fun s => Cg.getD s 0) (q.getD i 0) 82};"
