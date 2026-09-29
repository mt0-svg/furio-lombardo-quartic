import FurioLombardo.Discharge.R7.ConcreteKv
/-! Residues at 28 bits of `4 · coeff_i F_k` (the table `tG28` of M4Log/IntModelKv.lean).
Run from lean/: lake env lean ../code/local-group/integral_model_residues.lean -/
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7.ConcreteKv
#eval (List.range 7).map fun i => modT (zres (rl 0 i)) 28
#eval (List.range 7).map fun i => modT (zres (rl 1 i)) 28
#eval (List.range 7).map fun i => (modT (zres (rl 0 i)) 16 == tG 0 i, modT (zres (rl 1 i)) 16 == tG 1 i)
