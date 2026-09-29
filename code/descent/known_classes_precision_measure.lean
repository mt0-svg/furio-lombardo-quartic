import FurioLombardo.M1.SelmerSet
/-! Measures the Kronecker precisions of the identities of SelmerSet.lean (`ck_known0`, `ck_known1`, `ck_inv0`,
`ck_inv1`; compiled evaluation, not trusted). Run from lean/: `lake env lean ../code/descent/known_classes_precision_measure.lean`.
Output: [512, 832, 192, 192]. -/
namespace FurioLombardo.M1
open Kron
def minKx (e : KE) : ℕ :=
  ((List.range 160).map (fun t => 64 * (t + 1))).find? (fun k => checkK k e) |>.getD 0
#eval IO.println (toString [minKx (.sub (knownL 0) (knownR 0)), minKx (.sub (knownL 1) (knownR 1)),
  minKx (.sub (.mul (.lin (dKL 0)) (.lin (diKL 0))) (.int 1)),
  minKx (.sub (.mul (.lin (dKL 1)) (.lin (diKL 1))) (.int 1))])
end FurioLombardo.M1
