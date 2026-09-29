import FurioLombardo.M1.Local2
/-! Measures the Kronecker precisions of the identities of Local2.lean (run from lean/: `lake env lean
../code/descent/sieve_2adic_precision_measure.lean`; compiled evaluation, not trusted; the
result goes to code/descent/sieve_2adic_precisions.gp as `lcK`). -/
namespace FurioLombardo.M1
open Kron
def minK (e : KE) : ℕ :=
  ((List.range 160).map (fun t => 64 * (t + 1))).find? (fun k => checkK k e) |>.getD 0
#eval IO.println (toString ([minK (lcGE 5 lcGp5 lcH5), minK (lcGE 7 lcGp7 lcH7),
  minK (.sub (gE 12) (onePE lcT12)), minK (.sub (gE 13) (onePE lcT13))] ++
  lcLeaves.flatMap fun l => [minK (l.2.1.idE lcGp5 l.1), minK (l.2.2.idE lcGp7 l.1)]))
end FurioLombardo.M1
