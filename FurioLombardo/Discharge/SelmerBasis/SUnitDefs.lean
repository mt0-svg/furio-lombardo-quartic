import FurioLombardo.Discharge.M3b.Fields
import FurioLombardo.Discharge.M3a.PolyK
import FurioLombardo.Discharge.SelmerBasis.SUnitData

/-!
# The global generators (frozen definitions)

* `gensL : Fin 29 → L42`, `gensN : Fin 53 → N84`: S-units (S = the primes above 2 and 7) whose
  classes span `L42^×/(L42^×)²`, `N84^×/(N84^×)²` restricted to `K(S,2)` (`SUnitSpan`).
* `Pgen : Fin 82 → K21[X]`: `Pgen s (α) = gensL s`, `Pgen s (β) = 1` for `s < 29`, and
  `Pgen s (α) = 1`, `Pgen s (β) = gensN (s - 29)` for `s ≥ 29`, where `α ∈ L42`, `β ∈ N84` are the
  roots `alphaR`, `betaR` of `q k`, `h k`. The class of `Pgen s (T)` in `H (fRev k)` is the global
  generator `gK k s` (GlobalGens.lean).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b

/-- An element of `L42` from two zk lists. -/
noncomputable def mkL (l : List (List ℤ)) : L42 := ⟨zkE (l.getD 0 []), zkE (l.getD 1 [])⟩

/-- An element `a0 + a1 ω + (b0 + b1 ω) (2 ω_N)` of `N84` from four zk lists. -/
noncomputable def mkN (l : List (List ℤ)) : N84 :=
  ⟨⟨zkE (l.getD 0 []), zkE (l.getD 1 [])⟩, ⟨2 * zkE (l.getD 2 []), 2 * zkE (l.getD 3 [])⟩⟩

/-- The 29 generators of `L42`. -/
noncomputable def gensL (s : Fin 29) : L42 := mkL (SUnitData.gL.getD s [])

/-- The 53 generators of `N84`. -/
noncomputable def gensN (s : Fin 53) : N84 := mkN (SUnitData.gN.getD s [])

/-- The polynomial representative of the global generator `s`. -/
noncomputable def Pgen (s : Fin 82) : K21[X] :=
  pQ (SUnitData.pgenDen.getD s 1) ((SUnitData.pgen.getD s []).map .lin)

/-- The root `α` of `q k` in `L42`. -/
noncomputable def alphaR : L42 :=
  ⟨zkE (SUnitData.alphaL.getD 0 []) / SUnitData.alphaDen,
    zkE (SUnitData.alphaL.getD 1 []) / SUnitData.alphaDen⟩

/-- The root `β` of `h k` in `N84`. -/
noncomputable def betaR : N84 :=
  ⟨⟨zkE (SUnitData.betaN.getD 0 []) / SUnitData.betaDen,
      zkE (SUnitData.betaN.getD 1 []) / SUnitData.betaDen⟩,
    ⟨zkE (SUnitData.betaN.getD 2 []) / SUnitData.betaDen,
      zkE (SUnitData.betaN.getD 3 []) / SUnitData.betaDen⟩⟩

end FurioLombardo.Discharge.SelmerBasis
