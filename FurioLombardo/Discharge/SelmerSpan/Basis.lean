import FurioLombardo.Discharge.SelmerSpan.Indep
import FurioLombardo.Discharge.M3a.ConcreteKv

/-!
# The Selmer input of (K2), one statement per twist (lane SelmerSpan)

Lane M3a's `TwistInputsKv k D φ xa xb` asks for points `Dpt : Fin 7 → A(K_v)` and, for (K2), two
things about them: a Selmer basis `g_1, ..., g_4` over K21 whose images at `v` are
`∏ μ_v(D_i)^(SB i j)`, and the independence of the `μ_v(D_i)` in `H g`. With the points `Dpt k i` of
Dpt.lean the independence is `indep_Dpt` (Indep.lean); the first part is the statement
`SelmerBasisK21 k SB`.

What `SelmerBasisK21 k SB` asserts is the output of the 2-descent over K21 (the 2-Selmer group
has dimension 4, computed from the S-units of the factor fields of degree 42 and 84 of `fRev k`),
together with the expression of the local images of its generators in the basis `μ_v(D_i)` (the
matrix `SB` of lane M4's `T0.data`, `T1.data`). It is proved for both twists:
`SelmerBasis.Assembly.selmerBasis_0`, `selmerBasis_1` (SelmerBasis/Assembly.lean, through
`selmerBasis_of_interfaces`).

`twistInputsKv_of_selmerBasis`: `TwistInputsKv` from `SelmerBasisK21`, the logarithm conditions and
`M4RestKv`, all at the points `Dpt k` ((K1) is lane M3a's theorem `Bruin.poonenSchaefer_fRev`).
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin
open FurioLombardo.Discharge.Analytic (LogChartFin)

namespace FurioLombardo.Discharge.SelmerSpan

attribute [local instance] goodSextic_fRev_Kv

/-- **A Selmer basis of the twist `k`.** Four classes `g_j` of
`H(fRev k) = L^× / K21^× (L^×)²` over K21 span the image of the `x - T` map on `A(K21)`, and the image
of `g_j` at `v` is `∏_i μ_v(D_i)^(SB i j)` for the local divisors `D_i = Dpt k i`. Proved for lane M4's
`SB` by `SelmerBasis.Assembly.selmerBasis_0`, `selmerBasis_1`. -/
def SelmerBasisK21 (k : Fin 2) (SB : Matrix (Fin 7) (Fin 4) ℤ) : Prop :=
  ∃ g : Fin 4 → H (fRev k), SelmerSpan (fRev k) g ∧
    ∀ j, Hmap σ (fRev k) (g j) = ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt k i)) ^ SB i j

/-- **`TwistInputsKv` at the points `Dpt k`**: the independence conjunct is `indep_Dpt`. -/
theorem twistInputsKv_of_selmerBasis {k : Fin 2} {D : FurioLombardo.M4.TwistData}
    {φ : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k) → Jac (fRev k)}
    {xa xb : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)}
    {lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2])} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    (hB : SelmerBasisK21 k D.SB) (hL : LogChartFin lam)
    (hM : M4RestKv k D φ xa xb lam (Dpt k) lamD) : TwistInputsKv k D φ xa xb :=
  ⟨lam, Dpt k, lamD, hB, indep_Dpt k, hL, hM⟩

end FurioLombardo.Discharge.SelmerSpan
