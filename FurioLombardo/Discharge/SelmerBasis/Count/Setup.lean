import Mathlib
import FurioLombardo.Discharge.R7.Psi
import FurioLombardo.Vendor.Toolbox.Padic.UnitBall

/-!
# Count lane: R7's base point data over a local field

R7's `SetupKv` (R7/ChartKv.lean) fixes the scaling pair of `FurioLombardo.Vendor.Toolbox.G2Formal.Setup` to
`(OKv, pv)` over `M4Cert.Kv`. Here the same data over any nontrivially normed ultrametric field
`K` of characteristic zero with a uniformizer `π` (`FurioLombardo.Vendor.Toolbox.UnitBall.IsUniformizer`):
`LSetup.toSetup hπ` has `O = unitBall K` and `π = hπ.toBall`.
-/

open Polynomial
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall

namespace FurioLombardo.Discharge.SelmerBasis.Count

/-- The genericity data of a base point over a field `K` (the fields of `Setup` after `O`, `π`). -/
structure LSetup (K : Type*) [Field K] where
  f : K[X]
  hf : f.natDegree ≤ 6
  V0 : K[X]
  hV0d : V0.degree < 4
  hV00 : V0.coeff 0 ≠ 0
  c0 : K
  hc0 : c0 ≠ 0
  w0 : K[X]
  hw0m : w0.Monic
  hw0d : w0.natDegree = 2
  hfV0 : f - V0 ^ 2 = C c0 * (X ^ 4 * w0)
  hw00 : w0.coeff 0 ≠ 0

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CharZero K]

/-- The `Setup` of an `LSetup`, with `O = unitBall K` and `π` a uniformizer. -/
noncomputable abbrev LSetup.toSetup (D : LSetup K) {π : K} (hπ : IsUniformizer π) : Setup K where
  O := unitBall K
  π := hπ.toBall
  hπ0 := hπ.ne_zero
  hbd := hπ.exists_pow_mul_mem
  h2 := two_ne_zero
  f := D.f
  hf := D.hf
  V0 := D.V0
  hV0d := D.hV0d
  hV00 := D.hV00
  c0 := D.c0
  hc0 := D.hc0
  w0 := D.w0
  hw0m := D.hw0m
  hw0d := D.hw0d
  hfV0 := D.hfV0
  hw00 := D.hw00

end FurioLombardo.Discharge.SelmerBasis.Count
