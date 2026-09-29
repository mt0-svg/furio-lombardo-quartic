/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
/- Toolbox port of https://github.com/MichaelStollBayreuth/EllipticCurves at commit 1e47094 (Apache License 2.0,
copy in Toolbox/Stoll/LICENSE). Changed: module paths EllipticCurves.* renamed Toolbox.Stoll.*, namespaces
ChabautyColeman and InfiniteOrderExample renamed Toolbox.Stoll.*, data instances on Mathlib types scoped to
Toolbox.Stoll; details in Toolbox/THIRD_PARTY.md. -/
-- Vendored from the Chabauty project (`Chabauty/Series/FormalGroupLaw.lean`).

module

public import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.FormalGroupLaw.Basic
public import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.FormalGroupLaw.Invariance
public import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.FormalGroupLaw.Points
public import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.FormalGroupLaw.Log

@[expose] public section


/-!
# Formal group laws and their points in the maximal ideal

`FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw O ι` is an `ι`-dimensional commutative formal group law
over `O`: a family of power series `F i` in two blocks of `ι` variables with
`F(X,0) = X`, `F(0,Y) = Y`, `F(X,Y) = F(Y,X)` and `F(F(X,Y),Z) = F(X,F(Y,Z))`, the
substitutions being Mathlib's formal `MvPowerSeries.subst`. (Mathlib's `FormalGroup` is
one-dimensional with points valued in power series rings; here arbitrary finite
dimension and topological `𝔪`-points are needed.)

The development is split across the files re-exported here:
* `Chabauty.Series.FormalGroupLaw.Basic` — the structure, the differential (Jacobian) matrix at the
  origin, and base change along a ring homomorphism;
* `Chabauty.Series.FormalGroupLaw.Invariance` — closedness of the invariant differential
  (`pderiv_diffMatrixInv_symm`), the technical heart of the logarithm construction;
* `Chabauty.Series.FormalGroupLaw.Points` — the commutative monoid of `𝔪`-points, each monoid axiom
  being the corresponding formal axiom of `F` evaluated via `MvPSeries.eval_subst`;
* `Chabauty.Series.FormalGroupLaw.Log` — the formal logarithm `log` (radial antiderivative of the
  invariant differential) and exponential `exp`, with their `p`-adic denominator estimates.

Blueprint nodes: `def:fgl`, `def:fgl-diff`, `def:fgl-log`.
-/

end
