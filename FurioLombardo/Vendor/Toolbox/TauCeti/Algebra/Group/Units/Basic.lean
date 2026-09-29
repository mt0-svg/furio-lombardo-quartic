/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Toolbox port of https://github.com/TauCetiProject/TauCeti at commit b5174264c004 (Apache License 2.0, copy in
Toolbox/TauCeti/LICENSE). Changed: module paths and namespace TauCeti renamed Toolbox.TauCeti; data instances on
Mathlib types scoped to Toolbox.TauCeti; details in Toolbox/THIRD_PARTY.md. -/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Units.Defs

import Mathlib.Algebra.Group.Commute.Units

/-!
# Squares of units

This file relates squares in a monoid to squares in its group of units.

## Main results

* `FurioLombardo.Vendor.Toolbox.TauCeti.isSquare_units_val_iff`: a unit is a square exactly when its underlying monoid element
  is a square.
-/

public section

namespace FurioLombardo.Vendor.Toolbox.TauCeti

/-- A unit is a square exactly when its underlying monoid element is a square. -/
@[simp]
theorem isSquare_units_val_iff {M : Type*} [Monoid M] {u : Mˣ} :
    IsSquare (u : M) ↔ IsSquare u := by
  constructor
  · rintro ⟨x, hx⟩
    have hxu : IsUnit x := isUnit_mul_self_iff.mp (hx ▸ u.isUnit)
    exact ⟨hxu.unit, Units.ext (by simpa using hx)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(v : M), by simp⟩

end FurioLombardo.Vendor.Toolbox.TauCeti
