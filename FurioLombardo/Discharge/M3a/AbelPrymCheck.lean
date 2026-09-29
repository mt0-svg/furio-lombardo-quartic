import FurioLombardo.Discharge.M3a.AbelPrymDefs

/-!
# Kernel checks of the Abel-Prym certificates (WP4 of the M3a discharge)

Each theorem is one `decide +kernel` run of lane M1's Kronecker test (`checkK`, `eqCheck`) on the
expressions of AbelPrymDefs.lean, or a residue computation in `ZMod 13` at the degree one prime
`(13, θ - 11)`. The known lifts are `i = 0` (`x0`, `p = (0:0:1)`, twist 0), `i = 1` (`x1`,
`(1:1:1)`, twist 1), `i = 2` (`x2`, `(2:0:1)`, twist 0), `i = 3` (`x3`, `(-1:0:1)`, twist 1).
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a

/-! ## `2 · (4 fRev_k) = -δ_k det(2 (M3 + 2t M2 + t² M1))` -/

theorem ck_detS0 : eqCheck 400 (detLhsS 0) (detRhsS 0) = true := by decide +kernel

theorem ck_detS1 : eqCheck 400 (detLhsS 1) (detRhsS 1) = true := by decide +kernel

/-! ## The tangent equations -/

theorem ck_tan0 : ∀ j : Fin 3, checkK 320 (.sub (tanE 0 0 0 0 j) (.int 0)) = true := by
  decide +kernel

theorem ck_tan1 : ∀ j : Fin 3, checkK 320 (.sub (tanE 1 1 1 1 j) (.int 0)) = true := by
  decide +kernel

theorem ck_tan2 : ∀ j : Fin 3, checkK 320 (.sub (tanE 2 0 2 0 j) (.int 0)) = true := by
  decide +kernel

theorem ck_tan3 : ∀ j : Fin 3, checkK 320 (.sub (tanE 3 1 (-1) 0 j) (.int 0)) = true := by
  decide +kernel

/-! ## The coefficients of `U'` -/

theorem ck_u0 : checkK 400 (u0Chk 0 0) = true ∧ checkK 400 (u1Chk 0 0) = true := by
  decide +kernel

theorem ck_u1 : checkK 576 (u0Chk 1 1) = true ∧ checkK 576 (u1Chk 1 1) = true := by
  decide +kernel

theorem ck_u2 : checkK 576 (u0Chk 2 0) = true ∧ checkK 576 (u1Chk 2 0) = true := by
  decide +kernel

theorem ck_u3 : checkK 400 (u0Chk 3 1) = true ∧ checkK 400 (u1Chk 3 1) = true := by
  decide +kernel

/-! ## The rank condition -/

theorem ck_n0 : checkK 320 (nChk 0 0 0) = true := by decide +kernel

theorem ck_n1 : checkK 320 (nChk 1 1 1) = true := by decide +kernel

theorem ck_n2 : checkK 320 (nChk 2 2 0) = true := by decide +kernel

theorem ck_n3 : checkK 320 (nChk 3 (-1) 0) = true := by decide +kernel

/-- `apN` has a nonzero residue at `(13, θ - 11)` for the four points. -/
theorem ck_nres : ∀ i : Fin 4, (1 : ZMod 13) * evalL (11 : ZMod 13) (combo (apNL i) zkNum) ≠ 0 := by
  decide +kernel

/-! ## The ruling entry `(1, 3)` -/

theorem ck_ent0 : eqCheck 416 (entLhs 0 0 0 0) (entRhs 0 0) = true := by decide +kernel

theorem ck_ent1 : eqCheck 720 (entLhs 1 1 1 1) (entRhs 1 1) = true := by decide +kernel

theorem ck_ent2 : eqCheck 736 (entLhs 2 0 2 0) (entRhs 2 0) = true := by decide +kernel

theorem ck_ent3 : eqCheck 416 (entLhs 3 1 (-1) 0) (entRhs 3 1) = true := by decide +kernel

/-! ## Nonzero integers -/

theorem ck_apNZ : ∀ i : Fin 4, apMN i ≠ 0 ∧ apUdN i ≠ 0 ∧ apDN i ≠ 0 := by decide +kernel

end FurioLombardo.Discharge.M3a.Bruin
