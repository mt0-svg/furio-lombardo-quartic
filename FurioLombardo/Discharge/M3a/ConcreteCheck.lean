import FurioLombardo.Discharge.M3a.ConcreteDefs

/-!
# Kernel checks of the concrete data (WP2 of the M3a discharge)

Each theorem is one `decide +kernel` run: a Kronecker test (lane M1's `checkK`, at `N = 2 ^ K`) of
every coefficient of a polynomial identity over K21, or a residue computation in `ZMod p` at a
degree one prime `(p, θ - r)` (`r` a root of `f` modulo `p`, found by bruin_data.gp).
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a

/-! ## `2 · (4 f_k) = -δ_k det(2 (M1 + 2t M2 + t² M3))` -/

theorem ck_det0 : eqCheck 448 (detLhs 0) (detRhs 0) = true := by decide +kernel

theorem ck_det1 : eqCheck 448 (detLhs 1) (detRhs 1) = true := by decide +kernel

/-! ## `fRev = c q h` -/

theorem ck_fac0 : eqCheck 320 (facLhs 0) (facRhs 0) = true := by decide +kernel

theorem ck_fac1 : eqCheck 320 (facLhs 1) (facRhs 1) = true := by decide +kernel

/-! ## Bezout certificate `A R + B R' = m` -/

theorem ck_bez0 : eqCheck 384 (bezLhs 0) [.int (bezMZ 0)] = true := by decide +kernel

theorem ck_bez1 : eqCheck 384 (bezLhs 1) [.int (bezMZ 1)] = true := by decide +kernel

theorem ck_bezM : bezMZ 0 ≠ 0 ∧ bezMZ 1 ≠ 0 := by decide +kernel

/-! ## `qDen² disc(q)` and `β² - d = fRev γ` -/

theorem ck_dn0 : checkK 256 (.sub (.lin (dnL 0)) (dnRhs 0)) = true := by decide +kernel

theorem ck_dn1 : checkK 256 (.sub (.lin (dnL 1)) (dnRhs 1)) = true := by decide +kernel

theorem ck_sq0 : eqCheck 512 (sqLhs 0) (sqRhs 0) = true := by decide +kernel

theorem ck_sq1 : eqCheck 512 (sqLhs 1) (sqRhs 1) = true := by decide +kernel

/-! ## The known lifts -/

theorem ck_lift0 : (liftEqs 0 0 0 0 1).all (checkK 320) = true := by decide +kernel

theorem ck_lift1 : (liftEqs 1 1 1 1 1).all (checkK 320) = true := by decide +kernel

theorem ck_lift2 : (liftEqs 2 0 2 0 1).all (checkK 320) = true := by decide +kernel

theorem ck_lift3 : (liftEqs 3 1 (-1) 0 1).all (checkK 320) = true := by decide +kernel

/-! ## Denominators and list lengths -/

theorem ck_dens : qDenN 0 = 46 ∧ qDenN 1 = 46 ∧ hDenN 0 = 46 ∧ hDenN 1 = 46 ∧
    betaDenN 0 ≠ 0 ∧ betaDenN 1 ≠ 0 ∧ gamDenN 0 ≠ 0 ∧ gamDenN 1 ≠ 0 := by decide +kernel

theorem ck_lengths : (betaL 0).length = 6 ∧ (betaL 1).length = 6 ∧ (gamL 0).length = 5 ∧
    (gamL 1).length = 5 := by decide +kernel

/-! ## Residues at degree one primes -/

theorem ck_root13 : evalL (11 : ZMod 13) fL = 0 := by decide +kernel

theorem ck_root23 : evalL (5 : ZMod 23) fL = 0 := by decide +kernel

theorem ck_root3 : evalL (2 : ZMod 3) fL = 0 := by decide +kernel

theorem ck_DB13 : (11 : ZMod 13) * (DB : ZMod 13) = 1 := by decide +kernel

theorem ck_Dz13 : (1 : ZMod 13) * (Dz : ZMod 13) = 1 := by decide +kernel

theorem ck_DB23 : (12 : ZMod 23) * (DB : ZMod 23) = 1 := by decide +kernel

theorem ck_Dz23 : (4 : ZMod 23) * (Dz : ZMod 23) = 1 := by decide +kernel

theorem ck_DB3 : (2 : ZMod 3) * (DB : ZMod 3) = 1 := by decide +kernel

theorem ck_Dz3 : (2 : ZMod 3) * (Dz : ZMod 3) = 1 := by decide +kernel

/-- `4 c_0` is a non residue at `(13, θ - 11)`. -/
theorem ck_resLc0 :
    ¬ IsSquare ((1 : ZMod 13) * evalL (11 : ZMod 13) (combo ((FnData.getD 0 []).getD 0 []) zkNum)) := by
  decide +kernel

/-- `4 c_1` is a non residue at `(23, θ - 5)`. -/
theorem ck_resLc1 :
    ¬ IsSquare ((4 : ZMod 23) * evalL (5 : ZMod 23) (combo ((FnData.getD 1 []).getD 0 []) zkNum)) := by
  decide +kernel

/-- `qDen² d_0` is a non residue at `(13, θ - 11)`. -/
theorem ck_resD0 : ¬ IsSquare ((1 : ZMod 13) * evalL (11 : ZMod 13) (combo (dnL 0) zkNum)) := by
  decide +kernel

/-- `qDen² d_1` is a non residue at `(13, θ - 11)`. -/
theorem ck_resD1 : ¬ IsSquare ((1 : ZMod 13) * evalL (11 : ZMod 13) (combo (dnL 1) zkNum)) := by
  decide +kernel

/-- The leading coefficient `4 lc(f_k)` is nonzero at `(3, θ - 2)`, `k = 0, 1`. -/
theorem ck_resF6 : (2 : ZMod 3) * evalL (2 : ZMod 3) (combo ((FnData.getD 0 []).getD 6 []) zkNum) ≠ 0 ∧
    (2 : ZMod 3) * evalL (2 : ZMod 3) (combo ((FnData.getD 1 []).getD 6 []) zkNum) ≠ 0 := by
  decide +kernel

end FurioLombardo.Discharge.M3a.Bruin
