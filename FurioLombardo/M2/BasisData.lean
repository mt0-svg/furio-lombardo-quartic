import FurioLombardo.M2.Check

/-!
# Kernel checks on the integral basis data of lane M2

`omL`, `Fk` are the Kronecker values of `WL`, `fL`; every `W ∈ WL` has 21 coefficients bounded
by `2^77`; `w_j = W_j(θ)/DD` is a root of the monic integer polynomial `X^21 + Σ chi_i X^i`
(`homogL` check, one theorem per `j`); `U fZ + V fZ' = ResZ`; `DD ∣ ResZ`. No Mathlib in the
import chain.
-/

namespace FurioLombardo.M2

theorem omL_eq : omL = WL.map (evalI tK) := by decide +kernel

theorem Fk_eq : Fk = evalI tK fL := by decide +kernel

theorem WL_shape : WL.length = 21 ∧ chiL.length = 21 ∧
    WL.all (fun W => W.length == 21 && allBounded (2 ^ 77) W) = true := by decide +kernel

theorem fL_eq : fL = fLow ++ [1] := by decide +kernel

theorem fL_bound : fL.length = 22 ∧ allBounded 1072 fL = true := by decide +kernel

theorem resultant_check : allZero (addZ (addZ (mulZ UL fL) (mulZ VL fdL)) [-ResZ]) = true := by
  decide +kernel

theorem DD_dvd_ResZ : ResZ % DD = 0 := by decide +kernel

theorem DD_pos : 0 < DD ∧ DD < 2 ^ 68 := by decide +kernel

theorem integral_0 : allZero (homogL fLow (WL.getD 0 []) DD (chiL.getD 0 [] ++ [1])) = true := by
  decide +kernel

theorem integral_1 : allZero (homogL fLow (WL.getD 1 []) DD (chiL.getD 1 [] ++ [1])) = true := by
  decide +kernel

theorem integral_2 : allZero (homogL fLow (WL.getD 2 []) DD (chiL.getD 2 [] ++ [1])) = true := by
  decide +kernel

theorem integral_3 : allZero (homogL fLow (WL.getD 3 []) DD (chiL.getD 3 [] ++ [1])) = true := by
  decide +kernel

theorem integral_4 : allZero (homogL fLow (WL.getD 4 []) DD (chiL.getD 4 [] ++ [1])) = true := by
  decide +kernel

theorem integral_5 : allZero (homogL fLow (WL.getD 5 []) DD (chiL.getD 5 [] ++ [1])) = true := by
  decide +kernel

theorem integral_6 : allZero (homogL fLow (WL.getD 6 []) DD (chiL.getD 6 [] ++ [1])) = true := by
  decide +kernel

theorem integral_7 : allZero (homogL fLow (WL.getD 7 []) DD (chiL.getD 7 [] ++ [1])) = true := by
  decide +kernel

theorem integral_8 : allZero (homogL fLow (WL.getD 8 []) DD (chiL.getD 8 [] ++ [1])) = true := by
  decide +kernel

theorem integral_9 : allZero (homogL fLow (WL.getD 9 []) DD (chiL.getD 9 [] ++ [1])) = true := by
  decide +kernel

theorem integral_10 : allZero (homogL fLow (WL.getD 10 []) DD (chiL.getD 10 [] ++ [1])) = true := by
  decide +kernel

theorem integral_11 : allZero (homogL fLow (WL.getD 11 []) DD (chiL.getD 11 [] ++ [1])) = true := by
  decide +kernel

theorem integral_12 : allZero (homogL fLow (WL.getD 12 []) DD (chiL.getD 12 [] ++ [1])) = true := by
  decide +kernel

theorem integral_13 : allZero (homogL fLow (WL.getD 13 []) DD (chiL.getD 13 [] ++ [1])) = true := by
  decide +kernel

theorem integral_14 : allZero (homogL fLow (WL.getD 14 []) DD (chiL.getD 14 [] ++ [1])) = true := by
  decide +kernel

theorem integral_15 : allZero (homogL fLow (WL.getD 15 []) DD (chiL.getD 15 [] ++ [1])) = true := by
  decide +kernel

theorem integral_16 : allZero (homogL fLow (WL.getD 16 []) DD (chiL.getD 16 [] ++ [1])) = true := by
  decide +kernel

theorem integral_17 : allZero (homogL fLow (WL.getD 17 []) DD (chiL.getD 17 [] ++ [1])) = true := by
  decide +kernel

theorem integral_18 : allZero (homogL fLow (WL.getD 18 []) DD (chiL.getD 18 [] ++ [1])) = true := by
  decide +kernel

theorem integral_19 : allZero (homogL fLow (WL.getD 19 []) DD (chiL.getD 19 [] ++ [1])) = true := by
  decide +kernel

theorem integral_20 : allZero (homogL fLow (WL.getD 20 []) DD (chiL.getD 20 [] ++ [1])) = true := by
  decide +kernel

end FurioLombardo.M2
