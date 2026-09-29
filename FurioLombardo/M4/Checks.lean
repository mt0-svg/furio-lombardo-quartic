import FurioLombardo.M4.Data

/-!
# Kernel checked facts about the integer data of the M4 certificates

Every theorem here is a finite computation on the literal data of `FurioLombardo.M4.Data`, checked by
`decide +kernel` (no `native_decide`). Their meaning is given by the lemmas of Lattice.lean, Leading.lean,
Series.lean and Main.lean, which use them as hypotheses.
-/

namespace FurioLombardo.M4

namespace T0

theorem cover : ∀ d ∈ [1, 2, 3, 4, 5], coverCheck (boxesOf excluded constant tails d) 12 0 0 = true := by
  decide +kernel

theorem counts : excluded.length = 11 ∧ constant.length = 82 ∧ tails.length = 2 := by decide +kernel

theorem hHG : H * G = (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide +kernel

theorem hC : ∀ k j : Fin 6, (8 : ℤ) ∣ (∑ i, C k i * lD i j) - (if j = k then 4 else 0) := by decide +kernel

theorem hCp : ∀ j k : Fin 6, (4 : ℤ) ∣ H j k - ∑ i, lD i j * Cp i k := by decide +kernel

theorem hGl : ∀ (i : Fin 7) (j : Fin 6), (4 : ℤ) ∣ G.mulVec (lD i) j := by decide +kernel

theorem hUG : U * G = UG := by decide +kernel

theorem hid : H * Ui * UG = (4 * 1 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide +kernel

theorem hGcol : ∀ j k : Fin 6, (4 : ℤ) ∣ (G * (H * Ui)) j k := by decide +kernel

theorem hDel : UG.mulVec la 0 * UG.mulVec lb 1 - UG.mulVec la 1 * UG.mulVec lb 0 = Del := by decide +kernel

theorem hdl : (2 : ℤ) ^ dl ∣ Del ∧ ¬ (2 : ℤ) ^ (dl + 1) ∣ Del := by decide +kernel

theorem hJab : ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ) ^ Jab ∣ UG.mulVec la o ∧ (2 : ℤ) ^ Jab ∣ UG.mulVec lb o := by
  decide +kernel

theorem hr : r + dl = min Jab (min qa qb) ∧ dl < min qa qb := by decide +kernel

theorem hsig : ∀ (j : Fin 2) (i : Fin 6), (2 : ℤ) ^ (r + sigE j + 2) ∣
    2 ^ sigE j * (H * Ui) i (Fin.castLE (by omega) j) - sigA j * la i - sigB j * lb i := by decide +kernel

theorem hsigq : ∀ j : Fin 2, r + sigE j + 2 ≤ qa ∧ r + sigE j + 2 ≤ qb := by decide +kernel

theorem hqD : ∀ i : Fin 7, 3 ≤ qD i := by decide +kernel

theorem centres : ∀ b ∈ constant, ClassOK UG W b.nu b.y ∧ b.nu + 3 ≤ b.q ∧ b.nu + 1 ≤ r ∧ b.vM % 3 = 0 ∧
    b.vM / 3 + b.s = b.nu + 3 ∧ 1 ≤ b.s := by decide +kernel

theorem tailsOK : ∀ b ∈ tails, ClassOK UG W b.nu b.g ∧ b.nu + 3 ≤ b.q ∧ b.nu + 1 ≤ r ∧ b.vM % 3 = 0 ∧
    1 ≤ b.s0 ∧ b.s0 ≤ b.s ∧ b.nu + 2 + b.s0 ≤ b.vM / 3 + b.s ∧ (b.c : ℤ) % 2 ^ b.s = b.Xi % 2 ^ b.s := by
  decide +kernel

theorem centresMem : ∀ b ∈ constant, ∀ j : Fin 6, (4 : ℤ) ∣ G.mulVec b.y j := by decide +kernel

theorem tailsVM : ∀ b ∈ tails, 3 ≤ b.vM := by decide +kernel

theorem hWc : ∀ (m : Fin 16) (o : Fin 6), W m o = ∑ i, selc SB m i * lD i o := by decide +kernel

/-- A left inverse of `SB` modulo 2 (computed in GP by matinverseimage over F_2): the columns of `SB`, the local images
at `v` of the four generators of `Sel²` in the basis `D_1, ..., D_7`, are independent. -/
def SBL : Matrix (Fin 4) (Fin 7) ℤ := !![1, 1, 1, 0, 0, 0, 0; 1, 1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0]

theorem hSBL : ∀ a b : Fin 4, (2 : ℤ) ∣ (SBL * SB) a b - (if a = b then 1 else 0) := by decide +kernel

end T0

namespace T1

theorem cover : ∀ d ∈ [1, 2, 3, 4, 5], coverCheck (boxesOf excluded constant tails d) 12 0 0 = true := by
  decide +kernel

theorem counts : excluded.length = 12 ∧ constant.length = 22 ∧ tails.length = 2 := by decide +kernel

theorem hHG : H * G = (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide +kernel

theorem hC : ∀ k j : Fin 6, (8 : ℤ) ∣ (∑ i, C k i * lD i j) - (if j = k then 4 else 0) := by decide +kernel

theorem hCp : ∀ j k : Fin 6, (4 : ℤ) ∣ H j k - ∑ i, lD i j * Cp i k := by decide +kernel

theorem hGl : ∀ (i : Fin 7) (j : Fin 6), (4 : ℤ) ∣ G.mulVec (lD i) j := by decide +kernel

theorem hUG : U * G = UG := by decide +kernel

theorem hid : H * Ui * UG = (4 * 1 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by decide +kernel

theorem hGcol : ∀ j k : Fin 6, (4 : ℤ) ∣ (G * (H * Ui)) j k := by decide +kernel

theorem hDel : UG.mulVec la 0 * UG.mulVec lb 1 - UG.mulVec la 1 * UG.mulVec lb 0 = Del := by decide +kernel

theorem hdl : (2 : ℤ) ^ dl ∣ Del ∧ ¬ (2 : ℤ) ^ (dl + 1) ∣ Del := by decide +kernel

theorem hJab : ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ) ^ Jab ∣ UG.mulVec la o ∧ (2 : ℤ) ^ Jab ∣ UG.mulVec lb o := by
  decide +kernel

theorem hr : r + dl = min Jab (min qa qb) ∧ dl < min qa qb := by decide +kernel

theorem hsig : ∀ (j : Fin 2) (i : Fin 6), (2 : ℤ) ^ (r + sigE j + 2) ∣
    2 ^ sigE j * (H * Ui) i (Fin.castLE (by omega) j) - sigA j * la i - sigB j * lb i := by decide +kernel

theorem hsigq : ∀ j : Fin 2, r + sigE j + 2 ≤ qa ∧ r + sigE j + 2 ≤ qb := by decide +kernel

theorem hqD : ∀ i : Fin 7, 3 ≤ qD i := by decide +kernel

theorem centres : ∀ b ∈ constant, ClassOK UG W b.nu b.y ∧ b.nu + 3 ≤ b.q ∧ b.nu + 1 ≤ r ∧ b.vM % 3 = 0 ∧
    b.vM / 3 + b.s = b.nu + 3 ∧ 1 ≤ b.s := by decide +kernel

theorem tailsOK : ∀ b ∈ tails, ClassOK UG W b.nu b.g ∧ b.nu + 3 ≤ b.q ∧ b.nu + 1 ≤ r ∧ b.vM % 3 = 0 ∧
    1 ≤ b.s0 ∧ b.s0 ≤ b.s ∧ b.nu + 2 + b.s0 ≤ b.vM / 3 + b.s ∧ (b.c : ℤ) % 2 ^ b.s = b.Xi % 2 ^ b.s := by
  decide +kernel

theorem centresMem : ∀ b ∈ constant, ∀ j : Fin 6, (4 : ℤ) ∣ G.mulVec b.y j := by decide +kernel

theorem tailsVM : ∀ b ∈ tails, 3 ≤ b.vM := by decide +kernel

theorem hWc : ∀ (m : Fin 16) (o : Fin 6), W m o = ∑ i, selc SB m i * lD i o := by decide +kernel

/-- A left inverse of `SB` modulo 2 (computed in GP by matinverseimage over F_2). -/
def SBL : Matrix (Fin 4) (Fin 7) ℤ := !![1, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0; 1, 0, 1, 0, 0, 1, 1; 0, 0, 0, 0, 0, 0, 1]

theorem hSBL : ∀ a b : Fin 4, (2 : ℤ) ∣ (SBL * SB) a b - (if a = b then 1 else 0) := by decide +kernel

end T1

end FurioLombardo.M4
