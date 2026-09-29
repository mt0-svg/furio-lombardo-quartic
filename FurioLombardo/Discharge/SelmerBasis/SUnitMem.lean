import FurioLombardo.Discharge.SelmerBasis.SUnitDefs
import FurioLombardo.Discharge.SelmerBasis.SUnitTower
import FurioLombardo.Discharge.SelmerBasis.SUnitRes
import FurioLombardo.Discharge.SelmerBasis.SUnitCount
import FurioLombardo.Discharge.SelmerBasis.SUnitMemGen

/-!
# The generators are nonzero and lie in `K(S27, 2)` (piece (c))

For every generator `gensL s` (`gensN s`) the cofactor `mkL (gLw s)` (`mkN (gNw s)`) of
SUnitData.lean gives `gensL s * w = 2 ^ a * 7 ^ b` with `(a, b) = gLab s` (`gNab s`): one Kronecker
check per generator (`ckL_s`, `ckN_s`, `decide +kernel`, SUnitTower's `checkLC`, `checkNC`). Both
factors are algebraic integers (images of the orders `OL`, `ON`), so the generator is nonzero and
a unit outside the primes above 2 and 7 (`mem_selmerGroup_of_mul_eq`).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField IsDedekindDomain FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3b
  QuadraticAlgebra SUnitData Tower SU

/-! ### Generic part -/

theorem evL_ofL (l : List (List ℤ)) : evL (ofL l) = mkL l := by
  simp [evL, ofL, mkL]

theorem evN_ofN (l : List (List ℤ)) : evN (ofN l) = mkN l := by
  simp [evN, evL, ofN, mkN]

theorem mkL_mul_of_check {k : ℕ} {l w : List (List ℤ)} {n : ℤ}
    (h : checkLC k (mulLC (ofL l) (ofL w)) (.int n, .int 0) = true) : mkL l * mkL w = (n : L42) := by
  have e := evL_eq_of_checkLC h
  rw [evL_mulLC, evL_ofL, evL_ofL] at e
  rw [e]
  ext <;> simp [evL]

theorem mkN_mul_of_check {k : ℕ} {l w : List (List ℤ)} {n : ℤ}
    (h : checkNC k (mulNC (ofN l) (ofN w)) ((.int n, .int 0), (.int 0, .int 0)) = true) :
    mkN l * mkN w = (n : N84) := by
  have e := evN_eq_of_checkNC h
  rw [evN_mulNC, evN_ofN, evN_ofN] at e
  rw [e]
  ext <;> simp [evN, evL]

theorem ιL_mkOL (l : List (List ℤ)) : ιL (mkOL l) = mkL l := by
  rw [ιL_apply]; rfl

theorem ιN_mkON (l : List (List ℤ)) : ιN (mkON l) = mkN l := by
  rw [ιN_apply, mkON, ιL_apply, ιL_apply]
  ext <;> simp [mkN]

theorem isIntegral_mkL (l : List (List ℤ)) : IsIntegral ℤ (mkL l) := by
  rw [← ιL_mkOL]; exact isIntegral_ιL _

theorem isIntegral_mkN (l : List (List ℤ)) : IsIntegral ℤ (mkN l) := by
  rw [← ιN_mkON]; exact isIntegral_ιN _

theorem not_mem_S27 {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ S27 F) : (2 : 𝓞 F) ∉ v.asIdeal ∧ (7 : 𝓞 F) ∉ v.asIdeal := by
  simpa [S27, not_or] using hv

/-- The Kronecker check of the cofactor of `gensL s`. -/
def ckL (s : ℕ) : Bool :=
  checkLC 1024 (mulLC (ofL (gL.getD s [])) (ofL (gLw.getD s [])))
    (.int (2 ^ (gLab.getD s (0, 0)).1 * 7 ^ (gLab.getD s (0, 0)).2), .int 0)

/-- The Kronecker check of the cofactor of `gensN s`. -/
def ckN (s : ℕ) : Bool :=
  checkNC 1024 (mulNC (ofN (gN.getD s [])) (ofN (gNw.getD s [])))
    ((.int (2 ^ (gNab.getD s (0, 0)).1 * 7 ^ (gNab.getD s (0, 0)).2), .int 0), (.int 0, .int 0))

/-! ### Kernel checks, one per generator -/

theorem ckL_0 : ckL 0 = true := by decide +kernel
theorem ckL_1 : ckL 1 = true := by decide +kernel
theorem ckL_2 : ckL 2 = true := by decide +kernel
theorem ckL_3 : ckL 3 = true := by decide +kernel
theorem ckL_4 : ckL 4 = true := by decide +kernel
theorem ckL_5 : ckL 5 = true := by decide +kernel
theorem ckL_6 : ckL 6 = true := by decide +kernel
theorem ckL_7 : ckL 7 = true := by decide +kernel
theorem ckL_8 : ckL 8 = true := by decide +kernel
theorem ckL_9 : ckL 9 = true := by decide +kernel
theorem ckL_10 : ckL 10 = true := by decide +kernel
theorem ckL_11 : ckL 11 = true := by decide +kernel
theorem ckL_12 : ckL 12 = true := by decide +kernel
theorem ckL_13 : ckL 13 = true := by decide +kernel
theorem ckL_14 : ckL 14 = true := by decide +kernel
theorem ckL_15 : ckL 15 = true := by decide +kernel
theorem ckL_16 : ckL 16 = true := by decide +kernel
theorem ckL_17 : ckL 17 = true := by decide +kernel
theorem ckL_18 : ckL 18 = true := by decide +kernel
theorem ckL_19 : ckL 19 = true := by decide +kernel
theorem ckL_20 : ckL 20 = true := by decide +kernel
theorem ckL_21 : ckL 21 = true := by decide +kernel
theorem ckL_22 : ckL 22 = true := by decide +kernel
theorem ckL_23 : ckL 23 = true := by decide +kernel
theorem ckL_24 : ckL 24 = true := by decide +kernel
theorem ckL_25 : ckL 25 = true := by decide +kernel
theorem ckL_26 : ckL 26 = true := by decide +kernel
theorem ckL_27 : ckL 27 = true := by decide +kernel
theorem ckL_28 : ckL 28 = true := by decide +kernel

theorem ckN_0 : ckN 0 = true := by decide +kernel
theorem ckN_1 : ckN 1 = true := by decide +kernel
theorem ckN_2 : ckN 2 = true := by decide +kernel
theorem ckN_3 : ckN 3 = true := by decide +kernel
theorem ckN_4 : ckN 4 = true := by decide +kernel
theorem ckN_5 : ckN 5 = true := by decide +kernel
theorem ckN_6 : ckN 6 = true := by decide +kernel
theorem ckN_7 : ckN 7 = true := by decide +kernel
theorem ckN_8 : ckN 8 = true := by decide +kernel
theorem ckN_9 : ckN 9 = true := by decide +kernel
theorem ckN_10 : ckN 10 = true := by decide +kernel
theorem ckN_11 : ckN 11 = true := by decide +kernel
theorem ckN_12 : ckN 12 = true := by decide +kernel
theorem ckN_13 : ckN 13 = true := by decide +kernel
theorem ckN_14 : ckN 14 = true := by decide +kernel
theorem ckN_15 : ckN 15 = true := by decide +kernel
theorem ckN_16 : ckN 16 = true := by decide +kernel
theorem ckN_17 : ckN 17 = true := by decide +kernel
theorem ckN_18 : ckN 18 = true := by decide +kernel
theorem ckN_19 : ckN 19 = true := by decide +kernel
theorem ckN_20 : ckN 20 = true := by decide +kernel
theorem ckN_21 : ckN 21 = true := by decide +kernel
theorem ckN_22 : ckN 22 = true := by decide +kernel
theorem ckN_23 : ckN 23 = true := by decide +kernel
theorem ckN_24 : ckN 24 = true := by decide +kernel
theorem ckN_25 : ckN 25 = true := by decide +kernel
theorem ckN_26 : ckN 26 = true := by decide +kernel
theorem ckN_27 : ckN 27 = true := by decide +kernel
theorem ckN_28 : ckN 28 = true := by decide +kernel
theorem ckN_29 : ckN 29 = true := by decide +kernel
theorem ckN_30 : ckN 30 = true := by decide +kernel
theorem ckN_31 : ckN 31 = true := by decide +kernel
theorem ckN_32 : ckN 32 = true := by decide +kernel
theorem ckN_33 : ckN 33 = true := by decide +kernel
theorem ckN_34 : ckN 34 = true := by decide +kernel
theorem ckN_35 : ckN 35 = true := by decide +kernel
theorem ckN_36 : ckN 36 = true := by decide +kernel
theorem ckN_37 : ckN 37 = true := by decide +kernel
theorem ckN_38 : ckN 38 = true := by decide +kernel
theorem ckN_39 : ckN 39 = true := by decide +kernel
theorem ckN_40 : ckN 40 = true := by decide +kernel
theorem ckN_41 : ckN 41 = true := by decide +kernel
theorem ckN_42 : ckN 42 = true := by decide +kernel
theorem ckN_43 : ckN 43 = true := by decide +kernel
theorem ckN_44 : ckN 44 = true := by decide +kernel
theorem ckN_45 : ckN 45 = true := by decide +kernel
theorem ckN_46 : ckN 46 = true := by decide +kernel
theorem ckN_47 : ckN 47 = true := by decide +kernel
theorem ckN_48 : ckN 48 = true := by decide +kernel
theorem ckN_49 : ckN 49 = true := by decide +kernel
theorem ckN_50 : ckN 50 = true := by decide +kernel
theorem ckN_51 : ckN 51 = true := by decide +kernel
theorem ckN_52 : ckN 52 = true := by decide +kernel

theorem ckL_all (s : Fin 29) : ckL s = true := by
  fin_cases s
  exacts [ckL_0, ckL_1, ckL_2, ckL_3, ckL_4, ckL_5, ckL_6, ckL_7, ckL_8, ckL_9, ckL_10, ckL_11, ckL_12, ckL_13, ckL_14, ckL_15, ckL_16, ckL_17, ckL_18, ckL_19, ckL_20, ckL_21, ckL_22, ckL_23, ckL_24, ckL_25, ckL_26, ckL_27, ckL_28]

theorem ckN_all (s : Fin 53) : ckN s = true := by
  fin_cases s
  exacts [ckN_0, ckN_1, ckN_2, ckN_3, ckN_4, ckN_5, ckN_6, ckN_7, ckN_8, ckN_9, ckN_10, ckN_11, ckN_12, ckN_13, ckN_14, ckN_15, ckN_16, ckN_17, ckN_18, ckN_19, ckN_20, ckN_21, ckN_22, ckN_23, ckN_24, ckN_25, ckN_26, ckN_27, ckN_28, ckN_29, ckN_30, ckN_31, ckN_32, ckN_33, ckN_34, ckN_35, ckN_36, ckN_37, ckN_38, ckN_39, ckN_40, ckN_41, ckN_42, ckN_43, ckN_44, ckN_45, ckN_46, ckN_47, ckN_48, ckN_49, ckN_50, ckN_51, ckN_52]

/-! ### The generators -/

/-- The cofactor identity of `gensL s`. -/
theorem gensL_mul_eq (s : Fin 29) :
    gensL s * mkL (gLw.getD s []) = 2 ^ (gLab.getD s (0, 0)).1 * 7 ^ (gLab.getD s (0, 0)).2 := by
  have h := mkL_mul_of_check (ckL_all s)
  rw [gensL, h]; push_cast; rfl

/-- The cofactor identity of `gensN s`. -/
theorem gensN_mul_eq (s : Fin 53) :
    gensN s * mkN (gNw.getD s []) = 2 ^ (gNab.getD s (0, 0)).1 * 7 ^ (gNab.getD s (0, 0)).2 := by
  have h := mkN_mul_of_check (ckN_all s)
  rw [gensN, h]; push_cast; rfl

theorem gensL_ne_zero (i : Fin 29) : gensL i ≠ 0 := by
  intro h
  have e := gensL_mul_eq i
  rw [h, zero_mul] at e
  exact (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ (by norm_num))) e.symm

theorem gensN_ne_zero (j : Fin 53) : gensN j ≠ 0 := by
  intro h
  have e := gensN_mul_eq j
  rw [h, zero_mul] at e
  exact (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ (by norm_num))) e.symm

/-- **Piece (c), `L42`.** -/
theorem gensL_mem (s : Fin 29) :
    (QuotientGroup.mk (Units.mk0 (gensL s) (gensL_ne_zero s)) : SqClass L42) ∈
      selmerGroup (K := L42) (S := S27 L42) (n := 2) := by
  let x : 𝓞 L42 := ⟨gensL s, isIntegral_mkL _⟩
  let w : 𝓞 L42 := ⟨mkL (gLw.getD s []), isIntegral_mkL _⟩
  have hxw : x * w = 2 ^ (gLab.getD s (0, 0)).1 * 7 ^ (gLab.getD s (0, 0)).2 := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_pow, map_ofNat]
    exact gensL_mul_eq s
  exact mem_selmerGroup_of_mul_eq (S27 L42) not_mem_S27 x w _ _ hxw (gensL_ne_zero s)

/-- **Piece (c), `N84`.** -/
theorem gensN_mem (s : Fin 53) :
    (QuotientGroup.mk (Units.mk0 (gensN s) (gensN_ne_zero s)) : SqClass N84) ∈
      selmerGroup (K := N84) (S := S27 N84) (n := 2) := by
  let x : 𝓞 N84 := ⟨gensN s, isIntegral_mkN _⟩
  let w : 𝓞 N84 := ⟨mkN (gNw.getD s []), isIntegral_mkN _⟩
  have hxw : x * w = 2 ^ (gNab.getD s (0, 0)).1 * 7 ^ (gNab.getD s (0, 0)).2 := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_pow, map_ofNat]
    exact gensN_mul_eq s
  exact mem_selmerGroup_of_mul_eq (S27 N84) not_mem_S27 x w _ _ hxw (gensN_ne_zero s)

end FurioLombardo.Discharge.SelmerBasis
