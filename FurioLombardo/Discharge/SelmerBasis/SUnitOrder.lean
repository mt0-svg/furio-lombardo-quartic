import FurioLombardo.Discharge.SelmerBasis.SUnitIndepGen
import FurioLombardo.Discharge.M3b.QuadReal
import FurioLombardo.Discharge.M3b.RamN

/-!
# Orders of `L42` and `N84` for the residue characters (piece (d))

* `OL = 𝓞 K21[√ε]` (`QuadraticAlgebra (𝓞 K21) epsO 0`) with `ιL : OL → L42`, `a + b ω ↦ a + b ω`;
* `ON = OL[√EO]` with `EO = 2 ea + 2 eb ω = 4 e'` and `ιN : ON → N84`, `ω ↦ 2 ω_N`: the element
  `a + b ω'` goes to `a + b (2 ω_N)`, the convention of `mkN`.

Both are injective ring maps with integral image. A square root `y` of an element of the order
has `D y` in the order (`exists_DL_mul`, `exists_DN_mul`), with `DL = 2 ε` and `DN = DL · EO`:
`2 y.re` and `2 d y.im` are integral for `y` integral in `K(√d)` (`quad_coords_integral`).
-/

namespace FurioLombardo.Discharge.SelmerBasis.SU

open NumberField QuadraticAlgebra FurioLombardo.M1 FurioLombardo.M1.Kron
  FurioLombardo.Discharge.M3b

/-! ### `OL` -/

/-- The order `𝓞 K21[√ε]` of `L42`. -/
abbrev OL : Type := QuadraticAlgebra (𝓞 K21) epsO 0

/-- `𝓞 K21 → L42`. -/
noncomputable def φK : 𝓞 K21 →+* L42 := (algebraMap K21 L42).comp (algebraMap (𝓞 K21) K21)

theorem φK_eps : (ω : L42) * ω = φK epsO := omega_mul_omega_zero

/-- `OL → L42`. -/
noncomputable def ιL : OL →+* L42 := extendHom φK ω φK_eps

theorem φK_apply (a : 𝓞 K21) : φK a = algebraMap K21 L42 (a : K21) := rfl

theorem ιL_apply (x : OL) : ιL x = ⟨(x.re : K21), (x.im : K21)⟩ := by
  rw [ιL, extendHom_apply, φK_apply, φK_apply]
  ext <;> simp [algebraMap_eq]

theorem ιL_algebraMap (a : 𝓞 K21) : ιL (algebraMap (𝓞 K21) OL a) = φK a :=
  extendHom_algebraMap _ _ _ _

theorem ιL_injective : Function.Injective ιL := by
  intro x y h
  rw [ιL_apply, ιL_apply] at h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  ext
  · exact h1
  · exact h2

theorem isIntegral_φK (a : 𝓞 K21) : IsIntegral ℤ (φK a) :=
  (RingOfIntegers.isIntegral_coe a).algebraMap

theorem isIntegral_omega_L : IsIntegral ℤ (ω : L42) :=
  IsIntegral.of_pow two_pos (by rw [sq, φK_eps]; exact isIntegral_φK _)

theorem isIntegral_ιL (x : OL) : IsIntegral ℤ (ιL x) := by
  rw [ιL, extendHom_apply]
  exact (isIntegral_φK _).add ((isIntegral_φK _).mul isIntegral_omega_L)

/-- `DL = 2 ε`. -/
noncomputable def DL : OL := algebraMap (𝓞 K21) OL (2 * epsO)

/-- `DL` times an integral element of `L42` lies in `OL`. -/
theorem exists_DL_mul (y : L42) (hy : IsIntegral ℤ y) : ∃ Y : OL, ιL Y = ιL DL * y := by
  obtain ⟨h1, h2⟩ := quad_coords_integral epsO y hy
  let A : 𝓞 K21 := ⟨2 * y.re, h1⟩
  let B : 𝓞 K21 := ⟨2 * (epsO : K21) * y.im, h2⟩
  have hA : (A : K21) = 2 * y.re := rfl
  have hB : (B : K21) = 2 * (epsO : K21) * y.im := rfl
  have hD : ιL DL = ⟨2 * (epsO : K21), 0⟩ := by
    rw [DL, ιL_algebraMap, φK_apply, algebraMap_eq]
    congr 1
  refine ⟨⟨epsO * A, B⟩, ?_⟩
  rw [ιL_apply, hD]
  ext
  · rw [re_mul]; dsimp only
    rw [show ((epsO * A : 𝓞 K21) : K21) = (epsO : K21) * A from rfl, hA]; ring
  · rw [im_mul]; dsimp only
    rw [hB]; ring

theorem hDy_L (X : OL) (y : L42) (h : ιL X = y ^ 2) : ∃ Y : OL, ιL Y = ιL DL * y :=
  exists_DL_mul y (IsIntegral.of_pow two_pos (h ▸ isIntegral_ιL X))

/-! ### `ON` -/

/-- `EO = 2 ea + 2 eb ω = 4 e'`. -/
noncomputable def EO : OL := ⟨2 * zkO eaL, 2 * zkO ebL⟩

theorem ιL_EO : ιL EO = 4 * eN := by
  have c2 : ((2 : 𝓞 K21) : K21) = 2 := map_ofNat (algebraMap (𝓞 K21) K21) 2
  rw [ιL_apply]
  ext
  · show ((2 * zkO eaL : 𝓞 K21) : K21) = (4 * eN).re
    rw [show (4 * eN).re = 4 * eN.re by simp [re_mul]]
    simp only [eN, eaK]
    rw [show ((2 * zkO eaL : 𝓞 K21) : K21) = ((2 : 𝓞 K21) : K21) * zkE eaL from rfl, c2]; ring
  · show ((2 * zkO ebL : 𝓞 K21) : K21) = (4 * eN).im
    rw [show (4 * eN).im = 4 * eN.im by simp [im_mul]]
    simp only [eN, ebK]
    rw [show ((2 * zkO ebL : 𝓞 K21) : K21) = ((2 : 𝓞 K21) : K21) * zkE ebL from rfl, c2]; ring

/-- The order `OL[√EO]` of `N84`. -/
abbrev ON : Type := QuadraticAlgebra OL EO 0

/-- `OL → N84`. -/
noncomputable def φL : OL →+* N84 := (algebraMap L42 N84).comp ιL

theorem φL_EO : (2 * ω : N84) * (2 * ω) = φL EO := by
  rw [φL, RingHom.comp_apply, ιL_EO, map_mul, ← omega_mul_omega_zero, map_ofNat]
  ring

/-- `ON → N84`, `ω ↦ 2 ω_N`. -/
noncomputable def ιN : ON →+* N84 := extendHom φL (2 * ω) φL_EO

theorem ιN_apply (x : ON) : ιN x = ⟨ιL x.re, 2 * ιL x.im⟩ := by
  rw [ιN, extendHom_apply, φL, RingHom.comp_apply, RingHom.comp_apply]
  ext <;> simp [algebraMap_eq] <;> ring

theorem ιN_algebraMap (a : OL) : ιN (algebraMap OL ON a) = φL a :=
  extendHom_algebraMap _ _ _ _

theorem ιN_injective : Function.Injective ιN := by
  intro x y h
  rw [ιN_apply, ιN_apply] at h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  dsimp only at h1 h2
  ext : 1
  · exact ιL_injective h1
  · exact ιL_injective (mul_left_cancel₀ two_ne_zero h2)

theorem isIntegral_φL (a : OL) : IsIntegral ℤ (φL a) :=
  (isIntegral_ιL a).algebraMap

theorem isIntegral_omega_N : IsIntegral ℤ (ω : N84) := by
  refine IsIntegral.of_pow two_pos ?_
  rw [sq, omega_mul_omega_zero]
  exact (RingOfIntegers.isIntegral_coe eNO).algebraMap

theorem isIntegral_ιN (x : ON) : IsIntegral ℤ (ιN x) := by
  rw [ιN, extendHom_apply]
  exact (isIntegral_φL _).add ((isIntegral_φL _).mul
    (((map_ofNat (algebraMap ℤ N84) 2) ▸ isIntegral_algebraMap).mul
      isIntegral_omega_N))

/-- `DN = DL · EO`. -/
noncomputable def DN : ON := algebraMap OL ON (DL * EO)

/-- `DN` times an integral element of `N84` lies in `ON`. -/
theorem exists_DN_mul (y : N84) (hy : IsIntegral ℤ y) : ∃ Y : ON, ιN Y = ιN DN * y := by
  obtain ⟨h1, h2⟩ := quad_coords_integral eNO y hy
  have heN : IsIntegral ℤ ((eNO : L42)) := RingOfIntegers.isIntegral_coe eNO
  obtain ⟨A, hA⟩ := exists_DL_mul (2 * (eNO : L42) * (2 * y.re))
    (((map_ofNat (algebraMap ℤ L42) 2) ▸ isIntegral_algebraMap).mul heN |>.mul h1)
  obtain ⟨B, hB⟩ := exists_DL_mul (2 * (eNO : L42) * y.im) h2
  refine ⟨⟨A, B⟩, ?_⟩
  have hD : ιN DN = ⟨ιL DL * (4 * eN), 0⟩ := by
    rw [DN, ιN_algebraMap, φL, RingHom.comp_apply, map_mul, ιL_EO, algebraMap_eq]
  rw [ιN_apply, hD]
  ext : 1
  · show ιL A = (⟨ιL DL * (4 * eN), 0⟩ * y : N84).re
    rw [re_mul, hA]; dsimp only
    rw [show (eNO : L42) = eN from rfl]; ring
  · show 2 * ιL B = (⟨ιL DL * (4 * eN), 0⟩ * y : N84).im
    rw [im_mul, hB]; dsimp only
    rw [show (eNO : L42) = eN from rfl]; ring

theorem hDy_N (X : ON) (y : N84) (h : ιN X = y ^ 2) : ∃ Y : ON, ιN Y = ιN DN * y :=
  exists_DN_mul y (IsIntegral.of_pow two_pos (h ▸ isIntegral_ιN X))

end FurioLombardo.Discharge.SelmerBasis.SU
