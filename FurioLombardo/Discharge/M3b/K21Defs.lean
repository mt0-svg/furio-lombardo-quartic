import FurioLombardo.M1.Gens

/-!
# Elements of `K21` used by the M3b discharge

* `ε` (`epsO`, `epsU`, `epsK`): the unit of `𝓞 K21` with zk coordinates `epsL`, inverse `epsInvL`.
  PARI: `ε = gO 0 · gO 1 · gO 4 · gO 6 · gO 9 · gO 10` in M1's numbering, the unit in the square class
  of `d` (code/selmer-global-bound/tower_data_explore.gp); `L = K21(√ε)`.
* `Π = la (1 + la + la² + la⁴)` (`PiO`, `la = gO 12`): `Π³ + 2 ∈ la⁶ 𝓞 K21`, a uniformizer at the
  prime `(la)` above 2 with `e = 3`; `t = 1 + Π²` (`tO`) (code/selmer-global-bound/tower_field_data.gp).
* `ε` is not a square in `K21` (`not_sq_epsK`): under the residue map `𝓞 K21 → ZMod 3`, `θ ↦ 2`,
  its image is `2` (code/selmer-global-bound/eps_irreducibility.gp).
-/

namespace FurioLombardo.Discharge.M3b

open Polynomial NumberField FurioLombardo.M1 FurioLombardo.M1.Kron

/-- zk coordinates of `ε`. -/
def epsL : List ℤ := [26, -28, -8, -5, 1, -3, 0, 3, 9, -1, 8, -16, -3, 14, -6, -12, -8, 13, -3, -4, 0]

/-- zk coordinates of `ε⁻¹`. -/
def epsInvL : List ℤ := [18, -20, -5, 4, -6, -9, -2, -6, 13, 3, 0, -2, 0, -2, -5, -2, -6, 0, 4, 6, -2]

theorem ck_eps_inv : checkK 1024 (.sub (.mul (.lin epsL) (.lin epsInvL)) (.int 1)) = true := by
  decide +kernel

/-- `ε` in `𝓞 K21`. -/
noncomputable def epsO : 𝓞 K21 := zkO epsL

/-- `ε` in `K21`. -/
noncomputable def epsK : K21 := (epsO : K21)

theorem epsK_eq : epsK = zkE epsL := rfl

theorem epsO_mul_inv : epsO * zkO epsInvL = 1 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_eps_inv
  simp only [evK_mul, evK_lin, evK_int, Int.cast_one] at h
  rw [map_mul, map_one]
  exact h

/-- `ε` as a unit of `𝓞 K21`. -/
noncomputable def epsU : (𝓞 K21)ˣ :=
  ⟨epsO, zkO epsInvL, epsO_mul_inv, by rw [mul_comm]; exact epsO_mul_inv⟩

@[simp] theorem coe_epsU : (epsU : 𝓞 K21) = epsO := rfl

/-- `Π = la (1 + la + la² + la⁴)`. -/
noncomputable def PiO : 𝓞 K21 := gO 12 * (1 + gO 12 + gO 12 ^ 2 + gO 12 ^ 4)

/-- `t = 1 + Π²`. -/
noncomputable def tO : 𝓞 K21 := 1 + PiO ^ 2

/-! ## `ε` is not a square in `K21` -/

theorem Dz_dvd_DB : DB = (DB / Dz) * (Dz : ℤ) := by decide +kernel

theorem aeval_two_fZ : aeval (2 : ZMod 3) fZ = 0 := by
  rw [← ofListL_fL, aeval_ofListL]; decide +kernel

theorem invDB_three : (2 : ZMod 3) * (DB : ZMod 3) = 1 := by decide +kernel

/-- The residue map `𝓞 K21 → ZMod 3`, `θ ↦ 2`. -/
noncomputable def res3 : 𝓞 K21 →+* ZMod 3 := resHom (2 : ZMod 3) aeval_two_fZ 2 invDB_three

/-- Ring homomorphisms commute with `evalL`. -/
theorem evalL_hom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : R) :
    ∀ l : List ℤ, f (evalL t l) = evalL (f t) l
  | [] => by simp [evalL]
  | c :: l => by simp [evalL, evalL_hom f t l]

/-- `DB · zkO a = (DB / Dz) · combo a zkNum (θ)`. -/
theorem DB_mul_zkO (a : List ℤ) :
    (DB : 𝓞 K21) * zkO a = aeval θO (C (DB / Dz) * ofListL (combo a zkNum)) := by
  rw [map_mul, aeval_C, aeval_ofListL]
  apply RingOfIntegers.coe_injective
  rw [map_mul, map_mul, evalL_hom]
  simp only [map_intCast, algebraMap_int_eq, eq_intCast]
  show (DB : K21) * zkE a = ((DB / Dz : ℤ) : K21) * evalL θ (combo a zkNum)
  rw [zkE, evK, KE.ev, ← mul_assoc]
  congr 1
  rw [dInv]
  conv_lhs => rw [Dz_dvd_DB]
  push_cast
  rw [mul_assoc, mul_inv_cancel₀ Dz_ne_zero, mul_one]

theorem res3_zkO (a : List ℤ) :
    res3 (zkO a) = 2 * (((DB / Dz : ℤ) : ZMod 3) * evalL (2 : ZMod 3) (combo a zkNum)) := by
  rw [res3, resHom_apply _ _ _ _ _ _ (DB_mul_zkO a), map_mul, aeval_C, aeval_ofListL]
  simp

theorem res3_epsO : res3 epsO = 2 := by
  rw [epsO, res3_zkO]; decide +kernel

theorem not_sq_epsK : ¬ ∃ s : K21, s ^ 2 = epsK := by
  rintro ⟨s, hs⟩
  have hint : IsIntegral ℤ s := by
    have h1 : IsIntegral (𝓞 K21) s := by
      refine ⟨X ^ 2 - C epsO, monic_X_pow_sub_C _ (by norm_num), ?_⟩
      simp [hs, epsK]
    exact isIntegral_trans (R := ℤ) s h1
  let s' : 𝓞 K21 := ⟨s, hint⟩
  have hs' : s' ^ 2 = epsO := by
    apply RingOfIntegers.coe_injective
    rw [map_pow]
    exact hs
  have h := congrArg res3 hs'
  rw [map_pow, res3_epsO] at h
  revert h
  generalize res3 s' = z
  revert z
  decide

end FurioLombardo.Discharge.M3b
