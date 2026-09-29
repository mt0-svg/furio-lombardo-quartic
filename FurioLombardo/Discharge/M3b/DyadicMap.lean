import FurioLombardo.Discharge.M3b.K21Primes
import FurioLombardo.Discharge.M3b.DataK21
import FurioLombardo.Discharge.M3b.DataDyadic
import FurioLombardo.M3b.DyadicCert

/-!
# The reduction `𝓞 K21 → 𝓞 K21 ⧸ (la⁶) ≅ R = (ℤ/4)[π]/(π³ + 2)` at the dyadic prime `(la)`

`Π = la w` with `w = 1 + la + la² + la⁴` (`PiO`, K21Defs.lean). The kernel checks (Kronecker test)
`Π = zkO PiL`, `Π³ + 2 = la⁶ z1`, `u - (3 + 3Π + 3Π²) = la⁶ z2`, `ε t² - (1 + 2Π²) = la⁶ z3` with
`t = 1 + Π²` (`tO`) and `u u⁻¹ = 1` (data: DataK21.lean, DataDyadic.lean).

* `psiLa : R →+* 𝓞 K21 ⧸ (la⁶)`, `π ↦ Π` (well defined: `4 ∈ (la⁶)` by `two_eq`, `Π³ + 2 ∈ (la⁶)`).
* `psiLa` is injective: every nonzero `r ∈ R` has a multiple equal to `π⁵` (finite check on the 64
  triples), and `Π⁵ = la⁵ w⁵ ∉ (la⁶)` because `w ≡ 1` modulo the prime `(la)`. Both sides have 64
  elements (`absNorm (la⁶) = 2⁶`), so `psiLa` is bijective; `rho0` is its inverse after the quotient map.
* `rho0 s` is a unit for `s ∉ (la)`: `y s = 1 - la c` and `rho0 (la)⁶ = 0`.
-/

namespace FurioLombardo.Discharge.M3b

open Polynomial NumberField FurioLombardo.M1 FurioLombardo.M1.Kron
open FurioLombardo.M3b.DyadicCert

/-! ## Kernel identities -/

theorem ck_Pi : checkK 512 (.sub (.lin PiL)
    (.mul (gE 12) (.add (.add (.add (.int 1) (gE 12)) ((gE 12).pow 2)) ((gE 12).pow 4)))) = true := by
  decide +kernel

theorem ck_z1 : checkK 1024 (.sub (.add ((KE.lin PiL).pow 3) (.int 2))
    (.mul ((gE 12).pow 6) (.lin z1L))) = true := by
  decide +kernel

theorem ck_z2 : checkK 1024 (.sub (.sub (.lin uL)
    (.add (.add (.int 3) (.mul (.int 3) (.lin PiL))) (.mul (.int 3) ((KE.lin PiL).pow 2))))
    (.mul ((gE 12).pow 6) (.lin z2L))) = true := by
  decide +kernel

theorem ck_z3 : checkK 1024 (.sub (.sub (.mul (.lin epsL) ((KE.add (.int 1) ((KE.lin PiL).pow 2)).pow 2))
    (.add (.int 1) (.mul (.int 2) ((KE.lin PiL).pow 2))))
    (.mul ((gE 12).pow 6) (.lin z3L))) = true := by
  decide +kernel

theorem ck_u : checkK 512 (.sub (.mul (.lin uL) (.lin uInvL)) (.int 1)) = true := by
  decide +kernel

/-- `w = 1 + la + la² + la⁴`. -/
noncomputable def wO : 𝓞 K21 := 1 + gO 12 + gO 12 ^ 2 + gO 12 ^ 4

theorem PiO_eq_mul : PiO = gO 12 * wO := rfl

theorem PiO_eq_zkO : PiO = zkO PiL := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_Pi
  simp only [evK_mul, evK_add, evK_lin, evK_int, evK_pow, evK_gE, Int.cast_one] at h
  rw [← coe_zkO] at h
  rw [PiO]
  simp only [map_add, map_mul, map_pow, map_one]
  exact h.symm

theorem coe_PiO : ((PiO : 𝓞 K21) : K21) = zkE PiL := by rw [PiO_eq_zkO, coe_zkO]

theorem z1_eq : PiO ^ 3 + 2 = gO 12 ^ 6 * zkO z1L := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_z1
  simp only [evK_mul, evK_add, evK_lin, evK_int, evK_pow, evK_gE] at h
  rw [← coe_PiO, ← coe_zkO z1L] at h
  push_cast at h
  simp only [map_add, map_mul, map_pow, map_ofNat]
  exact h

theorem z2_eq : zkO uL - (3 + 3 * PiO + 3 * PiO ^ 2) = gO 12 ^ 6 * zkO z2L := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_z2
  simp only [evK_mul, evK_add, evK_sub, evK_lin, evK_int, evK_pow, evK_gE] at h
  rw [← coe_PiO, ← coe_zkO uL, ← coe_zkO z2L] at h
  push_cast at h
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  exact h

theorem z3_eq : epsO * tO ^ 2 - (1 + 2 * PiO ^ 2) = gO 12 ^ 6 * zkO z3L := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_z3
  simp only [evK_mul, evK_add, evK_sub, evK_lin, evK_int, evK_pow, evK_gE] at h
  rw [← coe_PiO, ← coe_zkO epsL, ← coe_zkO z3L] at h
  push_cast at h
  rw [tO, epsO]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  exact h

theorem u_mul_inv : zkO uL * zkO uInvL = 1 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_u
  simp only [evK_mul, evK_lin, evK_int, Int.cast_one] at h
  rw [← coe_zkO uL, ← coe_zkO uInvL] at h
  simp only [map_mul, map_one]
  exact h

/-- The unit `u = zk[19] - 1`. -/
noncomputable def uU : (𝓞 K21)ˣ :=
  ⟨zkO uL, zkO uInvL, u_mul_inv, by rw [mul_comm]; exact u_mul_inv⟩

/-! ## The quotient `𝓞 K21 ⧸ (la⁶)` -/

/-- The ideal `(la⁶)`. -/
noncomputable def I6 : Ideal (𝓞 K21) := Ideal.span {gO 12 ^ 6}

/-- `𝓞 K21 ⧸ (la⁶)`. -/
abbrev Q6 : Type := 𝓞 K21 ⧸ I6

/-- The quotient map. -/
noncomputable abbrev mk6 : 𝓞 K21 →+* Q6 := Ideal.Quotient.mk I6

theorem mk6_eq_zero {x : 𝓞 K21} (c : 𝓞 K21) (h : x = gO 12 ^ 6 * c) : mk6 x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ⟨c, h⟩)

theorem mk6_eq {x y : 𝓞 K21} (c : 𝓞 K21) (h : x - y = gO 12 ^ 6 * c) : mk6 x = mk6 y :=
  Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 ⟨c, h⟩)

theorem gO12_ne_zero : gO 12 ≠ 0 := by
  intro h
  have := absNorm_span_gO12
  rw [h, Ideal.span_singleton_eq_bot.2 rfl, Ideal.absNorm_bot] at this
  norm_num at this

theorem four_eq : (4 : 𝓞 K21) = gO 12 ^ 6 * (eO 0 * gO 13 ^ 12 * gO 14 ^ 6) ^ 2 := by
  rw [show (4 : 𝓞 K21) = 2 * 2 by norm_num, two_eq]; ring

/-- `ZMod 4 → 𝓞 K21 ⧸ (la⁶)`, through `ℤ ⧸ (4)` (`4 ∈ (la⁶)`, `four_eq`). -/
noncomputable def z4 : ZMod 4 →+* Q6 :=
  (Ideal.Quotient.lift (Ideal.span {((4 : ℕ) : ℤ)}) (Int.castRingHom Q6) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    rw [map_mul, map_natCast, show ((4 : ℕ) : Q6) = mk6 4 by rw [Nat.cast_ofNat, map_ofNat], mk6_eq_zero _ four_eq,
      zero_mul])).comp (Int.quotientSpanNatEquivZMod 4).symm.toRingHom

theorem eval₂_E4 : E4.eval₂ z4 (mk6 PiO) = 0 := by
  rw [E4, eval₂_add, eval₂_X_pow, eval₂_C, map_ofNat, ← map_pow, ← map_ofNat mk6 2, ← map_add]
  exact mk6_eq_zero _ z1_eq

/-- `psiLa : R → 𝓞 K21 ⧸ (la⁶)`, `π ↦ Π`. -/
noncomputable def psiLa : R →+* Q6 := AdjoinRoot.lift z4 (mk6 PiO) eval₂_E4

theorem psiLa_elt (a b c : ZMod 4) :
    psiLa (elt (a, b, c)) = z4 a + z4 b * mk6 PiO + z4 c * mk6 PiO ^ 2 := by
  simp only [elt, psiLa, map_add, map_mul, map_pow, of, AdjoinRoot.lift_of,
    FurioLombardo.M3b.DyadicCert.pi, AdjoinRoot.lift_root]

/-! ## `psiLa` is bijective -/

/-- Every nonzero element of `R` has a multiple equal to `π⁵ = 2π²`. -/
theorem socle_T : ∀ a b c : ZMod 4, ((a, b, c) : T) ≠ 0 → ∃ s : T, tmul s (a, b, c) = (0, 0, 2) := by
  decide +kernel

theorem four_R : (4 : R) = 0 := by
  rw [show (4 : R) = of 4 from (map_ofNat of 4).symm]
  rw [show (4 : ZMod 4) = 0 from rfl, map_zero]

theorem elt_socle : elt (0, 0, 2) = pi ^ 5 := by
  simp only [elt, map_zero, map_ofNat, zero_mul, zero_add]
  linear_combination (-pi ^ 2) * pi_cube + pi ^ 2 * four_R

theorem PiO_pow_five_not_mem : PiO ^ 5 ∉ I6 := by
  rw [I6, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have hw : wO ^ 5 = gO 12 * c := by
    have h' : gO 12 ^ 5 * wO ^ 5 = gO 12 ^ 5 * (gO 12 * c) := by
      rw [← mul_pow, ← PiO_eq_mul, hc]; ring
    exact mul_left_cancel₀ (pow_ne_zero 5 gO12_ne_zero) h'
  have hwP : wO ∈ Ideal.span {gO 12} :=
    isMaximal_span_gO12.isPrime.mem_of_pow_mem 5 (Ideal.mem_span_singleton.2 ⟨c, hw⟩)
  have h1 : (1 : 𝓞 K21) ∈ Ideal.span {gO 12} := by
    have : (1 : 𝓞 K21) = wO - gO 12 * (1 + gO 12 + gO 12 ^ 3) := by rw [wO]; ring
    rw [this]
    exact Ideal.sub_mem _ hwP (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  exact isMaximal_span_gO12.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem psiLa_injective : Function.Injective psiLa := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨⟨a, b, c⟩, rfl⟩ := elt_surjective r
  by_contra hne
  have ht : ((a, b, c) : T) ≠ 0 := by
    rintro h
    apply hne
    rw [h]
    simp [elt]
  obtain ⟨s, hs⟩ := socle_T a b c ht
  have h5 : psiLa (pi ^ 5) = 0 := by
    rw [← elt_socle, ← hs, ← elt_mul, map_mul, hr, mul_zero]
  have hpi : psiLa pi = mk6 PiO := AdjoinRoot.lift_root eval₂_E4
  rw [map_pow, hpi, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h5
  exact PiO_pow_five_not_mem h5

theorem card_Q6 : Nat.card Q6 = 64 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, I6, Ideal.absNorm_span_singleton, map_pow,
    Int.natAbs_pow]
  rw [show (Algebra.norm ℤ (gO 12)).natAbs = 2 from natAbs_nZ_la]

theorem card_R : Nat.card R = 64 := by
  rw [← Nat.card_congr (Equiv.ofBijective elt ⟨elt_injective, elt_surjective⟩)]
  simp

instance : Finite Q6 := Nat.finite_of_card_ne_zero (by rw [card_Q6]; norm_num)

theorem psiLa_bijective : Function.Bijective psiLa :=
  psiLa_injective.bijective_of_nat_card_le (by rw [card_Q6, card_R])

/-- `R ≅ 𝓞 K21 ⧸ (la⁶)`. -/
noncomputable def psiLaEquiv : R ≃+* Q6 := RingEquiv.ofBijective psiLa psiLa_bijective

/-- The reduction `𝓞 K21 → R`. -/
noncomputable def rho0 : 𝓞 K21 →+* R := psiLaEquiv.symm.toRingHom.comp mk6

theorem rho0_eq {x : 𝓞 K21} {t : T} (h : psiLa (elt t) = mk6 x) : rho0 x = elt t := by
  show psiLaEquiv.symm (mk6 x) = elt t
  rw [RingEquiv.symm_apply_eq]
  exact h.symm

theorem rho0_eq_zero {x : 𝓞 K21} (c : 𝓞 K21) (h : x = gO 12 ^ 6 * c) : rho0 x = 0 := by
  show psiLaEquiv.symm (mk6 x) = 0
  rw [mk6_eq_zero c h, map_zero]

theorem isUnit_rho0 {s : 𝓞 K21} (hs : s ∉ Ideal.span {gO 12}) : IsUnit (rho0 s) := by
  obtain ⟨y, i, hi, hyi⟩ := isMaximal_span_gO12.exists_inv hs
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hi
  have hnil : IsNilpotent (rho0 (gO 12 * c)) :=
    ⟨6, by rw [← map_pow]; exact rho0_eq_zero (c ^ 6) (by ring)⟩
  have hys : rho0 y * rho0 s = 1 - rho0 (gO 12 * c) := by
    rw [← map_mul, ← map_one rho0, ← map_sub, ← hyi]; congr 1; ring
  have hu := hnil.isUnit_one_sub
  rw [← hys] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem rho0_u : rho0 (zkO uL) = elt U := by
  apply rho0_eq
  rw [U, psiLa_elt, map_ofNat, ← map_ofNat mk6 3, ← map_pow, ← map_mul, ← map_mul, ← map_add,
    ← map_add]
  exact (mk6_eq (zkO z2L) z2_eq).symm

theorem rho0_d : rho0 (epsO * tO ^ 2) = elt D := by
  apply rho0_eq
  rw [D, psiLa_elt, map_one, map_zero, zero_mul, add_zero, map_ofNat, ← map_ofNat mk6 2, ← map_pow,
    ← map_mul, ← map_one mk6, ← map_add]
  exact (mk6_eq (zkO z3L) z3_eq).symm

end FurioLombardo.Discharge.M3b
