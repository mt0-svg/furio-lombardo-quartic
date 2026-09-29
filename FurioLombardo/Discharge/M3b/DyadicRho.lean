import FurioLombardo.Discharge.M3b.K21Primes
import FurioLombardo.Discharge.M3b.DataK21
import FurioLombardo.M3b.DyadicCert
import FurioLombardo.Discharge.M3b.DyadicMap

/-!
# The reduction map at the dyadic prime `(la)` of `K21` onto `R = (ℤ/4)[π]/(π³ + 2)`

`v` is the adic valuation of the height one prime `(la)` (`Pla`). Its valuation ring is Mathlib's
`valuationSubringAtPrime K21 Pla`, a localization of `𝓞 K21` at `(la)`
(`valuationSubringAtPrime_eq_valuationSubring`). The reduction `rho0 : 𝓞 K21 → R` of DyadicMap.lean
sends every `s ∉ (la)` to a unit, so it extends to the localization (`IsLocalization.lift`), whence
`ρ : v.integer → R`. The images of `u = zk[19] - 1` and of `d = ε t²` are `U = (3, 3, 3)` and
`D = (1, 0, 2)` (`rho0_u`, `rho0_d`).
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 NumberField

section Loc

open IsDedekindDomain HeightOneSpectrum

/-- The height one prime `(la)` of `𝓞 K21`. -/
noncomputable def Pla : HeightOneSpectrum (𝓞 K21) :=
  ⟨Ideal.span {gO 12}, isMaximal_span_gO12.isPrime, by
    intro h
    have := absNorm_span_gO12
    rw [h, Ideal.absNorm_bot] at this
    norm_num at this⟩

/-- The `(la)`-adic valuation of `K21`. -/
noncomputable def vla : Valuation K21 (WithZero (Multiplicative ℤ)) := Pla.valuation K21

/-- `rho0` on the localization of `𝓞 K21` at `(la)`. -/
noncomputable def rhoLoc : valuationSubringAtPrime K21 Pla →+* FurioLombardo.M3b.DyadicCert.R :=
  IsLocalization.lift (M := Pla.asIdeal.primeCompl) (g := rho0) (fun y => isUnit_rho0 y.2)

theorem mem_valuationSubringAtPrime {x : K21} (hx : x ∈ vla.integer) :
    x ∈ valuationSubringAtPrime K21 Pla := by
  rw [valuationSubringAtPrime_eq_valuationSubring]; exact hx

/-- The reduction map on `v.integer`. -/
noncomputable def rhoV : vla.integer →+* FurioLombardo.M3b.DyadicCert.R where
  toFun x := rhoLoc ⟨x.1, mem_valuationSubringAtPrime x.2⟩
  map_one' := by rw [← rhoLoc.map_one]; rfl
  map_mul' x y := by rw [← rhoLoc.map_mul]; rfl
  map_zero' := by rw [← rhoLoc.map_zero]; rfl
  map_add' x y := by rw [← rhoLoc.map_add]; rfl

theorem coe_mem_integer (a : 𝓞 K21) : (a : K21) ∈ vla.integer :=
  valuation_le_one Pla a

theorem rhoV_coe (a : 𝓞 K21) : rhoV ⟨(a : K21), coe_mem_integer a⟩ = rho0 a := by
  have h := IsLocalization.lift_eq (M := Pla.asIdeal.primeCompl)
    (S := valuationSubringAtPrime K21 Pla) (fun y : Pla.asIdeal.primeCompl => isUnit_rho0 y.2) a
  exact h

end Loc

theorem exists_dyadic :
    ∃ (v : Valuation K21 (WithZero (Multiplicative ℤ))) (ρ : v.integer →+* FurioLombardo.M3b.DyadicCert.R)
      (d : v.integer) (u : (𝓞 K21)ˣ) (u' : v.integer),
      (d : K21) = epsK * (tO : K21) ^ 2 ∧ (u' : K21) = ((u : 𝓞 K21) : K21) ∧
        ρ u' = FurioLombardo.M3b.DyadicCert.elt FurioLombardo.M3b.DyadicCert.U ∧
        ρ d = FurioLombardo.M3b.DyadicCert.elt FurioLombardo.M3b.DyadicCert.D := by
  have hd : ((epsO * tO ^ 2 : 𝓞 K21) : K21) = epsK * (tO : K21) ^ 2 := by
    rw [epsK]; push_cast; rfl
  refine ⟨vla, rhoV, ⟨((epsO * tO ^ 2 : 𝓞 K21) : K21), coe_mem_integer _⟩, uU,
    ⟨((uU : 𝓞 K21) : K21), coe_mem_integer _⟩, hd, rfl, ?_, ?_⟩
  · rw [rhoV_coe]; exact rho0_u
  · rw [rhoV_coe]; exact rho0_d

end FurioLombardo.Discharge.M3b
