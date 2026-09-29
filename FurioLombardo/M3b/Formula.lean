import FurioLombardo.M3b.Ideals
import FurioLombardo.M3b.UnitsIndex

/-!
# Lane M3b: Chevalley's ambiguous class number formula for quadratic extensions

For a quadratic extension `L/K` of number fields with nontrivial automorphism `σ`,
`chevalley_formula`:

  `|Cl(L)^σ| * [E_K : E_K ∩ N(Lˣ)] * 2 = h_K * 2 ^ t`,

`t` the number of places of `K`, finite and real, ramified in `L` (`ramifiedPlaceCount K L`).
The class group is taken in the model `I_L / P_L` (invertible fractional ideals of `L` modulo
principal ones, isomorphic to `ClassGroup (𝓞 L)` by `ClassGroup.equiv`), where `σ` acts by
`InvData.sCl`. Consequence `twoTorsion_trivial`: if `h_K` is odd and
`2 ^ t ≤ 2 [E_K : E_K ∩ N(Lˣ)]`, then `Cl(L)` has no element of order 2.

Proof of the formula: the abstract count `InvData.chevalley_abstract` for `galData`, with
`[E⁻ : (E⁻)²] = 2 ^ (r_L - r_K + 1)`, `[E⁺ : (E⁺)²] = 2 ^ (r_K + 1)` (`UnitsIndex`),
`[fix I_L : PK] = 2 ^ t_f h_K` (`Ideals`) and `r_L + t_∞ = 2 r_K + 1`.
-/

namespace FurioLombardo.M3b

open NumberField Module
open scoped nonZeroDivisors

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Chevalley's ambiguous class number formula** for a quadratic extension of number fields. -/
theorem chevalley_formula (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    Nat.card (galData h2 σ).amb * (normUnits K L).index * 2 =
      classNumber K * 2 ^ ramifiedPlaceCount K L := by
  have hA := (galData h2 σ).chevalley_abstract (galData_H90X h2 σ hσ1) (galData_H90I h2 σ)
  rw [galData_index_sq_Eminus h2 σ, galData_relIndex_NXE h2 σ hσ1, relIndex_PK_fixI h2 σ hσ1,
    galData_index_sq_Eplus h2 σ hσ1] at hA
  have hm := galData_finrank_Eminus h2 σ hσ1
  have hr := rank_add_ncard_ramifiedRealPlaces (K := K) (L := L) h2
  set m := finrank ℤ (Additive (galData h2 σ).Eminus)
  set a := Nat.card (galData h2 σ).amb
  set i := (normUnits K L).index
  set h := classNumber K
  set r := Units.rank K
  set tf := (ramifiedPrimes K L).ncard
  set ti := (ramifiedRealPlaces K L).ncard
  have hmt : r + 1 = m + ti := by omega
  have key : a * i * 2 * 2 ^ (r + 1) = h * 2 ^ (tf + ti) * 2 ^ (r + 1) := by
    calc a * i * 2 * 2 ^ (r + 1) = a * 2 ^ (m + 1) * i * 2 ^ ti := by rw [hmt]; ring
      _ = 2 ^ tf * h * 2 ^ (r + 1) * 2 ^ ti := by rw [hA]
      _ = h * 2 ^ (tf + ti) * 2 ^ (r + 1) := by ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) key

theorem galData_P (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    (galData h2 σ).P = (toPrincipalIdeal (𝓞 L) L).range := rfl

instance finite_quotient_principal :
    Finite ((FractionalIdeal (𝓞 L)⁰ L)ˣ ⧸ (toPrincipalIdeal (𝓞 L) L).range) :=
  Finite.of_equiv _ (ClassGroup.equiv L).toEquiv

theorem sCl_sCl (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (c : (FractionalIdeal (𝓞 L)⁰ L)ˣ ⧸ (galData h2 σ).P) :
    (galData h2 σ).sCl ((galData h2 σ).sCl c) = c := by
  induction c using QuotientGroup.induction_on with
  | H a => rw [InvData.sCl_mk, InvData.sCl_mk, (galData h2 σ).sI_sI]

/-- **`Cl(L)[2] = 0`** for a quadratic extension `L/K` of number fields with `h_K` odd and
`2 ^ t ≤ 2 [E_K : E_K ∩ N(Lˣ)]`, `t` the number of ramified places of `K`. -/
theorem twoTorsion_trivial (h2 : Module.finrank K L = 2) (hK : Odd (classNumber K))
    (hidx : 2 ^ ramifiedPlaceCount K L ≤ 2 * (normUnits K L).index) :
    ∀ c : ClassGroup (𝓞 L), c ^ 2 = 1 → c = 1 := by
  obtain ⟨σ, hσ1, -⟩ := exists_involution (K := K) (L := L) h2
  have hf := chevalley_formula h2 σ hσ1
  have hfin : (normUnits K L).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_mul] at hf
    exact (Nat.mul_ne_zero (classNumber_ne_zero K) (by positivity)) hf.symm
  obtain ⟨k, hk⟩ := exists_index_normUnits_eq_two_pow h2 hfin
  have ha := eq_of_chevalley_arith hf hk hidx hK
  have : Finite ((FractionalIdeal (𝓞 L)⁰ L)ˣ ⧸ (galData h2 σ).P) := finite_quotient_principal
  have hcl := eq_one_of_sq_eq_one_of_odd_card_fixed (galData h2 σ).sCl (sCl_sCl h2 σ)
    (by change Odd (Nat.card (galData h2 σ).amb); rw [ha]; exact hK)
  have hcl' : ∀ a : (FractionalIdeal (𝓞 L)⁰ L)ˣ ⧸ (toPrincipalIdeal (𝓞 L) L).range,
      a ^ 2 = 1 → a = 1 := hcl
  intro c hc
  have h1 : ClassGroup.equiv L c = 1 := hcl' _ (by rw [← map_pow, hc, map_one])
  simpa using h1

end FurioLombardo.M3b
