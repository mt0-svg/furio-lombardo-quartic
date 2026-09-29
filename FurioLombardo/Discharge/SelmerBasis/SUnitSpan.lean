import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.SelmerBasis.SUnitDefs
import FurioLombardo.Discharge.SelmerBasis.SUnitRank
import FurioLombardo.Discharge.SelmerBasis.SUnitCount
import FurioLombardo.Discharge.SelmerBasis.SUnitMemGen
import FurioLombardo.Discharge.SelmerBasis.SUnitIndepGen
import FurioLombardo.Discharge.M3b.Main
import FurioLombardo.M2.ZimmertProved
import FurioLombardo.Discharge.SelmerBasis.SUnitMem
import FurioLombardo.Discharge.SelmerBasis.SUnitIndep

/-!
# `SUnitSpan` for `L42` and `N84` (piece (e))

`sUnitSpan_of`: in a number field `F` with `Cl(F)[2] = 1`, `m ≥ rank + #S27 F + 1` nonzero
generators whose classes lie in `K(S27 F, 2)` and are independent modulo squares satisfy
`SUnitSpan F`. This is M1's `exists_isSquare_mul_prod` with `S = S27 F`, and the hypothesis of
`SUnitSpan` puts the class of `x` in `K(S27 F, 2)`.

For `L42` and `N84`: `Cl[2] = 1` (lane M3b's `classGroups_L42_N84` from `h(K21) = 1`, lane M2),
`rank ≤ 23, 44` (SUnitRank.lean) and `#S27 ≤ 5, 8` (SUnitCount.lean), so `29` and `53` generators
suffice. `sUnitSpan_L42_of`, `sUnitSpan_N84_of` leave the three facts on the generators
(nonzero, in `K(S27, 2)`, independent), proved in SUnitMem.lean and SUnitIndep.lean.

Coordinates (piece (f)): `isSquare_mul_prod_of_mod_two` (only the exponents modulo 2 matter) and
`isSquare_of_chars` (the exponents modulo 2 are read off the residue characters of `x`).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField IsDedekindDomain FurioLombardo.M1 FurioLombardo.Discharge.M3b
open scoped nonZeroDivisors

/-- `subprod` as a product of powers. -/
theorem subprod_eq_prod_pow {M : Type*} [CommMonoid M] {m : ℕ} (g : Fin m → M)
    (e : Fin m → Bool) : subprod g e = ∏ s, g s ^ (if e s then 1 else 0) := by
  simp only [subprod]
  refine Finset.prod_congr rfl fun s _ => ?_
  split <;> simp

/-- **`SUnitSpan` from a Selmer basis.** -/
theorem sUnitSpan_of {F : Type*} [Field F] [NumberField F] {m : ℕ} (gens : Fin m → F)
    (hCl : ∀ c : ClassGroup (𝓞 F), c ^ 2 = 1 → c = 1) (hS : (S27 F).Finite)
    (hm : Units.rank F + (S27 F).ncard + 1 ≤ m) (h0 : ∀ s, gens s ≠ 0)
    (hg : ∀ s, (QuotientGroup.mk (Units.mk0 (gens s) (h0 s)) : SqClass F) ∈
      selmerGroup (K := F) (S := S27 F) (n := 2))
    (hind : ∀ e : Fin m → Bool, IsSquare (subprod gens e) → ∀ s, e s = false) :
    SUnitSpan F gens := by
  intro x hx hev
  have hu : (QuotientGroup.mk (Units.mk0 x hx) : SqClass F) ∈
      selmerGroup (K := F) (S := S27 F) (n := 2) := by
    refine mem_selmerGroup_of_even_count (S27 F) (Units.mk0 x hx) fun v hv => ?_
    simp only [S27, Set.mem_ofPred_eq, not_or] at hv
    exact hev v hv.1 hv.2
  obtain ⟨e, he⟩ := exists_isSquare_mul_prod (S27 F) hS hCl hm (fun s => Units.mk0 (gens s) (h0 s))
    hg (fun e h => hind e (by simpa using h)) (Units.mk0 x hx) hu
  refine ⟨fun s => if e s then 1 else 0, ?_⟩
  rw [← subprod_eq_prod_pow]
  simpa using he

/-- `Cl(K21)[2] = 1` (lane M2: `h(K21) = 1`). -/
theorem clTwoTrivial_K21 : FurioLombardo.M3b.ClTwoTrivial K21 :=
  @clTwoTrivial_of_pid FurioLombardo.M2.Proved.isPrincipalIdealRing_M1K21

theorem clTwo_L42 : ∀ c : ClassGroup (𝓞 L42), c ^ 2 = 1 → c = 1 :=
  (classGroups_L42_N84 clTwoTrivial_K21).1

theorem clTwo_N84 : ∀ c : ClassGroup (𝓞 N84), c ^ 2 = 1 → c = 1 :=
  (classGroups_L42_N84 clTwoTrivial_K21).2

/-- `SUnitSpan L42 gensL` from the three facts on the generators. -/
theorem sUnitSpan_L42_of (h0 : ∀ s, gensL s ≠ 0)
    (hg : ∀ s, (QuotientGroup.mk (Units.mk0 (gensL s) (h0 s)) : SqClass L42) ∈
      selmerGroup (K := L42) (S := S27 L42) (n := 2))
    (hind : ∀ e : Fin 29 → Bool, IsSquare (subprod gensL e) → ∀ s, e s = false) :
    SUnitSpan L42 gensL :=
  sUnitSpan_of gensL clTwo_L42 S27_L42_finite
    (by have := rank_L42_le; have := ncard_S27_L42; omega) h0 hg hind

/-- `SUnitSpan N84 gensN` from the three facts on the generators. -/
theorem sUnitSpan_N84_of (h0 : ∀ s, gensN s ≠ 0)
    (hg : ∀ s, (QuotientGroup.mk (Units.mk0 (gensN s) (h0 s)) : SqClass N84) ∈
      selmerGroup (K := N84) (S := S27 N84) (n := 2))
    (hind : ∀ e : Fin 53 → Bool, IsSquare (subprod gensN e) → ∀ s, e s = false) :
    SUnitSpan N84 gensN :=
  sUnitSpan_of gensN clTwo_N84 S27_N84_finite
    (by have := rank_N84_le; have := ncard_S27_N84; omega) h0 hg hind

/-! ### Coordinates (piece (f)) -/

/-- Only the exponents modulo 2 matter. -/
theorem isSquare_mul_prod_of_mod_two {F : Type*} [Field F] {m : ℕ} (g : Fin m → F)
    (hg : ∀ s, g s ≠ 0) (x : F) (a b : Fin m → ℕ) (hab : ∀ s, a s % 2 = b s % 2)
    (hb : IsSquare (x * ∏ s, g s ^ b s)) : IsSquare (x * ∏ s, g s ^ a s) := by
  obtain ⟨y, hy⟩ := hb
  set k : Fin m → ℤ := fun s => ((a s : ℤ) - b s) / 2
  have hk : ∀ s, (a s : ℤ) = b s + 2 * k s := fun s => by
    have := hab s; simp only [k]; omega
  have e : ∀ s, g s ^ a s = g s ^ b s * (g s ^ k s) ^ 2 := fun s => by
    rw [← zpow_natCast, ← zpow_natCast (g s) (b s), ← zpow_natCast (g s ^ k s) 2, ← zpow_mul,
      ← zpow_add₀ (hg s), hk s]
    push_cast; ring_nf
  refine ⟨y * ∏ s, g s ^ k s, ?_⟩
  simp_rw [e, Finset.prod_mul_distrib, Finset.prod_pow]
  rw [← mul_assoc, hy]
  ring

/-- **Coordinates from characters.** With the data of `coord_of_chars`, nonzero generators, and
`ι X ∏ ι (G s) ^ b s` a square for some `b`, the exponents `a s = [dotB r (T s) c]` computed from
the characters `c` of `X` also give a square. -/
theorem isSquare_of_chars {O F : Type*} [CommRing O] [Field F] (ι : O →+* F) {m r : ℕ}
    (G : Fin m → O) (hG : ∀ s, ι (G s) ≠ 0) (p : Fin r → ℕ) [hp : ∀ j, Fact (p j).Prime]
    (hp2 : ∀ j, p j ≠ 2)
    (ρ : ∀ j, O →+* ZMod (p j)) (hsq : ∀ j (X : O), IsSquare (ι X) → IsSquare (ρ j X))
    (R : ℕ → ℕ) (hR : ∀ j (s : Fin m),
      ρ j (G s) ^ ((p j - 1) / 2) = if (R j).testBit s then -1 else 1)
    (T : ℕ → ℕ) (hT : leftInvOK R r m T = true) (X : O) (c : ℕ)
    (hc : ∀ j : Fin r, ρ j X ^ ((p j - 1) / 2) = if c.testBit j then -1 else 1)
    (b : Fin m → ℕ) (hb : IsSquare (ι X * ∏ s, ι (G s) ^ b s)) :
    IsSquare (ι X * ∏ s, ι (G s) ^ (if dotB r (T s) c then 1 else 0)) := by
  refine isSquare_mul_prod_of_mod_two (fun s => ι (G s)) hG (ι X) _ b (fun s => ?_) hb
  rw [coord_of_chars ι G p hp2 ρ hsq R hR T hT X c hc b hb s]
  split <;> rfl

/-! ### The targets -/

/-- **`SUnitSpan` for `L42`.** -/
theorem sUnitSpan_L42 : SUnitSpan L42 gensL :=
  sUnitSpan_L42_of gensL_ne_zero gensL_mem gensL_indep

/-- **`SUnitSpan` for `N84`.** -/
theorem sUnitSpan_N84 : SUnitSpan N84 gensN :=
  sUnitSpan_N84_of gensN_ne_zero gensN_mem gensN_indep

end FurioLombardo.Discharge.SelmerBasis
