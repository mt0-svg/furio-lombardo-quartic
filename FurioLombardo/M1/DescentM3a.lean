import FurioLombardo.M1.SelmerSet
import FurioLombardo.Discharge.M3a.ConcreteDefs
import FurioLombardo.M3a.Sections

/-!
# The descent in the form of lane M3a

**`descent_Mmat`**: assuming `Cl(K21)[2] = 0`, every rational point of `C` lifts to
`D_δ0(K21)` or `D_δ1(K21)`, i.e. `FurioLombardo.M3a.Descent K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 δ1`
with the matrices `Mmat i` of Bruin's quadrics and the twists `δ0`, `δ1` of the M3a discharge
(`FurioLombardo.Discharge.M3a.Bruin`), the input of `Bruin.onlyFourPoints_fRev` and
`Bruin.onlyFourPoints_Kv`.

The data agree with lane M1's (`QcData_eq`, `dData_eq`), so `p ⬝ᵥ (Mmat i *ᵥ p) = Q_(i+1)(p)`
(`quad_eq`) and `δ k = δK k` (`δ_eq`). A rational point is `l a` with `a` a primitive integer
point; with `p = a`:

* if `Q1(a) ≠ 0`, `Q1(a) = δ_k t²` (`selmer_int`), and `(p, r, s) = (a, t, Q2(a) / (δ_k t))`
  is on `D_δk` because `Q1 Q3 = Q2²`;
* if `Q1(a) = 0`, then `Q2(a) = 0`, `Q3(a) = δ_k t²` (`selmer_int` at `i = 2`), and
  `(p, r, s) = (a, 0, t)` is on `D_δk`.

`p = l⁻¹ (x, y, z)`, so the lift is over `(x : y : z)`.
-/

namespace FurioLombardo.M1

open NumberField Matrix FurioLombardo.M3a
open FurioLombardo.Discharge.M3a.Bruin (Mmat δ0 δ1 δ Qc QcL QcData dL dData)

theorem QcData_eq : QcData = qcL := by decide +kernel

theorem dData_eq : dData = [d0L, d1L] := by decide +kernel

theorem Qc_eq (i : Fin 3) (m : Fin 6) : Qc i m = ((qC i m : 𝓞 K21) : K21) := by
  rw [Qc, QcL, QcData_eq]; rfl

theorem δ_eq (k : Fin 2) : δ k = δK k := by
  rw [δ, dL, dData_eq]; rfl

/-- `p ⬝ᵥ (Mmat i *ᵥ p)` is lane M1's `Q_(i+1)(p)`. -/
theorem quad_eq (i : Fin 3) (p : Fin 3 → K21) : p ⬝ᵥ (Mmat i *ᵥ p) = qK i p := by
  simp only [Mmat, qK, Vendor.NetOfConics.qev, dotProduct, mulVec, Fin.sum_univ_three, ← Qc_eq]
  simp
  ring

/-- A point of `D_δ` from `Q1(p) = δ t² ≠ 0`. -/
theorem exists_dpoint_q1 (d : K21) (hd : d ≠ 0) (p : Fin 3 → K21) (hp : p ≠ 0) (t : K21)
    (hb : qK 0 p * qK 2 p = qK 1 p ^ 2) (h0 : qK 0 p ≠ 0) (ht : qK 0 p = d * t ^ 2) :
    ∃ x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) d, x.p = p := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero] at ht
    exact h0 ht
  refine ⟨⟨p, t, qK 1 p / (d * t), hp, ?_, ?_, ?_⟩, rfl⟩
  · rw [quad_eq, ht]
  · rw [quad_eq]; field_simp
  · rw [quad_eq]
    field_simp
    rw [ht] at hb
    linear_combination hb

/-- A point of `D_δ` from `Q1(p) = 0` and `Q3(p) = δ t²`. -/
theorem exists_dpoint_q3 (d : K21) (p : Fin 3 → K21) (hp : p ≠ 0) (t : K21)
    (hb : qK 0 p * qK 2 p = qK 1 p ^ 2) (h0 : qK 0 p = 0) (ht : qK 2 p = d * t ^ 2) :
    ∃ x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) d, x.p = p := by
  have h1 : qK 1 p = 0 := by
    rw [h0, zero_mul] at hb
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hb.symm
  refine ⟨⟨p, 0, t, hp, ?_, ?_, ?_⟩, rfl⟩
  · rw [quad_eq, h0]; ring
  · rw [quad_eq, h1]; ring
  · rw [quad_eq, ht]

/-- **Lane M1 in the form of lane M3a**: every rational point of `C` lifts to `D_δ0(K21)` or
`D_δ1(K21)`, assuming `Cl(K21)[2] = 0`. -/
theorem descent_Mmat (hCl : ClK21TwoTorsionTrivial) :
    Descent K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0 δ1 := by
  intro x y z hne hF
  obtain ⟨a, r, l, hl, hr, hFa, hP⟩ := exists_int_point x y z hne hF
  set p : Fin 3 → K21 := fun j => ((a j : ℤ) : K21) with hpdef
  have hl' : algebraMap ℚ K21 l ≠ 0 := (map_ne_zero _).mpr hl
  have hp : p ≠ 0 := by
    intro h0
    have ha : ∀ j, a j = 0 := fun j => by
      have := congrFun h0 j
      simpa [hpdef] using this
    simp [ha] at hr
  have hq : ∀ i, qK i p = ((qO i a : 𝓞 K21) : K21) := fun i => qK_intCast i a
  have hb : qK 0 p * qK 2 p = qK 1 p ^ 2 := by
    rw [hq, hq, hq, ← map_mul, bruin_point a hFa, map_pow]
  have hover : ∀ (d : K21) (X : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) d), X.p = p →
      X.Over x y z := by
    intro d X hX
    refine ⟨(algebraMap ℚ K21 l)⁻¹, inv_ne_zero hl', ?_⟩
    rw [hX]
    change p = _ • ptK x y z
    rw [hP, smul_smul, inv_mul_cancel₀ hl', one_smul]
  have hlift : ∀ k : Fin 2, (∃ X : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k), X.p = p) →
      (∃ X : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ0, X.Over x y z) ∨
        (∃ X : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) δ1, X.Over x y z) := by
    intro k ⟨X, hX⟩
    fin_cases k
    · left
      exact ⟨X, hover _ X hX⟩
    · right
      exact ⟨X, hover _ X hX⟩
  by_cases h0 : qO 0 a = 0
  · obtain ⟨i, hi, hne'⟩ := exists_qO_ne_zero a r hr hFa
    have hi2 : i = 2 := by
      rcases hi with rfl | rfl
      · exact absurd h0 hne'
      · rfl
    subst hi2
    obtain ⟨k, t, ht⟩ := selmer_int hCl a r hr hFa 2 (Or.inr rfl) hne'
    rw [← δ_eq] at ht
    refine hlift k (exists_dpoint_q3 _ p hp t hb ?_ (by rw [hq]; exact ht))
    rw [hq, h0]; rfl
  · obtain ⟨k, t, ht⟩ := selmer_int hCl a r hr hFa 0 (Or.inl rfl) h0
    rw [← δ_eq] at ht
    refine hlift k (exists_dpoint_q1 _ (by rw [δ_eq]; exact δK_ne_zero k) p hp t hb ?_
      (by rw [hq]; exact ht))
    rw [hq, Ne, RingOfIntegers.coe_eq_zero_iff]
    exact h0

end FurioLombardo.M1
