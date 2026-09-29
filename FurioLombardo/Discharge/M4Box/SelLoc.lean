import Mathlib
import FurioLombardo.Discharge.SelmerSpan.Basis
import FurioLombardo.Discharge.M4Log.LamInt

/-!
# `HSelLoc` from the Selmer basis (lane lean-m4box, `hSel`)

For a global point `Q`, write `ι Q = Σ c_i D_i + 2 b` (the `D_i` generate `J(K_v)` modulo 2,
`genModTwo_Dpt`). The `x - T` map at `v` kills `2 b` and commutes with the localisation
(`muJ_jacMap`), and the Selmer basis writes `μ(Q) = ∏ g_j^(e_j)` with `Hmap(g_j) = ∏ μ_v(D_i)^(SB i j)`.
So `∏ μ_v(D_i)^(c_i - Σ_j SB i j e_j) = 1`, and the independence of the `μ_v(D_i)` (`indep_Dpt`)
makes every `c_i ≡ Σ_j SB i j e_j ≡ selc SB m i (mod 2)` for the number `m` with binary digits the
parities of the `e_j`. Hence `ι Q = Σ selc SB m i • D_i + 2 b'`.
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin

namespace FurioLombardo.Discharge.M4Box

attribute [local instance] goodSextic_fRev_Kv

/-- `μ` of `Σ c_i D_i + 2 b` is `∏ μ(D_i)^(c_i)`. -/
theorem muJ_sum_smul {L : Type*} [Field L] (g : L[X]) [GoodSextic g] (D : Fin 7 → Additive (Jac g))
    (c : Fin 7 → ℤ) (b : Additive (Jac g)) :
    muJ g (Additive.toMul (∑ i, c i • D i + (2 : ℕ) • b)) = ∏ i, muJ g (Additive.toMul (D i)) ^ c i := by
  rw [toMul_add, map_mul, toMul_sum, map_prod, toMul_nsmul, map_pow]
  rw [← map_pow (muJ g) (Additive.toMul b) (2 : ℕ), muJ_sq g (Additive.toMul b)]
  rw [mul_one (a := (∏ i, muJ g (Additive.toMul (c i • D i)) : H g))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [toMul_zsmul, map_zpow]

/-- The images of a product of the generators. -/
theorem prod_pow_prod {G : Type*} [CommGroup G] (x : Fin 7 → G) (SB : Matrix (Fin 7) (Fin 4) ℤ)
    (e : Fin 4 → ℤ) : ∏ j, (∏ i, x i ^ SB i j) ^ e j = ∏ i, x i ^ ∑ j, SB i j * e j := by
  have zpow_sum {a : G} (s : Finset (Fin 4)) (f : Fin 4 → ℤ) : a ^ (∑ j ∈ s, f j) = ∏ j ∈ s, a ^ f j := by
    induction' s using Finset.induction_on with j s hjs ih
    · simp
    · simp [Finset.sum_insert hjs, Finset.prod_insert hjs, zpow_add, ih]
  calc
    ∏ j, (∏ i, x i ^ SB i j) ^ e j = ∏ j, ∏ i, (x i ^ SB i j) ^ e j := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Finset.prod_zpow]
    _ = ∏ i, ∏ j, (x i ^ SB i j) ^ e j := by rw [Finset.prod_comm]
    _ = ∏ i, ∏ j, x i ^ (SB i j * e j) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← zpow_mul]
    _ = ∏ i, x i ^ (∑ j, SB i j * e j) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_sum Finset.univ (fun j => SB i j * e j)]

theorem prod_zpow_sub_eq_one {G : Type*} [CommGroup G] (x : Fin 7 → G) {a c : Fin 7 → ℤ}
    (h : ∏ i, x i ^ c i = ∏ i, x i ^ a i) : ∏ i, x i ^ (c i - a i) = 1 := by
  calc
    ∏ i, x i ^ (c i - a i) = ∏ i, (x i ^ c i * (x i ^ a i)⁻¹) := by
      refine Finset.prod_congr rfl (λ i hi => ?_)
      rw [zpow_sub (x i) (c i) (a i)]
    _ = ∏ i, (x i ^ c i / x i ^ a i) := by
      refine Finset.prod_congr rfl (λ i hi => ?_)
      rw [div_eq_mul_inv]
    _ = (∏ i, x i ^ c i) / (∏ i, x i ^ a i) := by rw [Finset.prod_div_distrib]
    _ = (∏ i, x i ^ a i) / (∏ i, x i ^ a i) := by rw [h]
    _ = 1 := by rw [div_self']

theorem exists_bits_aux1 :
    ∀ p : Fin 4 → Bool, ∃ m : Fin 16, ∀ j : Fin 4, Nat.testBit m.val (3 - j.val) = p j := by
  decide

/-- The number `m` with binary digits the parities of the `e_j` (most significant first). -/
theorem exists_bits (e : Fin 4 → ℤ) :
    ∃ m : Fin 16, ∀ j : Fin 4, (2 : ℤ) ∣ e j - (if Nat.testBit m.val (3 - j.val) then 1 else 0) := by
  let p : Fin 4 → Bool := λ j => decide (e j % 2 = 1)
  obtain ⟨m, hm⟩ := FurioLombardo.Discharge.M4Box.exists_bits_aux1 p
  refine ⟨m, λ j => ?_⟩
  have hbit := hm j
  have hmod := Int.emod_two_eq_zero_or_one (e j)
  dsimp [p] at hbit
  rcases hmod with (hmod | hmod)
  · -- hmod: e j % 2 = 0
    have hbit_false : Nat.testBit m.val (3 - j.val) = false := by
      rw [hbit]
      simp [hmod]
    have htarget : (if Nat.testBit m.val (3 - j.val) then (1 : ℤ) else 0) = (0 : ℤ) := by
      simp [hbit_false]
    rw [htarget]
    omega
  · -- hmod: e j % 2 = 1
    have hbit_true : Nat.testBit m.val (3 - j.val) = true := by
      rw [hbit]
      simp [hmod]
    have htarget : (if Nat.testBit m.val (3 - j.val) then (1 : ℤ) else 0) = (1 : ℤ) := by
      simp [hbit_true]
    rw [htarget]
    omega

theorem dvd_sub_selc {SB : Matrix (Fin 7) (Fin 4) ℤ} {e : Fin 4 → ℤ} {m : Fin 16}
    (hm : ∀ j : Fin 4, (2 : ℤ) ∣ e j - (if Nat.testBit m.val (3 - j.val) then 1 else 0))
    {c : ℤ} {i : Fin 7} (h : (2 : ℤ) ∣ c - ∑ j, SB i j * e j) : (2 : ℤ) ∣ c - FurioLombardo.M4.selc SB m i := by
  have e1 : c - FurioLombardo.M4.selc SB m i = (c - ∑ j, SB i j * e j) +
      ∑ j, SB i j * (e j - (if Nat.testBit m.val (3 - j.val) then 1 else 0)) := by
    unfold FurioLombardo.M4.selc
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun j _ => mul_comm (SB i j) (if Nat.testBit m.val (3 - j.val) then (1 : ℤ) else 0)]
    ring
  rw [e1]
  exact dvd_add h (Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hm j) _)

theorem sum_smul_split {B : Type*} [AddCommGroup B] (D : Fin 7 → B) {c s d : Fin 7 → ℤ}
    (h : ∀ i, c i - s i = 2 * d i) (b : B) :
    ∑ i, c i • D i + (2 : ℕ) • b = ∑ i, s i • D i + (2 : ℕ) • (∑ i, d i • D i + b) := by
  have hc : ∀ i, c i • D i = s i • D i + (d i • D i + d i • D i) := fun i => by
    rw [show c i = s i + 2 * d i by linarith [h i], add_smul, mul_smul, two_zsmul]
  simp only [hc, Finset.sum_add_distrib, two_nsmul]
  abel

/-- **`HSelLoc` from the Selmer basis of the twist `k`.** -/
theorem hSel_of_selmerBasis (k : Fin 2) {D : FurioLombardo.M4.TwistData}
    (hB : SelmerSpan.SelmerBasisK21 k D.SB) :
    FurioLombardo.M4.HSelLoc (iotaA σ (fRev k)) (SelmerSpan.Dpt k) D := by
  obtain ⟨g, hspan, hg⟩ := hB
  intro Q
  obtain ⟨c, b, hc⟩ := FurioLombardo.Discharge.M4Log.genModTwo_Dpt k (iotaA σ (fRev k) Q)
  obtain ⟨e, he⟩ := hspan (Additive.toMul Q)
  obtain ⟨m, hm⟩ := exists_bits e
  have h1 : muJ ((fRev k).map σ) (Additive.toMul (iotaA σ (fRev k) Q)) =
      ∏ i, muJ ((fRev k).map σ) (Additive.toMul (SelmerSpan.Dpt k i)) ^ c i := by
    rw [hc, muJ_sum_smul]
  have h2 : muJ ((fRev k).map σ) (Additive.toMul (iotaA σ (fRev k) Q)) =
      ∏ i, muJ ((fRev k).map σ) (Additive.toMul (SelmerSpan.Dpt k i)) ^ ∑ j, D.SB i j * e j := by
    change muJ ((fRev k).map σ) (jacMap σ (fRev k) (Additive.toMul Q)) = _
    rw [muJ_jacMap, he, map_prod]
    simp only [map_zpow, hg]
    exact prod_pow_prod _ D.SB e
  have h3 := SelmerSpan.indep_Dpt k _ (prod_zpow_sub_eq_one _ (h1.symm.trans h2))
  have h4 : ∀ i, ∃ d : ℤ, c i - FurioLombardo.M4.selc D.SB m i = 2 * d := fun i =>
    dvd_sub_selc hm (h3 i)
  choose d hd using h4
  exact ⟨m, ∑ i, d i • SelmerSpan.Dpt k i + b, by rw [hc]; exact sum_smul_split _ hd b⟩

end FurioLombardo.Discharge.M4Box
