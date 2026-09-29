import Mathlib
import FurioLombardo.Vendor.Toolbox.PowerSeries.SqrtMod
import FurioLombardo.Vendor.Toolbox.PowerSeries.FormalFix

/-!
# Square roots modulo `m = X^d + m̃` with the root in `V0 + 2 O⟦t⟧[X]` (lane lean-m4log)

Let `K` be a field of characteristic not `2`, `O` a subring of `K`, and `A = K⟦t⟧` the power
series in the variables `σ`. Let `f, V0, U0, q, h ∈ K[X]` with `f - V0² = 4 X^d q`,
`V0 U0 = 1 + X^d h`, `U0(0) ≠ 0`, and `U0, q, h` with coefficients in `O`. For every monic
`m = X^d + m̃` over `A` with `m̃` of degree `< d`, coefficients in `O⟦t⟧` and no constant term,
there is `Y ∈ O⟦t⟧[X]` of degree `< d`, without constant term, such that
`m ∣ f - (V0 + 2 Y)²` (`exists_sqrtMod_two`).

`Y` is the fixed point of `T(Y) = (m̃ h Y - U0 Y² - U0 m̃ q) mod m`, a contraction for the order in
`t` (`FurioLombardo.Vendor.Toolbox.FormalFix`), as in `FurioLombardo.Vendor.Toolbox.SqrtMod.exists_sqrtMod`; here no power of a uniformizer
enters the modulus, which is what the chart of R7 needs in the integral model of a sextic.
-/

namespace FurioLombardo.Discharge.M4Log.Model

open Polynomial FurioLombardo.Vendor.Toolbox.SqrtMod


variable {K : Type*} [Field K] {σ : Type*} (O : Subring K)

/-- **Square roots modulo `m = X^d + m̃` in `V0 + 2 O⟦t⟧[X]`.** -/
theorem exists_sqrtMod_two {d : ℕ} (hd : 0 < d) (f V0 U0 q h : K[X])
    (hq : f - V0 ^ 2 = 4 * X ^ d * q) (hU : V0 * U0 = 1 + X ^ d * h) (hU0 : U0.coeff 0 ≠ 0)
    (hUO : ∀ n, U0.coeff n ∈ O) (hqO : ∀ n, q.coeff n ∈ O) (hhO : ∀ n, h.coeff n ∈ O)
    (mt : (MvPowerSeries σ K)[X]) (hmt : mt ∈ liftsRing (incl (σ := σ) O))
    (hmt1 : mt ∈ (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X]))
    (hmtd : mt.degree < d) :
    ∃ Y : (MvPowerSeries σ K)[X], Y ∈ liftsRing (incl (σ := σ) O) ∧
      Y ∈ (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X]) ∧
      Y.natDegree < d ∧ (X ^ d + mt) ∣ cst f - (cst V0 + 2 * Y) ^ 2 := by
  classical
  set I1 := (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X]) with hI1
  set L := liftsRing (incl (σ := σ) O) with hL
  set m := X ^ d + mt with hmdef
  have hmmonic : m.Monic := monic_X_pow_add hmtd
  have hmdeg : m.natDegree = d := by
    rw [hmdef, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact hmtd
  have hmL : m ∈ L := L.add_mem (L.pow_mem (mem_liftsRing_of_coeff _ fun n => by
      rw [coeff_X]; split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩) _) hmt
  set u := cst (σ := σ) U0 with hu
  set qc := cst (σ := σ) q with hqc
  set hc := cst (σ := σ) h with hhc
  have huL : u ∈ L := cst_mem_liftsRing O hUO
  have hqL : qc ∈ L := cst_mem_liftsRing O hqO
  have hhL : hc ∈ L := cst_mem_liftsRing O hhO
  let G : (MvPowerSeries σ K)[X] → (MvPowerSeries σ K)[X] :=
    fun V => mt * hc * V - u * V ^ 2 - u * mt * qc
  let T : (Fin d → MvPowerSeries σ K) → (Fin d → MvPowerSeries σ K) :=
    fun y i => (G (toPoly y) %ₘ m).coeff i
  have hGL : ∀ V ∈ L, G V ∈ L := fun V hV =>
    L.sub_mem (L.sub_mem (L.mul_mem (L.mul_mem hmt hhL) hV) (L.mul_mem huL (L.pow_mem hV 2)))
      (L.mul_mem (L.mul_mem huL hmt) hqL)
  have hGI : ∀ V ∈ I1, G V ∈ I1 := fun V hV =>
    I1.sub_mem (I1.sub_mem (I1.mul_mem_left _ hV)
      (I1.mul_mem_left _ (by rw [pow_two]; exact I1.mul_mem_left _ hV)))
      (I1.mul_mem_right _ (I1.mul_mem_left _ hmt1))
  have hS : ∀ y ∈ FurioLombardo.Vendor.Toolbox.FormalFix.CoeffSet (IntNoConst O), T y ∈ FurioLombardo.Vendor.Toolbox.FormalFix.CoeffSet (IntNoConst O) := by
    intro y hy
    obtain ⟨hyL, hyI⟩ := toPoly_mem_of_coeffSet O hy
    exact coeffSet_of_mem O (modByMonic_mem_liftsRing _ hmmonic hmL (hGL _ hyL))
      (modByMonic_mem_map_C hmmonic (hGI _ hyI))
  have h0 : (0 : Fin d → MvPowerSeries σ K) ∈ FurioLombardo.Vendor.Toolbox.FormalFix.CoeffSet (IntNoConst O) := by
    intro i e
    exact ⟨by simp [O.zero_mem], fun _ => by simp⟩
  have hT : FurioLombardo.Vendor.Toolbox.FormalFix.Contracting (FurioLombardo.Vendor.Toolbox.FormalFix.CoeffSet (IntNoConst O)) T := by
    intro y hy z hz n hn i
    obtain ⟨-, hyI⟩ := toPoly_mem_of_coeffSet O hy
    obtain ⟨-, hzI⟩ := toPoly_mem_of_coeffSet O hz
    have hsub := toPoly_sub_mem hn
    have hsum : toPoly y + toPoly z ∈ I1 := I1.add_mem hyI hzI
    have hprod : ∀ P ∈ (ordIdeal (σ := σ) (R := K) n).map (C : _ →+* (MvPowerSeries σ K)[X]),
        ∀ Q ∈ I1, P * Q ∈ (ordIdeal (σ := σ) (R := K) (n + 1)).map
          (C : _ →+* (MvPowerSeries σ K)[X]) := by
      intro P hP Q hQ
      have := Ideal.mul_mem_mul hP hQ
      rw [← Ideal.map_mul] at this
      exact Ideal.map_mono (ordIdeal_mul_le n 1) this
    have hdiff : G (toPoly y) - G (toPoly z) ∈ (ordIdeal (σ := σ) (R := K) (n + 1)).map
        (C : _ →+* (MvPowerSeries σ K)[X]) := by
      have e : G (toPoly y) - G (toPoly z) =
          hc * ((toPoly y - toPoly z) * mt) -
            u * ((toPoly y - toPoly z) * (toPoly y + toPoly z)) := by
        simp only [G]; ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hprod _ hsub _ hmt1))
        (Ideal.mul_mem_left _ _ (hprod _ hsub _ hsum))
    have := Ideal.mem_map_C_iff.mp (modByMonic_mem_map_C hmmonic hdiff) i
    rw [sub_modByMonic, coeff_sub] at this
    exact this
  -- the fixed point
  set y := FurioLombardo.Vendor.Toolbox.FormalFix.fix T with hydef
  have hyS : y ∈ FurioLombardo.Vendor.Toolbox.FormalFix.CoeffSet (IntNoConst O) := FurioLombardo.Vendor.Toolbox.FormalFix.fix_mem_coeffSet h0 hS
  have hTy : T y = y := FurioLombardo.Vendor.Toolbox.FormalFix.T_fix h0 hS hT
  obtain ⟨hyL, hyI⟩ := toPoly_mem_of_coeffSet O hyS
  set Y := toPoly y with hY
  refine ⟨Y, hyL, hyI, natDegree_toPoly_lt hd y, ?_⟩
  have hm1 : m ≠ 1 := by
    intro h1; have := congrArg natDegree h1; rw [hmdeg, natDegree_one] at this; omega
  have hmod : G Y %ₘ m = Y := by
    have e1 : toPoly (T y) = G Y %ₘ m := by
      apply toPoly_fromPoly
      exact lt_of_lt_of_eq (natDegree_modByMonic_lt _ hmmonic hm1) hmdeg
    rw [← e1, hTy]
  have hdvd1 : m ∣ G Y - Y := by
    have := modByMonic_add_div (G Y) m
    rw [hmod] at this
    exact ⟨G Y /ₘ m, by linear_combination (-1 : (MvPowerSeries σ K)[X]) * this⟩
  -- the identity
  have hq' : cst (σ := σ) f - cst V0 ^ 2 = 4 * X ^ d * qc := by
    have := congrArg (cst (σ := σ)) hq
    simpa [qc, map_sub, map_pow, map_mul, map_ofNat] using this
  have hU' : cst (σ := σ) V0 * u = 1 + X ^ d * hc := by
    have := congrArg (cst (σ := σ)) hU
    simpa [u, hc, map_add, map_mul, map_pow] using this
  have hG : G Y = mt * hc * Y - u * Y ^ 2 - u * mt * qc := rfl
  have key : u * (cst f - (cst V0 + 2 * Y) ^ 2) =
      4 * (G Y - Y) + m * (4 * (u * qc - hc * Y)) := by
    rw [hG, hmdef]
    linear_combination u * hq' - 4 * Y * hU'
  have hdvd2 : m ∣ u * (cst f - (cst V0 + 2 * Y) ^ 2) := by
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right hdvd1 _) (dvd_mul_right _ _)
  have hm0 : m.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = X ^ m.natDegree := by
    rw [hmdeg, hmdef, Polynomial.map_add, Polynomial.map_pow, map_X]
    have : mt.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = 0 := by
      ext n
      rw [coeff_map, coeff_zero, ← ordIdeal_one_iff]
      exact Ideal.mem_map_C_iff.mp hmt1 n
    rw [this, add_zero]
  refine dvd_of_dvd_mul_of_map hmmonic hm0 ?_ hdvd2
  simpa [u, cst, coeff_map] using hU0

end FurioLombardo.Discharge.M4Log.Model
