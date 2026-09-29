import Mathlib
import FurioLombardo.Vendor.Toolbox.PowerSeries.SqrtMod
import FurioLombardo.Vendor.Toolbox.PowerSeries.BoundedRes
import FurioLombardo.Discharge.M4Log.Transport

/-!
# Generic leaves of the integral-model chain

Self-contained facts on polynomials over `K` and over `MvPowerSeries σ K` used by `Model.lean`:
inverses modulo `X^d`, remainders modulo monic divisors and `X^d`, the chart polynomials `uP t`, and the
transport `tw` of `Transport.lean` on constants and powers of `X`. They import only Mathlib, the
Toolbox and `Transport.lean`.
-/

open Polynomial

namespace FurioLombardo.Discharge.M4Log.Model

open FurioLombardo.Vendor.Toolbox.SqrtMod FurioLombardo.Vendor.Toolbox.Bounded

set_option autoImplicit false

variable {K : Type*} [Field K]


/-- An inverse modulo `X^d` of a polynomial with constant coefficient `1`, integral. -/
theorem exists_inv_mod_X_pow {O : Subring K} {V : K[X]} (hV0 : V.coeff 0 = 1)
    (hVO : ∀ n, V.coeff n ∈ O) (d : ℕ) :
    ∃ U h : K[X], (∀ n, U.coeff n ∈ O) ∧ (∀ n, h.coeff n ∈ O) ∧ V * U = 1 + X ^ d * h ∧
      U.coeff 0 = 1 := by
  induction d with
  | zero =>
    refine ⟨1, V - 1, fun n => ?_, fun n => ?_, by ring, by simp⟩
    · rw [coeff_one]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    · rw [coeff_sub, coeff_one]
      refine O.sub_mem (hVO n) ?_
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
  | succ d ih =>
    obtain ⟨U, h, hU, hh, hVU, hU0⟩ := ih
    set g := h - C (h.coeff 0) * V with hg
    have hg0 : g.coeff 0 = 0 := by simp [hg, coeff_C_mul, hV0]
    refine ⟨U - C (h.coeff 0) * X ^ d, g.divX, fun n => ?_, fun n => ?_, ?_, ?_⟩
    · rw [coeff_sub, coeff_C_mul, coeff_X_pow]
      refine O.sub_mem (hU n) (O.mul_mem (hh 0) ?_)
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    · rw [coeff_divX, hg, coeff_sub, coeff_C_mul]
      exact O.sub_mem (hh _) (O.mul_mem (hh 0) (hVO _))
    · have e := divX_mul_X_add g
      rw [hg0, map_zero, add_zero] at e
      calc V * (U - C (h.coeff 0) * X ^ d) = V * U - X ^ d * (C (h.coeff 0) * V) := by ring
        _ = 1 + X ^ d * g := by rw [hVU, hg]; ring
        _ = 1 + X ^ (d + 1) * g.divX := by conv_lhs => rw [← e]
                                           ring
    · rw [coeff_sub, coeff_C_mul, coeff_X_pow, hU0]
      split_ifs with hd
      · have e0 := congrArg (fun q => q.coeff 0) hVU
        simp only [mul_coeff_zero, hV0, hU0, coeff_add, coeff_one_zero, ← hd, pow_zero, one_mul,
          mul_one] at e0
        linear_combination e0
      · rw [mul_zero, sub_zero]

/-- `X ↦ c X` commutes with the remainder modulo `X^d`. -/
theorem modByMonic_X_pow_comp {R : Type*} [CommRing R] (P : R[X]) (c : R) (d : ℕ) :
    (P %ₘ X ^ d).comp (C c * X) = P.comp (C c * X) %ₘ X ^ d := by
  nontriviality R
  have hm : (X ^ d : R[X]).Monic := monic_X_pow d
  have e := modByMonic_add_div P (X ^ d)
  have hc : ((X ^ d : R[X]).comp (C c * X)) = C (c ^ d) * X ^ d := by
    rw [X_pow_comp, mul_pow, ← map_pow]
  have hdc : ((P %ₘ X ^ d).comp (C c * X)).degree ≤ (P %ₘ X ^ d).degree := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    rw [comp_C_mul_X_coeff, coeff_eq_zero_of_degree_lt hm, zero_mul]
  have hdeg : ((P %ₘ X ^ d).comp (C c * X)).degree < (X ^ d : R[X]).degree :=
    lt_of_le_of_lt hdc (degree_modByMonic_lt _ hm)
  refine ((div_modByMonic_unique (C (c ^ d) * (P /ₘ X ^ d).comp (C c * X))
    ((P %ₘ X ^ d).comp (C c * X)) hm ⟨?_, hdeg⟩).2).symm
  conv_rhs => rw [← e]
  rw [add_comp, mul_comp, hc]
  ring

theorem coeff_zero_comp_C_mul_X {R : Type*} [CommRing R] (P : R[X]) (c : R) :
    (P.comp (C c * X)).coeff 0 = P.coeff 0 := by
  rw [comp_C_mul_X_coeff, pow_zero, mul_one]

/-- A nonzero constant times `P` divides a nonzero constant times `Q`: `P ∣ Q`. -/
theorem dvd_of_C_mul_dvd_C_mul {σ : Type*} {c e : K} (hc : c ≠ 0)
    {P Q : (MvPowerSeries σ K)[X]}
    (h : C (MvPowerSeries.C c) * P ∣ C (MvPowerSeries.C e) * Q) (he : e ≠ 0) : P ∣ Q := by
  have hu : IsUnit (C (MvPowerSeries.C e) : (MvPowerSeries σ K)[X]) :=
    ((isUnit_iff_ne_zero.mpr he).map (MvPowerSeries.C (σ := σ))).map C
  exact (dvd_mul_left P _).trans (hu.dvd_mul_left.mp h)

/-- A linear polynomial has degree `< 2`. -/
theorem degree_lin_lt_two {R : Type*} [CommRing R] (a b : R) : (C a * X + C b).degree < 2 :=
  lt_of_le_of_lt (degree_add_le _ _)
    (max_lt (lt_of_le_of_lt (degree_C_mul_X_le _) (by exact_mod_cast (by norm_num : 1 < 2)))
      (lt_of_le_of_lt degree_C_le (by exact_mod_cast (by norm_num : 0 < 2))))

theorem uP_sub_eq {σ : Type*} (t : Fin 2 → σ) :
    uP (K := K) t - X ^ 2 = C (MvPowerSeries.X (t 0)) * X + C (MvPowerSeries.X (t 1)) := by
  simp only [uP]; ring

theorem C_X_mem_liftsRing {σ : Type*} (O : Subring K) (i : σ) :
    (C (MvPowerSeries.X i) : (MvPowerSeries σ K)[X]) ∈ liftsRing (incl (σ := σ) O) := by
  rw [← lifts_iff_liftsRing]
  simpa using C_mem_lifts (incl (σ := σ) O) (MvPowerSeries.X i)

theorem X_mem_liftsRing' {σ : Type*} (O : Subring K) :
    (X : (MvPowerSeries σ K)[X]) ∈ liftsRing (incl (σ := σ) O) := by
  rw [← lifts_iff_liftsRing]; exact X_mem_lifts _

/-- The chart polynomial minus `X²` is integral without constant term, of degree `< 2`. -/
theorem uP_sub_mem {σ : Type*} (O : Subring K) (t : Fin 2 → σ) :
    uP (K := K) t - X ^ 2 ∈ liftsRing (incl (σ := σ) O) ∧
      uP (K := K) t - X ^ 2 ∈ (ordIdeal (σ := σ) (R := K) 1).map
        (C : _ →+* (MvPowerSeries σ K)[X]) ∧ (uP (K := K) t - X ^ 2).degree < 2 := by
  rw [uP_sub_eq]
  refine ⟨add_mem (mul_mem (C_X_mem_liftsRing O _) (X_mem_liftsRing' O)) (C_X_mem_liftsRing O _), ?_,
    degree_lin_lt_two _ _⟩
  rw [Ideal.mem_map_C_iff]
  intro n
  rw [ordIdeal_one_iff]
  rcases n with _ | _ | n <;> simp [coeff_X, coeff_C]

theorem uP_mem {σ : Type*} (O : Subring K) (t : Fin 2 → σ) :
    uP (K := K) t ∈ liftsRing (incl (σ := σ) O) := by
  have e : uP (K := K) t = (uP (K := K) t - X ^ 2) + X ^ 2 := by ring
  rw [e]
  exact add_mem (uP_sub_mem O t).1 (pow_mem (X_mem_liftsRing' O) 2)

theorem uP_monic {σ : Type*} (t : Fin 2 → σ) : (uP (K := K) t).Monic := by
  have e : uP (K := K) t = X ^ 2 + (C (MvPowerSeries.X (t 0)) * X + C (MvPowerSeries.X (t 1))) := by
    simp only [uP]; ring
  rw [e]
  exact monic_X_pow_add (degree_lin_lt_two _ _)

theorem uP_natDegree {σ : Type*} (t : Fin 2 → σ) : (uP (K := K) t).natDegree = 2 := by
  have e : uP (K := K) t = X ^ 2 + (C (MvPowerSeries.X (t 0)) * X + C (MvPowerSeries.X (t 1))) := by
    simp only [uP]; ring
  rw [e, natDegree_add_eq_left_of_degree_lt]
  · simp
  · rw [degree_X_pow]; exact degree_lin_lt_two _ _

theorem uP_map {σ : Type*} (t : Fin 2 → σ) :
    (uP (K := K) t).map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = X ^ 2 := by
  simp [uP]

/-- The product of the two chart polynomials minus `X⁴`. -/
theorem uLR_sub_mem (O : Subring K) :
    uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) * uP (K := K) Sum.inr - X ^ 4 ∈
        liftsRing (incl (σ := Fin 2 ⊕ Fin 2) O) ∧
      uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) * uP (K := K) Sum.inr - X ^ 4 ∈
        (ordIdeal (σ := Fin 2 ⊕ Fin 2) (R := K) 1).map
          (C : _ →+* (MvPowerSeries (Fin 2 ⊕ Fin 2) K)[X]) ∧
      (uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) * uP (K := K) Sum.inr - X ^ 4).degree < 4 := by
  have h1 := uP_sub_mem (K := K) O (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)
  have h2 := uP_sub_mem (K := K) O (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2)
  have e : uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) * uP (K := K) Sum.inr - X ^ 4 =
      (uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) - X ^ 2) * uP (K := K) Sum.inr +
        X ^ 2 * (uP (K := K) (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) - X ^ 2) := by ring
  refine ⟨?_, ?_, ?_⟩
  · exact sub_mem (mul_mem (uP_mem O _) (uP_mem O _)) (pow_mem (X_mem_liftsRing' O) 4)
  · rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ h1.2.1) (Ideal.mul_mem_left _ _ h2.2.1)
  · have e2 : uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) * uP (K := K) Sum.inr - X ^ 4 =
        (C (MvPowerSeries.X (Sum.inl 0)) + C (MvPowerSeries.X (Sum.inr 0))) * X ^ 3 +
          (C (MvPowerSeries.X (Sum.inl 1)) + C (MvPowerSeries.X (Sum.inr 1)) +
            C (MvPowerSeries.X (Sum.inl 0)) * C (MvPowerSeries.X (Sum.inr 0))) * X ^ 2 +
          (C (MvPowerSeries.X (Sum.inl 0)) * C (MvPowerSeries.X (Sum.inr 1)) +
            C (MvPowerSeries.X (Sum.inl 1)) * C (MvPowerSeries.X (Sum.inr 0))) * X +
          C (MvPowerSeries.X (Sum.inl 1)) * C (MvPowerSeries.X (Sum.inr 1)) := by
      simp only [uP]; ring
    rw [e2]
    refine lt_of_le_of_lt (b := ((3 : ℕ) : WithBot ℕ)) ?_ (WithBot.coe_lt_coe.mpr (by norm_num))
    compute_degree!

theorem cst_mem_liftsRing' {σ : Type*} {O : Subring K} {P : K[X]} (hP : ∀ n, P.coeff n ∈ O) :
    cst (σ := σ) P ∈ liftsRing (incl (σ := σ) O) :=
  cst_mem_liftsRing O hP

theorem map_cst_self {σ : Type*} (P : K[X]) :
    (cst (σ := σ) P).map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = P := by
  simp [cst, Polynomial.map_map, MvPowerSeries.constantCoeff_comp_C]

theorem map_eq_zero_of_mem_ord {σ : Type*} {Y : (MvPowerSeries σ K)[X]}
    (hY : Y ∈ (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X])) :
    Y.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = 0 := by
  ext n
  rw [coeff_map, coeff_zero]
  exact ordIdeal_one_iff.mp (Ideal.mem_map_C_iff.mp hY n)

theorem C_mul_modByMonic {R : Type*} [CommRing R] (c : R) (P q : R[X]) :
    (C c * P) %ₘ q = C c * (P %ₘ q) := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, smul_modByMonic]

theorem coeff_modByMonic_X_pow {R : Type*} [CommRing R] (P : R[X]) {d n : ℕ} (hn : n < d) :
    (P %ₘ X ^ d).coeff n = P.coeff n := by
  nontriviality R
  conv_rhs => rw [← modByMonic_add_div P (X ^ d)]
  rw [coeff_add, coeff_X_pow_mul', if_neg (by omega), add_zero]

theorem two_mem_liftsRing {σ : Type*} (O : Subring K) :
    (2 : (MvPowerSeries σ K)[X]) ∈ liftsRing (incl (σ := σ) O) := by
  rw [show (2 : (MvPowerSeries σ K)[X]) = 1 + 1 by norm_num]
  exact add_mem (one_mem _) (one_mem _)

/-- A square root modulo `m` stays one after reduction modulo `m`. -/
theorem dvd_sub_sq_modByMonic {R : Type*} [CommRing R] {m F A : R[X]} (hm : m.Monic)
    (h : m ∣ F - A ^ 2) : m ∣ F - (A %ₘ m) ^ 2 := by
  obtain ⟨k, hk⟩ := h
  have e := modByMonic_add_div A m
  refine ⟨k + (A /ₘ m) * (A + A %ₘ m), ?_⟩
  linear_combination hk - (A + A %ₘ m) * e

/-- Cancelling a nonzero factor and a nonzero constant. -/
theorem eq_of_C_mul_eq {σ : Type*} {c e : K} (hc : c ≠ 0) {m P Q : (MvPowerSeries σ K)[X]}
    (hm : m ≠ 0) (h : C (MvPowerSeries.C c) * m * P = C (MvPowerSeries.C e) * m * Q) :
    P = C (MvPowerSeries.C (e / c)) * Q := by
  have h' : m * (C (MvPowerSeries.C c) * P) = m * (C (MvPowerSeries.C e) * Q) := by
    linear_combination h
  have h2 := mul_left_cancel₀ hm h'
  have hcc : (C (MvPowerSeries.C c⁻¹) : (MvPowerSeries σ K)[X]) * C (MvPowerSeries.C c) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
  calc P = C (MvPowerSeries.C c⁻¹) * (C (MvPowerSeries.C c) * P) := by rw [← mul_assoc, hcc, one_mul]
    _ = C (MvPowerSeries.C (e / c)) * Q := by
      rw [h2, ← mul_assoc, ← map_mul, ← map_mul, div_eq_mul_inv, mul_comm e]

theorem tw_C_mul {τ : Type*} (w : τ → K) (p : K) (s : MvPowerSeries τ K) (P : (MvPowerSeries τ K)[X]) :
    tw w p (C s * P) = C (MvPowerSeries.rescale w s) * tw w p P := by
  rw [map_mul, tw_C]

theorem tw_X_pow {τ : Type*} (w : τ → K) (p : K) (n : ℕ) :
    tw w p (X ^ n : (MvPowerSeries τ K)[X]) = C (MvPowerSeries.C (p ^ n)) * X ^ n := by
  rw [map_pow, tw_X, mul_pow, ← map_pow, ← map_pow]

theorem rescale_X_eq {τ : Type*} (w : τ → K) (i : τ) :
    MvPowerSeries.rescale w (MvPowerSeries.X i : MvPowerSeries τ K) =
      MvPowerSeries.C (w i) * MvPowerSeries.X i := by
  exact rescale_X_tw w i

/-- The inverse of `c q` for a series `q` with nonzero constant term. -/
theorem inv_C_mul {τ : Type*} {c : K} (hc : c ≠ 0) {q : MvPowerSeries τ K}
    (hq : MvPowerSeries.constantCoeff q ≠ 0) :
    (MvPowerSeries.C c * q)⁻¹ = MvPowerSeries.C c⁻¹ * q⁻¹ := by
  rw [MvPowerSeries.mul_inv_rev, MvPowerSeries.C_inv, mul_comm]

theorem degree_comp_C_mul_X_le {R : Type*} [CommRing R] (P : R[X]) (c : R) :
    (P.comp (C c * X)).degree ≤ P.degree := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  rw [comp_C_mul_X_coeff, coeff_eq_zero_of_degree_lt hm, zero_mul]

/-- The coefficients of `P` after rescaling, from `tw P = c Q`. -/
theorem rescale_coeff_of_tw {τ : Type*} {w : τ → K} {p c : K} (hp : p ≠ 0)
    {P Q : (MvPowerSeries τ K)[X]} (h : tw w p P = C (MvPowerSeries.C c) * Q) (n : ℕ) :
    MvPowerSeries.rescale w (P.coeff n) = MvPowerSeries.C (c / p ^ n) * Q.coeff n := by
  have e := congrArg (fun R => R.coeff n) h
  simp only [coeff_tw, Polynomial.coeff_C_mul] at e
  have hu : MvPowerSeries.C (p ^ n)⁻¹ * MvPowerSeries.C (p ^ n) = (1 : MvPowerSeries τ K) := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero n hp), map_one]
  calc MvPowerSeries.rescale w (P.coeff n)
      = MvPowerSeries.C (p ^ n)⁻¹ * (MvPowerSeries.C (p ^ n) * MvPowerSeries.rescale w (P.coeff n)) := by
        rw [← mul_assoc, hu, one_mul]
    _ = MvPowerSeries.C (p ^ n)⁻¹ * (MvPowerSeries.C c * Q.coeff n) := by rw [e]
    _ = MvPowerSeries.C (c / p ^ n) * Q.coeff n := by
        rw [← mul_assoc, ← map_mul, div_eq_mul_inv, mul_comm c]

/-- A constant factor that is a unit can be dropped from the right of a divisibility. -/
theorem dvd_of_dvd_C_mul {σ : Type*} {e : K} (he : e ≠ 0) {m N : (MvPowerSeries σ K)[X]}
    (h : m ∣ C (MvPowerSeries.C e) * N) : m ∣ N := by
  have hu : IsUnit (C (MvPowerSeries.C e) : (MvPowerSeries σ K)[X]) :=
    ((isUnit_iff_ne_zero.mpr he).map (MvPowerSeries.C (σ := σ))).map C
  exact hu.dvd_mul_left.mp h

/-- The exact quotient by a monic divisor. -/
theorem eq_mul_divByMonic {R : Type*} [CommRing R] {m N : R[X]} (hm : m.Monic) (h : m ∣ N) :
    N = m * (N /ₘ m) := by
  have e := modByMonic_add_div N m
  rw [(modByMonic_eq_zero_iff_dvd hm).2 h, zero_add] at e
  exact e.symm

end FurioLombardo.Discharge.M4Log.Model
