import Mathlib
import FurioLombardo.Vendor.Toolbox.PowerSeries.SqrtMod

/-!
# Power series convergent near the origin (item R7)

Let `O` be a subring of a field `K` and `π ∈ O` such that every element of `K` has a multiple
`π ^ k x` in `O`. A series `G ∈ K⟦σ⟧` is convergent near the origin when some rescaling
`G(π ^ κ t)` has denominators bounded by `π ^ N` (`Data O π κ N G`). These series form a subring
`conv O π σ` which contains the constants and the variables, is stable under inverses of series with
nonzero constant term (`inv_mem_conv`), and polynomials over it are stable under division by monic
polynomials (`modByMonic_mem`, `divByMonic_mem`). The square root step of `FurioLombardo.Vendor.Toolbox.SqrtMod` has a
form without any explicit scaling (`exists_sqrtMod_conv`): a monic `X ^ d + mt` with `mt` convergent
without constant term has a convergent square root of `f` modulo it, starting from any square root
`V0` of `f` modulo `X ^ d`.

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

open MvPowerSeries Polynomial

namespace FurioLombardo.Vendor.Toolbox.Conv

variable {K : Type*} [Field K] (O : Subring K) (π : O) {σ : Type*}

/-- `G(π ^ κ t)` has denominators bounded by `π ^ N`. -/
def Data (κ N : ℕ) (G : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, (π : K) ^ N * ((π : K) ^ (κ * d.degree) * MvPowerSeries.coeff d G) ∈ O

variable {O π}

theorem Data.mono {κ N κ' N' : ℕ} {G : MvPowerSeries σ K} (h : Data O π κ N G) (hκ : κ ≤ κ')
    (hN : N ≤ N') : Data O π κ' N' G := by
  intro d
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hN
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hκ
  have e : (π : K) ^ (N + a) * ((π : K) ^ ((κ + b) * d.degree) * MvPowerSeries.coeff d G) =
      ((π : K) ^ a * (π : K) ^ (b * d.degree)) *
        ((π : K) ^ N * ((π : K) ^ (κ * d.degree) * MvPowerSeries.coeff d G)) := by
    rw [add_mul, pow_add, pow_add]; ring
  rw [e]
  exact O.mul_mem (O.mul_mem (O.pow_mem π.2 _) (O.pow_mem π.2 _)) (h d)

variable (O π σ)

/-- The series convergent near the origin. -/
def conv : Subring (MvPowerSeries σ K) where
  carrier := {G | ∃ κ N, Data O π κ N G}
  zero_mem' := ⟨0, 0, fun d => by rw [map_zero, mul_zero, mul_zero]; exact O.zero_mem⟩
  one_mem' := ⟨0, 0, fun d => by
    classical
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · rw [pow_zero, zero_mul, pow_zero, one_mul, one_mul]; exact O.one_mem
    · rw [mul_zero, mul_zero]; exact O.zero_mem⟩
  add_mem' := by
    rintro a b ⟨κ1, N1, h1⟩ ⟨κ2, N2, h2⟩
    refine ⟨max κ1 κ2, max N1 N2, fun d => ?_⟩
    have e : (π : K) ^ max N1 N2 * ((π : K) ^ (max κ1 κ2 * d.degree) *
        (MvPowerSeries.coeff d a + MvPowerSeries.coeff d b)) =
        (π : K) ^ max N1 N2 * ((π : K) ^ (max κ1 κ2 * d.degree) * MvPowerSeries.coeff d a) +
        (π : K) ^ max N1 N2 * ((π : K) ^ (max κ1 κ2 * d.degree) * MvPowerSeries.coeff d b) := by
      ring
    rw [map_add, e]
    exact O.add_mem ((h1.mono (le_max_left _ _) (le_max_left _ _)) d)
      ((h2.mono (le_max_right _ _) (le_max_right _ _)) d)
  neg_mem' := by
    rintro a ⟨κ, N, h⟩
    exact ⟨κ, N, fun d => by
      rw [map_neg]
      convert O.neg_mem (h d) using 1
      ring⟩
  mul_mem' := by
    classical
    rintro a b ⟨κ1, N1, h1⟩ ⟨κ2, N2, h2⟩
    refine ⟨max κ1 κ2, N1 + N2, fun d => ?_⟩
    have h1' := h1.mono (le_max_left κ1 κ2) le_rfl
    have h2' := h2.mono (le_max_right κ1 κ2) le_rfl
    rw [MvPowerSeries.coeff_mul, Finset.mul_sum, Finset.mul_sum]
    refine O.sum_mem fun p hp => ?_
    have hdeg : d.degree = p.1.degree + p.2.degree := by
      rw [← (Finset.HasAntidiagonal.mem_antidiagonal.mp hp), map_add]
    have e : (π : K) ^ (N1 + N2) * ((π : K) ^ (max κ1 κ2 * d.degree) *
        (MvPowerSeries.coeff p.1 a * MvPowerSeries.coeff p.2 b)) =
        ((π : K) ^ N1 * ((π : K) ^ (max κ1 κ2 * p.1.degree) * MvPowerSeries.coeff p.1 a)) *
        ((π : K) ^ N2 * ((π : K) ^ (max κ1 κ2 * p.2.degree) * MvPowerSeries.coeff p.2 b)) := by
      rw [hdeg, mul_add, pow_add, pow_add]; ring
    rw [e]
    exact O.mul_mem (h1' p.1) (h2' p.2)

variable {O π σ}

theorem mem_conv {G : MvPowerSeries σ K} : G ∈ conv O π σ ↔ ∃ κ N, Data O π κ N G := Iff.rfl

theorem X_mem_conv (i : σ) : (X i : MvPowerSeries σ K) ∈ conv O π σ :=
  ⟨0, 0, fun d => by
    classical
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · rw [pow_zero, zero_mul, pow_zero, one_mul, one_mul]; exact O.one_mem
    · rw [mul_zero, mul_zero]; exact O.zero_mem⟩

theorem C_mem_conv (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O) (x : K) :
    (C x : MvPowerSeries σ K) ∈ conv O π σ := by
  classical
  obtain ⟨k, hk⟩ := hbd x
  refine ⟨0, k, fun d => ?_⟩
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · rw [zero_mul, pow_zero, one_mul]; exact hk
  · rw [mul_zero, mul_zero]; exact O.zero_mem

/-- The constant powers of the scaling: `π ^ (κ * deg d)` is the rescaling factor. -/
theorem coeff_rescale_const (κ : ℕ) (G : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (rescale (fun _ => (π : K) ^ κ) G) =
      (π : K) ^ (κ * d.degree) * MvPowerSeries.coeff d G := by
  rw [MvPowerSeries.coeff_rescale, Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, ← pow_mul]

theorem data_iff_rescale {κ N : ℕ} {G : MvPowerSeries σ K} :
    Data O π κ N G ↔ ∀ d, (π : K) ^ N *
      MvPowerSeries.coeff d (rescale (fun _ => (π : K) ^ κ) G) ∈ O := by
  simp only [coeff_rescale_const]
  rfl

/-- A convergent series without constant term becomes integral after a further rescaling. -/
theorem data_int_of_constantCoeff {κ N : ℕ} {G : MvPowerSeries σ K} (h : Data O π κ N G)
    (h0 : MvPowerSeries.constantCoeff G = 0) : Data O π (κ + N) 0 G := by
  intro d
  rw [pow_zero, one_mul]
  rcases Nat.eq_zero_or_pos d.degree with hd | hd
  · rw [(Finsupp.degree_eq_zero_iff d).mp hd, coeff_zero_eq_constantCoeff_apply, h0, mul_zero]
    exact O.zero_mem
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_lt hd
    have hx : (π : K) ^ ((κ + N) * d.degree) * MvPowerSeries.coeff d G =
        (π : K) ^ (N * e) * ((π : K) ^ N * ((π : K) ^ (κ * d.degree) * MvPowerSeries.coeff d G)) := by
      rw [he]; ring
    rw [hx]
    exact O.mul_mem (O.pow_mem π.2 _) (h d)

/-- Rescaling commutes with inverses of series with nonzero constant term. -/
theorem rescale_inv (a : σ → K) {G : MvPowerSeries σ K} (h0 : MvPowerSeries.constantCoeff G ≠ 0) :
    rescale a G⁻¹ = (rescale a G)⁻¹ := by
  have hc : MvPowerSeries.constantCoeff (rescale a G) = MvPowerSeries.constantCoeff G := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_rescale,
      Finsupp.prod_zero_index, one_mul]
  rw [MvPowerSeries.eq_inv_iff_mul_eq_one (hc ▸ h0), ← map_mul, MvPowerSeries.inv_mul_cancel _ h0,
    map_one]

/-- `(1 + H)⁻¹` has coefficients in `O` when `H` does and has no constant term. -/
theorem coeff_inv_one_add_mem {H : MvPowerSeries σ K} (hH : ∀ d, MvPowerSeries.coeff d H ∈ O)
    (h0 : MvPowerSeries.constantCoeff H = 0) : ∀ d, MvPowerSeries.coeff d (1 + H)⁻¹ ∈ O := by
  -- `1 + H` is already a unit over `O`: its inverse there maps to the inverse over `K`.
  let H' : MvPowerSeries σ O := fun d => ⟨MvPowerSeries.coeff d H, hH d⟩
  have hmap : MvPowerSeries.map O.subtype H' = H := by
    ext d; rfl
  have hc : MvPowerSeries.constantCoeff (1 + H') = ((1 : Oˣ) : O) := by
    apply Subtype.ext
    change MvPowerSeries.coeff 0 (MvPowerSeries.map O.subtype (1 + H')) = 1
    rw [map_add, map_one, hmap, map_add, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_one, add_zero]
  set u := MvPowerSeries.invOfUnit (1 + H') 1 with hu
  have hmul := MvPowerSeries.mul_invOfUnit (1 + H') 1 hc
  have h1H : MvPowerSeries.constantCoeff (1 + H) ≠ 0 := by
    rw [map_add, map_one, h0, add_zero]; exact one_ne_zero
  have hinv : MvPowerSeries.map O.subtype u = (1 + H)⁻¹ := by
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one h1H, mul_comm, ← hmap, ← map_one (MvPowerSeries.map O.subtype),
      ← map_add, ← map_mul, hmul, map_one]
  intro d
  rw [← hinv, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d u).2

/-- Inverses of convergent series with nonzero constant term are convergent. -/
theorem inv_mem_conv (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O) {G : MvPowerSeries σ K}
    (hG : G ∈ conv O π σ) (h0 : MvPowerSeries.constantCoeff G ≠ 0) : G⁻¹ ∈ conv O π σ := by
  set g0 := MvPowerSeries.constantCoeff G with hg0
  set H := MvPowerSeries.C g0⁻¹ * G - 1 with hHdef
  have hHc : H ∈ conv O π σ :=
    Subring.sub_mem _ (Subring.mul_mem _ (C_mem_conv hbd _) hG) (Subring.one_mem _)
  have hH0 : MvPowerSeries.constantCoeff H = 0 := by
    rw [hHdef, map_sub, map_mul, MvPowerSeries.constantCoeff_C, map_one, ← hg0, inv_mul_cancel₀ h0, sub_self]
  obtain ⟨κ, N, hκN⟩ := hHc
  have hint := data_int_of_constantCoeff hκN hH0
  rw [data_iff_rescale] at hint
  have hint' : ∀ d, MvPowerSeries.coeff d (rescale (fun _ => (π : K) ^ (κ + N)) H) ∈ O := by
    intro d; simpa using hint d
  have h1H : MvPowerSeries.constantCoeff (1 + H) ≠ 0 := by rw [map_add, map_one, hH0, add_zero]; exact one_ne_zero
  have hresc0 : MvPowerSeries.constantCoeff (rescale (fun _ => (π : K) ^ (κ + N)) H) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_rescale, Finsupp.prod_zero_index, one_mul,
      coeff_zero_eq_constantCoeff_apply, hH0]
  have hinv : (1 + H)⁻¹ ∈ conv O π σ := by
    refine ⟨κ + N, 0, ?_⟩
    rw [data_iff_rescale]
    intro d
    rw [pow_zero, one_mul, rescale_inv _ h1H, map_add, map_one]
    exact coeff_inv_one_add_mem hint' hresc0 d
  have hG' : G = MvPowerSeries.C g0 * (1 + H) := by
    rw [hHdef, add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
  have hGinv : G⁻¹ = MvPowerSeries.C g0⁻¹ * (1 + H)⁻¹ := by
    symm
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one h0, hG']
    calc MvPowerSeries.C g0⁻¹ * (1 + H)⁻¹ * (MvPowerSeries.C g0 * (1 + H))
        = (MvPowerSeries.C g0⁻¹ * MvPowerSeries.C g0) * ((1 + H)⁻¹ * (1 + H)) := by ring
      _ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h0, map_one, one_mul, MvPowerSeries.inv_mul_cancel _ h1H]
  rw [hGinv]
  exact Subring.mul_mem _ (C_mem_conv hbd _) hinv

section Poly

/-- Polynomials with convergent coefficients. -/
noncomputable abbrev convPoly (O : Subring K) (π : O) (σ : Type*) : Subring (MvPowerSeries σ K)[X] :=
  liftsRing (conv O π σ).subtype

theorem mem_convPoly {p : (MvPowerSeries σ K)[X]} :
    p ∈ convPoly O π σ ↔ ∀ n, p.coeff n ∈ conv O π σ := by
  constructor
  · intro h n
    obtain ⟨x, hx⟩ := FurioLombardo.Vendor.Toolbox.SqrtMod.coeff_mem_range_of_mem_liftsRing _ h n
    rw [← hx]; exact x.2
  · intro h
    exact FurioLombardo.Vendor.Toolbox.SqrtMod.mem_liftsRing_of_coeff _ fun n => ⟨⟨_, h n⟩, rfl⟩

theorem modByMonic_mem {m p : (MvPowerSeries σ K)[X]} (hm : m.Monic) (hml : m ∈ convPoly O π σ)
    (hpl : p ∈ convPoly O π σ) : p %ₘ m ∈ convPoly O π σ :=
  FurioLombardo.Vendor.Toolbox.SqrtMod.modByMonic_mem_liftsRing _ hm hml hpl

theorem divByMonic_mem {m p : (MvPowerSeries σ K)[X]} (hm : m.Monic) (hml : m ∈ convPoly O π σ)
    (hpl : p ∈ convPoly O π σ) : p /ₘ m ∈ convPoly O π σ := by
  obtain ⟨m', hm', hm'deg, hm'monic⟩ := lifts_and_degree_eq_and_monic hml hm
  obtain ⟨p', hp'⟩ := hpl
  refine ⟨p' /ₘ m', ?_⟩
  change Polynomial.map _ _ = _
  rw [map_divByMonic _ hm'monic, ← hm', ← hp']
  rfl

theorem cst_mem_convPoly (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O) (p : K[X]) :
    FurioLombardo.Vendor.Toolbox.SqrtMod.cst (σ := σ) p ∈ convPoly O π σ := by
  rw [mem_convPoly]
  intro n
  simp only [FurioLombardo.Vendor.Toolbox.SqrtMod.cst, coe_mapRingHom, Polynomial.coeff_map]
  exact C_mem_conv hbd _

end Poly

section SqrtConv

open FurioLombardo.Vendor.Toolbox.SqrtMod

theorem pow_mul_mem_of_le {x : K} {k k' : ℕ} (h : (π : K) ^ k * x ∈ O) (hk : k ≤ k') :
    (π : K) ^ k' * x ∈ O := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm ((π : K) ^ k), mul_assoc]
  exact O.mul_mem (O.pow_mem π.2 _) h

/-- A polynomial over `K` has a multiple `π ^ k P` with coefficients in `O`, for all large `k`. -/
theorem exists_pow_poly_mem (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O) (P : K[X]) :
    ∃ k : ℕ, ∀ k' ≥ k, ∀ n, (π : K) ^ k' * P.coeff n ∈ O := by
  classical
  choose kf hkf using hbd
  refine ⟨P.support.sup fun n => kf (P.coeff n), fun k' hk' n => ?_⟩
  by_cases hn : n ∈ P.support
  · exact pow_mul_mem_of_le (hkf _) ((Finset.le_sup hn).trans hk')
  · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]; exact O.zero_mem

/-- One `(κ, N)` for all coefficients of a polynomial over `conv`. -/
theorem exists_data_poly {p : (MvPowerSeries σ K)[X]} (hp : p ∈ convPoly O π σ) :
    ∃ κ N : ℕ, ∀ n, Data O π κ N (p.coeff n) := by
  classical
  rw [mem_convPoly] at hp
  choose κf Nf hf using hp
  refine ⟨p.support.sup κf, p.support.sup Nf, fun n => ?_⟩
  by_cases hn : n ∈ p.support
  · exact (hf n).mono (Finset.le_sup hn) (Finset.le_sup hn)
  · rw [Polynomial.notMem_support_iff.mp hn]
    intro d; rw [map_zero, mul_zero, mul_zero]; exact O.zero_mem

theorem rescale_C' (a : σ → K) (x : K) : rescale a (MvPowerSeries.C x) = MvPowerSeries.C x := by
  classical
  ext e
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
  split_ifs with he
  · rw [he, Finsupp.prod_zero_index, one_mul]
  · rw [mul_zero]

theorem constantCoeff_rescale' (a : σ → K) (G : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (rescale a G) = MvPowerSeries.constantCoeff G := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_rescale, Finsupp.prod_zero_index, one_mul]

/-- Truncated inverse modulo `X ^ d`. -/
theorem inv_trunc (V : K[X]) (hV : V.coeff 0 ≠ 0) (d : ℕ) :
    ∃ U h : K[X], V * U = 1 + Polynomial.X ^ d * h ∧ U.coeff 0 ≠ 0 := by
  by_cases hd : d = 0
  · subst hd
    exact ⟨1, V - 1, by simp, by simp⟩
  · have h_not_dvd : ¬ Polynomial.X ∣ V := by
      rw [Polynomial.X_dvd_iff]
      exact hV
    obtain ⟨a, b, h_eq⟩ : IsCoprime V (Polynomial.X ^ d) :=
      Irreducible.coprime_pow_of_not_dvd d Polynomial.irreducible_X h_not_dvd
    refine ⟨a, -b, by linear_combination h_eq, ?_⟩
    have h_eval := congrArg (fun p : K[X] => p.coeff 0) h_eq
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow,
      Polynomial.coeff_one_zero] at h_eval
    simp only [Ne.symm hd, ↓reduceIte, mul_zero, add_zero] at h_eval
    intro hzero
    rw [hzero, zero_mul] at h_eval
    exact zero_ne_one h_eval

/-- **Square root modulo a convergent perturbation of `X ^ d`.** -/
theorem exists_sqrtMod_conv (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O) (hπ0 : (π : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) {d : ℕ} (hd : 0 < d) (f V0 : K[X]) (hV0 : Polynomial.X ^ d ∣ f - V0 ^ 2)
    (hV00 : V0.coeff 0 ≠ 0) (hV0d : V0.degree < d) (mt : (MvPowerSeries σ K)[X])
    (hmt : mt ∈ convPoly O π σ) (hmt0 : ∀ n, MvPowerSeries.constantCoeff (mt.coeff n) = 0)
    (hmtd : mt.degree < d) :
    ∃ V : (MvPowerSeries σ K)[X], V ∈ convPoly O π σ ∧ V.degree < d ∧
      V.map MvPowerSeries.constantCoeff = V0 ∧ (Polynomial.X ^ d + mt) ∣ cst f - V ^ 2 := by
  classical
  obtain ⟨q, hq⟩ := hV0
  obtain ⟨U0, h, hU, hU0⟩ := inv_trunc V0 hV00 d
  obtain ⟨k, hk⟩ := exists_pow_poly_mem hbd (Polynomial.C 2⁻¹ * U0 * q)
  obtain ⟨j0, hj0⟩ := exists_pow_poly_mem hbd (Polynomial.C 2⁻¹ * U0)
  obtain ⟨l, hl⟩ := exists_pow_poly_mem hbd h
  set j := max j0 l with hj
  have ha : ∀ n, (Polynomial.C ((π : K) ^ k * 2⁻¹) * U0 * q).coeff n ∈ O := by
    intro n
    rw [Polynomial.C_mul, mul_assoc, mul_assoc, Polynomial.coeff_C_mul, ← mul_assoc]
    exact hk k le_rfl n
  have hb : ∀ n, (Polynomial.C ((π : K) ^ j * 2⁻¹) * U0).coeff n ∈ O := by
    intro n
    rw [Polynomial.C_mul, mul_assoc, Polynomial.coeff_C_mul]
    exact hj0 j (le_max_left _ _) n
  have hc : ∀ n, (Polynomial.C ((π : K) ^ (j + k)) * h).coeff n ∈ O := by
    intro n
    rw [Polynomial.coeff_C_mul]
    exact hl (j + k) ((le_max_right _ _).trans (Nat.le_add_right _ _)) n
  obtain ⟨κ, N, hκN⟩ := exists_data_poly hmt
  set μ := κ + N + j + k with hμ
  set a : σ → K := fun _ => (π : K) ^ μ with ha_def
  set b : σ → K := fun _ => ((π : K) ^ μ)⁻¹ with hb_def
  set RP := Polynomial.mapRingHom (rescale a) with hRP
  set RPi := Polynomial.mapRingHom (rescale b) with hRPi
  have hπμ : (π : K) ^ μ ≠ 0 := pow_ne_zero _ hπ0
  have hπjk : (π : K) ^ (j + k) ≠ 0 := pow_ne_zero _ hπ0
  have hinvR : ∀ p, RPi (RP p) = p := by
    intro p
    rw [hRP, hRPi, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map, ← rescale_mul]
    have : a * b = 1 := funext fun _ => by simp [ha_def, hb_def, mul_inv_cancel₀ hπμ]
    rw [this, rescale_one, Polynomial.map_id]
  have hinvR2 : ∀ p, RP (RPi p) = p := by
    intro p
    rw [hRP, hRPi, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map, ← rescale_mul]
    have : b * a = 1 := funext fun _ => by simp [ha_def, hb_def, inv_mul_cancel₀ hπμ]
    rw [this, rescale_one, Polynomial.map_id]
  have hRPcst : ∀ (c : σ → K) (p : K[X]),
      Polynomial.mapRingHom (rescale c) (cst (σ := σ) p) = cst p := by
    intro c p
    simp only [cst, coe_mapRingHom, Polynomial.map_map]
    congr 1
    ext x : 1
    exact rescale_C' c x
  -- the rescaled perturbation
  set mt'' := SqrtMod.CC (σ := σ) ((π : K) ^ (j + k))⁻¹ * RP mt with hmt''
  have hCCmul : ∀ x y : K, SqrtMod.CC (σ := σ) x * SqrtMod.CC y = SqrtMod.CC (x * y) := fun x y => by
    rw [SqrtMod.CC, SqrtMod.CC, SqrtMod.CC, ← Polynomial.C_mul, ← map_mul]
  have hRPmt : RP mt = SqrtMod.CC ((π : K) ^ (j + k)) * mt'' := by
    rw [hmt'', ← mul_assoc, hCCmul, mul_inv_cancel₀ hπjk, SqrtMod.CC, map_one, Polynomial.C_1, one_mul]
  have hcoef : ∀ n e, MvPowerSeries.coeff e (mt''.coeff n) =
      ((π : K) ^ (j + k))⁻¹ * ((π : K) ^ (μ * e.degree) * MvPowerSeries.coeff e (mt.coeff n)) := by
    intro n e
    rw [hmt'', SqrtMod.CC, Polynomial.coeff_C_mul, hRP, coe_mapRingHom, Polynomial.coeff_map,
      MvPowerSeries.coeff_C_mul, ha_def, coeff_rescale_const]
  have hmt''L : mt'' ∈ liftsRing (incl (σ := σ) O) := by
    refine mem_liftsRing_of_coeff _ fun n => ?_
    rw [mem_range_incl]
    intro e
    rw [hcoef]
    rcases Nat.eq_zero_or_pos e.degree with he | he
    · rw [(Finsupp.degree_eq_zero_iff e).mp he, coeff_zero_eq_constantCoeff_apply, hmt0, mul_zero,
        mul_zero]
      exact O.zero_mem
    · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt he
      have e1 : μ * e.degree = (j + k) + ((N + j + k) * t + (N + κ * e.degree)) := by
        rw [hμ, ht]; ring
      rw [e1, pow_add (π : K) (j + k), mul_assoc, inv_mul_cancel_left₀ hπjk]
      have hx : (π : K) ^ ((N + j + k) * t + (N + κ * e.degree)) * MvPowerSeries.coeff e (mt.coeff n) =
          (π : K) ^ ((N + j + k) * t) *
            ((π : K) ^ N * ((π : K) ^ (κ * e.degree) * MvPowerSeries.coeff e (mt.coeff n))) := by
        rw [pow_add, pow_add]; ring
      rw [hx]
      exact O.mul_mem (O.pow_mem π.2 _) (hκN n e)
  have hmt''1 : mt'' ∈ (ordIdeal (σ := σ) (R := K) 1).map
      (Polynomial.C : _ →+* (MvPowerSeries σ K)[X]) := by
    rw [mem_map_C_iff']
    intro n
    rw [ordIdeal_one_iff, hmt'', SqrtMod.CC, Polynomial.coeff_C_mul, map_mul, MvPowerSeries.constantCoeff_C,
      hRP, coe_mapRingHom, Polynomial.coeff_map, constantCoeff_rescale', hmt0, mul_zero]
  have hRPdeg : ∀ p, (RP p).degree ≤ p.degree := fun p => by
    rw [hRP, coe_mapRingHom]; exact Polynomial.degree_map_le
  have hmt''d : mt''.degree < d :=
    lt_of_le_of_lt (degree_CC_mul_le _ _) (lt_of_le_of_lt (hRPdeg mt) hmtd)
  obtain ⟨Vt, hVtL, hVt1, hVtd, hdvd⟩ := exists_sqrtMod O h2 hd π.2 f V0 U0 q h hq hU hU0 j k ha hb hc
    mt'' hmt''L hmt''1 hmt''d
  set V' := cst (σ := σ) V0 + SqrtMod.CC ((π : K) ^ j) * Vt with hV'
  have hVt0 : Vt.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = 0 := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact ordIdeal_one_iff.mp ((mem_map_C_iff'.mp hVt1) n)
  refine ⟨RPi V', ?_, ?_, ?_, ?_⟩
  · obtain ⟨N0, hN0⟩ := exists_pow_poly_mem hbd V0
    rw [mem_convPoly]
    intro n
    refine ⟨μ, N0, ?_⟩
    rw [data_iff_rescale]
    intro e
    have hre : rescale (fun _ => (π : K) ^ μ) ((RPi V').coeff n) = V'.coeff n := by
      have := congrArg (fun p => Polynomial.coeff p n) (hinvR2 V')
      simpa only [hRP, coe_mapRingHom, Polynomial.coeff_map] using this
    rw [hre, hV', Polynomial.coeff_add, map_add, SqrtMod.CC, Polynomial.coeff_C_mul, cst, coe_mapRingHom,
      Polynomial.coeff_map, MvPowerSeries.coeff_C_mul, mul_add]
    refine O.add_mem ?_ ?_
    · rw [MvPowerSeries.coeff_C]
      split_ifs
      · exact hN0 N0 le_rfl n
      · rw [mul_zero]; exact O.zero_mem
    · obtain ⟨x, hx⟩ := coeff_mem_range_of_mem_liftsRing _ hVtL n
      have hxe : MvPowerSeries.coeff e (Vt.coeff n) ∈ O := (mem_range_incl.mp ⟨x, hx⟩) e
      rw [← mul_assoc, ← pow_add]
      exact O.mul_mem (O.pow_mem π.2 _) hxe
  · have hV'd : V'.degree < d := by
      rw [hV']
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (by rw [cst, coe_mapRingHom]; exact Polynomial.degree_map_le) hV0d
      · refine lt_of_le_of_lt (degree_CC_mul_le _ _) ?_
        exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hVtd)
    exact lt_of_le_of_lt (by rw [hRPi, coe_mapRingHom]; exact Polynomial.degree_map_le) hV'd
  · have hcc : (MvPowerSeries.constantCoeff (σ := σ) (R := K)).comp (rescale b) =
        MvPowerSeries.constantCoeff := by
      ext G : 1
      exact constantCoeff_rescale' b G
    rw [hRPi, coe_mapRingHom, Polynomial.map_map, hcc, hV', Polynomial.map_add, Polynomial.map_mul,
      hVt0, mul_zero, add_zero, cst, coe_mapRingHom, Polynomial.map_map]
    have hcC : (MvPowerSeries.constantCoeff (σ := σ) (R := K)).comp (MvPowerSeries.C (σ := σ) (R := K)) =
        RingHom.id K := by
      ext x : 1
      simp
    rw [hcC, Polynomial.map_id]
  · have hm : RPi (Polynomial.X ^ d + SqrtMod.CC ((π : K) ^ (j + k)) * mt'') = Polynomial.X ^ d + mt := by
      rw [← hRPmt]
      have : Polynomial.X ^ d + RP mt = RP (Polynomial.X ^ d + mt) := by
        rw [map_add, map_pow, hRP, coe_mapRingHom, Polynomial.map_X]
      rw [this, hinvR]
    have := map_dvd RPi hdvd
    rwa [hm, map_sub, map_pow, hRPi, hRPcst] at this

end SqrtConv

end FurioLombardo.Vendor.Toolbox.Conv
