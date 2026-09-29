import Mathlib
import FurioLombardo.Vendor.Toolbox.FormalGroup.ScaledLog
import FurioLombardo.Discharge.R7.KvBall

/-!
# The truncated scaled logarithm (lane lean-kv-arith)

For a formal group law `Φ` over `O` with `f : O → K` injective into a field of characteristic 0, the
coefficient of degree `d` of the logarithm lies in `p^(-v_p(d)) O` (Toolbox `coeff_log_map_padic`), so the
scaled logarithm `logC = log(cX)/c` has `p^(v_p(deg)) coeff_d(logC) ∈ (c^(deg - 1))`
(`coeff_logC_mem_span`). Over `OKv` with R7's scaling `c = pv⁴` (`p = 2 = pv³ u₂`): `coeff_d(logC) ∈
(pv^(4(deg-1) - 3 v₂(deg)))` (`coeff_logC_OKv`), and the value `logVal` at `y ∈ (pv^s)^ι` differs from
any finite part `Σ_{d ∈ S}` containing the degrees `≤ N` by an element of `(pv^B)` as soon as
`B ≤ 4(n-1) - 3 v₂(n) + s n` for every `n > N` (`logVal_sub_sum_mem`).
-/

namespace FurioLombardo.Discharge.KvArith

open FurioLombardo.Vendor.Toolbox.FormalGroup FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman FurioLombardo.Vendor.Toolbox.UnitBall IsLocalRing
open FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Cert

/-- `p^(v_p(deg d)) coeff_d(log(cX)/c) ∈ (c^(deg d - 1))`. -/
theorem coeff_logC_mem_span {O : Type*} [CommRing O] [IsLocalRing O] {K : Type*} [Field K]
    [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {c : O} (hp : p.Prime)
    (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c) {f : O →+* K}
    (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    (p : O) ^ padicValNat p d.degree * MvPowerSeries.coeff d (logC Φ f c i) ∈
      Ideal.span {c ^ (d.degree - 1)} := by
  set D := d.degree with hD
  set v := padicValNat p D with hv
  by_cases hD0 : D = 0
  · -- D = 0: then d = 0, constantCoeff_logC gives coeff 0 (logC ...) = 0
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hD0
    rw [hd0]
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_logC hp hpm hc hf Φ i]
    simp
  · -- D ≥ 1
    have hDpos : 1 ≤ D := by omega
    have hfp : f (p : O) ≠ 0 := by
      rw [map_natCast]
      exact_mod_cast hp.ne_zero
    have hmap := map_coeff_logC hp hpm hc f Φ i d
    have hpad := Φ.coeff_log_map_padic hp hpm f hfp i d
    rcases hpad with ⟨b, hb⟩
    -- hb: f(p)^v * coeff_d(log(Φ.map f)) = f b
    have h_eq : f ((p : O) ^ v * MvPowerSeries.coeff d (logC Φ f c i)) = f (c ^ (D - 1) * b) := by
      calc
        f ((p : O) ^ v * MvPowerSeries.coeff d (logC Φ f c i))
            = f ((p : O) ^ v) * f (MvPowerSeries.coeff d (logC Φ f c i)) := by rw [map_mul]
        _ = (f (p : O)) ^ v * f (MvPowerSeries.coeff d (logC Φ f c i)) := by rw [map_pow]
        _ = (f (p : O)) ^ v * (f c ^ (D - 1) * MvPowerSeries.coeff d ((Φ.map f).log i)) := by rw [hmap]
        _ = (f c ^ (D - 1)) * ((f (p : O)) ^ v * MvPowerSeries.coeff d ((Φ.map f).log i)) := by ring
        _ = (f c ^ (D - 1)) * f b := by rw [hb]
        _ = f (c ^ (D - 1)) * f b := by rw [map_pow]
        _ = f (c ^ (D - 1) * b) := by rw [map_mul]
    have h_eq' : (p : O) ^ v * MvPowerSeries.coeff d (logC Φ f c i) = c ^ (D - 1) * b :=
      hf h_eq
    rw [h_eq']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (dvd_refl _))

/-- R7's scaled logarithm over `OKv`: `coeff_d(logC) ∈ (pv^(4(deg - 1) - 3 v₂(deg)))`. -/
theorem coeff_logC_OKv {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : FormalGroupLaw OKv ι)
    (i : ι) (d : ι →₀ ℕ) :
    MvPowerSeries.coeff d (logC Φ (unitBall Kv).subtype (pvO ^ (3 + 1)) i) ∈
      Ideal.span {pvO ^ (4 * (d.degree - 1) - 3 * padicValNat 2 d.degree)} := by
  set x := MvPowerSeries.coeff d (logC Φ (unitBall Kv).subtype (pvO ^ (3 + 1)) i) with hx
  set D := d.degree with hD
  set v := padicValNat 2 D with hv
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpm : (2 : OKv) ∈ maximalIdeal OKv := two_mem_maximalIdeal
  have hc : ScalingHyp 2 (pvO ^ (3 + 1)) :=
    scalingHyp_uniformizer two_mem_maximalIdeal isUnit_u2 two_eq
  have hf : Function.Injective ((unitBall Kv).subtype : OKv →+* Kv) := subtype_injective
  have hmem := coeff_logC_mem_span hp hpm hc hf Φ i d
  -- hmem : (2 : OKv) ^ padicValNat 2 (d.degree) * coeff d (logC ...) ∈ Ideal.span {(pvO ^ (3 + 1)) ^ (d.degree - 1)}
  rw [← hD, ← hv, ← hx] at hmem
  -- hmem : (2 : OKv) ^ v * x ∈ Ideal.span {(pvO ^ (3 + 1)) ^ (D - 1)}
  have h_two_pow : (2 : OKv) ^ v = pvO ^ (3 * v) * (u2 ^ v) := by
    calc
      (2 : OKv) ^ v = (pvO ^ 3 * u2) ^ v := by rw [two_eq]
      _ = (pvO ^ 3) ^ v * u2 ^ v := by rw [mul_pow]
      _ = pvO ^ (3 * v) * u2 ^ v := by rw [pow_mul]
  have h_span : (pvO ^ (3 + 1)) ^ (D - 1) = pvO ^ (4 * (D - 1)) := by
    calc
      (pvO ^ (3 + 1)) ^ (D - 1) = pvO ^ ((3 + 1) * (D - 1)) := by rw [pow_mul]
      _ = pvO ^ (4 * (D - 1)) := by ring
  -- hmem : (2 : OKv) ^ v * x ∈ Ideal.span {(pvO ^ (3 + 1)) ^ (D - 1)}
  -- rewrite using h_two_pow and h_span
  have hmem' : (pvO ^ (3 * v) * u2 ^ v) * x ∈ Ideal.span {pvO ^ (4 * (D - 1))} := by
    simpa [h_two_pow, h_span] using hmem
  have hu2v : IsUnit (u2 ^ v : OKv) := isUnit_u2.pow v
  rcases hu2v with ⟨u, hu⟩
  have hmem'' : pvO ^ (3 * v) * x ∈ Ideal.span {pvO ^ (4 * (D - 1))} := by
    -- from hmem': (pvO^(3v) * u2^v) * x ∈ I
    -- multiply by (u⁻¹) on the right to cancel u2^v
    have h := Ideal.mul_mem_right ((u⁻¹ : OKvˣ) : OKv) (Ideal.span {pvO ^ (4 * (D - 1))}) hmem'
    -- h : ((pvO ^ (3 * v) * u2 ^ v) * x) * ((u⁻¹ : OKvˣ) : OKv) ∈ I
    have h_simp : ((pvO ^ (3 * v) * u2 ^ v) * x) * ((u⁻¹ : OKvˣ) : OKv) = pvO ^ (3 * v) * x := by
      calc
        ((pvO ^ (3 * v) * u2 ^ v) * x) * ((u⁻¹ : OKvˣ) : OKv) = (pvO ^ (3 * v) * (u2 ^ v : OKv) * x) * ((u⁻¹ : OKvˣ) : OKv) := rfl
        _ = (pvO ^ (3 * v) * (u : OKv) * x) * ((u⁻¹ : OKvˣ) : OKv) := by rw [hu]
        _ = pvO ^ (3 * v) * x * ((u : OKv) * ((u⁻¹ : OKvˣ) : OKv)) := by ring
        _ = pvO ^ (3 * v) * x * 1 := by rw [Units.mul_inv]
        _ = pvO ^ (3 * v) * x := by simp
    rw [h_simp] at h
    exact h
  by_cases hle : 3 * v ≤ 4 * (D - 1)
  · set n := 4 * (D - 1) - 3 * v with hn
    have h_pow_eq : ‖pv‖ ^ (4 * (D - 1)) = ‖pv‖ ^ n * ‖pv‖ ^ (3 * v) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hnorm := (mem_span_pvO_pow_iff (4 * (D - 1))).mp hmem''
    -- hnorm : ‖((pvO ^ (3 * v) * x) : Kv)‖ ≤ ‖pv‖ ^ (4 * (D - 1))
    have hnorm' : ‖pv‖ ^ (3 * v) * ‖(x : Kv)‖ ≤ ‖pv‖ ^ n * ‖pv‖ ^ (3 * v) := by
      -- from hnorm and h_pow_eq
      have h := hnorm.trans_eq h_pow_eq
      simpa [Subring.coe_mul, coe_pvO, norm_mul, norm_pow] using h
    have ha_pos : 0 < ‖pv‖ ^ (3 * v) := pow_pos norm_pv_pos _
    have hx_norm : ‖(x : Kv)‖ ≤ ‖pv‖ ^ n := by
      -- from hnorm': a*‖x‖ ≤ b*a where a = ‖pv‖^(3v), b = ‖pv‖^n
      -- rewrite RHS: b*a = a*b
      have h : ‖pv‖ ^ (3 * v) * ‖(x : Kv)‖ ≤ ‖pv‖ ^ (3 * v) * ‖pv‖ ^ n := by
        simpa [mul_comm (‖pv‖ ^ n)] using hnorm'
      -- cancel a (since a > 0) using `le_of_mul_le_mul_left`
      exact le_of_mul_le_mul_left h ha_pos
    rw [hn]
    exact ((mem_span_pvO_pow_iff n).mpr hx_norm)
  · have hle' : 4 * (D - 1) ≤ 3 * v := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    have hn : 4 * (D - 1) - 3 * v = 0 := Nat.sub_eq_zero_of_le hle'
    rw [hn, pow_zero]
    simp [Ideal.span_singleton_one]

/-- **Truncation of the scaled logarithm** over `OKv`. -/
theorem logVal_sub_sum_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : FormalGroupLaw OKv ι)
    {s : ℕ} (y : ι → OKv) (hy : ∀ j, y j ∈ Ideal.span {pvO ^ s}) (S : Finset (ι →₀ ℕ)) {N B : ℕ}
    (hS : ∀ d, d ∉ S → N < d.degree)
    (hB : ∀ n, N < n → B ≤ 4 * (n - 1) - 3 * padicValNat 2 n + s * n) (i : ι) :
    logVal Φ (unitBall Kv).subtype (pvO ^ (3 + 1)) y i -
        ∑ d ∈ S, MvPowerSeries.coeff d (logC Φ (unitBall Kv).subtype (pvO ^ (3 + 1)) i) *
          d.prod (fun j e => y j ^ e) ∈ Ideal.span {pvO ^ B} := by
  classical
  let f := (unitBall Kv).subtype
  let c := pvO ^ (3 + 1)
  let F (d : ι →₀ ℕ) : OKv :=
    MvPowerSeries.coeff d (logC Φ f c i) * d.prod (fun j e => y j ^ e)
  have hc : ScalingHyp 2 c :=
    scalingHyp_uniformizer two_mem_maximalIdeal isUnit_u2 two_eq
  have hsum : HasSum F (logVal Φ f c y i) :=
    MvPSeries.hasSum_evalT y (decay_logC Nat.prime_two two_mem_maximalIdeal hc
      Subtype.val_injective Φ i)
  have hsumS : HasSum (fun d => if d ∈ S then F d else 0) (∑ d ∈ S, F d) := by
    have h_fin : Function.HasFiniteSupport (fun d => if d ∈ S then F d else 0) := by
      refine (Finset.finite_toSet S).subset ?_
      intro d hd
      rw [Function.mem_support] at hd
      by_contra h
      have hS : d ∉ S := λ hdS => h (by simpa using hdS)
      have hzero : (if d ∈ S then F d else 0) = 0 := by simp [hS]
      exact hd hzero
    have h_summable : Summable (fun d => if d ∈ S then F d else 0) :=
      summable_of_hasFiniteSupport h_fin
    have htsum := h_summable.hasSum
    rw [tsum_eq_sum (s := S) (f := fun d => if d ∈ S then F d else 0) (by
      intro d hd
      simp [hd])] at htsum
    have hsum_eq : (∑ d ∈ S, (if d ∈ S then F d else 0)) = (∑ d ∈ S, F d) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp [hd]
    rw [hsum_eq] at htsum
    exact htsum
  have hsub : HasSum (fun d => F d - (if d ∈ S then F d else 0))
      (logVal Φ f c y i - ∑ d ∈ S, F d) :=
    hsum.sub hsumS
  have hzero : (fun d => F d - (if d ∈ S then F d else 0)) =
      (fun d => if d ∈ S then (0 : OKv) else F d) := by
    ext d; by_cases hd : d ∈ S <;> simp [hd]
  rw [hzero] at hsub
  rw [← hsub.tsum_eq]
  have hclosed : IsClosed ((Ideal.span {pvO ^ B} : Ideal OKv) : Set OKv) := by
    have e : ((Ideal.span {pvO ^ B} : Ideal OKv) : Set OKv) = {x : OKv | ‖(x : Kv)‖ ≤ ‖pv‖ ^ B} := by
      ext x
      exact mem_span_pvO_pow_iff B
    rw [e]
    exact isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const
  refine tsum_mem hclosed fun d => ?_
  by_cases hd : d ∈ S
  · simp [hd]
  · have hcoeff := coeff_logC_OKv Φ i d
    have hP : d.prod (fun j e => y j ^ e) ∈ (Ideal.span {pvO ^ s}) ^ d.degree := by
      rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hy s) _
    have hP' : d.prod (fun j e => y j ^ e) ∈ Ideal.span {pvO ^ (s * d.degree)} := by
      rw [Ideal.span_singleton_pow] at hP
      simpa [pow_mul] using hP
    have hprod : MvPowerSeries.coeff d (logC Φ f c i) * d.prod (fun j e => y j ^ e) ∈
        Ideal.span {pvO ^ (4 * (d.degree - 1) - 3 * padicValNat 2 d.degree)} *
        Ideal.span {pvO ^ (s * d.degree)} :=
      Ideal.mul_mem_mul hcoeff hP'
    have hprod_span : Ideal.span {pvO ^ (4 * (d.degree - 1) - 3 * padicValNat 2 d.degree)} *
        Ideal.span {pvO ^ (s * d.degree)} =
        Ideal.span {pvO ^ ((4 * (d.degree - 1) - 3 * padicValNat 2 d.degree) + s * d.degree)} := by
      rw [Ideal.span_singleton_mul_span_singleton, pow_add]
    rw [hprod_span] at hprod
    have hdeg : N < d.degree := hS d hd
    have hineq : B ≤ (4 * (d.degree - 1) - 3 * padicValNat 2 d.degree) + s * d.degree := by
      simpa [add_comm, add_left_comm, add_assoc] using hB d.degree hdeg
    have hmem : pvO ^ ((4 * (d.degree - 1) - 3 * padicValNat 2 d.degree) + s * d.degree) ∈
        Ideal.span {pvO ^ B} :=
      Ideal.mem_span_singleton.mpr (pow_dvd_pow pvO hineq)
    have hspan_le : Ideal.span {pvO ^ ((4 * (d.degree - 1) - 3 * padicValNat 2 d.degree) + s * d.degree)} ≤
        Ideal.span {pvO ^ B} :=
      Ideal.span_le.mpr (by simpa using hmem)
    simpa [F, hd] using hspan_le hprod

end FurioLombardo.Discharge.KvArith
