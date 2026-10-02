import Mathlib
import FurioLombardo.Discharge.SelmerBasis.Count.Place
import FurioLombardo.Discharge.SelmerBasis.Count.Tors
import FurioLombardo.Discharge.R7.ConcreteKv
import FurioLombardo.Discharge.R7.LogChart
import FurioLombardo.Discharge.M3a.ConcreteInputs
import FurioLombardo.Discharge.M3a.MuT

/-!
# Count lane: `CountBound` at `v` (both twists)

At `v` (`M4Cert.Kv`, `e = 3`, `f = 1`), for `F_k = (fRev k).map σ`:

* the base point is R7's `baseKv k` (`lsetupV k`), with `F_k = f_k(X - a_k)` (R7's `hF`);
* `O_v² ≅ ℤ_[2]⁶` (R7's `coordEquiv`), so `O_v² / 2 O_v²` has at most `2^6` representatives;
* `q k` is the only monic quadratic divisor of `F_k` (`fRev k = q k · (c k h k)` with `h^σ` irreducible,
  M3a's `l1Inputs`, `eq_of_monic_quadratic_dvd`), so `#A(K_v)[2] ≤ 2`;
* `countBound_v k : CountBound ((fRev k).map σ) 7`.
-/

set_option autoImplicit false

open Polynomial
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall
open FurioLombardo.Discharge.M4Cert (σ Kv)
open FurioLombardo.Discharge.R7 (OKv pvO isUniformizer_pv isUnit_u2 natCast_two_eq
  natCast_two_mem_maximalIdeal coordEquiv)
open FurioLombardo.Discharge.R7.ConcreteKv (baseKv aK hF)
open FurioLombardo.Discharge.M3a (eq_of_monic_quadratic_dvd)
open FurioLombardo.Discharge.M3a.Bruin (fRev q l1Inputs irr_Kv nsq_Kv q_monic q_natDegree)

namespace FurioLombardo.Discharge.SelmerBasis.Count

/-- R7's base point data at `v`, as an `LSetup`. -/
noncomputable def lsetupV (k : Fin 2) : LSetup Kv where
  f := (baseKv k).f
  hf := (baseKv k).hf
  V0 := (baseKv k).V0
  hV0d := (baseKv k).hV0d
  hV00 := (baseKv k).hV00
  c0 := (baseKv k).c0
  hc0 := (baseKv k).hc0
  w0 := (baseKv k).w0
  hw0m := (baseKv k).hw0m
  hw0d := (baseKv k).hw0d
  hfV0 := (baseKv k).hfV0
  hw00 := (baseKv k).hw00

instance goodSextic_lsetupV (k : Fin 2) : GoodSextic (lsetupV k).f :=
  FurioLombardo.Discharge.R7.ConcreteKv.goodSextic_baseKv k

/-- At most `2^6` representatives of `O_v² / 2 O_v²`. -/
theorem reps_v : ∃ tV : Finset (Fin 2 → unitBall Kv), tV.card ≤ 2 ^ 6 ∧
    ∀ v : Fin 2 → unitBall Kv, ∃ r ∈ tV, ∃ w, v = r + 2 • w := by
  obtain ⟨t, htc, ht⟩ := cnt_reps_padic
  obtain ⟨T6, hT6c, hT6⟩ := cnt_reps_pi 6 t ht
  obtain ⟨T, hTc, hT⟩ := cnt_reps_equiv coordEquiv T6 hT6
  exact ⟨T, hTc.trans (hT6c.trans (Nat.pow_le_pow_left htc 6)), hT⟩

/-- `q k` is the only monic quadratic divisor of `F_k` over `K_v`. -/
theorem uniq_v (k : Fin 2) : ∀ u : Kv[X], u.Monic → u.natDegree = 2 → u ∣ (fRev k).map σ →
    u = (q k).map σ := by
  obtain ⟨r, hqr, hr, -⟩ := (l1Inputs σ k (irr_Kv k) (nsq_Kv k)).fac
  have hqr' : (fRev k).map σ = (q k).map σ * r.map σ := by rw [hqr, Polynomial.map_mul]
  have hdeg' : ((q k).map σ).natDegree = 2 := by rw [natDegree_map, q_natDegree]
  have hrdeg : 2 < (r.map σ).natDegree := by
    have h6 := GoodSextic.natDegree_eq (f := (fRev k).map σ)
    rw [hqr', natDegree_mul ((q_monic k).map σ).ne_zero hr.ne_zero, hdeg'] at h6
    omega
  exact eq_of_monic_quadratic_dvd hqr' ((q_monic k).map σ) hdeg' hr hrdeg

/-- `#A(K_v)[2] ≤ 2`. -/
theorem tors_v (k : Fin 2) : ∃ tT : Finset (Jac ((fRev k).map σ)), tT.card ≤ 2 ^ 1 ∧
    ∀ c : Jac ((fRev k).map σ), c ^ 2 = 1 → c ∈ tT := by
  classical
  obtain ⟨tT, htc, ht⟩ := exists_tors_finset ((fRev k).map σ) {(q k).map σ}
    (fun u hu hud huf => Finset.mem_singleton.mpr (uniq_v k u hu hud huf))
  exact ⟨tT, by simpa using htc, ht⟩

/-- **`CountBound` at `v`**: the image of `μ` on `A(K_v)` has at most `2^7` elements.
Lemma 5.6 of the paper. -/
theorem countBound_v (k : Fin 2) : CountBound ((fRev k).map σ) 7 := by
  obtain ⟨tV, htVc, htV⟩ := reps_v
  obtain ⟨tT, htTc, htT⟩ := tors_v k
  exact countBound_of_reps isUniformizer_pv 3 (lsetupV k) (hF k) Nat.prime_two
    natCast_two_mem_maximalIdeal isUnit_u2 natCast_two_eq tV htVc htV tT htTc htT

end FurioLombardo.Discharge.SelmerBasis.Count
