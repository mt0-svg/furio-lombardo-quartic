import FurioLombardo.Discharge.M3a.LocalCheck
import FurioLombardo.Discharge.M3a.LocalLead
import FurioLombardo.Discharge.M3a.ConcreteRoute

/-!
# The local facts at `v` (WP5 of the M3a discharge)

For `σ : K21 → K_v = ℚ_2[x]/(E)` (lane M4's `FurioLombardo.Discharge.M4Cert.σ`, the place `v`
above 2 with `e = 3`) and the twists `k = 0, 1`, with `N = K_v(ω)`, `ω² = σ(d k)`:

* `d_not_isSquare_Kv`: `σ(d k)` is not a square (so `N` is a field);
* `irr_Kv`: `(h k).map σ` is irreducible: `h = A² - d B²` over K21 (`h_eq_normForm`), `σ(b1) ≠ 0`,
  and the discriminant `D` of `X² + (a1 + b1 ω) X + (a0 + b0 ω)` is not a square in `N`
  (`irreducible_normForm`);
* `nsq_Kv`: the class of `q - c h` in `K_v[T]/(fRev k)` is not of the form `c' y²`: the
  resultant `ρ` of `q` and `A + ω B` is not a square in `N` (`nsq_normForm`);
* `localFacts_Kv`: lane M3a's `LocalFacts σ k`, with `lead_Kv` (LocalLead.lean).

The non-squares of `N` come from the certificates of LocalCheck.lean (`ck_res`).
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M4Cert

/-! ## Over K21 -/

/-- The coefficients of `A = X² + a1 X + a0` and `B = b1 X + b0`. -/
noncomputable def a0 (k : Fin 2) : K21 := (a0Q k).ev
noncomputable def a1 (k : Fin 2) : K21 := (a1Q k).ev
noncomputable def b0 (k : Fin 2) : K21 := (b0Q k).ev
noncomputable def b1 (k : Fin 2) : K21 := (b1Q k).ev

theorem ev_zQ (k i : ℕ) : (zQ k i).ev = ((zM k i : ℕ) : K21)⁻¹ * zkE (zL k i) := rfl

theorem ev_dQ (k : Fin 2) : (dQ k).ev = d k := (d_eq k).symm

theorem ev_q0Q (k : Fin 2) : (q0Q k).ev = (q k).coeff 0 := by rw [q, coeff_pQ]; rfl

theorem ev_q1Q (k : Fin 2) : (q1Q k).ev = (q k).coeff 1 := by rw [q, coeff_pQ]; rfl

theorem ev_of_mem {e f : QE} (h : QE.qcheck 1024 (.sub e f) = true) : e.ev = f.ev :=
  QE.ev_eq_of_qcheck 1024 e f h

theorem h3_eq (k : Fin 2) : (hQ k 3).ev = 2 * a1 k := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idH3 k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_int, Int.cast_ofNat] at this
  exact this

theorem h2_eq (k : Fin 2) : (hQ k 2).ev = a1 k ^ 2 + 2 * a0 k - d k * b1 k ^ 2 := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idH2 k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_int, QE.ev_add, QE.ev_sub, ev_sqQ, Int.cast_ofNat, ev_dQ] at this
  exact this

theorem h1_eq (k : Fin 2) : (hQ k 1).ev = 2 * a0 k * a1 k - 2 * d k * b0 k * b1 k := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idH1 k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_int, QE.ev_sub, Int.cast_ofNat, ev_dQ] at this
  rw [this, a0, a1, b0, b1]; ring

theorem h0_eq (k : Fin 2) : (hQ k 0).ev = a0 k ^ 2 - d k * b0 k ^ 2 := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idH0 k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_sub, ev_sqQ, ev_dQ] at this
  exact this

theorem D0_eq (k : Fin 2) : (zQ k 0).ev = a1 k ^ 2 + d k * b1 k ^ 2 - 4 * a0 k := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idD0 k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_int, QE.ev_add, QE.ev_sub, ev_sqQ, Int.cast_ofNat, ev_dQ] at this
  exact this

theorem D1_eq (k : Fin 2) : (zQ k 1).ev = 2 * a1 k * b1 k - 4 * b0 k := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idD1 k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_int, QE.ev_sub, Int.cast_ofNat] at this
  rw [this, a1, b1, b0]; ring

theorem ND_eq (k : Fin 2) : (zQ k 2).ev = (zQ k 0).ev ^ 2 - d k * (zQ k 1).ev ^ 2 := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idND k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_sub, ev_sqQ, ev_dQ] at this
  exact this

theorem R0_eq (k : Fin 2) :
    (zQ k 3).ev = rho0 (d k) (a0 k) (a1 k) (b0 k) (b1 k) ((q k).coeff 0) ((q k).coeff 1) := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idR0 k) (by simp [idsL]))
  rw [ev_rho0E, ev_dQ, ev_q0Q, ev_q1Q] at this
  exact this

theorem R1_eq (k : Fin 2) :
    (zQ k 4).ev = rho1 (d k) (a0 k) (a1 k) (b0 k) (b1 k) ((q k).coeff 0) ((q k).coeff 1) := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idR1 k) (by simp [idsL]))
  rw [ev_rho1E (dQ k), ev_dQ, ev_q0Q, ev_q1Q] at this
  exact this

theorem NR_eq (k : Fin 2) : (zQ k 5).ev = (zQ k 3).ev ^ 2 - d k * (zQ k 4).ev ^ 2 := by
  have := ev_of_mem (qcheck_of_mem (k := k) (e := idNR k) (by simp [idsL]))
  simp only [QE.ev_mul, QE.ev_sub, ev_sqQ, ev_dQ] at this
  exact this

theorem h_explicit (k : Fin 2) :
    h k = X ^ 4 + C ((hQ k 3).ev) * X ^ 3 + C ((hQ k 2).ev) * X ^ 2 + C ((hQ k 1).ev) * X +
      C ((hQ k 0).ev) := by
  have hm : ((hDenN k : ℕ) : K21) ≠ 0 :=
    natCast_ne_zero (by fin_cases k <;> simp [ck_dens.2.2.1, ck_dens.2.2.2.1])
  have hC : C ((hDenN k : K21)⁻¹) * C (hDenN k : K21) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hm, map_one]
  rw [h, pQ, hL]
  simp only [pK_cons, pK_nil, hQ, QE.ev_atom, hE, evK_lin, evK_int, Int.cast_natCast, map_mul,
    mul_zero, add_zero]
  linear_combination X ^ 4 * hC

/-- **`h = A² - d B²` over K21.** -/
theorem h_eq_normForm (k : Fin 2) : h k = normForm (d k) (a0 k) (a1 k) (b0 k) (b1 k) := by
  rw [h_explicit, normForm_eq, h3_eq, h2_eq, h1_eq, h0_eq]

theorem q_explicit (k : Fin 2) : q k = X ^ 2 + C ((q k).coeff 1) * X + C ((q k).coeff 0) := by
  have hm := q_monic k
  have hd := q_natDegree k
  ext n
  simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · have := hm.coeff_natDegree
    rw [hd] at this
    simp [this]
  · have : (q k).coeff (n + 3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [this]

/-! ## At `v` -/

theorem natCast_ne_zero_Kv {m : ℕ} (hm : m ≠ 0) : ((m : ℕ) : Kv) ≠ 0 := by
  rw [← map_natCast σ]
  exact (map_ne_zero σ).mpr (natCast_ne_zero hm)

theorem σ_ev_zQ (k i : ℕ) : σ ((zQ k i).ev) = σ (((zM k i : ℕ) : K21)⁻¹ * zkE (zL k i)) := rfl

/-- `σ(d k)` is not a square in `K_v`. -/
theorem d_not_isSquare_Kv (k : Fin 2) : ¬ IsSquare (σ (d k)) := by
  obtain ⟨_, _, hz, hP, ht, _, _⟩ := ck_res k
  have hx := approx_σ_zkE _ hz hP
  have hns : ¬ IsSquare (σ (zkE (dnL k))) := by
    rintro ⟨r, hr⟩
    exact not_sq_of_sqTest hx ht r (by rw [hr]; ring)
  have hq : qDenN k ≠ 0 := by fin_cases k <;> simp [ck_dens.1, ck_dens.2.1]
  rw [d_eq, map_mul, map_inv₀, map_natCast, Nat.cast_mul, ← sq]
  exact not_isSquare_inv_sq_mul (natCast_ne_zero_Kv hq) hns

theorem b1_ne_zero_Kv (k : Fin 2) : σ (b1 k) ≠ 0 := by
  obtain ⟨_, _, _, _, _, hz, hne⟩ := ck_res k
  have hx := ne_zero_of_approx (approx_σ_zkE _ hz (by norm_num : 3 ≤ 28)) hne
  have hm : mbDen.getD k 1 ≠ 0 := by fin_cases k <;> decide
  rw [b1, b1Q, QE.ev_atom, map_mul, map_inv₀, map_natCast]
  exact mul_ne_zero (inv_ne_zero (natCast_ne_zero_Kv hm)) hx

/-- `X² + (a1 + b1 ω) X + (a0 + b0 ω)` has no root in `N`: its discriminant is not a square. -/
theorem noRoot_Kv (k : Fin 2) (r : QuadraticAlgebra Kv (σ (d k)) 0) :
    r ^ 2 + ⟨σ (a1 k), σ (b1 k)⟩ * r + ⟨σ (a0 k), σ (b0 k)⟩ ≠ 0 := by
  apply no_root_of_not_isSquare
  rw [discN_eq]
  have e0 : σ (a1 k) ^ 2 + σ (d k) * σ (b1 k) ^ 2 - 4 * σ (a0 k) = σ ((zQ k 0).ev) := by
    rw [D0_eq]; simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  have e1 : 2 * σ (a1 k) * σ (b1 k) - 4 * σ (b0 k) = σ ((zQ k 1).ev) := by
    rw [D1_eq]; simp only [map_sub, map_mul, map_ofNat]
  rw [e0, e1, σ_ev_zQ]
  refine not_isSquare_of_ZCheck (ck_res k).1 ?_
  rw [← σ_ev_zQ, ← σ_ev_zQ, ND_eq]
  simp only [map_sub, map_mul, map_pow]

/-- The resultant `ρ` of `q` and `A + ω B` is not a square in `N`. -/
theorem rho_not_isSquare_Kv (k : Fin 2) :
    ¬ IsSquare (rhoN (σ (d k)) (σ (a0 k)) (σ (a1 k)) (σ (b0 k)) (σ (b1 k)) (σ ((q k).coeff 0))
      (σ ((q k).coeff 1))) := by
  rw [rhoN_eq]
  have e0 : rho0 (σ (d k)) (σ (a0 k)) (σ (a1 k)) (σ (b0 k)) (σ (b1 k)) (σ ((q k).coeff 0))
      (σ ((q k).coeff 1)) = σ ((zQ k 3).ev) := by
    rw [R0_eq]; simp only [rho0, map_add, map_sub, map_mul, map_pow, map_ofNat]
  have e1 : rho1 (σ (d k)) (σ (a0 k)) (σ (a1 k)) (σ (b0 k)) (σ (b1 k)) (σ ((q k).coeff 0))
      (σ ((q k).coeff 1)) = σ ((zQ k 4).ev) := by
    rw [R1_eq]; simp only [rho1, map_add, map_sub, map_mul, map_pow, map_ofNat]
  rw [e0, e1, σ_ev_zQ]
  refine not_isSquare_of_ZCheck (ck_res k).2.1 ?_
  rw [← σ_ev_zQ, ← σ_ev_zQ, NR_eq]
  simp only [map_sub, map_mul, map_pow]

theorem h_map_eq (k : Fin 2) :
    (h k).map σ = normForm (σ (d k)) (σ (a0 k)) (σ (a1 k)) (σ (b0 k)) (σ (b1 k)) := by
  rw [h_eq_normForm, map_normForm_ringHom]

/-- **(irr)**: `(h k).map σ` is irreducible over `K_v`. -/
theorem irr_Kv (k : Fin 2) : Irreducible ((h k).map σ) := by
  have : Fact (¬ IsSquare (σ (d k))) := ⟨d_not_isSquare_Kv k⟩
  rw [h_map_eq]
  exact irreducible_normForm (b1_ne_zero_Kv k) (noRoot_Kv k)

/-- **(nsq)**: `(q - c h)(T)` is not of the form `c' y²` in `K_v[T]/(fRev k)`. -/
theorem nsq_Kv (k : Fin 2) (c' : Kv) (y : AdjoinRoot ((fRev k).map σ)) :
    AdjoinRoot.mk ((fRev k).map σ) ((q k).map σ - (C (c k) * h k).map σ) ≠
      algebraMap Kv (AdjoinRoot ((fRev k).map σ)) c' * y ^ 2 := by
  have : Fact (¬ IsSquare (σ (d k))) := ⟨d_not_isSquare_Kv k⟩
  have hc : σ (c k) ≠ 0 :=
    (map_ne_zero σ).mpr fun h0 => c_not_isSquare k ⟨0, by rw [h0, mul_zero]⟩
  have hδ : σ ((q k).coeff 1) ^ 2 - 4 * σ ((q k).coeff 0) = σ (d k) := by
    rw [d]; simp only [map_sub, map_mul, map_pow, map_ofNat]
  have hq : (q k).map σ = X ^ 2 + C (σ ((q k).coeff 1)) * X + C (σ ((q k).coeff 0)) := by
    conv_lhs => rw [q_explicit k]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C]
  have hf : (fRev k).map σ = C (σ (c k)) * (q k).map σ * (h k).map σ := by
    rw [fRev_eq_mul, Polynomial.map_mul, Polynomial.map_mul, map_C]
  have hcop : IsCoprime ((q k).map σ) ((h k).map σ) := by
    have hs := (fRev_separable k).map (f := σ)
    rw [hf, mul_assoc] at hs
    exact hs.of_mul_right.isCoprime
  rw [Polynomial.map_mul, map_C]
  exact nsq_normForm two_ne_zero_Kv (b1_ne_zero_Kv k) hc hδ (noRoot_Kv k) (rho_not_isSquare_Kv k)
    hq (h_map_eq k) hf hcop c' y

/-- **The local facts at `v`** for both twists. -/
theorem localFacts_Kv (k : Fin 2) : LocalFacts FurioLombardo.Discharge.M4Cert.σ k :=
  ⟨lead_Kv k, irr_Kv k, nsq_Kv k⟩

end FurioLombardo.Discharge.M3a.Bruin
