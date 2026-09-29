import Mathlib
import FurioLombardo.Discharge.R7.Psi
import FurioLombardo.Discharge.M4Log.Transport
import FurioLombardo.Discharge.M4Log.ModelLeaves
import FurioLombardo.Discharge.M4Log.SqrtModTwo

/-!
# `Setup.Adm (4 a)` from an integral model

For a Setup `S` of R7 (a sextic `f`, the cubic `V0` with `f - V0² = c0 X⁴ w0`), `p = π^a` and
`b = V0(0)`, the integral model is `f̃ = f(p X) / b²`, `Ṽ0 = V0(p X) / b`. `IntModel S a` asks:
`Ṽ0` integral (H1), `f̃ - Ṽ0² = 4 X⁴ q` with `q` integral (H2), and `c0 p⁶ / (4 b²)` a unit (H3).
Then every object of R7's chain is, after the transport `X ↦ p X`, `t ↦ (p t₀, p² t₁)` (`tw`),
an explicit constant times an integral polynomial (`TInt`), and `S.Adm (4 a)` holds
(`adm_of_intModel`).
-/

open Polynomial

namespace FurioLombardo.Discharge.M4Log.Model

open FurioLombardo.Vendor.Toolbox.SqrtMod FurioLombardo.Vendor.Toolbox.Bounded FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.SubPoly
open FurioLombardo.Vendor.Toolbox.G2Formal.Setup (A2 uL uR u1)

set_option autoImplicit false

variable {K : Type*} [Field K]

/-! ## Leaves -/

theorem uT_X_eq_uP : (u1 : (MvPowerSeries (Fin 2) K)[X]) = uP (K := K) (id : Fin 2 → Fin 2) := by
  rfl

theorem uL_eq_uP : (uL : (A2 K)[X]) = uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) := by
  rfl

theorem uR_eq_uP : (uR : (A2 K)[X]) = uP (K := K) (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) := by
  rfl

/-! ## The integral model -/

/-- The scale `p = π^a`. -/
noncomputable abbrev pw (S : Setup K) (a : ℕ) : K := (S.π : K) ^ a

theorem pw_ne (S : Setup K) (a : ℕ) : pw S a ≠ 0 := pow_ne_zero _ S.hπ0

theorem pw_mem (S : Setup K) (a : ℕ) : pw S a ∈ S.O := S.O.pow_mem S.π.2 _

theorem four_ne (S : Setup K) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero S.h2 S.h2

/-- **The integral model hypotheses** at the scale `p = π^a`, `b = V0(0)`. -/
structure IntModel (S : Setup K) (a : ℕ) where
  /-- The constant `b = V0(0)`. -/
  b : K
  hb : b ≠ 0
  hV00 : S.V0.coeff 0 = b
  /-- The quotient `(f̃ - Ṽ0²) / (4 X⁴)`. -/
  q : K[X]
  hVt : ∀ n, (C b⁻¹ * S.V0.comp (C (pw S a) * X)).coeff n ∈ S.O
  hqO : ∀ n, q.coeff n ∈ S.O
  hfq : C (b ^ 2)⁻¹ * S.f.comp (C (pw S a) * X) - (C b⁻¹ * S.V0.comp (C (pw S a) * X)) ^ 2 =
    4 * X ^ 4 * q
  hc0 : (S.c0 * pw S a ^ 6 / (4 * b ^ 2))⁻¹ ∈ S.O

namespace IntModel

variable {S : Setup K} {a : ℕ} (H : IntModel S a)

/-- `f̃ = f(p X) / b²`. -/
noncomputable def ft : K[X] := C (H.b ^ 2)⁻¹ * S.f.comp (C (pw S a) * X)

/-- `Ṽ0 = V0(p X) / b`. -/
noncomputable def Vt : K[X] := C H.b⁻¹ * S.V0.comp (C (pw S a) * X)

theorem Vt_coeff_zero : H.Vt.coeff 0 = 1 := by
  rw [Vt, coeff_C_mul, coeff_zero_comp_C_mul_X, H.hV00, inv_mul_cancel₀ H.hb]

theorem f_comp : S.f.comp (C (pw S a) * X) = C (H.b ^ 2) * H.ft := by
  rw [ft, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (pow_ne_zero 2 H.hb), C_1, one_mul]

theorem V0_comp : S.V0.comp (C (pw S a) * X) = C H.b * H.Vt := by
  rw [Vt, ← mul_assoc, ← C_mul, mul_inv_cancel₀ H.hb, C_1, one_mul]

theorem ft_sub : H.ft - H.Vt ^ 2 = 4 * X ^ 4 * H.q := H.hfq

theorem Vt_mem : ∀ n, H.Vt.coeff n ∈ S.O := H.hVt

/-! ### The chart branch `v` -/

theorem exists_vt : ∃ vt : (MvPowerSeries (Fin 2) K)[X], vt ∈ liftsRing (incl (σ := Fin 2) S.O) ∧
    vt.degree < 2 ∧ vt.map MvPowerSeries.constantCoeff = H.Vt %ₘ X ^ 2 ∧
    uP (K := K) (id : Fin 2 → Fin 2) ∣ cst H.ft - vt ^ 2 := by
  obtain ⟨U, h, hUO, hhO, hVU, hU0⟩ := exists_inv_mod_X_pow H.Vt_coeff_zero H.Vt_mem 2
  obtain ⟨hm1, hm2, hm3⟩ := uP_sub_mem (K := K) S.O (id : Fin 2 → Fin 2)
  obtain ⟨Y, hYL, hYI, -, hdvd⟩ := exists_sqrtMod_two S.O (d := 2) two_pos H.ft H.Vt U
    (X ^ 2 * H.q) h (by rw [H.ft_sub]; ring) hVU (by rw [hU0]; exact one_ne_zero) hUO
    (fun n => by
      rw [coeff_X_pow_mul']
      split_ifs
      · exact H.hqO _
      · exact S.O.zero_mem) hhO _ hm1 hm2 (by exact_mod_cast hm3)
  rw [add_sub_cancel] at hdvd
  set m := uP (K := K) (id : Fin 2 → Fin 2) with hm
  have hmon : m.Monic := uP_monic _
  set A := cst (σ := Fin 2) H.Vt + 2 * Y with hA
  refine ⟨A %ₘ m, modByMonic_mem_liftsRing _ hmon (uP_mem S.O _)
    (Subring.add_mem _ (cst_mem_liftsRing S.O H.Vt_mem)
      (Subring.mul_mem _ (two_mem_liftsRing S.O) hYL)), ?_, ?_, dvd_sub_sq_modByMonic hmon hdvd⟩
  · have := degree_modByMonic_lt A hmon
    rwa [degree_eq_natDegree hmon.ne_zero, uP_natDegree] at this
  · rw [map_modByMonic _ hmon, uP_map, hA, Polynomial.map_add, Polynomial.map_mul, map_cst_self,
      map_eq_zero_of_mem_ord hYI, mul_zero, add_zero]

/-- The integral chart branch `ṽ`. -/
noncomputable def vt : (MvPowerSeries (Fin 2) K)[X] := H.exists_vt.choose

theorem vt_mem : H.vt ∈ liftsRing (incl (σ := Fin 2) S.O) := H.exists_vt.choose_spec.1
theorem vt_degree : H.vt.degree < 2 := H.exists_vt.choose_spec.2.1
theorem vt_map : H.vt.map MvPowerSeries.constantCoeff = H.Vt %ₘ X ^ 2 :=
  H.exists_vt.choose_spec.2.2.1
theorem vt_dvd : uP (K := K) (id : Fin 2 → Fin 2) ∣ cst H.ft - H.vt ^ 2 :=
  H.exists_vt.choose_spec.2.2.2

theorem tw_cst_f {τ : Type*} (w : τ → K) :
    tw w (pw S a) (cst (σ := τ) S.f) = C (MvPowerSeries.C (H.b ^ 2)) * cst H.ft := by
  rw [tw_cst, H.f_comp, map_mul, cst_C]

theorem v0_comp : S.v0.comp (C (pw S a) * X) = C H.b * (H.Vt %ₘ X ^ 2) := by
  rw [Setup.v0, modByMonic_X_pow_comp, H.V0_comp, C_mul_modByMonic]

/-- **`v` is `b` times the integral branch** after transport. -/
theorem tw_v : tw (wt1 (pw S a)) (pw S a) S.v = C (MvPowerSeries.C H.b) * H.vt := by
  have hb' : (MvPowerSeries.C H.b : MvPowerSeries (Fin 2) K) ≠ 0 := by
    simpa using H.hb
  set A := C (MvPowerSeries.C H.b⁻¹) * tw (wt1 (pw S a)) (pw S a) S.v with hA
  have hAv : tw (wt1 (pw S a)) (pw S a) S.v = C (MvPowerSeries.C H.b) * A := by
    rw [hA, ← mul_assoc, ← C_mul, ← map_mul, mul_inv_cancel₀ H.hb, map_one, C_1, one_mul]
  have hmon := uP_monic (K := K) (id : Fin 2 → Fin 2)
  have hdeg2 : (uP (K := K) (id : Fin 2 → Fin 2)).degree = 2 := by
    rw [degree_eq_natDegree hmon.ne_zero, uP_natDegree]; rfl
  have hAm : A.map MvPowerSeries.constantCoeff = H.Vt %ₘ X ^ 2 := by
    rw [hA, Polynomial.map_mul, map_C, MvPowerSeries.constantCoeff_C, map_tw, S.v_map, H.v0_comp,
      ← mul_assoc, ← C_mul, inv_mul_cancel₀ H.hb, C_1, one_mul]
  have hAeq : A = H.vt := sqrtMod_unique (A := A) (B := H.vt) S.h2 hmon
    (by rw [uP_map, uP_natDegree]) (F := cst H.ft)
    (lt_of_le_of_lt (degree_CC_mul_le _ _) (by
      rw [degree_tw _ (pw_ne S a) (wt1_ne_zero (pw_ne S a)), hdeg2]; exact S.v_degree))
    (by rw [hdeg2]; exact H.vt_degree) (by rw [hAm, H.vt_map]) ?_ ?_ H.vt_dvd
  · rw [hAv, hAeq]
  · have := congrArg (fun P => P.coeff 0) hAm
    simp only [coeff_map] at this
    rw [this, coeff_modByMonic_X_pow _ two_pos, H.Vt_coeff_zero]
    exact one_ne_zero
  · have h := _root_.map_dvd (tw (wt1 (pw S a)) (pw S a)) S.u1_dvd
    rw [map_sub, map_pow, H.tw_cst_f, uT_X_eq_uP, tw_uP_one, hAv, mul_pow, ← C_pow, ← map_pow,
      ← mul_sub] at h
    exact dvd_of_C_mul_dvd_C_mul (pow_ne_zero 2 (pw_ne S a)) h (pow_ne_zero 2 H.hb)

theorem Vt_degree : H.Vt.degree < 4 := by
  rw [Vt, ← smul_eq_C_mul]
  exact lt_of_le_of_lt ((degree_smul_le _ _).trans (degree_comp_C_mul_X_le _ _)) S.hV0d

/-! ### The branch `V` modulo `u_s u_s'` -/

/-- `uL uR` in `uP` form. -/
noncomputable abbrev uLR : (A2 K)[X] :=
  uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) * uP (K := K) Sum.inr

theorem uLR_monic' : (uLR (K := K)).Monic := (uP_monic _).mul (uP_monic _)

theorem uLR_natDegree' : (uLR (K := K)).natDegree = 4 := by
  rw [(uP_monic _).natDegree_mul (uP_monic _), uP_natDegree, uP_natDegree]

theorem uLR_map' : (uLR (K := K)).map MvPowerSeries.constantCoeff = X ^ 4 := by
  rw [Polynomial.map_mul, uP_map, uP_map, ← pow_add]

theorem uLR_eq : (uL * uR : (A2 K)[X]) = uLR := by rw [uL_eq_uP, uR_eq_uP]

theorem exists_Y2 : ∃ Y : (A2 K)[X], Y ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) ∧
    Y ∈ (ordIdeal (σ := Fin 2 ⊕ Fin 2) (R := K) 1).map (C : _ →+* (A2 K)[X]) ∧
    Y.natDegree < 4 ∧ uLR ∣ cst H.ft - (cst H.Vt + 2 * Y) ^ 2 := by
  obtain ⟨U, h, hUO, hhO, hVU, hU0⟩ := exists_inv_mod_X_pow H.Vt_coeff_zero H.Vt_mem 4
  obtain ⟨hm1, hm2, hm3⟩ := uLR_sub_mem (K := K) S.O
  obtain ⟨Y, hYL, hYI, hYd, hdvd⟩ := exists_sqrtMod_two S.O (d := 4) (by norm_num) H.ft H.Vt U
    H.q h H.ft_sub hVU (by rw [hU0]; exact one_ne_zero) hUO H.hqO hhO _ hm1 hm2
    (by exact_mod_cast hm3)
  rw [add_sub_cancel] at hdvd
  exact ⟨Y, hYL, hYI, hYd, hdvd⟩

/-- The correction `Y` of the integral branch `Ṽ = Ṽ0 + 2 Y`. -/
noncomputable def Y2 : (A2 K)[X] := H.exists_Y2.choose

theorem Y2_mem : H.Y2 ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) := H.exists_Y2.choose_spec.1
theorem Y2_ord : H.Y2 ∈ (ordIdeal (σ := Fin 2 ⊕ Fin 2) (R := K) 1).map (C : _ →+* (A2 K)[X]) :=
  H.exists_Y2.choose_spec.2.1
theorem Y2_natDegree : H.Y2.natDegree < 4 := H.exists_Y2.choose_spec.2.2.1

/-- The integral branch `Ṽ = Ṽ0 + 2 Y`. -/
noncomputable def VV : (A2 K)[X] := cst H.Vt + 2 * H.Y2

theorem VV_dvd : uLR ∣ cst H.ft - H.VV ^ 2 := H.exists_Y2.choose_spec.2.2.2

theorem VV_mem : H.VV ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  Subring.add_mem _ (cst_mem_liftsRing S.O H.Vt_mem)
    (Subring.mul_mem _ (two_mem_liftsRing S.O) H.Y2_mem)

theorem VV_map : H.VV.map MvPowerSeries.constantCoeff = H.Vt := by
  rw [VV, Polynomial.map_add, Polynomial.map_mul, map_cst_self, map_eq_zero_of_mem_ord H.Y2_ord,
    mul_zero, add_zero]

theorem VV_degree : H.VV.degree < 4 := by
  rw [VV]
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (lt_of_le_of_lt degree_map_le H.Vt_degree) ?_)
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  have h2 : (2 : (A2 K)[X]).degree ≤ 0 := by
    rw [show (2 : (A2 K)[X]) = C 2 by rw [map_ofNat]]; exact degree_C_le
  have hY : H.Y2.degree < 4 := by
    by_cases h0 : H.Y2 = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0]; exact_mod_cast H.Y2_natDegree
  calc (2 : (A2 K)[X]).degree + H.Y2.degree ≤ 0 + H.Y2.degree := add_le_add_left h2 _
    _ = H.Y2.degree := zero_add _
    _ < 4 := hY

/-- **`V` is `b` times the integral branch** after transport. -/
theorem tw_V : tw (wt2 (pw S a)) (pw S a) S.V = C (MvPowerSeries.C H.b) * H.VV := by
  set A := C (MvPowerSeries.C H.b⁻¹) * tw (wt2 (pw S a)) (pw S a) S.V with hA
  have hAv : tw (wt2 (pw S a)) (pw S a) S.V = C (MvPowerSeries.C H.b) * A := by
    rw [hA, ← mul_assoc, ← C_mul, ← map_mul, mul_inv_cancel₀ H.hb, map_one, C_1, one_mul]
  have hmon := uLR_monic' (K := K)
  have hdeg4 : (uLR (K := K)).degree = 4 := by
    rw [degree_eq_natDegree hmon.ne_zero, uLR_natDegree']; rfl
  have hAm : A.map MvPowerSeries.constantCoeff = H.Vt := by
    rw [hA, Polynomial.map_mul, map_C, MvPowerSeries.constantCoeff_C, map_tw, S.V_map, H.V0_comp,
      ← mul_assoc, ← C_mul, inv_mul_cancel₀ H.hb, C_1, one_mul]
  have hAeq : A = H.VV := sqrtMod_unique (A := A) (B := H.VV) S.h2 hmon
    (by rw [uLR_map', uLR_natDegree']) (F := cst H.ft)
    (lt_of_le_of_lt (degree_CC_mul_le _ _) (by
      rw [degree_tw _ (pw_ne S a) (wt2_ne_zero (pw_ne S a)), hdeg4]; exact S.V_degree))
    (by rw [hdeg4]; exact H.VV_degree) (by rw [hAm, H.VV_map]) ?_ ?_ H.VV_dvd
  · rw [hAv, hAeq]
  · have := congrArg (fun P => P.coeff 0) hAm
    simp only [coeff_map] at this
    rw [this, H.Vt_coeff_zero]
    exact one_ne_zero
  · have h := _root_.map_dvd (tw (wt2 (pw S a)) (pw S a)) S.uLR_dvd
    rw [map_sub, map_pow, H.tw_cst_f, map_mul, uL_eq_uP, uR_eq_uP, tw_uP_inl, tw_uP_inr, hAv,
      mul_pow, ← C_pow, ← map_pow, ← mul_sub, mul_mul_mul_comm, ← C_mul, ← map_mul, ← pow_add] at h
    exact dvd_of_C_mul_dvd_C_mul (pow_ne_zero _ (pw_ne S a)) h (pow_ne_zero 2 H.hb)

/-! ### The resultant `R1` -/

/-- `R̃1 = ṽ0² - t0 ṽ0 ṽ1 + t1 ṽ1²`. -/
noncomputable def R1t : MvPowerSeries (Fin 2) K :=
  H.vt.coeff 0 ^ 2 - MvPowerSeries.X 0 * H.vt.coeff 0 * H.vt.coeff 1 +
    MvPowerSeries.X 1 * H.vt.coeff 1 ^ 2

theorem rescale_R1 : MvPowerSeries.rescale (wt1 (pw S a)) S.R1 =
    MvPowerSeries.C (H.b ^ 2) * H.R1t := by
  have hp := pw_ne S a
  have h0 := rescale_coeff_of_tw hp H.tw_v 0
  have h1 := rescale_coeff_of_tw hp H.tw_v 1
  rw [Setup.R1, map_add, map_sub, map_mul, map_mul, map_mul, map_pow, map_pow, rescale_X_eq,
    rescale_X_eq, h0, h1, R1t]
  have e1 : (wt1 (pw S a) 0) * (H.b / pw S a ^ 0) * (H.b / pw S a ^ 1) = H.b ^ 2 := by
    simp only [wt1, Matrix.cons_val_zero]; field_simp
  have e2 : (wt1 (pw S a) 1) * (H.b / pw S a ^ 1) ^ 2 = H.b ^ 2 := by
    simp only [wt1, Matrix.cons_val_one, Matrix.cons_val_zero]; field_simp
  have e3 : (H.b / pw S a ^ 0) ^ 2 = H.b ^ 2 := by simp
  have E1 := congrArg (MvPowerSeries.C (σ := Fin 2)) e1
  have E2 := congrArg (MvPowerSeries.C (σ := Fin 2)) e2
  have E3 := congrArg (MvPowerSeries.C (σ := Fin 2)) e3
  simp only [map_mul, map_pow] at E1 E2 E3
  rw [show MvPowerSeries.C (H.b ^ 2) = (MvPowerSeries.C H.b : MvPowerSeries (Fin 2) K) ^ 2 from
    map_pow _ _ _]
  linear_combination H.vt.coeff 0 ^ 2 * E3 -
    (MvPowerSeries.X 0 * H.vt.coeff 0 * H.vt.coeff 1) * E1 +
    (MvPowerSeries.X 1 * H.vt.coeff 1 ^ 2) * E2

theorem R1t_mem : H.R1t ∈ intSeries S.O (Fin 2) := by
  have h0 := coeff_mem_intSeries_of_liftsRing H.vt_mem 0
  have h1 := coeff_mem_intSeries_of_liftsRing H.vt_mem 1
  have hX : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ intSeries S.O (Fin 2) :=
    fun i => X_mem_intSeries i
  exact Subring.add_mem _ (Subring.sub_mem _ (Subring.pow_mem _ h0 2)
    (Subring.mul_mem _ (Subring.mul_mem _ (hX 0) h0) h1))
    (Subring.mul_mem _ (hX 1) (Subring.pow_mem _ h1 2))

theorem vt_coeff_zero_const : MvPowerSeries.constantCoeff (H.vt.coeff 0) = 1 := by
  have := congrArg (fun P => P.coeff 0) H.vt_map
  simp only [coeff_map] at this
  rw [this, coeff_modByMonic_X_pow _ two_pos, H.Vt_coeff_zero]

theorem R1t_const : MvPowerSeries.constantCoeff H.R1t = 1 := by
  simp [R1t, H.vt_coeff_zero_const]

/-- **`R1⁻¹` after rescaling**: `b⁻²` times an integral series. -/
theorem tIntS_R1_inv : TIntS S.O (wt1 (pw S a)) (H.b ^ 2)⁻¹ S.R1⁻¹ :=
  tIntS_inv (pow_ne_zero 2 H.hb) H.R1t_mem (by rw [H.R1t_const, inv_one]; exact S.O.one_mem)
    (by rw [H.R1t_const]; exact one_ne_zero) H.rescale_R1

/-! ### The quotient `qw`, the constant `c1`, the quadratic `w` -/

/-- `N = X⁴ q - Ṽ0 Y - Y²`, with `f̃ - Ṽ² = 4 N`. -/
noncomputable def Nw : (A2 K)[X] := X ^ 4 * cst H.q - cst H.Vt * H.Y2 - H.Y2 ^ 2

theorem ft_sub_VV : cst H.ft - H.VV ^ 2 = C (MvPowerSeries.C 4) * H.Nw := by
  have h := congrArg (cst (σ := Fin 2 ⊕ Fin 2)) H.ft_sub
  simp only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.map_X, cst, coe_mapRingHom] at h
  rw [VV, Nw, show (C (MvPowerSeries.C (4 : K)) : (A2 K)[X]) = 4 by
    rw [map_ofNat, map_ofNat]]
  simp only [cst, coe_mapRingHom]
  linear_combination h

theorem Nw_mem : H.Nw ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) := by
  have hX : (X : (A2 K)[X]) ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
    (lifts_iff_liftsRing _ _).mp (X_mem_lifts _)
  exact Subring.sub_mem _ (Subring.sub_mem _ (Subring.mul_mem _ (Subring.pow_mem _ hX 4)
    (cst_mem_liftsRing S.O H.hqO)) (Subring.mul_mem _ (cst_mem_liftsRing S.O H.Vt_mem) H.Y2_mem))
    (Subring.pow_mem _ H.Y2_mem 2)

theorem uLR_mem : (uLR (K := K)) ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  Subring.mul_mem _ (uP_mem S.O _) (uP_mem S.O _)

theorem uLR_dvd_Nw : uLR ∣ H.Nw :=
  dvd_of_dvd_C_mul (four_ne S) (by rw [← H.ft_sub_VV]; exact H.VV_dvd)

/-- The integral quotient `Q̃w = N / (u_s u_s')`. -/
noncomputable def Qw : (A2 K)[X] := H.Nw /ₘ uLR

theorem Qw_mem : H.Qw ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  divByMonic_mem_liftsRing uLR_monic' (uLR_mem (S := S)) H.Nw_mem

theorem Nw_eq : H.Nw = uLR * H.Qw := eq_mul_divByMonic uLR_monic' H.uLR_dvd_Nw

theorem tw_qw : tw (wt2 (pw S a)) (pw S a) S.qw =
    C (MvPowerSeries.C (4 * H.b ^ 2 / pw S a ^ 4)) * H.Qw := by
  have h := congrArg (tw (wt2 (pw S a)) (pw S a)) S.f_sub_V_sq
  rw [map_sub, map_pow, H.tw_cst_f, H.tw_V, map_mul, map_mul, uL_eq_uP, uR_eq_uP, tw_uP_inl,
    tw_uP_inr, mul_pow, ← C_pow, ← map_pow, ← mul_sub, H.ft_sub_VV, H.Nw_eq] at h
  refine eq_of_C_mul_eq (pow_ne_zero 4 (pw_ne S a)) uLR_monic'.ne_zero ?_
  rw [show (4 * H.b ^ 2 : K) = H.b ^ 2 * 4 by ring, map_mul, C_mul]
  have e : C (MvPowerSeries.C (pw S a ^ 4)) * uLR * tw (wt2 (pw S a)) (pw S a) S.qw =
      C (MvPowerSeries.C (pw S a ^ 2)) * uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) *
        (C (MvPowerSeries.C (pw S a ^ 2)) * uP (K := K) Sum.inr) *
          tw (wt2 (pw S a)) (pw S a) S.qw := by
    rw [show pw S a ^ 4 = pw S a ^ 2 * pw S a ^ 2 by ring, map_mul, C_mul]; ring
  rw [e, ← h]; ring

theorem tInt_qw : TInt S.O (wt2 (pw S a)) (pw S a) (4 * H.b ^ 2 / pw S a ^ 4) S.qw :=
  ⟨H.Qw, H.Qw_mem, H.tw_qw⟩

/-- The scale of `c1`. -/
noncomputable abbrev sc1 : K := 4 * H.b ^ 2 / pw S a ^ 4 / pw S a ^ 2

theorem sc1_ne : H.sc1 ≠ 0 :=
  div_ne_zero (div_ne_zero (mul_ne_zero (four_ne S) (pow_ne_zero 2 H.hb))
    (pow_ne_zero 4 (pw_ne S a))) (pow_ne_zero 2 (pw_ne S a))

theorem rescale_c1 : MvPowerSeries.rescale (wt2 (pw S a)) S.c1 =
    MvPowerSeries.C H.sc1 * H.Qw.coeff 2 :=
  rescale_coeff_of_tw (pw_ne S a) H.tw_qw 2

theorem Qw2_const : MvPowerSeries.constantCoeff (H.Qw.coeff 2) =
    S.c0 * pw S a ^ 6 / (4 * H.b ^ 2) := by
  have h := congrArg MvPowerSeries.constantCoeff H.rescale_c1
  rw [FurioLombardo.Vendor.Toolbox.Conv.constantCoeff_rescale', S.c1_const, map_mul, MvPowerSeries.constantCoeff_C] at h
  have := pw_ne S a; have := H.hb; have := four_ne S
  rw [h]; unfold sc1; field_simp

theorem Qw2_ne : MvPowerSeries.constantCoeff (H.Qw.coeff 2) ≠ 0 := by
  rw [H.Qw2_const]
  exact div_ne_zero (mul_ne_zero S.hc0 (pow_ne_zero 6 (pw_ne S a)))
    (mul_ne_zero (four_ne S) (pow_ne_zero 2 H.hb))

theorem Qw2_inv_mem : (MvPowerSeries.constantCoeff (H.Qw.coeff 2))⁻¹ ∈ S.O := by
  rw [H.Qw2_const]; exact H.hc0

theorem tIntS_c1 : TIntS S.O (wt2 (pw S a)) H.sc1 S.c1 :=
  ⟨_, coeff_mem_intSeries_of_liftsRing H.Qw_mem 2, H.rescale_c1⟩

theorem tIntS_c1_inv : TIntS S.O (wt2 (pw S a)) H.sc1⁻¹ S.c1⁻¹ :=
  tIntS_inv H.sc1_ne (coeff_mem_intSeries_of_liftsRing H.Qw_mem 2) H.Qw2_inv_mem H.Qw2_ne
    H.rescale_c1

/-- The integral monic quadratic `w̃ = Q̃w / Q̃w₂`. -/
noncomputable def wt : (A2 K)[X] := C (H.Qw.coeff 2)⁻¹ * H.Qw

theorem wt_mem : H.wt ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  Subring.mul_mem _ (liftsRing_of_coeff_mem_intSeries fun n => by
      rw [coeff_C]; split_ifs
      · exact inv_mem_intSeries (coeff_mem_intSeries_of_liftsRing H.Qw_mem 2)
          H.Qw2_inv_mem H.Qw2_ne
      · exact Subring.zero_mem _) H.Qw_mem

theorem Qw_eq_wt : H.Qw = C (H.Qw.coeff 2) * H.wt := by
  rw [wt, ← mul_assoc, ← C_mul, MvPowerSeries.mul_inv_cancel _ H.Qw2_ne, C_1, one_mul]

theorem tw_w : tw (wt2 (pw S a)) (pw S a) S.w = C (MvPowerSeries.C (pw S a ^ 2)) * H.wt := by
  rw [Setup.w, tw_C_mul, FurioLombardo.Vendor.Toolbox.Conv.rescale_inv _ S.c1_ne, H.rescale_c1,
    inv_C_mul H.sc1_ne H.Qw2_ne, H.tw_qw, wt]
  have e : H.sc1⁻¹ * (4 * H.b ^ 2 / pw S a ^ 4) = pw S a ^ 2 := by
    have := pw_ne S a; have := H.hb; have := four_ne S; unfold sc1; field_simp
  have E : C (MvPowerSeries.C H.sc1⁻¹) * C (MvPowerSeries.C (4 * H.b ^ 2 / pw S a ^ 4)) =
      (C (MvPowerSeries.C (pw S a ^ 2)) : (A2 K)[X]) := by
    rw [← C_mul, ← map_mul, e]
  rw [C_mul]
  linear_combination (C (H.Qw.coeff 2)⁻¹ * H.Qw) * E

include H in
theorem tInt_w : TInt S.O (wt2 (pw S a)) (pw S a) (pw S a ^ 2) S.w := ⟨H.wt, H.wt_mem, H.tw_w⟩

/-! ### `Z` and `W` -/

theorem X2_mem : (X ^ 2 : (A2 K)[X]) ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  Subring.pow_mem _ ((lifts_iff_liftsRing _ _).mp (X_mem_lifts _)) 2

theorem X2_map : (X ^ 2 : (A2 K)[X]).map (MvPowerSeries.constantCoeff (σ := Fin 2 ⊕ Fin 2)
    (R := K)) = X ^ (X ^ 2 : (A2 K)[X]).natDegree := by
  rw [natDegree_X_pow, Polynomial.map_pow, Polynomial.map_X]

/-- `E = (Ṽ0 + Y) mod X²`, so that `ṽ0 + Ṽ ≡ 2 E` modulo `X²`. -/
noncomputable def E : (A2 K)[X] := (cst H.Vt + H.Y2) %ₘ X ^ 2

theorem E_mem : H.E ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  modByMonic_mem_liftsRing _ (monic_X_pow 2) (X2_mem (S := S))
    (Subring.add_mem _ (cst_mem_liftsRing S.O H.Vt_mem) H.Y2_mem)

theorem E_const : MvPowerSeries.constantCoeff (H.E.coeff 0) = 1 := by
  have hY := congrArg (fun P => P.coeff 0) (map_eq_zero_of_mem_ord H.Y2_ord)
  simp only [coeff_map, coeff_zero] at hY
  rw [E, coeff_modByMonic_X_pow _ two_pos, coeff_add, map_add, hY, add_zero, cst,
    coe_mapRingHom, coeff_map, MvPowerSeries.constantCoeff_C, H.Vt_coeff_zero]

theorem exists_Ei : ∃ Ei ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O),
    (X ^ 2 : (A2 K)[X]) ∣ H.E * Ei - 1 :=
  exists_inv_mod_X2 H.E_mem (by rw [H.E_const, inv_one]; exact S.O.one_mem)
    (by rw [H.E_const]; exact one_ne_zero)

/-- An inverse of `E` modulo `X²`. -/
noncomputable def Ei : (A2 K)[X] := H.exists_Ei.choose

theorem Ei_mem : H.Ei ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) := H.exists_Ei.choose_spec.1
theorem Ei_dvd : (X ^ 2 : (A2 K)[X]) ∣ H.E * H.Ei - 1 := H.exists_Ei.choose_spec.2

/-- The integral `Z̃' = (-(Q̃w₂ u_s u_s' E⁻¹)) mod X²`. -/
noncomputable def Zt : (A2 K)[X] := (-(C (H.Qw.coeff 2) * uLR * H.Ei)) %ₘ X ^ 2

theorem Qw2_mem : C (H.Qw.coeff 2) ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  liftsRing_of_coeff_mem_intSeries fun n => by
    rw [coeff_C]; split_ifs
    · exact coeff_mem_intSeries_of_liftsRing H.Qw_mem 2
    · exact Subring.zero_mem _

theorem Zt_mem : H.Zt ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  modByMonic_mem_liftsRing _ (monic_X_pow 2) (X2_mem (S := S))
    (Subring.neg_mem _ (Subring.mul_mem _ (Subring.mul_mem _ H.Qw2_mem (uLR_mem (S := S)))
      H.Ei_mem))

theorem wt_coeff_zero_const : MvPowerSeries.constantCoeff (H.wt.coeff 0) ≠ 0 := by
  have h := congrArg MvPowerSeries.constantCoeff (rescale_coeff_of_tw (pw_ne S a) H.tw_w 0)
  rw [FurioLombardo.Vendor.Toolbox.Conv.constantCoeff_rescale', map_mul, MvPowerSeries.constantCoeff_C] at h
  intro h0
  rw [h0, mul_zero] at h
  exact S.a0_ne h

theorem wt_ne : H.wt ≠ 0 := by
  intro h
  apply H.wt_coeff_zero_const
  rw [h, coeff_zero, map_zero]

theorem cst_mod : cst (σ := Fin 2 ⊕ Fin 2) (H.Vt %ₘ X ^ 2) = cst H.Vt %ₘ X ^ 2 := by
  rw [cst, coe_mapRingHom, map_modByMonic _ (monic_X_pow 2), Polynomial.map_pow, Polynomial.map_X]

/-- **`Z` after transport**: `2 b / p²` times the integral `Z̃'`. -/
theorem tw_Z : tw (wt2 (pw S a)) (pw S a) S.Z = C (MvPowerSeries.C (2 * H.b / pw S a ^ 2)) * H.Zt := by
  have hp := pw_ne S a
  set T := tw (wt2 (pw S a)) (pw S a) with hT
  set Zs := C (MvPowerSeries.C (pw S a ^ 2 / H.b)) * T S.Z with hZs
  set rc := cst (σ := Fin 2 ⊕ Fin 2) H.Vt %ₘ X ^ 2 with hrc
  -- the branch condition of `W` at `X²`, transported
  have D5 : (X ^ 2 : (A2 K)[X]) ∣ -H.VV + H.wt * Zs + rc := by
    have h := _root_.map_dvd T S.X2_dvd_W_add_v0
    rw [tw_X_pow, Setup.W, map_add, map_add, map_neg, map_mul, H.tw_V, H.tw_w, tw_cst, H.v0_comp,
      map_mul, cst_C, H.cst_mod] at h
    refine dvd_of_C_mul_dvd_C_mul (pow_ne_zero 2 hp) ?_ H.hb
    convert h using 1
    rw [hZs]
    have e : H.b * (pw S a ^ 2 / H.b) = pw S a ^ 2 := by field_simp [H.hb]
    have E := congrArg (fun x => (C (MvPowerSeries.C (σ := Fin 2 ⊕ Fin 2) x) : (A2 K)[X])) e
    simp only [map_mul] at E
    linear_combination (H.wt * T S.Z) * E
  have D1 : (X ^ 2 : (A2 K)[X]) ∣ rc + H.VV - 2 * H.E := by
    have h1 := modByMonic_add_div (cst (σ := Fin 2 ⊕ Fin 2) H.Vt) (X ^ 2)
    have h2 := modByMonic_add_div (cst (σ := Fin 2 ⊕ Fin 2) H.Vt + H.Y2) (X ^ 2)
    refine ⟨-(cst H.Vt /ₘ X ^ 2) + 2 * ((cst H.Vt + H.Y2) /ₘ X ^ 2), ?_⟩
    rw [hrc, VV, E]
    linear_combination h1 - 2 * h2
  have D2 : (X ^ 2 : (A2 K)[X]) ∣ cst H.ft - rc ^ 2 := by
    have h1 := modByMonic_add_div (cst (σ := Fin 2 ⊕ Fin 2) H.Vt) (X ^ 2)
    have hf := congrArg (cst (σ := Fin 2 ⊕ Fin 2)) H.ft_sub
    simp only [map_sub, map_mul, map_pow, map_ofNat, cst, coe_mapRingHom, Polynomial.map_X] at hf
    refine ⟨4 * X ^ 2 * cst H.q + (cst H.Vt /ₘ X ^ 2) * (cst H.Vt + rc), ?_⟩
    rw [hrc]
    simp only [cst, coe_mapRingHom] at h1 ⊢
    linear_combination hf + (-(Polynomial.map MvPowerSeries.C H.Vt) -
      Polynomial.map MvPowerSeries.C H.Vt %ₘ X ^ 2) * h1
  have D3 : cst H.ft - H.VV ^ 2 = 4 * (uLR * H.Qw) := by
    rw [H.ft_sub_VV, H.Nw_eq, show (C (MvPowerSeries.C (4 : K)) : (A2 K)[X]) = 4 by
      rw [map_ofNat, map_ofNat]]
  obtain ⟨k5, hk5⟩ := D5
  obtain ⟨k1, hk1⟩ := D1
  obtain ⟨k2, hk2⟩ := D2
  obtain ⟨k4, hk4⟩ := H.Ei_dvd
  have hQ := H.Qw_eq_wt
  -- `X² ∣ w̃ (Zs + 2 Q̃w₂ u_s u_s' E⁻¹)`
  have key : (X ^ 2 : (A2 K)[X]) ∣ H.wt * (Zs + 2 * (C (H.Qw.coeff 2) * uLR * H.Ei)) := by
    refine dvd_of_dvd_C_mul (e := 2) S.h2 ⟨2 * k5 + H.Ei * k2 + (rc - H.VV) * H.Ei * k1 +
      2 * (rc - H.VV) * k4, ?_⟩
    rw [show (C (MvPowerSeries.C (2 : K)) : (A2 K)[X]) = 2 by rw [map_ofNat, map_ofNat]]
    linear_combination 2 * hk5 + H.Ei * hk2 + (rc - H.VV) * H.Ei * hk1 + 2 * (rc - H.VV) * hk4 +
      -(H.Ei * D3) - (4 * uLR * H.Ei) * hQ
  have key2 : (X ^ 2 : (A2 K)[X]) ∣ Zs + 2 * (C (H.Qw.coeff 2) * uLR * H.Ei) :=
    dvd_of_dvd_mul_of_map (monic_X_pow 2) X2_map H.wt_coeff_zero_const key
  -- `Zs` is the remainder
  have hZsd : Zs.degree < 2 := lt_of_le_of_lt (degree_CC_mul_le _ _) (by
    rw [hT, degree_tw _ hp (wt2_ne_zero hp)]; exact S.Z_degree)
  have hZs2 : Zs = C (MvPowerSeries.C 2) * H.Zt := by
    rw [Zt, ← C_mul_modByMonic]
    set R := C (MvPowerSeries.C (2 : K)) * -(C (H.Qw.coeff 2) * uLR * H.Ei) with hR
    have hdiv := modByMonic_add_div R (X ^ 2)
    have hdvd : (X ^ 2 : (A2 K)[X]) ∣ Zs - R %ₘ X ^ 2 := by
      obtain ⟨k, hk⟩ := key2
      refine ⟨k + R /ₘ X ^ 2, ?_⟩
      rw [hR, show (C (MvPowerSeries.C (2 : K)) : (A2 K)[X]) = 2 by rw [map_ofNat, map_ofNat]] at hdiv ⊢
      linear_combination hk - hdiv
    have hdeg : (Zs - R %ₘ X ^ 2).degree < (X ^ 2 : (A2 K)[X]).degree := by
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt hZsd ?_)
      have := degree_modByMonic_lt R (monic_X_pow (R := A2 K) 2)
      rwa [degree_X_pow] at this
    exact sub_eq_zero.mp (eq_zero_of_monic_dvd (monic_X_pow 2) hdvd hdeg)
  -- back to `Z`
  have e : (2 * H.b / pw S a ^ 2) = (H.b / pw S a ^ 2) * 2 := by ring
  rw [e, map_mul, C_mul, mul_assoc, ← hZs2, hZs, ← mul_assoc, ← C_mul, ← map_mul]
  rw [show H.b / pw S a ^ 2 * (pw S a ^ 2 / H.b) = 1 by field_simp [H.hb], map_one, C_1, one_mul]

include H in
theorem tInt_Z : TInt S.O (wt2 (pw S a)) (pw S a) (2 * H.b / pw S a ^ 2) S.Z :=
  ⟨H.Zt, H.Zt_mem, H.tw_Z⟩

/-- The integral `W̃ = -Ṽ + 2 w̃ Z̃'`. -/
noncomputable def Wt : (A2 K)[X] := -H.VV + 2 * H.wt * H.Zt

theorem Wt_mem : H.Wt ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  Subring.add_mem _ (Subring.neg_mem _ H.VV_mem) (Subring.mul_mem _
    (Subring.mul_mem _ (two_mem_liftsRing S.O) H.wt_mem) H.Zt_mem)

theorem tw_W : tw (wt2 (pw S a)) (pw S a) S.W = C (MvPowerSeries.C H.b) * H.Wt := by
  rw [Setup.W, map_add, map_neg, map_mul, H.tw_V, H.tw_w, H.tw_Z, Wt]
  have e : pw S a ^ 2 * (2 * H.b / pw S a ^ 2) = H.b * 2 := by field_simp [pw_ne S a]
  have E := congrArg (fun x => (C (MvPowerSeries.C (σ := Fin 2 ⊕ Fin 2) x) : (A2 K)[X])) e
  simp only [map_mul, map_ofNat] at E
  linear_combination (H.wt * H.Zt) * E

include H in
theorem tInt_W : TInt S.O (wt2 (pw S a)) (pw S a) H.b S.W := ⟨H.Wt, H.Wt_mem, H.tw_W⟩

/-! ### `qu`, `c2`, `u2` and the addition series `G` -/

/-- `N2 = Q̃w₂ u_s u_s' + Ṽ Z̃' - w̃ Z̃'²`, with `f̃ - W̃² = 4 w̃ N2`. -/
noncomputable def N2 : (A2 K)[X] :=
  C (H.Qw.coeff 2) * uLR + H.VV * H.Zt - H.wt * H.Zt ^ 2

theorem N2_mem : H.N2 ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  Subring.sub_mem _ (Subring.add_mem _ (Subring.mul_mem _ H.Qw2_mem (uLR_mem (S := S)))
    (Subring.mul_mem _ H.VV_mem H.Zt_mem)) (Subring.mul_mem _ H.wt_mem (Subring.pow_mem _ H.Zt_mem 2))

theorem ft_sub_Wt : cst H.ft - H.Wt ^ 2 = 4 * (H.wt * H.N2) := by
  have D3 : cst H.ft - H.VV ^ 2 = 4 * (uLR * H.Qw) := by
    rw [H.ft_sub_VV, H.Nw_eq, show (C (MvPowerSeries.C (4 : K)) : (A2 K)[X]) = 4 by
      rw [map_ofNat, map_ofNat]]
  rw [Wt, N2]
  linear_combination D3 + (4 * uLR) * H.Qw_eq_wt

/-- The integral quotient `Q̃u = N2 / X²`. -/
noncomputable def Qu : (A2 K)[X] := H.N2 /ₘ X ^ 2

theorem Qu_mem : H.Qu ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  divByMonic_mem_liftsRing (monic_X_pow 2) (X2_mem (S := S)) H.N2_mem

theorem tw_qu : tw (wt2 (pw S a)) (pw S a) S.qu =
    C (MvPowerSeries.C (4 * H.b ^ 2 / pw S a ^ 4)) * H.Qu := by
  have hp := pw_ne S a
  set T := tw (wt2 (pw S a)) (pw S a) with hT
  have h := congrArg T S.f_sub_W_sq
  rw [map_sub, map_pow, H.tw_cst_f, H.tw_W, map_mul, map_mul, H.tw_w, tw_X_pow, mul_pow, ← C_pow,
    ← map_pow, ← mul_sub, H.ft_sub_Wt] at h
  -- cancel `w̃`
  have h1 : X ^ 2 * T S.qu = C (MvPowerSeries.C (4 * H.b ^ 2 / pw S a ^ 4)) * H.N2 := by
    refine eq_of_C_mul_eq (pow_ne_zero 4 hp) H.wt_ne ?_
    rw [show (4 * H.b ^ 2 : K) = H.b ^ 2 * 4 by ring, map_mul, C_mul,
      show pw S a ^ 4 = pw S a ^ 2 * pw S a ^ 2 by ring, map_mul, C_mul,
      show (C (MvPowerSeries.C (4 : K)) : (A2 K)[X]) = 4 by rw [map_ofNat, map_ofNat]]
    linear_combination -h
  have hdvd : (X ^ 2 : (A2 K)[X]) ∣ H.N2 := by
    refine ⟨C (MvPowerSeries.C (pw S a ^ 4 / (4 * H.b ^ 2))) * T S.qu, ?_⟩
    have e : pw S a ^ 4 / (4 * H.b ^ 2) * (4 * H.b ^ 2 / pw S a ^ 4) = 1 := by
      field_simp [hp, H.hb, four_ne S]
    have E := congrArg (fun x => (C (MvPowerSeries.C (σ := Fin 2 ⊕ Fin 2) x) : (A2 K)[X])) e
    simp only [map_mul, map_one] at E
    linear_combination -(C (MvPowerSeries.C (pw S a ^ 4 / (4 * H.b ^ 2)))) * h1 - H.N2 * E
  have hN : H.N2 = X ^ 2 * H.Qu := eq_mul_divByMonic (monic_X_pow 2) hdvd
  rw [hN] at h1
  have hX : (X ^ 2 : (A2 K)[X]) ≠ 0 := pow_ne_zero 2 X_ne_zero
  exact mul_left_cancel₀ hX (by rw [h1]; ring)

theorem tInt_qu : TInt S.O (wt2 (pw S a)) (pw S a) (4 * H.b ^ 2 / pw S a ^ 4) S.qu :=
  ⟨H.Qu, H.Qu_mem, H.tw_qu⟩

theorem rescale_c2 : MvPowerSeries.rescale (wt2 (pw S a)) S.c2 =
    MvPowerSeries.C H.sc1 * H.Qu.coeff 2 :=
  rescale_coeff_of_tw (pw_ne S a) H.tw_qu 2

theorem Qu2_const : MvPowerSeries.constantCoeff (H.Qu.coeff 2) =
    S.c0 * pw S a ^ 6 / (4 * H.b ^ 2) := by
  have h := congrArg MvPowerSeries.constantCoeff H.rescale_c2
  rw [FurioLombardo.Vendor.Toolbox.Conv.constantCoeff_rescale', S.c2_const, map_mul, MvPowerSeries.constantCoeff_C] at h
  have := pw_ne S a; have := H.hb; have := four_ne S
  rw [h]; unfold sc1; field_simp

theorem Qu2_ne : MvPowerSeries.constantCoeff (H.Qu.coeff 2) ≠ 0 := by
  rw [H.Qu2_const]
  exact div_ne_zero (mul_ne_zero S.hc0 (pow_ne_zero 6 (pw_ne S a)))
    (mul_ne_zero (four_ne S) (pow_ne_zero 2 H.hb))

theorem Qu2_inv_mem : (MvPowerSeries.constantCoeff (H.Qu.coeff 2))⁻¹ ∈ S.O := by
  rw [H.Qu2_const]; exact H.hc0

theorem tIntS_c2 : TIntS S.O (wt2 (pw S a)) H.sc1 S.c2 :=
  ⟨_, coeff_mem_intSeries_of_liftsRing H.Qu_mem 2, H.rescale_c2⟩

theorem tIntS_c2_inv : TIntS S.O (wt2 (pw S a)) H.sc1⁻¹ S.c2⁻¹ :=
  tIntS_inv H.sc1_ne (coeff_mem_intSeries_of_liftsRing H.Qu_mem 2) H.Qu2_inv_mem H.Qu2_ne
    H.rescale_c2

/-- The integral monic quadratic `ũ2 = Q̃u / Q̃u₂`. -/
noncomputable def ut2 : (A2 K)[X] := C (H.Qu.coeff 2)⁻¹ * H.Qu

theorem ut2_mem : H.ut2 ∈ liftsRing (incl (σ := Fin 2 ⊕ Fin 2) S.O) :=
  Subring.mul_mem _ (liftsRing_of_coeff_mem_intSeries fun n => by
      rw [coeff_C]; split_ifs
      · exact inv_mem_intSeries (coeff_mem_intSeries_of_liftsRing H.Qu_mem 2)
          H.Qu2_inv_mem H.Qu2_ne
      · exact Subring.zero_mem _) H.Qu_mem

theorem tw_u2 : tw (wt2 (pw S a)) (pw S a) S.u2 = C (MvPowerSeries.C (pw S a ^ 2)) * H.ut2 := by
  rw [Setup.u2, tw_C_mul, FurioLombardo.Vendor.Toolbox.Conv.rescale_inv _ S.c2_ne, H.rescale_c2,
    inv_C_mul H.sc1_ne H.Qu2_ne, H.tw_qu, ut2]
  have e : H.sc1⁻¹ * (4 * H.b ^ 2 / pw S a ^ 4) = pw S a ^ 2 := by
    have := pw_ne S a; have := H.hb; have := four_ne S; unfold sc1; field_simp
  have E : C (MvPowerSeries.C H.sc1⁻¹) * C (MvPowerSeries.C (4 * H.b ^ 2 / pw S a ^ 4)) =
      (C (MvPowerSeries.C (pw S a ^ 2)) : (A2 K)[X]) := by
    rw [← C_mul, ← map_mul, e]
  rw [C_mul]
  linear_combination (C (H.Qu.coeff 2)⁻¹ * H.Qu) * E

include H in
theorem tIntS_G (i : Fin 2) : TIntS S.O (wt2 (pw S a)) (pw S a ^ 2 / pw S a ^ (1 - (i : ℕ)))
    (S.G i) := by
  fin_cases i
  · exact ⟨_, coeff_mem_intSeries_of_liftsRing H.ut2_mem 1,
      rescale_coeff_of_tw (pw_ne S a) H.tw_u2 1⟩
  · exact ⟨_, coeff_mem_intSeries_of_liftsRing H.ut2_mem 0,
      rescale_coeff_of_tw (pw_ne S a) H.tw_u2 0⟩

end IntModel
/-! ## `Adm (4 a)` -/

theorem hl1 (S : Setup K) (a : ℕ) :
    ∀ i, ∃ r ∈ S.O, (S.π : K) ^ (4 * a) = r * wt1 (pw S a) i := by
  intro i
  fin_cases i
  · exact ⟨(S.π : K) ^ (3 * a), S.O.pow_mem S.π.2 _, by
      simp only [wt1, pw, Fin.zero_eta, Matrix.cons_val_zero]; rw [← pow_add]; ring_nf⟩
  · exact ⟨(S.π : K) ^ (2 * a), S.O.pow_mem S.π.2 _, by
      simp only [wt1, pw, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← pow_mul, ← pow_add]; ring_nf⟩

theorem hl2 (S : Setup K) (a : ℕ) :
    ∀ i, ∃ r ∈ S.O, (S.π : K) ^ (4 * a) = r * wt2 (pw S a) i := by
  rintro (i | i)
  · exact hl1 S a i
  · exact hl1 S a i

theorem hlG (S : Setup K) (a : ℕ) :
    ∀ i, ∃ r ∈ S.O, pw S a ^ 2 = r * wt2 (pw S a) i := by
  have h1 : ∀ i, ∃ r ∈ S.O, pw S a ^ 2 = r * wt1 (pw S a) i := by
    intro i
    fin_cases i
    · exact ⟨pw S a, pw_mem S a, by simp only [wt1, Fin.zero_eta, Matrix.cons_val_zero]; ring⟩
    · exact ⟨1, S.O.one_mem, by
        simp only [wt1, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]; ring⟩
  rintro (i | i)
  · exact h1 i
  · exact h1 i

/-- **R7's `Adm (4 a)` from an integral model.** -/
theorem adm_of_intModel {S : Setup K} {a : ℕ} (H : IntModel S a) : S.Adm (4 * a) where
  good := by
    refine ⟨2 * a, by omega, fun i d => ?_⟩
    have hc : pw S a ^ 2 / pw S a ^ (1 - (i : ℕ)) ∈ S.O := by
      have hp := pw_ne S a
      fin_cases i
      · show pw S a ^ 2 / pw S a ^ (1 - 0) ∈ S.O
        rw [Nat.sub_zero, pow_one, pow_two, mul_div_cancel_right₀ _ hp]
        exact pw_mem S a
      · show pw S a ^ 2 / pw S a ^ (1 - 1) ∈ S.O
        rw [Nat.sub_self, pow_zero, div_one]
        exact S.O.pow_mem (pw_mem S a) 2
    have := pow_mul_coeff_mem_of_tIntS (hlG S a) hc (H.tIntS_G i) d
    rwa [pw, ← pow_mul, ← pow_mul, show a * (2 * d.degree) = 2 * a * d.degree by ring] at this
  v := mem_LR.mpr fun n => coeff_mem_bddR_of_tInt S.hπ0 S.hbd (pw_ne S a) (hl1 S a)
    ⟨H.vt, H.vt_mem, H.tw_v⟩ n
  r := mem_bddR_of_tIntS S.hπ0 S.hbd (hl1 S a) H.tIntS_R1_inv
  V := mem_LR.mpr fun n => coeff_mem_bddR_of_tInt S.hπ0 S.hbd (pw_ne S a) (hl2 S a)
    ⟨H.VV, H.VV_mem, H.tw_V⟩ n
  W := mem_LR.mpr fun n => coeff_mem_bddR_of_tInt S.hπ0 S.hbd (pw_ne S a) (hl2 S a) H.tInt_W n
  w := mem_LR.mpr fun n => coeff_mem_bddR_of_tInt S.hπ0 S.hbd (pw_ne S a) (hl2 S a) H.tInt_w n
  c1 := mem_bddR_of_tIntS S.hπ0 S.hbd (hl2 S a) H.tIntS_c1
  c1' := mem_bddR_of_tIntS S.hπ0 S.hbd (hl2 S a) H.tIntS_c1_inv
  c2 := mem_bddR_of_tIntS S.hπ0 S.hbd (hl2 S a) H.tIntS_c2
  c2' := mem_bddR_of_tIntS S.hπ0 S.hbd (hl2 S a) H.tIntS_c2_inv

end FurioLombardo.Discharge.M4Log.Model
