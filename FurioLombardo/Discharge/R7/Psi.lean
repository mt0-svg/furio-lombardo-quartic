import Mathlib
import FurioLombardo.Discharge.R7.FGLO
import FurioLombardo.Vendor.Toolbox.PowerSeries.Bounded
import FurioLombardo.Vendor.Toolbox.Polynomial.SubPoly
import FurioLombardo.Vendor.Toolbox.PowerSeries.BoundedRes

/-!
# The pointwise chart of the formal group (item R7)

For a `Setup K` whose ring `O` is a complete local ring with the adic topology, and an admissible
exponent `M` (`Setup.Adm`), a point `z` of the formal group `S.fglO` (a pair of elements of the
maximal ideal) gives the Mumford pair `u = X² + π^M z₀ X + π^M z₁`, `v = v(π^M z)` over `K`
(`tPt`, `vPt`), whose class `chartCls z` lies in `Jac f`. The map
`psi z = chartCls z · E0⁻¹` is an injective homomorphism from the points of `S.fglO` to
`Jac f` (`psi`, `psi_injective`).

The addition law at points (`chartCls_add`) is the formal law of `Formal.lean` evaluated at
`(π^M z, π^M w)`. Series are evaluated through the subrings `bddR σ π l` of series `G` with
`G(l t)` of bounded denominators (`evS`), and polynomials over such a subring through
`FurioLombardo.Vendor.Toolbox.SubPoly.evR`; the identities of `Formal.lean` are first lifted to polynomials over the
subring (`law_sub`), then mapped (`law_poly`).
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.Conv FurioLombardo.Vendor.Toolbox.SqrtMod FurioLombardo.Vendor.Toolbox.FGLResc FurioLombardo.Vendor.Toolbox.Bounded
  FurioLombardo.Vendor.Toolbox.SubPoly

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.R7

/-! ### Translated chart classes -/

section Cls

variable {L : Type*} [Field L] (fL : L[X]) [GoodSextic fL]

theorem monic_uT_comp (a : L) (t : Fin 2 → L) : ((uT t).comp (X - C a)).Monic :=
  (uT_monic t).comp (monic_X_sub_C a) (by rw [natDegree_X_sub_C]; exact one_ne_zero)

theorem natDegree_uT_comp (a : L) (t : Fin 2 → L) : ((uT t).comp (X - C a)).natDegree = 2 := by
  rw [natDegree_comp, uT_natDegree, natDegree_X_sub_C]

/-- The class of `⟨u(X - a), Y - v(X - a)⟩` for `u = X² + t₀ X + t₁`: the chart class of
`(t, v)` for the model translated by `a`. -/
noncomputable def clsA (a : L) (t : Fin 2 → L) (v : L[X]) : ClassGroup (CoordRing fL) :=
  ClassGroup.mk0 (mumford0 fL (monic_uT_comp a t).ne_zero (v.comp (X - C a)))

theorem comp_sub_comp_add (a : L) (p : L[X]) : (p.comp (X - C a)).comp (X + C a) = p := by
  rw [comp_assoc, sub_comp, X_comp, C_comp, add_sub_cancel_right, comp_X]

/-- Chart injectivity for translated classes. -/
theorem eq_of_clsA_eq {a : L} {f0 : L[X]} (hf : f0.comp (X - C a) = fL) {t1 t2 : Fin 2 → L}
    {v1 v2 : L[X]} (h1 : uT t1 ∣ f0 - v1 ^ 2) (h2 : uT t2 ∣ f0 - v2 ^ 2)
    (h : clsA fL a t1 v1 = clsA fL a t2 v2) : t1 = t2 := by
  have hd : ∀ {t : Fin 2 → L} {v : L[X]}, uT t ∣ f0 - v ^ 2 →
      (uT t).comp (X - C a) ∣ (v.comp (X - C a)) ^ 2 - fL := fun {t v} hd => by
    have := map_dvd (compRingHom (X - C a)) hd
    simp only [coe_compRingHom_apply, sub_comp, pow_comp, hf] at this
    have h2 := (dvd_neg).mpr this
    rwa [neg_sub] at h2
  have := (eq_of_mk0_mumford_eq fL (monic_uT_comp a t1) (monic_uT_comp a t2)
    (natDegree_uT_comp a t1) (natDegree_uT_comp a t2) (hd h1) (hd h2) h).1
  have hu := congrArg (fun p => p.comp (X + C a)) this
  simp only [comp_sub_comp_add] at hu
  have e1 := congrArg (fun p => p.coeff 1) hu
  have e0 := congrArg (fun p => p.coeff 0) hu
  simp only [uT, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at e1 e0
  funext i
  fin_cases i
  · simpa using e1
  · simpa using e0

/-- **The addition law from identities over a ring `R`**, mapped to `L` by `Φ` and translated
by `a`. -/
theorem law_poly {R : Type*} [CommRing R] (Φ : R →+* L) (a : L) (v0 : L[X])
    {fR V W w vL vR vG v0R : R[X]} {tL tR tG : Fin 2 → R} {c1 c2 : R}
    (hf : (fR.map Φ).comp (X - C a) = fL) (hv0 : v0R.map Φ = v0)
    (hVL : uT tL ∣ V - vL) (hVR : uT tR ∣ V - vR) (hWV : w ∣ W + V)
    (hWX : (X ^ 2 : R[X]) ∣ W + v0R) (hWu : uT tG ∣ vG + W)
    (hV : fR - V ^ 2 = C c1 * (uT tL * uT tR * w))
    (hW : fR - W ^ 2 = C c2 * (w * X ^ 2 * uT tG)) (hc1 : Φ c1 ≠ 0) (hc2 : Φ c2 ≠ 0) :
    clsA fL a (Φ ∘ tL) (vL.map Φ) * clsA fL a (Φ ∘ tR) (vR.map Φ) =
      clsA fL a 0 v0 * clsA fL a (Φ ∘ tG) (vG.map Φ) := by
  set T := compRingHom (X - C a)
  have hT : ∀ p : L[X], T p = p.comp (X - C a) := fun p => coe_compRingHom_apply _ _
  have hTC : ∀ c : L, T (C c) = C c := fun c => by rw [hT, C_comp]
  have hTuT0 : T (uT 0) = T X ^ 2 := by rw [uT_zero, map_pow]
  have hVu := map_dvd T (Polynomial.map_dvd Φ hVL)
  have hVu' := map_dvd T (Polynomial.map_dvd Φ hVR)
  have hWw := map_dvd T (Polynomial.map_dvd Φ hWV)
  have hWX' := map_dvd T (Polynomial.map_dvd Φ hWX)
  have hWu' := map_dvd T (Polynomial.map_dvd Φ hWu)
  rw [Polynomial.map_sub, map_uT, map_sub] at hVu hVu'
  rw [Polynomial.map_add, map_add] at hWw
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, hv0, map_add,
    show (X ^ 2 : L[X]) = uT 0 from uT_zero.symm] at hWX'
  rw [Polynomial.map_add, map_uT, map_add] at hWu'
  have hV' : (T (V.map Φ)) ^ 2 - fL =
      C (-Φ c1) * (T (uT (Φ ∘ tL)) * T (uT (Φ ∘ tR)) * T (w.map Φ)) := by
    have := congrArg (fun p => T (p.map Φ)) hV
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
      map_uT, map_sub, map_pow, map_mul, hTC] at this
    rw [hT (fR.map Φ), hf] at this
    rw [C_neg]
    linear_combination -this
  have hW' : (T (W.map Φ)) ^ 2 - fL =
      C (-Φ c2) * (T (w.map Φ) * T (uT 0) * T (uT (Φ ∘ tG))) := by
    have := congrArg (fun p => T (p.map Φ)) hW
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, map_uT, map_sub, map_pow, map_mul, hTC] at this
    rw [hT (fR.map Φ), hf] at this
    rw [hTuT0, C_neg]
    linear_combination -this
  have law := mk0_add_law fL (neg_ne_zero.mpr hc1) (neg_ne_zero.mpr hc2)
    (monic_uT_comp a _).ne_zero (monic_uT_comp a _).ne_zero (monic_uT_comp a 0).ne_zero
    (monic_uT_comp a _).ne_zero (hT _ ▸ hVu) (hT _ ▸ hVu') hV' hWw hWX' hW' hWu'
  simp only [hT] at law
  exact law

end Cls

/-! ### Coprimality and parity of a chart class -/

section Parity

variable {L : Type*} [Field L]

/-- The resultant of `X² + t₀ X + t₁` and `v₁ X + v₀`. -/
noncomputable def resQ (t : Fin 2 → L) (v : L[X]) : L :=
  v.coeff 0 ^ 2 - t 0 * v.coeff 0 * v.coeff 1 + t 1 * v.coeff 1 ^ 2

theorem eq_linear_of_degree_lt_two {v : L[X]} (hv : v.degree < 2) :
    v = C (v.coeff 1) * X + C (v.coeff 0) := by
  ext n
  rcases n with _ | _ | n
  · simp
  · simp
  · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hv (by exact_mod_cast (by omega : 2 ≤ n + 2)))]
    simp

/-- A quadratic `uT t` and a polynomial `v` of degree `< 2` with nonzero resultant are
coprime. -/
theorem isCoprime_uT (t : Fin 2 → L) {v : L[X]} (hv : v.degree < 2) (hr : resQ t v ≠ 0) :
    IsCoprime (uT t) v := by
  set a := v.coeff 1
  set b := v.coeff 0
  have hv' : v = C a * X + C b := eq_linear_of_degree_lt_two hv
  have hr' : resQ t v = b ^ 2 - t 0 * b * a + t 1 * a ^ 2 := rfl
  have key : C (a ^ 2) * uT t + (-(C a * X) + C (b - t 0 * a)) * v = C (resQ t v) := by
    rw [hr', hv', uT]
    simp only [map_sub, map_mul, map_pow, map_add]
    ring
  have hinv : C (resQ t v)⁻¹ * C (resQ t v) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hr, C_1]
  exact ⟨C (resQ t v)⁻¹ * C (a ^ 2), C (resQ t v)⁻¹ * (-(C a * X) + C (b - t 0 * a)),
    by linear_combination C (resQ t v)⁻¹ * key + hinv⟩

variable (fL : L[X]) [GoodSextic fL]

/-- A translated chart class with nonzero resultant has even degree. -/
theorem clsA_mem_Jac {a : L} {f0 : L[X]} (hf : f0.comp (X - C a) = fL) (t : Fin 2 → L)
    {v : L[X]} (hv : v.degree < 2) (hd : uT t ∣ f0 - v ^ 2) (hr : resQ t v ≠ 0) :
    clsA fL a t v ∈ Jac fL := by
  obtain ⟨q, hq⟩ := hd
  have hq' := congrArg (fun p => p.comp (X - C a)) hq
  simp only [sub_comp, pow_comp, mul_comp, hf] at hq'
  have hw : (v.comp (X - C a)) ^ 2 - fL = (uT t).comp (X - C a) * (-(q.comp (X - C a))) := by
    linear_combination -hq'
  obtain ⟨a', b', hab⟩ := (isCoprime_uT t hv hr).map (compRingHom (X - C a))
  have hp := parity_mumford fL (monic_uT_comp a t) hw
    ⟨a', b', 0, by
      rw [zero_mul, add_zero, ← coe_compRingHom_apply, ← coe_compRingHom_apply]; exact hab⟩
  rw [natDegree_uT_comp] at hp
  change parity fL (clsA fL a t v) = 1
  exact hp

end Parity

end FurioLombardo.Discharge.R7


/-! ### The law over a subring of `K⟦s, s'⟧` -/

namespace FurioLombardo.Vendor.Toolbox.G2Formal.Setup

open FurioLombardo.Discharge.R7

variable {K : Type*} [Field K] (S : Setup K)

/-- **The addition law through a homomorphism from a subring** `B` of `K⟦s, s'⟧` containing the
data of the law. -/
theorem law_sub (F : K[X]) [GoodSextic F] (a : K) (hF : S.f.comp (X - C a) = F)
    (B : Subring (A2 K)) (Φ2 : B →+* K)
    (hC : ∀ a : K, (MvPowerSeries.C a : A2 K) ∈ B) (hΦC : ∀ a, Φ2 ⟨_, hC a⟩ = a)
    (hX : ∀ j, (MvPowerSeries.X j : A2 K) ∈ B) (hG : ∀ i, S.G i ∈ B)
    (hV : S.V ∈ LR B) (hW : S.W ∈ LR B) (hw : S.w ∈ LR B)
    (hvL : S.vL ∈ LR B) (hvR : S.vR ∈ LR B) (hvG : S.vG ∈ LR B)
    (hc1 : S.c1 ∈ B) (hc1' : S.c1⁻¹ ∈ B) (hc2 : S.c2 ∈ B) (hc2' : S.c2⁻¹ ∈ B) :
    clsA F a (fun i => Φ2 ⟨_, hX (Sum.inl i)⟩) (evR B Φ2 ⟨S.vL, hvL⟩) *
        clsA F a (fun i => Φ2 ⟨_, hX (Sum.inr i)⟩) (evR B Φ2 ⟨S.vR, hvR⟩) =
      clsA F a 0 S.v0 * clsA F a (fun i => Φ2 ⟨_, hG i⟩) (evR B Φ2 ⟨S.vG, hvG⟩) := by
  have hcst : ∀ p : K[X], cst (σ := Fin 2 ⊕ Fin 2) p ∈ LR B := fun p =>
    map_mem_LR B MvPowerSeries.C hC p
  have hml : ∀ (P : (A2 K)[X]) (hP : P ∈ LR B), ((liftE B).symm ⟨P, hP⟩).map B.subtype = P :=
    fun P hP => map_liftE_symm B ⟨P, hP⟩
  have inj : Function.Injective (Polynomial.map (B.subtype)) :=
    Polynomial.map_injective _ Subtype.val_injective
  have hcf : ∀ p : K[X], ((liftE B).symm ⟨cst p, hcst p⟩).map Φ2 = p := fun p =>
    (evR_map B Φ2 MvPowerSeries.C hC (RingHom.id K) hΦC p (hcst p)).trans (Polynomial.map_id)
  let tL : Fin 2 → B := fun i => ⟨_, hX (Sum.inl i)⟩
  let tR : Fin 2 → B := fun i => ⟨_, hX (Sum.inr i)⟩
  let tG : Fin 2 → B := fun i => ⟨_, hG i⟩
  have huL : (uT tL).map B.subtype = uL := by rw [map_uT]; rfl
  have huR : (uT tR).map B.subtype = uR := by rw [map_uT]; rfl
  have huG : (uT tG).map B.subtype = S.u2 := by rw [map_uT, S.u2_eq]; rfl
  have hne : ∀ (c : A2 K) (hc : c ∈ B) (hc' : c⁻¹ ∈ B), MvPowerSeries.constantCoeff c ≠ 0 →
      Φ2 ⟨c, hc⟩ ≠ 0 := by
    intro c hc hc' h0
    have h : (⟨c, hc⟩ : B) * ⟨c⁻¹, hc'⟩ = 1 := Subtype.ext (MvPowerSeries.mul_inv_cancel _ h0)
    have := congrArg Φ2 h
    rw [map_mul, map_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hwm : ((liftE B).symm ⟨S.w, hw⟩).Monic :=
    monic_of_injective Subtype.val_injective (by rw [hml]; exact S.w_monic.1)
  refine law_poly F Φ2 a S.v0 (by rw [hcf S.f]; exact hF) (hcf S.v0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hne _ hc1 hc1' S.c1_ne) (hne _ hc2 hc2' S.c2_ne)
    (tL := tL) (tR := tR) (tG := tG) (V := (liftE B).symm ⟨S.V, hV⟩)
    (W := (liftE B).symm ⟨S.W, hW⟩) (w := (liftE B).symm ⟨S.w, hw⟩)
    (vL := (liftE B).symm ⟨S.vL, hvL⟩) (vR := (liftE B).symm ⟨S.vR, hvR⟩)
    (vG := (liftE B).symm ⟨S.vG, hvG⟩) (c1 := ⟨S.c1, hc1⟩) (c2 := ⟨S.c2, hc2⟩)
  · refine (map_dvd_map B.subtype Subtype.val_injective (uT_monic _)).mp ?_
    rw [huL, Polynomial.map_sub, hml, hml]
    exact S.uL_dvd_V_sub
  · refine (map_dvd_map B.subtype Subtype.val_injective (uT_monic _)).mp ?_
    rw [huR, Polynomial.map_sub, hml, hml]
    exact S.uR_dvd_V_sub
  · refine (map_dvd_map B.subtype Subtype.val_injective hwm).mp ?_
    rw [Polynomial.map_add, hml, hml, hml]
    exact ⟨S.Z, S.W_add_V⟩
  · refine (map_dvd_map B.subtype Subtype.val_injective (monic_X_pow 2)).mp ?_
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, hml, hml]
    exact S.X2_dvd_W_add_v0
  · refine (map_dvd_map B.subtype Subtype.val_injective (uT_monic _)).mp ?_
    rw [huG, Polynomial.map_add, hml, hml]
    exact S.u2_dvd_vG_add_W
  · apply inj
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_C, hml, hml, hml, huL, huR]
    exact S.f_sub_V_sq_eq
  · apply inj
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hml, hml, hml,
      huG]
    exact S.f_sub_W_sq_eq

/-! ### Admissible exponents -/

/-- The subring of evaluation at scale `π ^ M`, one set of variables. -/
noncomputable abbrev B1 (M : ℕ) : Subring (MvPowerSeries (Fin 2) K) :=
  bddR (Fin 2) S.π ((S.π : K) ^ M)

/-- The subring of evaluation at scale `π ^ M`, two sets of variables. -/
noncomputable abbrev B2 (M : ℕ) : Subring (A2 K) := bddR (Fin 2 ⊕ Fin 2) S.π ((S.π : K) ^ M)

/-- The resultant of the chart pair `(u_t, v)` over `K⟦t⟧`. -/
noncomputable def R1 : MvPowerSeries (Fin 2) K :=
  S.v.coeff 0 ^ 2 - MvPowerSeries.X 0 * S.v.coeff 0 * S.v.coeff 1 +
    MvPowerSeries.X 1 * S.v.coeff 1 ^ 2

theorem v_coeff_zero_const : MvPowerSeries.constantCoeff (S.v.coeff 0) = S.V0.coeff 0 := by
  have := congrArg (fun p => p.coeff 0) S.v_map
  simp only [coeff_map] at this
  rw [this, S.v0_coeff_zero]

theorem R1_const : MvPowerSeries.constantCoeff S.R1 = S.V0.coeff 0 ^ 2 := by
  simp [R1, S.v_coeff_zero_const]

theorem R1_mem : S.R1 ∈ conv S.O S.π (Fin 2) := by
  have h := mem_convPoly.mp S.v_mem
  exact Subring.add_mem _ (Subring.sub_mem _ (Subring.pow_mem _ (h 0) 2)
    (Subring.mul_mem _ (Subring.mul_mem _ (X_mem_conv 0) (h 0)) (h 1)))
    (Subring.mul_mem _ (X_mem_conv 1) (Subring.pow_mem _ (h 1) 2))

theorem R1_inv_mem : S.R1⁻¹ ∈ conv S.O S.π (Fin 2) :=
  inv_mem_conv S.hbd S.R1_mem (by rw [S.R1_const]; exact pow_ne_zero 2 S.hV00)

theorem c2_inv_mem : S.c2⁻¹ ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) :=
  inv_mem_conv S.hbd S.c2_mem S.c2_ne

/-- An admissible exponent: the data of the law evaluate at scale `π ^ M`, and the conjugate
formal group law is integral. -/
structure Adm (M : ℕ) : Prop where
  good : S.GoodM M
  v : S.v ∈ LR (S.B1 M)
  r : S.R1⁻¹ ∈ S.B1 M
  V : S.V ∈ LR (S.B2 M)
  W : S.W ∈ LR (S.B2 M)
  w : S.w ∈ LR (S.B2 M)
  c1 : S.c1 ∈ S.B2 M
  c1' : S.c1⁻¹ ∈ S.B2 M
  c2 : S.c2 ∈ S.B2 M
  c2' : S.c2⁻¹ ∈ S.B2 M

theorem exists_adm : ∃ M, S.Adm M := by
  obtain ⟨M0, hM0⟩ := S.exists_goodM
  have hg : ∀ᶠ M in Filter.atTop, S.GoodM M := Filter.eventually_atTop.mpr ⟨M0, hM0⟩
  obtain ⟨M, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    (hg.and <| (eventually_mem_LR S.v_mem).and <| (eventually_mem_bddR S.R1_inv_mem).and <|
      (eventually_mem_LR S.V_mem).and <| (eventually_mem_LR S.W_mem).and <|
      (eventually_mem_LR S.w_mem).and <| (eventually_mem_bddR S.c1_mem).and <|
      (eventually_mem_bddR S.c1_inv_mem).and <| (eventually_mem_bddR S.c2_mem).and <|
      eventually_mem_bddR S.c2_inv_mem).exists
  exact ⟨M, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩

theorem X_mem_B {σ : Type*} (M : ℕ) (j : σ) :
    (MvPowerSeries.X j : MvPowerSeries σ K) ∈ bddR σ S.π ((S.π : K) ^ M) :=
  X_mem_bddR (Subring.pow_mem _ S.π.2 M) j

theorem C_mem_B {σ : Type*} (M : ℕ) (a : K) :
    (MvPowerSeries.C a : MvPowerSeries σ K) ∈ bddR σ S.π ((S.π : K) ^ M) :=
  C_mem_bddR S.hπ0 S.hbd _ a

theorem vL_mem {M : ℕ} (hM : S.Adm M) : S.vL ∈ LR (S.B2 M) := by
  refine mem_LR.mpr fun n => ?_
  rw [vL, coeff_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sb_apply]
  exact rename_mem_bddR Sum.inl (mem_LR.mp hM.v n)

theorem vR_mem {M : ℕ} (hM : S.Adm M) : S.vR ∈ LR (S.B2 M) := by
  refine mem_LR.mpr fun n => ?_
  rw [vR, coeff_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sb_apply]
  exact rename_mem_bddR Sum.inr (mem_LR.mp hM.v n)

variable [CharZero K] [GoodSextic S.f]

theorem rescale_G {M : ℕ} (hM : S.GoodM M) (i : Fin 2) :
    MvPowerSeries.rescale (fun _ => (S.π : K) ^ M) (S.G i) =
      MvPowerSeries.C ((S.π : K) ^ M) * MvPowerSeries.map S.O.subtype ((S.fglO hM).F i) := by
  rw [S.map_fglO_F hM i, ← MvPowerSeries.smul_eq_C_mul, smul_resc (pow_ne_zero M S.hπ0)]

theorem G_mem_B2 {M : ℕ} (hM : S.GoodM M) (i : Fin 2) : S.G i ∈ S.B2 M := by
  rw [mem_bddR, S.rescale_G hM]
  exact intSeries_le_bdd _ (Subring.mul_mem _ (C_mem_intSeries (Subring.pow_mem _ S.π.2 M))
    (map_mem_intSeries _))

/-- The addition series of the integral formal group law, over `K`. -/
noncomputable def famK {M : ℕ} (hM : S.GoodM M) (s : Fin 2) : A2 K :=
  MvPowerSeries.map S.O.subtype ((S.fglO hM).F s)

theorem famK_mem {M : ℕ} (hM : S.GoodM M) (s : Fin 2) :
    S.famK hM s ∈ intSeries S.O (Fin 2 ⊕ Fin 2) := map_mem_intSeries _

theorem famK_const {M : ℕ} (hM : S.GoodM M) (s : Fin 2) :
    MvPowerSeries.constantCoeff (S.famK hM s) = 0 := by
  rw [famK, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, (S.fglO hM).zero_constantCoeff s, map_zero]

theorem rescale_subst_G {M : ℕ} (hM : S.GoodM M) (g : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.rescale (fun _ => (S.π : K) ^ M) (MvPowerSeries.subst S.G g) =
      MvPowerSeries.subst (S.famK hM) (MvPowerSeries.rescale (fun _ => (S.π : K) ^ M) g) := by
  have hb : MvPowerSeries.HasSubst S.G := MvPowerSeries.hasSubst_of_constantCoeff_zero S.G_const
  have hb' : MvPowerSeries.HasSubst (S.famK hM) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (S.famK_const hM)
  rw [← rescale_subst' _ hb, subst_rescale' _ hb']
  congr 1
  funext s
  rw [famK, S.map_fglO_F hM s, smul_resc (pow_ne_zero M S.hπ0)]

theorem vG_mem {M : ℕ} (hM : S.Adm M) : S.vG ∈ LR (S.B2 M) := by
  refine mem_LR.mpr fun n => ?_
  rw [vG, coeff_map]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sb_apply]
  rw [mem_bddR, S.rescale_subst_G hM.good]
  exact subst_mem_bdd (S.famK_mem hM.good) (S.famK_const hM.good) (mem_LR.mp hM.v n)

/-! ### The chart at points -/

section Points

variable [IsLocalRing S.O] [UniformSpace S.O] [Fact (IsAdic (IsLocalRing.maximalIdeal S.O))]
  [IsUniformAddGroup S.O] [CompleteSpace S.O] [T2Space S.O] [IsTopologicalRing S.O]

/-- The first Mumford coordinates of the point `z`: `t = π^M z`. -/
def tPt (M : ℕ) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) : Fin 2 → K :=
  fun i => (S.π : K) ^ M * ((z i : S.O) : K)

/-- The second Mumford coordinate of the point `z`: `v(π^M z)`. -/
noncomputable def vPt {M : ℕ} (hM : S.Adm M) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) : K[X] :=
  evR (S.B1 M) (evS S.hπ0 ((S.π : K) ^ M) z) ⟨S.v, hM.v⟩

theorem coeff_vPt {M : ℕ} (hM : S.Adm M) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) (n : ℕ) :
    (S.vPt hM z).coeff n = evS S.hπ0 ((S.π : K) ^ M) z ⟨S.v.coeff n, mem_LR.mp hM.v n⟩ :=
  coeff_evR _ _ _ n

theorem tPt_eq (M : ℕ) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) (i : Fin 2) :
    S.tPt M z i = evS S.hπ0 ((S.π : K) ^ M) z ⟨MvPowerSeries.X i, S.X_mem_B M i⟩ :=
  (evS_X S.hπ0 (Subring.pow_mem _ S.π.2 M) z i _).symm

theorem vPt_degree {M : ℕ} (hM : S.Adm M) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) :
    (S.vPt hM z).degree < 2 := by
  refine (degree_lt_iff_coeff_zero _ 2).mpr fun m hm => ?_
  rw [coeff_vPt]
  have : (⟨S.v.coeff m, mem_LR.mp hM.v m⟩ : S.B1 M) = 0 :=
    Subtype.ext (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le S.v_degree (by exact_mod_cast hm)))
  rw [this, map_zero]

theorem dvd_pt {M : ℕ} (hM : S.Adm M) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) :
    uT (S.tPt M z) ∣ S.f - (S.vPt hM z) ^ 2 := by
  set B := S.B1 M
  set Φ := evS S.hπ0 ((S.π : K) ^ M) z
  let tX : Fin 2 → B := fun i => ⟨MvPowerSeries.X i, S.X_mem_B M i⟩
  have hu : (uT tX).map B.subtype = u1 := by rw [map_uT]; rfl
  have hcf : cst S.f ∈ LR B := map_mem_LR B MvPowerSeries.C (S.C_mem_B M) S.f
  have hQ : cst S.f - S.v ^ 2 ∈ LR B := Subring.sub_mem _ hcf (Subring.pow_mem _ hM.v 2)
  have hP0 : (uT tX).map B.subtype ∈ LR B := map_mem_LR B B.subtype (fun x => x.2) _
  have hP : (u1 : (MvPowerSeries (Fin 2) K)[X]) ∈ LR B := hu ▸ hP0
  have hd := evR_dvd B Φ hP hQ (uT_monic _) S.u1_dvd
  have e1 : evR B Φ ⟨u1, hP⟩ = uT (S.tPt M z) := by
    have : (⟨u1, hP⟩ : LR B) = ⟨(uT tX).map B.subtype, hP0⟩ := Subtype.ext hu.symm
    rw [this, evR_map B Φ B.subtype (fun x => x.2) Φ (fun x => rfl), map_uT]
    congr 1
    funext i
    exact (S.tPt_eq M z i).symm
  have e2 : evR B Φ ⟨cst S.f - S.v ^ 2, hQ⟩ = S.f - (S.vPt hM z) ^ 2 := by
    have : (⟨cst S.f - S.v ^ 2, hQ⟩ : LR B) = ⟨cst S.f, hcf⟩ - ⟨S.v, hM.v⟩ ^ 2 := rfl
    have e3 : evR B Φ ⟨cst S.f, hcf⟩ = S.f :=
      (evR_map B Φ MvPowerSeries.C (S.C_mem_B M) (RingHom.id K)
        (fun a => evS_C S.hπ0 _ z a _) S.f hcf).trans Polynomial.map_id
    rw [this, map_sub, map_pow, e3]
    rfl
  rwa [e1, e2] at hd

theorem resQ_pt_ne {M : ℕ} (hM : S.Adm M) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) :
    resQ (S.tPt M z) (S.vPt hM z) ≠ 0 := by
  set Φ := evS S.hπ0 ((S.π : K) ^ M) z
  have h0 := mem_LR.mp hM.v 0
  have h1 := mem_LR.mp hM.v 1
  have hR : S.R1 ∈ S.B1 M :=
    Subring.add_mem _ (Subring.sub_mem _ (Subring.pow_mem _ h0 2)
      (Subring.mul_mem _ (Subring.mul_mem _ (S.X_mem_B M 0) h0) h1))
      (Subring.mul_mem _ (S.X_mem_B M 1) (Subring.pow_mem _ h1 2))
  have key : resQ (S.tPt M z) (S.vPt hM z) = Φ ⟨S.R1, hR⟩ := by
    have : (⟨S.R1, hR⟩ : S.B1 M) = ⟨_, h0⟩ ^ 2 - ⟨_, S.X_mem_B M 0⟩ * ⟨_, h0⟩ * ⟨_, h1⟩ +
        ⟨_, S.X_mem_B M 1⟩ * ⟨_, h1⟩ ^ 2 := rfl
    rw [this, resQ, coeff_vPt, coeff_vPt, S.tPt_eq, S.tPt_eq]
    simp only [map_add, map_sub, map_mul, map_pow]
    rfl
  rw [key]
  have h : (⟨S.R1, hR⟩ : S.B1 M) * ⟨S.R1⁻¹, hM.r⟩ = 1 :=
    Subtype.ext (MvPowerSeries.mul_inv_cancel _ (by rw [S.R1_const]; exact pow_ne_zero 2 S.hV00))
  have := congrArg Φ h
  rw [map_mul, map_one] at this
  exact left_ne_zero_of_mul_eq_one this

variable (F : K[X]) [GoodSextic F] (a : K)

/-- The chart class of the point `z`, on the model `F` (translated by `a`). -/
noncomputable def chartCls {M : ℕ} (hM : S.Adm M) (z : Fin 2 → IsLocalRing.maximalIdeal S.O) :
    ClassGroup (CoordRing F) :=
  clsA F a (S.tPt M z) (S.vPt hM z)

variable {F a}

theorem chartCls_mem (hF : S.f.comp (X - C a) = F) {M : ℕ} (hM : S.Adm M)
    (z : Fin 2 → IsLocalRing.maximalIdeal S.O) : S.chartCls F a hM z ∈ Jac F :=
  clsA_mem_Jac F hF _ (S.vPt_degree hM z) (S.dvd_pt hM z) (S.resQ_pt_ne hM z)

theorem E0_mem (hF : S.f.comp (X - C a) = F) : clsA F a 0 S.v0 ∈ Jac F := by
  refine clsA_mem_Jac F hF 0 S.degree_v0 (by rw [uT_zero]; exact S.dvd_f_sub_v0) ?_
  simp only [resQ, Pi.zero_apply, zero_mul, sub_zero, add_zero, S.v0_coeff_zero]
  exact pow_ne_zero 2 S.hV00

end Points

/-! ### The law at points and the chart homomorphism -/

section Psi

variable [IsLocalRing S.O] [UniformSpace S.O] [Fact (IsAdic (IsLocalRing.maximalIdeal S.O))]
  [IsUniformAddGroup S.O] [CompleteSpace S.O] [T2Space S.O] [IsTopologicalRing S.O]
  {F : K[X]} [GoodSextic F] {a : K}

open FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman in
/-- The value of `G(π^M s, π^M s')` at a pair of points is `π^M` times their sum in the
formal group `S.fglO`. -/
theorem evS_G {M : ℕ} (hM : S.GoodM M) (z w : (S.fglO hM).Points) (i : Fin 2) :
    evS S.hπ0 ((S.π : K) ^ M) (Sum.elim z w) ⟨S.G i, S.G_mem_B2 hM i⟩ =
      (S.π : K) ^ M * (((z + w) i : S.O) : K) := by
  set p : Fin 2 ⊕ Fin 2 → IsLocalRing.maximalIdeal S.O := Sum.elim z w
  have hC : (MvPowerSeries.C ((S.π : K) ^ M) : A2 K) ∈ bdd S.O (Fin 2 ⊕ Fin 2) S.π :=
    intSeries_le_bdd _ (C_mem_intSeries (Subring.pow_mem _ S.π.2 M))
  rw [evS_apply, evB_congr S.hπ0 p (H := ⟨_, hC⟩ * ⟨_, map_mem_bdd S.π ((S.fglO hM).F i)⟩)
    (S.rescale_G hM i), map_mul, evB_C, evB_map]
  congr 2
  rw [FormalGroupLaw.add_apply_coe]
  unfold evO
  congr 1
  funext j
  rcases j with j | j <;> rfl

open FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman in
/-- **The addition law at points.** -/
theorem chartCls_add (hF : S.f.comp (X - C a) = F) {M : ℕ} (hM : S.Adm M)
    (z w : (S.fglO hM.good).Points) :
    S.chartCls F a hM z * S.chartCls F a hM w = clsA F a 0 S.v0 * S.chartCls F a hM (z + w) := by
  set p : Fin 2 ⊕ Fin 2 → IsLocalRing.maximalIdeal S.O := Sum.elim z w
  set Φ2 := evS S.hπ0 ((S.π : K) ^ M) p
  have hlaw := S.law_sub F a hF (S.B2 M) Φ2 (S.C_mem_B M) (fun a => evS_C S.hπ0 _ p a _)
    (S.X_mem_B M) (S.G_mem_B2 hM.good) hM.V hM.W hM.w (S.vL_mem hM) (S.vR_mem hM) (S.vG_mem hM)
    hM.c1 hM.c1' hM.c2 hM.c2'
  have eL : (fun i => Φ2 ⟨_, S.X_mem_B M (Sum.inl i)⟩) = S.tPt M z :=
    funext fun i => evS_X S.hπ0 (Subring.pow_mem _ S.π.2 M) p (Sum.inl i) _
  have eR : (fun i => Φ2 ⟨_, S.X_mem_B M (Sum.inr i)⟩) = S.tPt M w :=
    funext fun i => evS_X S.hπ0 (Subring.pow_mem _ S.π.2 M) p (Sum.inr i) _
  have eG : (fun i => Φ2 ⟨_, S.G_mem_B2 hM.good i⟩) = S.tPt M (z + w) :=
    funext fun i => S.evS_G hM.good z w i
  have hL : evR (S.B2 M) Φ2 ⟨S.vL, S.vL_mem hM⟩ = S.vPt hM z := by
    refine evR_eq _ _ fun n => ?_
    rw [S.coeff_vPt hM z n]
    have hn := mem_LR.mp hM.v n
    have e : S.vL.coeff n =
        MvPowerSeries.subst (fun s => (MvPowerSeries.X (Sum.inl s) : A2 K)) (S.v.coeff n) := by
      simp only [vL, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sb_apply]
    calc Φ2 ⟨_, coeff_mem n⟩ = Φ2 ⟨_, rename_mem_bddR Sum.inl hn⟩ := congrArg Φ2 (Subtype.ext e)
      _ = _ := evS_rename S.hπ0 _ p Sum.inl hn
  have hR : evR (S.B2 M) Φ2 ⟨S.vR, S.vR_mem hM⟩ = S.vPt hM w := by
    refine evR_eq _ _ fun n => ?_
    rw [S.coeff_vPt hM w n]
    have hn := mem_LR.mp hM.v n
    have e : S.vR.coeff n =
        MvPowerSeries.subst (fun s => (MvPowerSeries.X (Sum.inr s) : A2 K)) (S.v.coeff n) := by
      simp only [vR, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sb_apply]
    calc Φ2 ⟨_, coeff_mem n⟩ = Φ2 ⟨_, rename_mem_bddR Sum.inr hn⟩ := congrArg Φ2 (Subtype.ext e)
      _ = _ := evS_rename S.hπ0 _ p Sum.inr hn
  have hG : evR (S.B2 M) Φ2 ⟨S.vG, S.vG_mem hM⟩ = S.vPt hM (z + w) := by
    refine evR_eq _ _ fun n => ?_
    rw [S.coeff_vPt hM (z + w) n]
    have hn : MvPowerSeries.rescale (fun _ => (S.π : K) ^ M) (S.v.coeff n) ∈
        bdd S.O (Fin 2) S.π := mem_LR.mp hM.v n
    have hs := subst_mem_bdd (S.famK_mem hM.good) (S.famK_const hM.good) hn
    have hv : MvPowerSeries.rescale (fun _ => (S.π : K) ^ M) (S.vG.coeff n) =
        MvPowerSeries.subst (S.famK hM.good)
          (MvPowerSeries.rescale (fun _ => (S.π : K) ^ M) (S.v.coeff n)) := by
      simp only [vG, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sb_apply]
      exact S.rescale_subst_G hM.good _
    have hfam : (fun s => (⟨evO p (toO (S.famK_mem hM.good s)), evO_mem_maximalIdeal p _ (by
        have h := S.famK_const hM.good s
        rw [← map_toO (S.famK_mem hM.good s), ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPowerSeries.coeff_map] at h
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [Subring.coe_subtype] at h
        exact (show MvPowerSeries.coeff 0 (toO (S.famK_mem hM.good s)) = 0 from
          Subtype.ext h) ▸ Ideal.zero_mem _)⟩ : IsLocalRing.maximalIdeal S.O)) = z + w := by
      funext s
      apply Subtype.ext
      simp only [famK]
      rw [toO_map, FormalGroupLaw.add_apply_coe]
      unfold evO
      congr 1
      funext j
      rcases j with j | j <;> rfl
    calc Φ2 ⟨_, coeff_mem (P := ⟨S.vG, S.vG_mem hM⟩) n⟩ = evB S.hπ0 p ⟨_, hs⟩ :=
          evB_congr S.hπ0 p hv
      _ = _ := evB_subst S.hπ0 p (S.famK_mem hM.good) (S.famK_const hM.good) hn
      _ = evB S.hπ0 (z + w) ⟨_, hn⟩ := by rw [hfam]
  rw [eL, eR, eG, hL, hR, hG] at hlaw
  exact hlaw

/-- **The chart homomorphism** from the points of `S.fglO` to `Jac F`:
`z ↦ [chart class of z] - E0`. -/
noncomputable def psi (hF : S.f.comp (X - C a) = F) {M : ℕ} (hM : S.Adm M) :
    (S.fglO hM.good).Points →+ Additive (Jac F) :=
  AddMonoidHom.mk'
    (fun z => Additive.ofMul ⟨S.chartCls F a hM z * (clsA F a 0 S.v0)⁻¹,
      Subgroup.mul_mem _ (S.chartCls_mem hF hM z) (Subgroup.inv_mem _ (S.E0_mem hF))⟩)
    (fun z w => by
      rw [← ofMul_mul]
      congr 1
      apply Subtype.ext
      have h := S.chartCls_add hF hM z w
      change S.chartCls F a hM (z + w) * (clsA F a 0 S.v0)⁻¹ =
        S.chartCls F a hM z * (clsA F a 0 S.v0)⁻¹ * (S.chartCls F a hM w * (clsA F a 0 S.v0)⁻¹)
      rw [eq_inv_mul_of_mul_eq h.symm]
      simp only [mul_comm, mul_assoc, mul_left_comm])

theorem psi_apply (hF : S.f.comp (X - C a) = F) {M : ℕ} (hM : S.Adm M)
    (z : (S.fglO hM.good).Points) :
    ((Additive.toMul (S.psi hF hM z) : Jac F) : Pic F) =
      S.chartCls F a hM z * (clsA F a 0 S.v0)⁻¹ := rfl

/-- **The chart homomorphism is injective.** -/
theorem psi_injective (hF : S.f.comp (X - C a) = F) {M : ℕ} (hM : S.Adm M) :
    Function.Injective (S.psi hF hM) := by
  intro z w h
  have h1 : S.chartCls F a hM z * (clsA F a 0 S.v0)⁻¹ =
      S.chartCls F a hM w * (clsA F a 0 S.v0)⁻¹ := by
    rw [← S.psi_apply hF hM z, ← S.psi_apply hF hM w, h]
  have ht := eq_of_clsA_eq F hF (S.dvd_pt hM z) (S.dvd_pt hM w) (mul_right_cancel h1)
  funext i
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel₀ (pow_ne_zero M S.hπ0) (congrFun ht i)

end Psi

end FurioLombardo.Vendor.Toolbox.G2Formal.Setup
