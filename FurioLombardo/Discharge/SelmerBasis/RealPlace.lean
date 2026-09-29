import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.SelmerBasis.RealPlaceAux
import FurioLombardo.Discharge.SelmerSpan.Mumford

/-!
# The local image at a real place (twist 0, places 5 and 6)

For a real sextic `f` with `GoodSextic f` (so `lc f < 0`) whose real roots are exactly
`r 0 < r 1 < r 2 < r 3`, the `x - T` image of `A(ℝ) = Jac f` lies in the subgroup `Wr f r hr` of the
classes whose values at the roots satisfy `g(r₀) g(r₃) > 0` and `g(r₁) g(r₂) > 0` (the image
`{1, (+, -, -, +)}` modulo the diagonal). The classes with `u ∣ f` are treated through `muJ_Tpt`,
the classes with `u(r_i) = 0` through one reduction step; `hall` says that the `r i` are all the real
roots of `f`.

Frozen statement (2026-09-28): `imageIn_real`.

Proof: `jac_eq_one_or_reduced` gives `Q = 1` or `Q = [⟨u, Y - v⟩]`. Three cases give a representative
`p` of `μ(Q)` (or of `μ(Q)⁻¹`): `u` coprime to `f` (`p = u`, `muJ_mumfordJac`), `u ∣ f` (`v = 0`,
`p = u - f/u`, `muJ_Tpt`), and otherwise one Cantor step (`p = w/lc w` with `v² - f = u w`, coprime to
`f`, `mumford_mul_mumford_eq_span`). In each case `RealAux.rp_sign_core` gives the sign conditions.
-/

open Polynomial FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M3a FurioLombardo.Discharge.SelmerSpan
  FurioLombardo.Discharge.SelmerBasis.RealAux

namespace FurioLombardo.Discharge.SelmerBasis

/-- Evaluation of `ℝ[T]/(f)` at a real root `r` of `f`. -/
noncomputable def evRoot {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) : AdjoinRoot f →+* ℝ :=
  AdjoinRoot.lift (RingHom.id ℝ) r (by simpa using hr)

/-- The units `g` of `ℝ[T]/(f)` with `g(r₀) g(r₃) > 0` and `g(r₁) g(r₂) > 0`. -/
noncomputable def realSignSub (f : ℝ[X]) (r : Fin 4 → ℝ) (hr : ∀ j, f.IsRoot (r j)) :
    Subgroup (AdjoinRoot f)ˣ where
  carrier := {g | 0 < evRoot (hr 0) g * evRoot (hr 3) g ∧ 0 < evRoot (hr 1) g * evRoot (hr 2) g}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul]
    exact ⟨by nlinarith [mul_pos ha0 hb0], by nlinarith [mul_pos ha1 hb1]⟩
  one_mem' := by
    simp
  inv_mem' := by
    intro a ha
    obtain ⟨ha0, ha1⟩ := ha
    simp only [Set.mem_ofPred_eq, map_units_inv]
    rw [← mul_inv, ← mul_inv]
    exact ⟨inv_pos.mpr ha0, inv_pos.mpr ha1⟩

theorem evRoot_mk {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) (p : ℝ[X]) :
    evRoot hr (AdjoinRoot.mk f p) = p.eval r := by
  rw [evRoot, AdjoinRoot.lift_mk]
  rfl

/-- `ℝ^× (L^×)²` lies in `realSignSub`. -/
theorem sqClass_le_realSignSub (f : ℝ[X]) (r : Fin 4 → ℝ) (hr : ∀ j, f.IsRoot (r j)) :
    sqClass f ≤ realSignSub f r hr := by
  unfold sqClass
  refine sup_le ?_ ?_
  · rintro _ ⟨c, rfl⟩
    have hc : (c : ℝ) ≠ 0 := c.ne_zero
    have e : ∀ j, evRoot (hr j)
        ((Units.map (algebraMap ℝ (AdjoinRoot f)).toMonoidHom c : (AdjoinRoot f)ˣ) :
          AdjoinRoot f) = c := by
      intro j
      rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AdjoinRoot.algebraMap_eq,
        evRoot, AdjoinRoot.lift_of]
      rfl
    show 0 < _ ∧ 0 < _
    rw [e, e, e, e]
    exact ⟨mul_self_pos.mpr hc, mul_self_pos.mpr hc⟩
  · rintro _ ⟨g, rfl⟩
    have hne : ∀ j, evRoot (hr j) (g : AdjoinRoot f) ≠ 0 := fun j =>
      (g.isUnit.map (evRoot (hr j))).ne_zero
    have hsq : ∀ j, 0 < evRoot (hr j) (g : AdjoinRoot f) ^ 2 := fun j =>
      lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (hne j)).symm
    show 0 < _ ∧ 0 < _
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow]
    exact ⟨mul_pos (hsq 0) (hsq 3), mul_pos (hsq 1) (hsq 2)⟩

/-- The subgroup `W_r` of `H f`. -/
noncomputable def Wr (f : ℝ[X]) (r : Fin 4 → ℝ) (hr : ∀ j, f.IsRoot (r j)) : Subgroup (H f) :=
  (realSignSub f r hr).map (QuotientGroup.mk' (sqClass f))

/-- A class represented by `p(T)` with `p(r₀) p(r₃) > 0` and `p(r₁) p(r₂) > 0` lies in `W_r`. -/
theorem mk_mem_Wr (f : ℝ[X]) (r : Fin 4 → ℝ) (hr : ∀ j, f.IsRoot (r j)) (x : (AdjoinRoot f)ˣ)
    (p : ℝ[X]) (hx : (x : AdjoinRoot f) = AdjoinRoot.mk f p)
    (hp : 0 < p.eval (r 0) * p.eval (r 3) ∧ 0 < p.eval (r 1) * p.eval (r 2)) :
    (QuotientGroup.mk x : H f) ∈ Wr f r hr := by
  refine Subgroup.mem_map_of_mem (QuotientGroup.mk' (sqClass f)) (?_ : x ∈ realSignSub f r hr)
  show 0 < _ ∧ 0 < _
  rw [hx, evRoot_mk, evRoot_mk, evRoot_mk, evRoot_mk]
  exact hp

/-- **The local image at a real place.** -/
theorem imageIn_real (f : ℝ[X]) [GoodSextic f] (r : Fin 4 → ℝ) (hmono : StrictMono r)
    (hr : ∀ j, f.IsRoot (r j)) (hall : ∀ x, f.IsRoot x → ∃ j, x = r j) :
    ImageIn f (Wr f r hr) := by
  classical
  -- the sign of `f` on `ℝ` and of `f'` at the roots
  have hsq : Squarefree f := GoodSextic.squarefree
  have hdeg6 : f.natDegree = 6 := GoodSextic.natDegree_eq
  have hlc : f.leadingCoeff < 0 := rp_lc_neg _ GoodSextic.not_isSquare_leadingCoeff
  have h01 : r 0 < r 1 := hmono (by decide)
  have h12 : r 1 < r 2 := hmono (by decide)
  have h23 : r 2 < r 3 := hmono (by decide)
  have hroot : ∀ j, f.eval (r j) = 0 := fun j => hr j
  have hall' : ∀ x : ℝ, f.eval x = 0 → x = r 0 ∨ x = r 1 ∨ x = r 2 ∨ x = r 3 := by
    intro x hx
    obtain ⟨j, rfl⟩ := hall x hx
    fin_cases j <;> simp
  have hrs : ∀ s, (s = r 0 ∨ s = r 1 ∨ s = r 2 ∨ s = r 3) → f.eval s = 0 := by
    rintro s (rfl | rfl | rfl | rfl) <;> exact hroot _
  obtain ⟨G, hG⟩ := rp_factor4 f (r 0) (r 1) (r 2) (r 3) h01 h12 h23 (hroot 0) (hroot 1)
    (hroot 2) (hroot 3)
  obtain ⟨hGdeg, hGlc, hGno⟩ := rp_G_props f G _ _ _ _ hsq hdeg6 hG hall'
  have hGneg : ∀ x, G.eval x < 0 := by
    intro x
    have h := rp_quad_pos G hGdeg hGno x
    rw [hGlc] at h
    exact neg_of_mul_pos_right h hlc.le
  have hoval : ∀ x : ℝ, 0 < f.eval x → (r 0 - x) * (r 3 - x) < 0 ∧ 0 < (r 1 - x) * (r 2 - x) := by
    intro x hx
    apply rp_oval _ _ _ _ x h01 h12 h23
    rw [hG] at hx
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hx
    exact neg_of_mul_pos_right hx (hGneg x).le
  obtain ⟨hd0, hd1, hd2, hd3⟩ := rp_deriv_signs G _ _ _ _ h01 h12 h23 hGneg
  rw [← hG] at hd0 hd1 hd2 hd3
  -- the reduced classes
  intro Q
  rcases jac_eq_one_or_reduced f Q with rfl | ⟨u, v, w, hu, hudeg, hvdeg, hw, hQ⟩
  · rw [map_one]
    exact one_mem _
  have hc := exists_coprime_of_squarefree hsq hw
  have hnn : ∀ x, u.eval x = 0 → 0 ≤ f.eval x := by
    intro x hx
    have h := congrArg (eval x) hw
    simp only [eval_sub, eval_pow, eval_mul, hx, zero_mul] at h
    nlinarith [sq_nonneg (v.eval x)]
  have hnd : ∀ x, f.eval x = 0 → u ≠ (X - C x) ^ 2 := fun x hx hux =>
    rp_not_double f u v w hsq hw x hux hx
  have core := fun p => rp_sign_core f u p (r 0) (r 1) (r 2) (r 3) h01 h12 h23
    ⟨hroot 0, hroot 1, hroot 2, hroot 3⟩ hall' hoval hd0 hd1 hd2 hd3 hu hudeg hnn hnd
  change mu f (Q : Pic f) ∈ Wr f r hr
  by_cases hcop : IsCoprime u f
  · -- `u` coprime to `f`: `μ(Q) = [u(T)]`
    have hev : Even u.natDegree := by rw [hudeg]; exact even_two
    have hQ' : (Q : Pic f) = ((mumfordJac f hu hev hw hc : Jac f) : Pic f) := hQ
    rw [hQ']
    change muJ f (mumfordJac f hu hev hw hc) ∈ Wr f r hr
    rw [muJ_mumfordJac f hu hev hw hc hcop]
    refine mk_mem_Wr f r hr _ u (IsUnit.unit_spec _) (core u ?_ ?_)
    · intro s _ hus
      exact mul_self_pos.mpr hus
    · intro s hs hus
      exfalso
      obtain ⟨a, b, hab⟩ := hcop
      have h := congrArg (eval s) hab
      simp [hus, hrs s hs] at h
  by_cases hdvd : u ∣ f
  · -- `u ∣ f`: `v = 0`, `Q = T` and `μ(Q) = [(u - f/u)(T)]`
    have hv0 : v = 0 := rp_v_eq_zero f u v w hsq hu hudeg hvdeg hw hdvd
    subst hv0
    obtain ⟨q, hq⟩ := hdvd
    have hQ' : (Q : Pic f) = ((Tpt f hu ⟨q, hq⟩ hudeg : Jac f) : Pic f) := by
      rw [coe_Tpt]; exact hQ
    rw [hQ']
    change muJ f (Tpt f hu ⟨q, hq⟩ hudeg) ∈ Wr f r hr
    rw [muJ_Tpt f hu ⟨q, hq⟩ hudeg hq]
    refine mk_mem_Wr f r hr _ (u - q) (IsUnit.unit_spec _) (core (u - q) ?_ ?_)
    · intro s hs hus
      have h1 := congrArg (eval s) hq
      rw [eval_mul, hrs s hs] at h1
      have hq0 : q.eval s = 0 := (mul_eq_zero.mp h1.symm).resolve_left hus
      rw [eval_sub, hq0, sub_zero]
      exact mul_self_pos.mpr hus
    · intro s _ hus
      exact rp_U2_tpt f u q s hq hus
  -- otherwise one Cantor step: `μ(Q) = [w(T)]⁻¹`, `w` coprime to `f`
  have hwcop : IsCoprime w f := rp_isCoprime_w f u v w hsq hu hvdeg hw hcop hdvd
  have hw4 : w.natDegree = 4 := rp_natDegree_w f u v w hdeg6 hu hudeg hvdeg hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hw4
    exact absurd hw4 (by norm_num)
  set c := w.leadingCoeff with hcdef
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hw0
  set w1 := C c⁻¹ * w with hw1def
  have hw1m : w1.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc0)
  have hev : Even w1.natDegree := by
    rw [hw1def, natDegree_C_mul (inv_ne_zero hc0), hw4]
    exact ⟨2, rfl⟩
  have hCC : C c⁻¹ * C c = (1 : ℝ[X]) := by rw [← C_mul, inv_mul_cancel₀ hc0, C_1]
  have hw1eq : v ^ 2 - f = w1 * (C c * u) := by
    rw [hw, hw1def]
    linear_combination (-(u * w)) * hCC
  have hc1 := exists_coprime_of_squarefree hsq hw1eq
  have hunit : IsUnit (C c⁻¹ : ℝ[X]) := isUnit_C.mpr (Ne.isUnit (inv_ne_zero hc0))
  have hassoc : Associated w w1 := by
    rw [hw1def, mul_comm]
    exact associated_mul_unit_right w _ hunit
  have hprod := mumford_mul_mumford_eq_span (f := f) (GoodSextic.two_ne_zero (f := f)) hw hc
  rw [mumford_eq_of_associated f hassoc] at hprod
  have hQ' : (Q : Pic f) = ((mumfordJac f hw1m hev hw1eq hc1 : Jac f) : Pic f)⁻¹ := by
    rw [hQ]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨_, Yc_sub_ne_zero f v, hprod⟩
  have hw1cop : IsCoprime w1 f := by
    rw [hw1def]
    exact (isCoprime_mul_unit_left_left hunit _ _).mpr hwcop
  rw [hQ', map_inv]
  apply inv_mem
  change muJ f (mumfordJac f hw1m hev hw1eq hc1) ∈ Wr f r hr
  rw [muJ_mumfordJac f hw1m hev hw1eq hc1 hw1cop]
  refine mk_mem_Wr f r hr _ w1 (IsUnit.unit_spec _) ?_
  have hgw := core w (fun s hs hus => by
      have h1 := congrArg (eval s) hw
      rw [eval_sub, eval_pow, eval_mul, hrs s hs, sub_zero] at h1
      have hws : w.eval s ≠ 0 := by
        intro h0
        obtain ⟨a, b, hab⟩ := hwcop
        have h := congrArg (eval s) hab
        simp [h0, hrs s hs] at h
      rw [← h1]
      exact lt_of_le_of_ne (sq_nonneg _) (by rw [h1]; exact (mul_ne_zero hus hws).symm))
    (fun s hs hus => rp_U2_w f u v w s hw hus (hrs s hs))
  obtain ⟨g1, g2⟩ := hgw
  have hc2 : 0 < c⁻¹ * c⁻¹ := mul_self_pos.mpr (inv_ne_zero hc0)
  simp only [hw1def, eval_mul, eval_C]
  exact ⟨by nlinarith [mul_pos hc2 g1], by nlinarith [mul_pos hc2 g2]⟩

end FurioLombardo.Discharge.SelmerBasis
