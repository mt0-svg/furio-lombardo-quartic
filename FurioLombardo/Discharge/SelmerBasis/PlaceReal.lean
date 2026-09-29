import FurioLombardo.Discharge.M3b.K21Real
import FurioLombardo.Discharge.M3a.LocalLead
import FurioLombardo.Discharge.SelmerBasis.RealPlace

/-!
# The real places: the local data of Interfaces.lean at `realEmb j : K21 →+* ℝ`

* `ck_lc`: `4 c_k` (zk coordinates `lcL k`) is negative at the three real embeddings of `K21`
  (sign certificates on lane M3b's root intervals, kernel check);
* `goodSextic_real`: `GoodSextic ((fRev k).map (realEmb j))` for both twists and every real
  embedding.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3b
  FurioLombardo.Discharge.M3a.Bruin

theorem ck_lc : ∀ k : Fin 2, elemCert (lcL k) ![-1, -1, -1] := by
  unfold elemCert; decide +kernel

theorem realEmb_lc_neg (k : Fin 2) (j : Fin 3) : realEmb j (fRev k).leadingCoeff < 0 := by
  have h := elem_sign (ck_lc k) j
  have hs : ∀ j : Fin 3, (![-1, -1, -1] : Fin 3 → ℤ) j = -1 := by decide
  rw [hs j] at h
  rw [fRev_leadingCoeff, c_eq_zkE, map_mul, map_inv₀, map_ofNat]
  have h4 : (0 : ℝ) < (4 : ℝ)⁻¹ := by norm_num
  push_cast at h
  nlinarith

/-- **`GoodSextic` at the real places.** -/
theorem goodSextic_real (k : Fin 2) (j : Fin 3) : GoodSextic ((fRev k).map (realEmb j)) := by
  refine goodSextic_fRev_map (realEmb j) k ?_
  rintro ⟨r, hr⟩
  have h := realEmb_lc_neg k j
  rw [hr] at h
  nlinarith [mul_self_nonneg r]


/-! ## `CoordCond` at a real place, from the signs of the generators at the real roots -/

/-- The sign bit of a product of powers of nonzero reals is the sum of the sign bits. -/
theorem prod_pow_sign {ι : Type*} [DecidableEq ι] (S : Finset ι) (w : ι → ℝ) (e : ι → ZMod 2)
    (he : ∀ s, (w s < 0 ∧ e s = 1) ∨ (0 < w s ∧ e s = 0)) (a : ι → ℕ) :
    (0 < ∏ s ∈ S, w s ^ a s ∧ ∑ s ∈ S, (a s : ZMod 2) * e s = 0) ∨
      (∏ s ∈ S, w s ^ a s < 0 ∧ ∑ s ∈ S, (a s : ZMod 2) * e s = 1) := by
  induction S using Finset.induction_on with
  | empty => left; simp
  | insert t S ht ih =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht]
    have hterm : (0 < w t ^ a t ∧ (a t : ZMod 2) * e t = 0) ∨
        (w t ^ a t < 0 ∧ (a t : ZMod 2) * e t = 1) := by
      rcases he t with ⟨hw, he1⟩ | ⟨hw, he0⟩
      · rcases Nat.even_or_odd (a t) with hev | hod
        · left
          refine ⟨hev.pow_pos hw.ne, ?_⟩
          rw [he1, mul_one, (ZMod.natCast_eq_zero_iff_even).2 hev]
        · right
          refine ⟨hod.pow_neg hw, ?_⟩
          rw [he1, mul_one]
          exact (ZMod.natCast_eq_one_iff_odd).2 hod
      · left
        exact ⟨pow_pos hw _, by rw [he0, mul_zero]⟩
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases hterm with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases ih with ⟨h2, e2⟩ | ⟨h2, e2⟩
    · exact Or.inl ⟨mul_pos h1 h2, by rw [e1, e2, add_zero]⟩
    · exact Or.inr ⟨mul_neg_of_pos_of_neg h1 h2, by rw [e1, e2, zero_add]⟩
    · exact Or.inr ⟨mul_neg_of_neg_of_pos h1 h2, by rw [e1, e2, add_zero]⟩
    · exact Or.inl ⟨mul_pos_of_neg_of_neg h1 h2, by rw [e1, e2, h11]⟩

/-- Evaluation at a real root of `f^φ` of the base change of a class `p(T)`. -/
theorem evRoot_etaleMap_mk {K : Type*} [Field K] (φ : K →+* ℝ) (f : K[X]) {r : ℝ}
    (hr : (f.map φ).IsRoot r) (p : K[X]) :
    evRoot hr (etaleMap φ f (AdjoinRoot.mk f p)) = p.eval₂ φ r := by
  have h1 : (evRoot hr).comp ((etaleMap φ f).comp (algebraMap K (AdjoinRoot f))) = φ := by
    ext a
    simp [etaleMap, evRoot]
  have h2 : evRoot hr (etaleMap φ f (AdjoinRoot.root f)) = r := by
    simp [etaleMap, evRoot]
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.hom_eval₂, h1, h2]

/-- **`CoordCond` at a real place.** For classes `g s = [P s (T)]` whose values at the real roots
`r j` of `f^φ` are nonzero with sign bits `Sg s j`, the two rows `Sg · 0 + Sg · 3` and
`Sg · 1 + Sg · 2` are a coordinate condition for `W_r`. -/
theorem coordCond_real {K : Type*} [Field K] (φ : K →+* ℝ) (f : K[X]) {m : ℕ}
    (gu : Fin m → (AdjoinRoot f)ˣ) (P : Fin m → K[X])
    (hP : ∀ s, (gu s : AdjoinRoot f) = AdjoinRoot.mk f (P s))
    (r : Fin 4 → ℝ) (hr : ∀ j, (f.map φ).IsRoot (r j)) (Sg : Fin m → Fin 4 → ZMod 2)
    (hS : ∀ s j, ((P s).eval₂ φ (r j) < 0 ∧ Sg s j = 1) ∨ (0 < (P s).eval₂ φ (r j) ∧ Sg s j = 0)) :
    CoordCond φ f (fun s => (QuotientGroup.mk (gu s) : H f)) (Wr (f.map φ) r hr)
      (Matrix.of ![fun s => Sg s 0 + Sg s 3, fun s => Sg s 1 + Sg s 2]) := by
  intro a ha
  set x : (AdjoinRoot (f.map φ))ˣ := ∏ s, Units.map (etaleMap φ f).toMonoidHom (gu s) ^ a s with hx
  have hmk : Hmap φ f (∏ s, (QuotientGroup.mk (gu s) : H f) ^ a s) = QuotientGroup.mk x := by
    rw [map_prod, hx, QuotientGroup.mk_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, QuotientGroup.mk_pow]
    rfl
  rw [hmk] at ha
  -- `x` itself lies in `realSignSub`
  have hxW : x ∈ realSignSub (f.map φ) r hr := by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 ha
    have hq : y⁻¹ * x ∈ sqClass (f.map φ) := QuotientGroup.eq.1 hyx
    have := Subgroup.mul_mem _ hy (sqClass_le_realSignSub (f.map φ) r hr hq)
    rwa [mul_inv_cancel_left] at this
  obtain ⟨h03, h12⟩ := hxW
  -- the values of `x` at the roots
  have hev : ∀ j, evRoot (hr j) (x : AdjoinRoot (f.map φ)) = ∏ s, ((P s).eval₂ φ (r j)) ^ a s := by
    intro j
    rw [hx, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    have hu : ((Units.map (etaleMap φ f).toMonoidHom (gu s) : (AdjoinRoot (f.map φ))ˣ) :
        AdjoinRoot (f.map φ)) = etaleMap φ f (gu s) := rfl
    rw [Units.val_pow_eq_pow_val, map_pow, hu, hP s, evRoot_etaleMap_mk]
  have hbit : ∀ j, (0 < evRoot (hr j) (x : AdjoinRoot (f.map φ)) ∧
      ∑ s, (a s : ZMod 2) * Sg s j = 0) ∨
      (evRoot (hr j) (x : AdjoinRoot (f.map φ)) < 0 ∧ ∑ s, (a s : ZMod 2) * Sg s j = 1) := by
    intro j
    rw [hev j]
    exact prod_pow_sign Finset.univ (fun s => (P s).eval₂ φ (r j)) (fun s => Sg s j)
      (fun s => hS s j) a
  have hpair : ∀ i j, 0 < evRoot (hr i) (x : AdjoinRoot (f.map φ)) *
      evRoot (hr j) (x : AdjoinRoot (f.map φ)) →
      ∑ s, (a s : ZMod 2) * Sg s i + ∑ s, (a s : ZMod 2) * Sg s j = 0 := by
    intro i j hij
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases hbit i with ⟨hi, ei⟩ | ⟨hi, ei⟩ <;> rcases hbit j with ⟨hj, ej⟩ | ⟨hj, ej⟩
    · rw [ei, ej, add_zero]
    · nlinarith
    · nlinarith
    · rw [ei, ej, h11]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    have := hpair 0 3 h03
    rw [← Finset.sum_add_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    change (Sg s 0 + Sg s 3) * _ = _
    ring
  · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    have := hpair 1 2 h12
    rw [← Finset.sum_add_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    change (Sg s 1 + Sg s 2) * _ = _
    ring

end FurioLombardo.Discharge.SelmerBasis
