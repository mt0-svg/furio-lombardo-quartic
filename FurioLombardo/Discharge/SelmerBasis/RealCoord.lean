import FurioLombardo.Discharge.SelmerBasis.RealInst
import FurioLombardo.Discharge.SelmerBasis.GlobalGens

/-!
# `CoordCond` at the real places 5 and 6 of twist 0: the data-independent layer

* `sgn_extend`: the sign of `ψ x = φ x.re + φ x.im w` for `ψ = extendHom φ w`, from the sign of the
  norm `φ (x.re² - a x.im²)` and the sign of `φ x.re` (norm positive) or of `w φ x.im` (norm
  negative); generic over the base ring, used for `L42 / K21` and `N84 / L42`.
* `qroots_eq`, `hroots_eq`: the roots of `q^σ` at `qIdx k` are the images of a root `x ∈ L42` of `q 0`
  under the two real embeddings `extendHom σ (± u)` (the smaller one where `u σ(x.im) < 0`); the real
  roots of `h^σ` at `hIdx k` are the images of a root `y ∈ N84` of `h 0` under the two embeddings
  `extendHom τ' (± v)` over any `τ' = extendHom σ u'` with `v² = τ'(eN)`.
* `coordCond_place`: `CoordCond` at place `k + 5` for the generators `gK 0` from sign bits `Sg` of
  `Pgen s` at the roots (`coordCond_real`).
* `hS_of_signs`: the sign hypothesis of `coordCond_place` from the tower facts (`q 0 (α) = 0`,
  `h 0 (β) = 0`, the values of `Pgen s` at `α`, `β`) and sign conditions on `ψ (gensL i)` and
  `ρ (gensN j)` at the four real embeddings.
-/

namespace FurioLombardo.Discharge.SelmerBasis.RealRoots

open Polynomial FurioLombardo.M1 FurioLombardo.Discharge.M3b FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.SelmerSpan
  FurioLombardo.Discharge.SelmerBasis

/-! ## Signs in a real quadratic extension -/

theorem sgn_extend {R : Type*} [CommRing R] {a : R} (φ : R →+* ℝ) (w : ℝ) (hw : w * w = φ a)
    (x : QuadraticAlgebra R a 0) (s : ℝ)
    (h : (0 < φ (x.re * x.re - a * (x.im * x.im)) ∧ 0 < s * φ x.re) ∨
      (φ (x.re * x.re - a * (x.im * x.im)) < 0 ∧ 0 < s * (w * φ x.im))) :
    0 < s * extendHom φ w hw x := by
  rw [extendHom_apply]
  set A := φ x.re + φ x.im * w
  set B := φ x.re - φ x.im * w
  have hN : φ (x.re * x.re - a * (x.im * x.im)) = A * B := by
    simp only [map_sub, map_mul, A, B]
    rw [← hw]; ring
  rw [hN] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hsum : s * A + s * B = 2 * (s * φ x.re) := by simp only [A, B]; ring
    have hprod : (s * A) * (s * B) = s * s * (A * B) := by ring
    have hs : s ≠ 0 := by rintro rfl; simp at h2
    have hss : 0 < s * s := mul_self_pos.mpr hs
    by_contra hc
    push Not at hc
    have : (s * A) * (s * B) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    nlinarith [mul_pos hss h1]
  · have hdiff : s * A - s * B = 2 * (s * (w * φ x.im)) := by simp only [A, B]; ring
    have hprod : (s * A) * (s * B) = s * s * (A * B) := by ring
    have hs : s ≠ 0 := by rintro rfl; simp at h2
    have hss : 0 < s * s := mul_self_pos.mpr hs
    by_contra hc
    push Not at hc
    have hB : s * B < 0 := by linarith
    have : 0 ≤ (s * A) * (s * B) := mul_nonneg_of_nonpos_of_nonpos hc hB.le
    nlinarith [mul_neg_of_pos_of_neg hss h1]

/-! ## Evaluation at the images of a root -/

theorem eval₂_of_comp {F : Type*} [CommRing F] [Algebra K21 F] {σ : K21 →+* ℝ} (ψ : F →+* ℝ)
    (hψ : ψ.comp (algebraMap K21 F) = σ) (x : F) (P : K21[X]) :
    P.eval₂ σ (ψ x) = ψ (aeval x P) := by
  rw [aeval_def, hom_eval₂, hψ]

theorem pair_eq {a b x y : ℝ} (hab : a < b) (hx : x = a ∨ x = b) (hy : y = a ∨ y = b)
    (hxy : x < y) : x = a ∧ y = b := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd hxy (lt_irrefl _)
  · exact ⟨rfl, rfl⟩
  · exact absurd (hxy.trans hab) (lt_irrefl _)
  · exact absurd hxy (lt_irrefl _)

theorem qIdx_lt (k : Fin 2) : qIdx k 0 < qIdx k 1 := by fin_cases k <;> decide
theorem hIdx_lt (k : Fin 2) : hIdx k 0 < hIdx k 1 := by fin_cases k <;> decide

theorem neg_mul_self_eq {u e : ℝ} (hu : u * u = e) : -u * -u = e := by rw [neg_mul_neg]; exact hu

/-- The roots of `q^σ` are the images of a root `x ∈ L42` of `q 0`. -/
theorem qroots_eq (k : Fin 2) {x : L42} (hx : aeval x (q 0) = 0) {u : ℝ}
    (hu : u * u = realEmb (Fin.castSucc k) epsK) (hux : u * realEmb (Fin.castSucc k) x.im < 0) :
    roots k (qIdx k 0) = extendHom (realEmb (Fin.castSucc k)) u hu x ∧
      roots k (qIdx k 1) = extendHom (realEmb (Fin.castSucc k)) (-u) (neg_mul_self_eq hu) x := by
  obtain ⟨hmono, -, hq, -⟩ := roots_spec k
  have hr (w : ℝ) (hw : w * w = realEmb (Fin.castSucc k) epsK) :
      (q 0).eval₂ (realEmb (Fin.castSucc k)) (extendHom (realEmb (Fin.castSucc k)) w hw x) = 0 := by
    rw [eval₂_of_comp _ (extendHom_comp_algebraMap _ _ _), hx, map_zero]
  have hlt : extendHom (realEmb (Fin.castSucc k)) u hu x <
      extendHom (realEmb (Fin.castSucc k)) (-u) (neg_mul_self_eq hu) x := by
    rw [extendHom_apply, extendHom_apply]; linarith
  obtain ⟨h1, h2⟩ := pair_eq (hmono (qIdx_lt k)) ((hq _).1 (hr u hu))
    ((hq _).1 (hr (-u) (neg_mul_self_eq hu))) hlt
  exact ⟨h1.symm, h2.symm⟩

theorem extendHom_comp_N84 {k : Fin 2} {u : ℝ} (hu : u * u = realEmb (Fin.castSucc k) epsK) {v : ℝ}
    (hv : v * v = extendHom (realEmb (Fin.castSucc k)) u hu eN) :
    (extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) v hv).comp (algebraMap K21 N84) =
      realEmb (Fin.castSucc k) := by
  refine RingHom.ext fun c => ?_
  show extendHom _ v hv (⟨algebraMap K21 L42 c, 0⟩ : N84) = _
  rw [extendHom_apply]
  simp only [map_zero, zero_mul, add_zero]
  exact RingHom.congr_fun (extendHom_comp_algebraMap _ _ hu) c

/-- The real roots of `h^σ` are the images of a root `y ∈ N84` of `h 0` under the two real
embeddings over `τ' = extendHom σ u`, `v² = τ'(eN)`. -/
theorem hroots_eq (k : Fin 2) {y : N84} (hy : aeval y (h 0) = 0) {u : ℝ}
    (hu : u * u = realEmb (Fin.castSucc k) epsK) {v : ℝ}
    (hv : v * v = extendHom (realEmb (Fin.castSucc k)) u hu eN)
    (hvy : v * extendHom (realEmb (Fin.castSucc k)) u hu y.im < 0) :
    roots k (hIdx k 0) = extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) v hv y ∧
      roots k (hIdx k 1) =
        extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) (-v) (neg_mul_self_eq hv) y := by
  obtain ⟨hmono, -, -, hh⟩ := roots_spec k
  have hr (w : ℝ) (hw : w * w = extendHom (realEmb (Fin.castSucc k)) u hu eN) :
      (h 0).eval₂ (realEmb (Fin.castSucc k))
        (extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) w hw y) = 0 := by
    rw [eval₂_of_comp _ (extendHom_comp_N84 hu hw), hy, map_zero]
  have hlt : extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) v hv y <
      extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) (-v) (neg_mul_self_eq hv) y := by
    rw [extendHom_apply (extendHom _ u hu) v hv, extendHom_apply (extendHom _ u hu) (-v)]; linarith
  obtain ⟨h1, h2⟩ := pair_eq (hmono (hIdx_lt k)) ((hh _).1 (hr v hv))
    ((hh _).1 (hr (-v) (neg_mul_self_eq hv))) hlt
  exact ⟨h1.symm, h2.symm⟩

/-! ## `CoordCond` at places 5 and 6 -/

/-- The sign bits `Sg s j` of `Pgen s` at the roots `roots k j`. -/
def SignOK (k : Fin 2) (Sg : Fin 82 → Fin 4 → ZMod 2) : Prop :=
  ∀ s j, ((Pgen s).eval₂ (realEmb (Fin.castSucc k)) (roots k j) < 0 ∧ Sg s j = 1) ∨
    (0 < (Pgen s).eval₂ (realEmb (Fin.castSucc k)) (roots k j) ∧ Sg s j = 0)

/-- **`CoordCond` at place `k + 5`** from the sign bits of the generators at the four roots. -/
theorem coordCond_place (k : Fin 2) (Sg : Fin 82 → Fin 4 → ZMod 2) (hS : SignOK k Sg) :
    CoordCond (realEmb (Fin.castSucc k)) (fRev 0) (gK 0) (Wplace k)
      (Matrix.of ![fun s => Sg s 0 + Sg s 3, fun s => Sg s 1 + Sg s 2]) :=
  coordCond_real (realEmb (Fin.castSucc k)) (fRev 0) (gKu 0) Pgen (gKu_coe 0) (roots k)
    (roots_isRoot k) Sg hS

/-- A real number with the sign `ς` (`ς = ±1`) and the bit of `ς`. -/
def SignBit (x : ℝ) (b : ZMod 2) : Prop := (x < 0 ∧ b = 1) ∨ (0 < x ∧ b = 0)

theorem signBit_one {b : ZMod 2} (hb : b = 0) : SignBit 1 b := Or.inr ⟨one_pos, hb⟩

theorem idx_cases (k : Fin 2) (j : Fin 4) :
    (∃ b : Fin 2, j = qIdx k b) ∨ (∃ b : Fin 2, j = hIdx k b) := by
  rcases idx_cover k j with h | h | h | h
  · exact Or.inl ⟨0, h⟩
  · exact Or.inl ⟨1, h⟩
  · exact Or.inr ⟨0, h⟩
  · exact Or.inr ⟨1, h⟩

/-- The real embedding of `L42` at the root `qIdx k b`: `ω ↦ u` for `b = 0`, `ω ↦ -u` for `b = 1`. -/
noncomputable def embQ (k : Fin 2) {u : ℝ} (hu : u * u = realEmb (Fin.castSucc k) epsK) (b : Fin 2) :
    L42 →+* ℝ :=
  if b = 0 then extendHom (realEmb (Fin.castSucc k)) u hu
  else extendHom (realEmb (Fin.castSucc k)) (-u) (neg_mul_self_eq hu)

/-- The real embedding of `N84` at the root `hIdx k b` over `τ' = extendHom σ u`. -/
noncomputable def embH (k : Fin 2) {u : ℝ} (hu : u * u = realEmb (Fin.castSucc k) epsK) {v : ℝ}
    (hv : v * v = extendHom (realEmb (Fin.castSucc k)) u hu eN) (b : Fin 2) : N84 →+* ℝ :=
  if b = 0 then extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) v hv
  else extendHom (extendHom (realEmb (Fin.castSucc k)) u hu) (-v) (neg_mul_self_eq hv)

theorem roots_qIdx (k : Fin 2) {x : L42} (hx : aeval x (q 0) = 0) {u : ℝ}
    (hu : u * u = realEmb (Fin.castSucc k) epsK) (hux : u * realEmb (Fin.castSucc k) x.im < 0)
    (b : Fin 2) : roots k (qIdx k b) = embQ k hu b x := by
  obtain ⟨h0, h1⟩ := qroots_eq k hx hu hux
  fin_cases b
  · exact h0
  · exact h1

theorem roots_hIdx (k : Fin 2) {y : N84} (hy : aeval y (h 0) = 0) {u : ℝ}
    (hu : u * u = realEmb (Fin.castSucc k) epsK) {v : ℝ}
    (hv : v * v = extendHom (realEmb (Fin.castSucc k)) u hu eN)
    (hvy : v * extendHom (realEmb (Fin.castSucc k)) u hu y.im < 0) (b : Fin 2) :
    roots k (hIdx k b) = embH k hu hv b y := by
  obtain ⟨h0, h1⟩ := hroots_eq k hy hu hv hvy
  fin_cases b
  · exact h0
  · exact h1

theorem embQ_comp (k : Fin 2) {u : ℝ} (hu : u * u = realEmb (Fin.castSucc k) epsK) (b : Fin 2) :
    (embQ k hu b).comp (algebraMap K21 L42) = realEmb (Fin.castSucc k) := by
  unfold embQ
  split_ifs
  · exact extendHom_comp_algebraMap _ _ _
  · exact extendHom_comp_algebraMap _ _ _

theorem embH_comp (k : Fin 2) {u : ℝ} (hu : u * u = realEmb (Fin.castSucc k) epsK) {v : ℝ}
    (hv : v * v = extendHom (realEmb (Fin.castSucc k)) u hu eN) (b : Fin 2) :
    (embH k hu hv b).comp (algebraMap K21 N84) = realEmb (Fin.castSucc k) := by
  unfold embH
  split_ifs
  · exact extendHom_comp_N84 hu hv
  · exact extendHom_comp_N84 hu (neg_mul_self_eq hv)

/-- **The sign hypothesis of `coordCond_place`** from the tower facts and the signs of the
generators at the four real embeddings (`embQ k hu b` at the root `qIdx k b`, `embH k hu' hv b` at
the root `hIdx k b`). -/
theorem hS_of_signs (k : Fin 2) (Sg : Fin 82 → Fin 4 → ZMod 2)
    (hα : aeval alphaR (q 0) = 0) (hβ : aeval betaR (h 0) = 0)
    (hPα : ∀ i : Fin 29, aeval alphaR (Pgen (Fin.castAdd 53 i)) = gensL i)
    (hPα' : ∀ j : Fin 53, aeval alphaR (Pgen (Fin.natAdd 29 j)) = 1)
    (hPβ : ∀ i : Fin 29, aeval betaR (Pgen (Fin.castAdd 53 i)) = 1)
    (hPβ' : ∀ j : Fin 53, aeval betaR (Pgen (Fin.natAdd 29 j)) = gensN j)
    {u : ℝ} (hu : u * u = realEmb (Fin.castSucc k) epsK)
    (hux : u * realEmb (Fin.castSucc k) alphaR.im < 0)
    {u' : ℝ} (hu' : u' * u' = realEmb (Fin.castSucc k) epsK) {v : ℝ}
    (hv : v * v = extendHom (realEmb (Fin.castSucc k)) u' hu' eN)
    (hvy : v * extendHom (realEmb (Fin.castSucc k)) u' hu' betaR.im < 0)
    (hL : ∀ (i : Fin 29) (b : Fin 2), SignBit (embQ k hu b (gensL i)) (Sg (Fin.castAdd 53 i) (qIdx k b)))
    (hL1 : ∀ (i : Fin 29) (b : Fin 2), Sg (Fin.castAdd 53 i) (hIdx k b) = 0)
    (hN1 : ∀ (j : Fin 53) (b : Fin 2), Sg (Fin.natAdd 29 j) (qIdx k b) = 0)
    (hN : ∀ (j : Fin 53) (b : Fin 2),
      SignBit (embH k hu' hv b (gensN j)) (Sg (Fin.natAdd 29 j) (hIdx k b))) :
    SignOK k Sg := by
  intro s j
  show SignBit _ _
  revert s
  show ∀ s : Fin (29 + 53), SignBit _ _
  intro s
  rcases idx_cases k j with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rw [roots_qIdx k hα hu hux b, eval₂_of_comp _ (embQ_comp k hu b)]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) s
    · rw [hPα i]; exact hL i b
    · rw [hPα' j, map_one]; exact signBit_one (hN1 j b)
  · rw [roots_hIdx k hβ hu' hv hvy b, eval₂_of_comp _ (embH_comp k hu' hv b)]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) s
    · rw [hPβ i, map_one]; exact signBit_one (hL1 i b)
    · rw [hPβ' j]; exact hN j b

end FurioLombardo.Discharge.SelmerBasis.RealRoots
