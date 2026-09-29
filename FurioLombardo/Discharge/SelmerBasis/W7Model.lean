import FurioLombardo.Discharge.SelmerBasis.W7Cert
import FurioLombardo.Discharge.SelmerBasis.PlaceWModel
import FurioLombardo.Discharge.SelmerBasis.GlobalCRT
import FurioLombardo.Discharge.SelmerBasis.AdicPlace
import FurioLombardo.Discharge.SelmerBasis.Bridge
import FurioLombardo.Discharge.SelmerBasis.Count.At7

/-!
# The model of `K_w7[T]/(fRev 1)` (lane selmer-p7)

`σ7 = adicCoe w7`, `π = σ7 al7`. From a table of squarings `tab` and a `Model` `M` passing their checks
(`Hyp tab M`, with `2 ≤ M.N`), Hensel's lemma (`exists_sqrt_near`) gives

* `r7 H` with `r² = σ ε` near `σ y0`, and the embeddings `ιp H : ω ↦ -r`, `ιm H : ω ↦ r` of `L42`;
* `S7 H` with `S² = ιp (4 eN)` near `σ S0`, and `ιN H b : N84 → K_w7` (`Ω ↦ ± S`);
* `A4 H = ιm (4 eN)`, `‖A4‖ = ‖π‖`, the Eisenstein component `F7 H = QF K_w7 (A4 H) 0` and
  `ι' H : N84 → F7 H` (`Ω ↦ Z`);
* the five components `ev4 H c` (`c < 4`, into `K_w7`) and `ev' H` (into `F7 H`) of
  `K_w7[T]/(fRev 1)`, and `evG H` into `(Fin 4 → K_w7ˣ) × (F7 H)ˣ`;
* the error bounds of `XLp`, `XLm`, `XNs` (`‖π‖ ^ M.N`).

The residue field is `𝔽₃₄₃` (`ferm7`, `euler7` with `343 = 2 · 171 + 1`) and `‖2‖ = 1` (`two7`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.M3b FurioLombardo.Discharge
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin FurioLombardo.M3a.Genus2
  FurioLombardo.Discharge.SelmerBasis.GlobalK21
open FurioLombardo.M2.Special (al7)
open scoped FurioLombardo.Discharge.SelmerBasis.Adic

namespace FurioLombardo.Discharge.SelmerBasis.W7

/-! ## The place -/

/-- The completion at `w7`. -/
abbrev K7 : Type := w7.adicCompletion K21

/-- `K21 → K_w7`. -/
noncomputable abbrev σ7 : K21 →+* K7 := adicCoe w7

theorem int7 (a : List ℤ) : ‖σ7 (zkE a)‖ ≤ 1 := by
  have h := primeOf_norm_le (hP := span_eltO_al7_isPrime) (hα := Count.ne_zero_w7) (x := zkE a) (n := 0)
    (a := eltO a) (b := 1) (b' := 1) (c' := 0) (by ring) (by simp [coe_elt])
  rw [zpow_zero] at h
  exact h

theorem unif7 : NormUnif (σ7 (zkE al7)) := by
  rw [← coe_elt]; exact normUnif_w7

theorem two7 : ‖(2 : K7)‖ = 1 := by
  rw [Count.norm_two_w7, pow_zero]

theorem ferm7 : ∀ ξ : K7, ‖ξ‖ = 1 → ‖ξ ^ (2 * 171) - 1‖ < 1 :=
  res_fermat (w7.adicCompletionIntegers K21) (adic_mem_integers_iff w7)
    ((adic_residue_card w7).trans card_res_w7)

theorem euler7 : ∀ ξ : K7, ‖ξ‖ = 1 → ‖ξ ^ 171 - 1‖ < 1 → ∃ s : K7, ‖ξ - s ^ 2‖ < 1 :=
  res_euler (w7.adicCompletionIntegers K21) (adic_mem_integers_iff w7)
    ((adic_residue_card w7).trans card_res_w7)

theorem negOne7 : ‖(-1 : K7)‖ = 1 ∧ ‖(-1 : K7) ^ 171 + 1‖ < 1 := by
  refine ⟨by simp, ?_⟩
  rw [show (-1 : K7) ^ 171 = -1 by norm_num, neg_add_cancel, norm_zero]
  exact one_pos

theorem two7_ne_zero : (2 : K7) ≠ 0 := by
  intro h; have := two7; rw [h, norm_zero] at this; exact zero_ne_one this

/-! ## The hypotheses on the data -/

/-- What the model needs from `tab` and `M` (W7Check facts, W7Place.lean). -/
structure Hyp (tab : List (List ℤ)) (M : Model) : Prop where
  h0 : tab.getD 0 [] = al7
  hsq : ∀ i, i + 1 < tab.length → zkE (tab.getD (i + 1) []) = zkE (tab.getD i []) ^ 2
  hM : M.ok tab = true
  hN : 2 ≤ M.N

variable {tab : List (List ℤ)} {M : Model}

/-- `π`. -/
noncomputable abbrev π7 : K7 := σ7 (zkE al7)

/-- The error bound `‖π‖ ^ N`. -/
noncomputable abbrev δ7 (M : Model) : ℝ := ‖π7‖ ^ M.N

theorem δ7_le_one (M : Model) : δ7 M ≤ 1 :=
  pow_le_one₀ (norm_nonneg _) unif7.norm_lt_one.le

theorem δ7_lt_norm (H : Hyp tab M) : δ7 M < ‖π7‖ := by
  have h1 := unif7.norm_lt_one
  have h0 : 0 < ‖π7‖ := norm_pos_iff.mpr unif7.ne_zero
  calc δ7 M ≤ ‖π7‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg _) h1.le H.hN
    _ < ‖π7‖ := by rw [sq]; exact mul_lt_of_lt_one_left h0 h1

theorem δ7_lt_one (H : Hyp tab M) : δ7 M < 1 := (δ7_lt_norm H).trans unif7.norm_lt_one

theorem pow_le_δ7 {n : ℕ} (hn : M.N ≤ n) : ‖π7‖ ^ n ≤ δ7 M :=
  pow_le_pow_of_le_one (norm_nonneg _) unif7.norm_lt_one.le hn

/-- The model identities in `K21`. -/
theorem Hyp.facts (H : Hyp tab M) :
    zkE M.y0 * zkE M.y0 - epsK = zkE al7 ^ M.ny * zkE M.y0R ∧ ‖σ7 (zkE M.y0)‖ = 1 ∧
    zkE M.S0 * zkE M.S0 - (2 * eaK - 2 * ebK * zkE M.y0) = zkE al7 ^ M.ns * zkE M.S0R ∧
    ‖σ7 (zkE M.S0)‖ = 1 ∧ 2 * eaK + 2 * ebK * zkE M.y0 = zkE al7 * zkE M.E4U ∧
    ‖σ7 (zkE M.E4U)‖ = 1 := by
  have hM := H.hM
  simp only [Model.ok, Model.okY, Model.okS, Model.okE, Bool.and_eq_true, decide_eq_true_eq] at hM
  obtain ⟨⟨⟨⟨⟨⟨hny, cY⟩, uY⟩, hns, cS⟩, uS⟩, cE⟩, uE⟩ := hM
  have eY := evK_eq_of_check _ _ _ cY
  have eS := evK_eq_of_check _ _ _ cS
  have eE := evK_eq_of_check _ _ _ cE
  rw [evK_mul, evK_alPw H.h0 H.hsq hny] at eY
  rw [evK_mul, evK_alPw H.h0 H.hsq hns] at eS
  simp only [evK_sub, evK_mul, evK_add, evK_lin, evK_int, Int.cast_ofNat] at eY eS eE
  refine ⟨?_, norm_unit σ7 int7 unif7 uY, ?_, norm_unit σ7 int7 unif7 uS, ?_, norm_unit σ7 int7 unif7 uE⟩
  · rw [epsK, epsO, M1.coe_zkO]; exact eY
  · rw [eaK, ebK]; exact eS
  · rw [eaK, ebK]; exact eE

/-! ## `r` and the embeddings of `L42` -/

theorem exists_r (H : Hyp tab M) : ∃ r : K7, r ^ 2 = σ7 epsK ∧ ‖r - σ7 (zkE M.y0)‖ ≤ δ7 M := by
  obtain ⟨eY, nY, -, -, -, -⟩ := H.facts
  have hz : ‖σ7 epsK‖ ≤ 1 := by rw [epsK, epsO, M1.coe_zkO]; exact int7 _
  have hd : σ7 (zkE M.y0) ^ 2 - σ7 epsK = π7 ^ M.ny * σ7 (zkE M.y0R) := by
    rw [sq, ← map_mul, ← map_sub, eY, map_mul, map_pow]
  have hdn : ‖σ7 (zkE M.y0) ^ 2 - σ7 epsK‖ ≤ δ7 M := by
    rw [hd, norm_mul, norm_pow]
    calc ‖π7‖ ^ M.ny * ‖σ7 (zkE M.y0R)‖ ≤ ‖π7‖ ^ M.ny * 1 :=
          mul_le_mul_of_nonneg_left (int7 _) (pow_nonneg (norm_nonneg _) _)
      _ ≤ δ7 M := by rw [mul_one]; exact pow_le_δ7 (min_le_left _ _)
  have h2s : ‖2 * σ7 (zkE M.y0)‖ = 1 := by rw [norm_mul, two7, nY, one_mul]
  obtain ⟨r, hr, hrn⟩ := exists_sqrt_near hz nY.le (by rw [h2s, one_pow]; exact hdn.trans_lt (δ7_lt_one H))
  exact ⟨r, hr, by rw [h2s, div_one] at hrn; exact hrn.trans hdn⟩

/-- The square root of `σ ε` near `σ y0`. -/
noncomputable def r7 (H : Hyp tab M) : K7 := (exists_r H).choose

theorem r7_sq (H : Hyp tab M) : r7 H ^ 2 = σ7 epsK := (exists_r H).choose_spec.1

theorem r7_near (H : Hyp tab M) : ‖r7 H - σ7 (zkE M.y0)‖ ≤ δ7 M := (exists_r H).choose_spec.2

theorem r7_norm (H : Hyp tab M) : ‖r7 H‖ ≤ 1 := by
  have h := IsUltrametricDist.norm_add_le_max (r7 H - σ7 (zkE M.y0)) (σ7 (zkE M.y0))
  rw [sub_add_cancel] at h
  exact h.trans (max_le ((r7_near H).trans (δ7_le_one M)) (int7 _))

theorem hu_p (H : Hyp tab M) : -r7 H * -r7 H = σ7 epsK + σ7 0 * -r7 H := by
  rw [map_zero, zero_mul, add_zero, neg_mul_neg, ← sq, r7_sq]

theorem hu_m (H : Hyp tab M) : r7 H * r7 H = σ7 epsK + σ7 0 * r7 H := by
  rw [map_zero, zero_mul, add_zero, ← sq, r7_sq]

/-- `ι₊ : ω ↦ -r`. -/
noncomputable def ιp (H : Hyp tab M) : L42 →+* K7 := qaLift σ7 (-r7 H) (hu_p H)

/-- `ι₋ : ω ↦ r`. -/
noncomputable def ιm (H : Hyp tab M) : L42 →+* K7 := qaLift σ7 (r7 H) (hu_m H)

theorem ιp_four_eN (H : Hyp tab M) : ιp H (4 * eN) = σ7 (2 * eaK) - σ7 (2 * ebK) * r7 H := by
  have h4 : (4 : L42) * eN = ⟨2 * eaK, 2 * ebK⟩ := by
    ext <;> simp [eN, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring
  rw [h4, ιp, qaLift_mk]; ring

theorem ιm_four_eN (H : Hyp tab M) : ιm H (4 * eN) = σ7 (2 * eaK) + σ7 (2 * ebK) * r7 H := by
  have h4 : (4 : L42) * eN = ⟨2 * eaK, 2 * ebK⟩ := by
    ext <;> simp [eN, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring
  rw [h4, ιm, qaLift_mk]

/-! ## `S` and the embeddings `ι_N (±)` of `N84` -/

theorem int7K (x : K21) (hx : ∃ a : List ℤ, x = zkE a) : ‖σ7 x‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ := hx; exact int7 a

theorem norm_two_eb : ‖σ7 (2 * ebK)‖ ≤ 1 := by
  rw [map_mul, map_ofNat, norm_mul, two7, one_mul, ebK]; exact int7 _

theorem exists_S (H : Hyp tab M) :
    ∃ S : K7, S ^ 2 = ιp H (4 * eN) ∧ ‖S - σ7 (zkE M.S0)‖ ≤ δ7 M := by
  obtain ⟨-, -, eS, nS, -, -⟩ := H.facts
  have hz : ‖ιp H (4 * eN)‖ ≤ 1 := by
    rw [ιp_four_eN, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [map_mul, map_ofNat, norm_mul, two7, one_mul, eaK]; exact int7 _
    · rw [norm_neg, norm_mul]
      calc ‖σ7 (2 * ebK)‖ * ‖r7 H‖ ≤ 1 * 1 :=
            mul_le_mul norm_two_eb (r7_norm H) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have hd : σ7 (zkE M.S0) ^ 2 - ιp H (4 * eN) =
      π7 ^ M.ns * σ7 (zkE M.S0R) + σ7 (2 * ebK) * (r7 H - σ7 (zkE M.y0)) := by
    have e := congrArg σ7 eS
    simp only [map_sub, map_mul, map_pow, map_ofNat] at e
    rw [ιp_four_eN, sq]
    simp only [map_mul, map_ofNat]
    linear_combination e
  have hdn : ‖σ7 (zkE M.S0) ^ 2 - ιp H (4 * eN)‖ ≤ δ7 M := by
    rw [hd]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      calc ‖π7‖ ^ M.ns * ‖σ7 (zkE M.S0R)‖ ≤ ‖π7‖ ^ M.ns * 1 :=
            mul_le_mul_of_nonneg_left (int7 _) (pow_nonneg (norm_nonneg _) _)
        _ ≤ δ7 M := by rw [mul_one]; exact pow_le_δ7 (min_le_right _ _)
    · rw [norm_mul]
      calc ‖σ7 (2 * ebK)‖ * ‖r7 H - σ7 (zkE M.y0)‖ ≤ 1 * δ7 M :=
            mul_le_mul norm_two_eb (r7_near H) (norm_nonneg _) zero_le_one
        _ = δ7 M := one_mul _
  have h2s : ‖2 * σ7 (zkE M.S0)‖ = 1 := by rw [norm_mul, two7, nS, one_mul]
  obtain ⟨S, hS, hSn⟩ := exists_sqrt_near hz nS.le (by rw [h2s, one_pow]; exact hdn.trans_lt (δ7_lt_one H))
  exact ⟨S, hS, by rw [h2s, div_one] at hSn; exact hSn.trans hdn⟩

/-- The square root of `ι₊ (4 eN)` near `σ S0`. -/
noncomputable def S7 (H : Hyp tab M) : K7 := (exists_S H).choose

theorem S7_sq (H : Hyp tab M) : S7 H ^ 2 = ιp H (4 * eN) := (exists_S H).choose_spec.1

theorem S7_near (H : Hyp tab M) : ‖S7 H - σ7 (zkE M.S0)‖ ≤ δ7 M := (exists_S H).choose_spec.2

/-- `± S / 2`. -/
noncomputable def uS (H : Hyp tab M) (b : Bool) : K7 := if b then S7 H / 2 else -S7 H / 2

theorem hs_N (H : Hyp tab M) (b : Bool) :
    (if b then S7 H / 2 else -S7 H / 2) * (if b then S7 H / 2 else -S7 H / 2) =
      ιp H eN + ιp H 0 * (if b then S7 H / 2 else -S7 H / 2) := by
  have h := S7_sq H
  rw [map_mul, map_ofNat] at h
  rw [map_zero, zero_mul, add_zero]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    linear_combination (1 / 4 : K7) * h

/-- `ι_N (±) : Ω ↦ ± S` (`ω_N ↦ ± S / 2`). -/
noncomputable def ιN (H : Hyp tab M) (b : Bool) : N84 →+* K7 :=
  qaLift (ιp H) (if b then S7 H / 2 else -S7 H / 2) (hs_N H b)

/-! ## `A4` and the Eisenstein component -/

/-- `A4 = ι₋ (4 eN)`. -/
noncomputable def A4 (H : Hyp tab M) : K7 := ιm H (4 * eN)

theorem A4_near (H : Hyp tab M) : ‖A4 H - σ7 (zkE al7 * zkE M.E4U)‖ ≤ δ7 M := by
  obtain ⟨-, -, -, -, eE, -⟩ := H.facts
  have hd : A4 H - σ7 (zkE al7 * zkE M.E4U) = σ7 (2 * ebK) * (r7 H - σ7 (zkE M.y0)) := by
    rw [A4, ιm_four_eN, ← eE]
    simp only [map_add, map_mul, map_ofNat]; ring
  rw [hd, norm_mul]
  calc ‖σ7 (2 * ebK)‖ * ‖r7 H - σ7 (zkE M.y0)‖ ≤ 1 * δ7 M :=
        mul_le_mul norm_two_eb (r7_near H) (norm_nonneg _) zero_le_one
    _ = δ7 M := one_mul _

theorem A4_norm (H : Hyp tab M) : ‖A4 H‖ = ‖π7‖ := by
  obtain ⟨-, -, -, -, -, nE⟩ := H.facts
  have ht : ‖σ7 (zkE al7 * zkE M.E4U)‖ = ‖π7‖ := by rw [map_mul, norm_mul, nE, mul_one]
  have hlt : ‖A4 H - σ7 (zkE al7 * zkE M.E4U)‖ < ‖σ7 (zkE al7 * zkE M.E4U)‖ := by
    rw [ht]; exact (A4_near H).trans_lt (δ7_lt_norm H)
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  rw [sub_add_cancel, max_eq_right hlt.le] at h
  rw [h, ht]

instance instFactA4 (H : Hyp tab M) : Fact (∀ x : K7, x ^ 2 ≠ A4 H + 0 * x) :=
  ⟨no_root_eisen unif7 (A4_norm H) (by simp)⟩

/-- The Eisenstein component `F' = K_w7 (√A4)`. -/
abbrev F7 (H : Hyp tab M) : Type := QF K7 (A4 H) 0

/-- `Z = √A4`, a uniformizer of `F7 H`. -/
noncomputable abbrev Z7 (H : Hyp tab M) : F7 H := QF.mk K7 (A4 H) 0 0 1

theorem hu' (H : Hyp tab M) :
    QF.mk K7 (A4 H) 0 0 (1 / 2) * QF.mk K7 (A4 H) 0 0 (1 / 2) =
      (algebraMap K7 (F7 H)).comp (ιm H) eN +
        (algebraMap K7 (F7 H)).comp (ιm H) 0 * QF.mk K7 (A4 H) 0 0 (1 / 2) := by
  have h4 : ιm H eN = A4 H / 4 := by
    rw [A4, map_mul, map_ofNat]; field_simp
  rw [RingHom.comp_apply, RingHom.comp_apply, map_zero, map_zero, zero_mul, add_zero, h4]
  change (⟨0, 1 / 2⟩ : QuadraticAlgebra K7 (A4 H) 0) * ⟨0, 1 / 2⟩ =
    algebraMap K7 (QuadraticAlgebra K7 (A4 H) 0) (A4 H / 4)
  ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re]; ring
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_im]; ring

/-- `ι' : N84 → F'`, extending `ι₋` by `Ω ↦ Z` (`ω_N ↦ Z / 2`). -/
noncomputable def ι' (H : Hyp tab M) : N84 →+* F7 H :=
  qaLift ((algebraMap K7 (F7 H)).comp (ιm H)) (QF.mk K7 (A4 H) 0 0 (1 / 2)) (hu' H)

/-! ## Compatibility with `σ7` -/

theorem ιp_comp (H : Hyp tab M) : (ιp H).comp (algebraMap K21 L42) = (algebraMap K7 K7).comp σ7 :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, ιp, qaLift_algebraMap]; rfl

theorem ιm_comp (H : Hyp tab M) : (ιm H).comp (algebraMap K21 L42) = (algebraMap K7 K7).comp σ7 :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, ιm, qaLift_algebraMap]; rfl

theorem ιN_comp (H : Hyp tab M) (b : Bool) :
    (ιN H b).comp (algebraMap K21 N84) = (algebraMap K7 K7).comp σ7 :=
  RingHom.ext fun x => by
    rw [RingHom.comp_apply, algebraMap_N84, ιN, qaLift_mk, map_zero, zero_mul, add_zero, ιp,
      qaLift_algebraMap]; rfl

theorem ι'_comp (H : Hyp tab M) :
    (ι' H).comp (algebraMap K21 N84) = (algebraMap K7 (F7 H)).comp σ7 :=
  RingHom.ext fun x => by
    rw [RingHom.comp_apply, algebraMap_N84, ι', qaLift_mk, map_zero, zero_mul, add_zero,
      RingHom.comp_apply, ιm, qaLift_algebraMap, RingHom.comp_apply]

/-! ## The five components -/

/-- The four components `K_w7`: `T ↦ ι₊ α`, `ι₋ α`, `ι_N (+) β`, `ι_N (-) β`. -/
noncomputable def ev4 (H : Hyp tab M) : Fin 4 → (AdjoinRoot ((fRev 1).map σ7) →+* K7) :=
  ![evAt σ7 (ιp H) (ιp_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1),
    evAt σ7 (ιm H) (ιm_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1),
    evAt σ7 (ιN H true) (ιN_comp H true) (fRev 1) betaR (aeval_betaR_fRev 1),
    evAt σ7 (ιN H false) (ιN_comp H false) (fRev 1) betaR (aeval_betaR_fRev 1)]

/-- The component `F'`: `T ↦ ι' β`. -/
noncomputable def ev' (H : Hyp tab M) : AdjoinRoot ((fRev 1).map σ7) →+* F7 H :=
  evAt σ7 (ι' H) (ι'_comp H) (fRev 1) betaR (aeval_betaR_fRev 1)

/-- `(K_w7[T]/(fRev 1))ˣ → (Fin 4 → K_w7ˣ) × F'ˣ`. -/
noncomputable def evG (H : Hyp tab M) :
    (AdjoinRoot ((fRev 1).map σ7))ˣ →* (Fin 4 → K7ˣ) × (F7 H)ˣ :=
  (MonoidHom.pi fun c => Units.map (ev4 H c).toMonoidHom).prod (Units.map (ev' H).toMonoidHom)

theorem evG_fst (H : Hyp tab M) (u : (AdjoinRoot ((fRev 1).map σ7))ˣ) (c : Fin 4) :
    (((evG H u).1 c : K7ˣ) : K7) = ev4 H c (u : AdjoinRoot ((fRev 1).map σ7)) := rfl

theorem evG_snd (H : Hyp tab M) (u : (AdjoinRoot ((fRev 1).map σ7))ˣ) :
    (((evG H u).2 : (F7 H)ˣ) : F7 H) = ev' H (u : AdjoinRoot ((fRev 1).map σ7)) := rfl

theorem ev4_mk (H : Hyp tab M) (P : K21[X]) :
    ev4 H 0 (AdjoinRoot.mk _ (P.map σ7)) = ιp H (aeval alphaR P) ∧
    ev4 H 1 (AdjoinRoot.mk _ (P.map σ7)) = ιm H (aeval alphaR P) ∧
    ev4 H 2 (AdjoinRoot.mk _ (P.map σ7)) = ιN H true (aeval betaR P) ∧
    ev4 H 3 (AdjoinRoot.mk _ (P.map σ7)) = ιN H false (aeval betaR P) :=
  ⟨evAt_mk σ7 _ (ιp_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1) P,
    evAt_mk σ7 _ (ιm_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1) P,
    evAt_mk σ7 _ (ιN_comp H true) (fRev 1) betaR (aeval_betaR_fRev 1) P,
    evAt_mk σ7 _ (ιN_comp H false) (fRev 1) betaR (aeval_betaR_fRev 1) P⟩

theorem ev'_mk (H : Hyp tab M) (P : K21[X]) :
    ev' H (AdjoinRoot.mk _ (P.map σ7)) = ι' H (aeval betaR P) :=
  evAt_mk σ7 _ (ι'_comp H) (fRev 1) betaR (aeval_betaR_fRev 1) P

theorem ev4_etale (H : Hyp tab M) (P : K21[X]) :
    ev4 H 0 (etaleMap σ7 (fRev 1) (AdjoinRoot.mk _ P)) = ιp H (aeval alphaR P) ∧
    ev4 H 1 (etaleMap σ7 (fRev 1) (AdjoinRoot.mk _ P)) = ιm H (aeval alphaR P) ∧
    ev4 H 2 (etaleMap σ7 (fRev 1) (AdjoinRoot.mk _ P)) = ιN H true (aeval betaR P) ∧
    ev4 H 3 (etaleMap σ7 (fRev 1) (AdjoinRoot.mk _ P)) = ιN H false (aeval betaR P) :=
  ⟨evAt_etaleMap σ7 _ (ιp_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1) P,
    evAt_etaleMap σ7 _ (ιm_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1) P,
    evAt_etaleMap σ7 _ (ιN_comp H true) (fRev 1) betaR (aeval_betaR_fRev 1) P,
    evAt_etaleMap σ7 _ (ιN_comp H false) (fRev 1) betaR (aeval_betaR_fRev 1) P⟩

theorem ev'_etale (H : Hyp tab M) (P : K21[X]) :
    ev' H (etaleMap σ7 (fRev 1) (AdjoinRoot.mk _ P)) = ι' H (aeval betaR P) :=
  evAt_etaleMap σ7 _ (ι'_comp H) (fRev 1) betaR (aeval_betaR_fRev 1) P

theorem ev4_algebraMap (H : Hyp tab M) (c : Fin 4) (x : K7) :
    ev4 H c (algebraMap K7 (AdjoinRoot ((fRev 1).map σ7)) x) = x := by
  fin_cases c
  · exact evAt_algebraMap σ7 _ (ιp_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1) x
  · exact evAt_algebraMap σ7 _ (ιm_comp H) (fRev 1) alphaR (aeval_alphaR_fRev 1) x
  · exact evAt_algebraMap σ7 _ (ιN_comp H true) (fRev 1) betaR (aeval_betaR_fRev 1) x
  · exact evAt_algebraMap σ7 _ (ιN_comp H false) (fRev 1) betaR (aeval_betaR_fRev 1) x

theorem ev'_algebraMap (H : Hyp tab M) (x : K7) :
    ev' H (algebraMap K7 (AdjoinRoot ((fRev 1).map σ7)) x) = algebraMap K7 (F7 H) x :=
  evAt_algebraMap σ7 _ (ι'_comp H) (fRev 1) betaR (aeval_betaR_fRev 1) x

/-! ## The approximations -/

theorem approxLp (H : Hyp tab M) (x : LC) : ‖ιp H (evL x) - σ7 (evK (XLp M.y0 x))‖ ≤ δ7 M :=
  norm_XLp_sub σ7 int7 (r7_near H) (hu_p H) x

theorem approxLm (H : Hyp tab M) (x : LC) : ‖ιm H (evL x) - σ7 (evK (XLm M.y0 x))‖ ≤ δ7 M :=
  norm_XLm_sub σ7 int7 (r7_near H) (hu_m H) x

theorem approxN (H : Hyp tab M) (b : Bool) (x : NC) :
    ‖ιN H b (evN x) - σ7 (evK (XNs M.y0 M.S0 b x))‖ ≤ δ7 M :=
  norm_XNs_sub σ7 int7 two7_ne_zero (δ7_le_one M) (r7_near H) (S7_near H) (hu_p H) b (hs_N H b) x

theorem approx' (H : Hyp tab M) (x : NC) :
    ι' H (evN x) = QF.mk K7 (A4 H) 0 (ιm H (evL x.1)) (ιm H (evL x.2)) :=
  iota'_evN two7_ne_zero (ιm H) (hu' H) x

end FurioLombardo.Discharge.SelmerBasis.W7
