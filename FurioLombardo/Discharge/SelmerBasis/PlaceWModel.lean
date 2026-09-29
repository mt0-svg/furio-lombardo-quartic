import FurioLombardo.Discharge.SelmerBasis.PlaceWCert
import FurioLombardo.Discharge.SelmerBasis.GlobalGens

/-!
# `L42` and `N84` inside an Eisenstein component (lane selmer-basis w-places)

At a place `σ : K21 →+* Kw` with an Eisenstein component `F = CF σ E` (PlaceWCert.lean), the
model data `M : LModel` give `ω ↦ y + c Y` with `(y + c Y)² = ε` (two `checkK` identities), hence
the ring hom `iL : L42 →+* F`. A square root `sF` of `iL (4 eN)` near a global approximation
(`SqrtData`, Hensel's lemma `exists_sqrt_near`) gives the two ring homs `iN M hM S hS b : N84 →+* F`,
`w_N ↦ ± sF / 2` (`b = true` for `+`).

`evAt`: for a ring hom `ψ : A →+* F` over `σ` and a root `α ∈ A` of `fRev k`, the ring hom
`K_w[T]/(fRev k)^σ →+* F`, `T ↦ ψ α`, with `evAt_mk`: the class of `P^σ` goes to `ψ (P(α))`.

Data format: code/selmer-local-conditions/local_data_w6.gp.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.M3a.Bruin

/-- The model `ω ↦ y + c Y` (zk lists) and the precision of its checks. -/
structure LModel where
  y : List ℤ
  c : List ℤ
  prec : ℕ
  deriving Inhabited

/-- `y² + c² A = ε` and `2 y + c B = 0`. -/
def LModel.ok (E : EisData) (M : LModel) : Bool :=
  checkK M.prec (.sub (.add (.mul (.lin M.y) (.lin M.y)) (.mul (.mul (.lin M.c) (.lin M.c))
    (.lin E.A))) (.lin epsL)) &&
  checkK M.prec (.add (.mul (.int 2) (.lin M.y)) (.mul (.lin M.c) (.lin E.B)))

/-- A square root certificate for `iL (4 eN)`: `s0 = s00 + s01 Y` with `s00 = al^j (1 + al d0)`,
`s01 = al^j d1`, and `s0² - iL (4 eN) = al^n (R0 + R1 Y)`. -/
structure SqrtData where
  j : ℕ
  n : ℕ
  s00 : List ℤ
  s01 : List ℤ
  d0 : List ℤ
  d1 : List ℤ
  R0 : List ℤ
  R1 : List ℤ
  prec : ℕ
  deriving Inhabited

/-- The kernel checks of a `SqrtData`. -/
def SqrtData.ok (E : EisData) (M : LModel) (S : SqrtData) : Bool :=
  decide (S.n < E.alPow.length) && decide (S.j + 1 < E.alPow.length) &&
  decide (2 * E.e + 2 * S.j < S.n) &&
  checkK S.prec (.sub (.lin S.s00) (.mul (.lin (E.alP S.j)) (.add (.int 1)
    (.mul (.lin E.al) (.lin S.d0))))) &&
  checkK S.prec (.sub (.lin S.s01) (.mul (.lin (E.alP S.j)) (.lin S.d1))) &&
  -- coordinate 1 of `s0² - (2 ea + 2 eb y) - 2 eb c Y`
  checkK S.prec (.sub (.sub (.add (.mul (.lin S.s00) (.lin S.s00))
      (.mul (.mul (.lin S.s01) (.lin S.s01)) (.lin E.A)))
      (.mul (.int 2) (.add (.lin eaL) (.mul (.lin ebL) (.lin M.y)))))
    (.mul (.lin (E.alP S.n)) (.lin S.R0))) &&
  -- coordinate `Y`
  checkK S.prec (.sub (.sub (.add (.mul (.int 2) (.mul (.lin S.s00) (.lin S.s01)))
      (.mul (.mul (.lin S.s01) (.lin S.s01)) (.lin E.B)))
      (.mul (.int 2) (.mul (.lin ebL) (.lin M.c))))
    (.mul (.lin (E.alP S.n)) (.lin S.R1)))

section Model

variable {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw]
  {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r)]
  {M : LModel}

theorem LModel.ok_eps (h : M.ok E = true) : zkE M.y ^ 2 + zkE M.c ^ 2 * zkE E.A = epsK := by
  simp only [LModel.ok, Bool.and_eq_true] at h
  have e := evK_eq_of_check _ _ _ h.1
  simp only [evK_add, evK_mul, evK_lin] at e
  rw [epsK_eq, ← e]; ring

theorem LModel.ok_B (h : M.ok E = true) : 2 * zkE M.y + zkE M.c * zkE E.B = 0 := by
  simp only [LModel.ok, Bool.and_eq_true] at h
  have e := evK_eq_zero_of_check _ _ h.2
  simpa [evK_add, evK_mul, evK_lin, evK_int] using e

variable (σ E M)

/-- The image `y + c Y` of `ω`. -/
noncomputable def omF : CF σ E := toF σ E (zkE M.y) (zkE M.c)

variable {σ E M}

theorem omF_sq (hM : M.ok E = true) : omF σ E M * omF σ E M =
    ((algebraMap Kw (CF σ E)).comp σ) epsK + ((algebraMap Kw (CF σ E)).comp σ) 0 * omF σ E M := by
  have hY := cY_sq (σ := σ) (E := E)
  have h1 := LModel.ok_eps hM
  have h2 := LModel.ok_B hM
  simp only [RingHom.comp_apply, map_zero, zero_mul, add_zero, omF, toF_eq]
  rw [← h1]
  have h2' : algebraMap Kw (CF σ E) (σ (zkE M.c)) * algebraMap Kw (CF σ E) (σ (zkE E.B)) =
      -(2 * algebraMap Kw (CF σ E) (σ (zkE M.y))) := by
    have := congrArg (fun z => algebraMap Kw (CF σ E) (σ z)) h2
    simp only [map_add, map_mul, map_ofNat, map_zero] at this
    linear_combination this
  simp only [map_add, map_mul, map_pow]
  linear_combination (algebraMap Kw (CF σ E) (σ (zkE M.c)) ^ 2) * hY +
    (algebraMap Kw (CF σ E) (σ (zkE M.c)) * cY σ E) * h2'

variable (σ E M)

/-- **`L42 →+* F`**, `ω ↦ y + c Y`. -/
noncomputable def iL (hM : M.ok E = true) : L42 →+* CF σ E :=
  qaLift ((algebraMap Kw (CF σ E)).comp σ) (omF σ E M) (omF_sq hM)

variable {σ E M}

theorem iL_apply (hM : M.ok E = true) (z : L42) :
    iL σ E M hM z = toF σ E (z.re + z.im * zkE M.y) (z.im * zkE M.c) := by
  rw [iL, qaLift_apply, omF, toF_eq, toF_eq]
  simp only [RingHom.comp_apply, map_add, map_mul]
  ring

theorem iL_algebraMap (hM : M.ok E = true) (x : K21) :
    iL σ E M hM (algebraMap K21 L42 x) = algebraMap Kw (CF σ E) (σ x) := by
  rw [iL, qaLift_algebraMap]; rfl

theorem iL_comp_algebraMap (hM : M.ok E = true) :
    (iL σ E M hM).comp (algebraMap K21 L42) = (algebraMap Kw (CF σ E)).comp σ :=
  RingHom.ext fun x => iL_algebraMap hM x

/-! ## The square root of `iL (4 eN)` -/

theorem iL_four_eN (hM : M.ok E = true) :
    iL σ E M hM (4 * eN) = toF σ E (2 * zkE eaL + 2 * zkE ebL * zkE M.y) (2 * zkE ebL * zkE M.c) := by
  rw [← Tower.evL_e4LC, iL_apply]
  simp only [Tower.evL, Tower.e4LC, evK_mul, evK_int, evK_lin, Int.cast_ofNat]

theorem toF_mul (u v u' v' : K21) : toF σ E u v * toF σ E u' v' =
    toF σ E (u * u' + v * v' * zkE E.A) (u * v' + v * u' + v * v' * zkE E.B) := by
  have hY := cY_sq (σ := σ) (E := E)
  simp only [toF_eq, map_add, map_mul]
  linear_combination (algebraMap Kw (CF σ E) (σ v) * algebraMap Kw (CF σ E) (σ v')) * hY

theorem norm_toF_unit (hW : WPlace σ E) (d0 d1 : List ℤ) :
    ‖toF σ E (1 + zkE E.al * zkE d0) (zkE d1)‖ = 1 := by
  have hπ1 := hW.unif.norm_lt_one
  have hsmall : ‖σ (zkE E.al * zkE d0)‖ < 1 := by
    rw [map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hW.int _)) hπ1
  have h1 : ‖σ (1 + zkE E.al * zkE d0)‖ = 1 := by
    rw [map_add, map_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_one]; exact hsmall.ne'), norm_one, max_eq_left hsmall.le]
  rw [toF, qfE_norm hW.unif hW.norm_A hW.norm_B, h1]
  refine max_eq_left ?_
  calc ‖σ (zkE d1)‖ * ‖QF.mk Kw (σ (zkE E.A)) (σ (zkE E.B)) 0 1‖ ≤ 1 * 1 :=
        mul_le_mul (hW.int _) (norm_cY_lt_one hW).le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem exists_sF [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) :
    ∃ s : CF σ E, s ^ 2 = iL σ E M hM (4 * eN) ∧
      ‖s - toF σ E (zkE S.s00) (zkE S.s01)‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  simp only [SqrtData.ok, Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨hnl, hjl⟩, hn⟩, hs00⟩, hs01⟩, hI0⟩, hI1⟩ := hS
  have e00 : zkE S.s00 = zkE E.al ^ S.j * (1 + zkE E.al * zkE S.d0) := by
    have := evK_eq_of_check _ _ _ hs00
    simp only [evK_lin, evK_mul, evK_add, evK_int, Int.cast_one] at this
    rw [this, EisData.ok_alP hW.ok _ (by omega)]
  have e01 : zkE S.s01 = zkE E.al ^ S.j * zkE S.d1 := by
    have := evK_eq_of_check _ _ _ hs01
    simp only [evK_lin, evK_mul] at this
    rw [this, EisData.ok_alP hW.ok _ (by omega)]
  have e0 := evK_eq_of_check _ _ _ hI0
  have e1 := evK_eq_of_check _ _ _ hI1
  simp only [evK_lin, evK_mul, evK_add, evK_sub, evK_int, Int.cast_ofNat,
    EisData.ok_alP hW.ok _ hnl] at e0 e1
  set π := σ (zkE E.al) with hπdef
  have hπ1 := hW.unif.norm_lt_one
  have hπ0 : 0 < ‖π‖ := norm_pos_iff.mpr hW.unif.ne_zero
  set s0 := toF σ E (zkE S.s00) (zkE S.s01) with hs0
  set z := iL σ E M hM (4 * eN) with hz
  have hzF : z = toF σ E (2 * zkE eaL + 2 * zkE ebL * zkE M.y) (2 * zkE ebL * zkE M.c) :=
    iL_four_eN hM
  -- `s0² - z = π^n (R0 + R1 Y)`
  have hdiff : s0 ^ 2 - z = algebraMap Kw (CF σ E) (π ^ S.n) * toF σ E (zkE S.R0) (zkE S.R1) := by
    rw [sq, hs0, toF_mul, hzF, ← map_pow, ← toF_smul]
    have hsub : ∀ u v u' v' : K21, toF σ E u v - toF σ E u' v' = toF σ E (u - u') (v - v') := by
      intro u v u' v'; simp only [toF_eq, map_sub]; ring
    rw [hsub]
    congr 1
    · linear_combination e0
    · linear_combination e1
  have hdn : ‖s0 ^ 2 - z‖ ≤ ‖π‖ ^ S.n := by
    rw [hdiff, norm_mul, QF.norm_algebraMap, norm_pow]
    have := norm_toF_le_one hW (.lin S.R0) (.lin S.R1)
    simp only [evK_lin] at this
    exact mul_le_of_le_one_right (by positivity) this
  have hs0n : ‖s0‖ = ‖π‖ ^ S.j := by
    rw [hs0, e00, e01, toF_smul, norm_mul, QF.norm_algebraMap, norm_toF_unit hW, map_pow, norm_pow,
      mul_one]
  have h2F : ‖(2 : CF σ E)‖ = ‖π‖ ^ E.e := by
    rw [show (2 : CF σ E) = algebraMap Kw (CF σ E) 2 from (map_ofNat _ 2).symm, QF.norm_algebraMap,
      hW.two]
  have h2s0 : ‖2 * s0‖ = ‖π‖ ^ (E.e + S.j) := by rw [norm_mul, h2F, hs0n, pow_add]
  have hz1 : ‖z‖ ≤ 1 := by
    have := norm_toF_le_one hW (.add (.mul (.int 2) (.lin eaL)) (.mul (.mul (.int 2) (.lin ebL))
      (.lin M.y))) (.mul (.mul (.int 2) (.lin ebL)) (.lin M.c))
    simp only [evK_lin, evK_mul, evK_add, evK_int, Int.cast_ofNat] at this
    rwa [hzF]
  have hs01 : ‖s0‖ ≤ 1 := by rw [hs0n]; exact pow_le_one₀ hπ0.le hπ1.le
  have hlt : ‖s0 ^ 2 - z‖ < ‖2 * s0‖ ^ 2 := by
    rw [h2s0, ← pow_mul]
    exact lt_of_le_of_lt hdn (pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 (by omega))
  obtain ⟨s, hs, hsn⟩ := exists_sqrt_near hz1 hs01 hlt
  refine ⟨s, hs, hsn.trans ?_⟩
  rw [h2s0, div_le_iff₀ (pow_pos hπ0 _), ← pow_add]
  calc ‖s0 ^ 2 - z‖ ≤ ‖π‖ ^ S.n := hdn
    _ = ‖π‖ ^ (S.n - E.e - S.j + (E.e + S.j)) := by congr 1; omega

variable (σ E M)

/-- The square root `sF` of `iL (4 eN)`. -/
noncomputable def sF [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) (S : SqrtData)
    (hS : S.ok E M = true) : CF σ E :=
  (exists_sF hW hM hS).choose

variable {σ E M}

theorem sF_sq [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) : sF σ E M hW hM S hS ^ 2 = iL σ E M hM (4 * eN) :=
  (exists_sF hW hM hS).choose_spec.1

theorem sF_near [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) :
    ‖sF σ E M hW hM S hS - toF σ E (zkE S.s00) (zkE S.s01)‖ ≤
      ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) :=
  (exists_sF hW hM hS).choose_spec.2

theorem two_ne_zero_CF (hW : WPlace σ E) : (2 : CF σ E) ≠ 0 := by
  have h2 : (2 : Kw) ≠ 0 := by
    intro h
    have := hW.two
    rw [h, norm_zero] at this
    exact absurd this.symm (pow_ne_zero _ (norm_ne_zero_iff.mpr hW.unif.ne_zero))
  have := (map_ne_zero (algebraMap Kw (CF σ E))).mpr h2
  rwa [map_ofNat] at this

theorem half_sF_sq [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) (b : Bool) :
    ((if b then 1 else -1) * sF σ E M hW hM S hS / 2) * ((if b then 1 else -1) * sF σ E M hW hM S hS / 2) =
      iL σ E M hM eN + iL σ E M hM 0 * ((if b then 1 else -1) * sF σ E M hW hM S hS / 2) := by
  have h := sF_sq hW hM hS
  have h4 : iL σ E M hM (4 * eN) = 4 * iL σ E M hM eN := by rw [map_mul, map_ofNat]
  rw [map_zero, zero_mul, add_zero]
  have h2 := two_ne_zero_CF hW
  field_simp
  cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> linear_combination h.trans h4

variable (σ E M)

/-- **`N84 →+* F`**, `w_N ↦ ± sF / 2` (`b = true`: `+`). -/
noncomputable def iN [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) (S : SqrtData)
    (hS : S.ok E M = true) (b : Bool) : N84 →+* CF σ E :=
  qaLift (iL σ E M hM) ((if b then 1 else -1) * sF σ E M hW hM S hS / 2) (half_sF_sq hW hM hS b)

variable {σ E M}

theorem iN_apply [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) (b : Bool) (z : N84) :
    iN σ E M hW hM S hS b z =
      iL σ E M hM z.re + iL σ E M hM z.im * ((if b then 1 else -1) * sF σ E M hW hM S hS / 2) :=
  rfl

theorem iN_algebraMap [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) (b : Bool) (x : K21) :
    iN σ E M hW hM S hS b (algebraMap K21 N84 x) = algebraMap Kw (CF σ E) (σ x) := by
  rw [Tower.algebraMap_N84, iN_apply]
  simp only [map_zero, zero_mul, add_zero]
  exact iL_algebraMap hM x

theorem iN_comp_algebraMap [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) (b : Bool) :
    (iN σ E M hW hM S hS b).comp (algebraMap K21 N84) = (algebraMap Kw (CF σ E)).comp σ :=
  RingHom.ext fun x => iN_algebraMap hW hM hS b x

end Model

/-! ## Evaluation at a root -/

section Ev

variable {Kw F A : Type*} [Field Kw] [Field F] [Algebra Kw F] [CommRing A] [Algebra K21 A]
  (σ : K21 →+* Kw) (ψ : A →+* F) (hψ : ψ.comp (algebraMap K21 A) = (algebraMap Kw F).comp σ)

include hψ in
theorem eval₂_map_eq_psi (α : A) (P : K21[X]) :
    (P.map σ).eval₂ (algebraMap Kw F) (ψ α) = ψ (aeval α P) := by
  rw [eval₂_map, ← hψ, aeval_def, hom_eval₂]

/-- **`T ↦ ψ α`** on `K_w[T]/(f^σ)`, for a root `α` of `f`. -/
noncomputable def evAt (f : K21[X]) (α : A) (hα : aeval α f = 0) : AdjoinRoot (f.map σ) →+* F :=
  AdjoinRoot.lift (algebraMap Kw F) (ψ α) (by rw [eval₂_map_eq_psi σ ψ hψ, hα, map_zero])

theorem evAt_mk (f : K21[X]) (α : A) (hα : aeval α f = 0) (P : K21[X]) :
    evAt σ ψ hψ f α hα (AdjoinRoot.mk (f.map σ) (P.map σ)) = ψ (aeval α P) := by
  rw [evAt, AdjoinRoot.lift_mk, eval₂_map_eq_psi σ ψ hψ]

theorem evAt_etaleMap (f : K21[X]) (α : A) (hα : aeval α f = 0) (P : K21[X]) :
    evAt σ ψ hψ f α hα (FurioLombardo.M3a.Genus2.etaleMap σ f (AdjoinRoot.mk f P)) =
      ψ (aeval α P) := by
  rw [FurioLombardo.M3a.Genus2.etaleMap, AdjoinRoot.map_mk, evAt_mk]

theorem evAt_algebraMap (f : K21[X]) (α : A) (hα : aeval α f = 0) (c : Kw) :
    evAt σ ψ hψ f α hα (algebraMap Kw (AdjoinRoot (f.map σ)) c) = algebraMap Kw F c := by
  rw [evAt, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]

end Ev

end FurioLombardo.Discharge.SelmerBasis
