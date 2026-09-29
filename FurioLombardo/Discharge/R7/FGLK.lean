import Mathlib
import FurioLombardo.Discharge.R7.Formal
import FurioLombardo.Discharge.R7.LineStep
import FurioLombardo.Discharge.M3a.PolyK
import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.FormalGroupLaw.Basic

/-!
# The formal addition law is a formal group law (item R7)

From a `Setup K` (`FurioLombardo.Discharge.R7.Formal`), the addition series `G = S.G` of the chart of `Jac` at the
class `E0 = [⟨X², Y - v0⟩]` satisfies the axioms of a commutative formal group law over `K`.

The proof uses no identity theorem. For a field `L`, a ring homomorphism `Φ2 : K⟦s, s'⟧ → L`
over `ψ : K → L` and `GoodSextic (f.map ψ)`, the two line steps (`mk0_add_law`) turn the formal
identities of `Formal.lean` into the law `χ(s) χ(s') = E0 χ(G(s, s'))` of classes of Mumford
ideals over `L` (`law_hom`). Over `L = Frac K⟦τ⟧` for the substitutions `(s, s') ↦ (a, b)` of
families without constant term this reads `χ(a) χ(b) = E0 χ(G(a, b))` (`law_frac`), with
`χ(0) = E0` (`chi_zero`); chart injectivity over `L` (`eq_of_mk0_mumford_eq`) then gives the
axioms `G(X, 0) = X`, `G(0, X) = X`, commutativity and associativity in `K⟦τ⟧`.
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.Conv FurioLombardo.Vendor.Toolbox.SqrtMod

namespace FurioLombardo.Discharge.R7

variable {K : Type*} [Field K]

/-! ### Classes of Mumford pairs with a quadratic of the form `uT t` -/

section Cls

variable {L : Type*} [Field L] (fL : L[X]) [GoodSextic fL]

/-- The class of `⟨X² + t₀ X + t₁, Y - v⟩`. -/
noncomputable def cls (t : Fin 2 → L) (v : L[X]) : ClassGroup (CoordRing fL) :=
  ClassGroup.mk0 (mumford0 fL (uT_monic t).ne_zero v)

theorem mk0_eq_cls {u : L[X]} (hu : u ≠ 0) {t : Fin 2 → L} (h : u = uT t) (v : L[X]) :
    ClassGroup.mk0 (mumford0 fL hu v) = cls fL t v := by
  subst h; rfl

/-- Chart injectivity for classes `cls`. -/
theorem eq_of_cls_eq {t1 t2 : Fin 2 → L} {v1 v2 : L[X]} (h1 : uT t1 ∣ fL - v1 ^ 2)
    (h2 : uT t2 ∣ fL - v2 ^ 2) (h : cls fL t1 v1 = cls fL t2 v2) : t1 = t2 := by
  have h1' : uT t1 ∣ v1 ^ 2 - fL := by
    rw [← neg_sub]; exact (dvd_neg).mpr h1
  have h2' : uT t2 ∣ v2 ^ 2 - fL := by
    rw [← neg_sub]; exact (dvd_neg).mpr h2
  have := (eq_of_mk0_mumford_eq fL (uT_monic t1) (uT_monic t2) (uT_natDegree t1)
    (uT_natDegree t2) h1' h2' h).1
  have e1 := congrArg (fun p => p.coeff 1) this
  have e0 := congrArg (fun p => p.coeff 0) this
  simp only [uT, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at e1 e0
  funext i
  fin_cases i
  · simpa using e1
  · simpa using e0

end Cls

end FurioLombardo.Discharge.R7

namespace FurioLombardo.Vendor.Toolbox.G2Formal.Setup

open FurioLombardo.Discharge.R7

variable {K : Type*} [Field K] (S : Setup K)

/-! ### The law over a field, through a ring homomorphism -/

section Hom

variable {L : Type*} [Field L] (ψ : K →+* L) [GoodSextic (S.f.map ψ)]

/-- The chart class at a homomorphism `φ : K⟦t⟧ → L` (the point `t ↦ φ t`). -/
noncomputable def chi (φ : MvPowerSeries (Fin 2) K →+* L) : ClassGroup (CoordRing (S.f.map ψ)) :=
  cls (S.f.map ψ) (fun i => φ (MvPowerSeries.X i)) (S.v.map φ)

/-- The base class `E0 = [⟨X², Y - v0⟩]`. -/
noncomputable def E0 : ClassGroup (CoordRing (S.f.map ψ)) :=
  ClassGroup.mk0 (mumford0 (S.f.map ψ) (pow_ne_zero 2 X_ne_zero) (S.v0.map ψ))

theorem map_cst_hom {σ : Type*} (φ : MvPowerSeries σ K →+* L)
    (hφ : φ.comp MvPowerSeries.C = ψ) (p : K[X]) : (cst (σ := σ) p).map φ = p.map ψ := by
  rw [cst, coe_mapRingHom, Polynomial.map_map, hφ]

variable {ψ}

theorem chi_dvd (φ : MvPowerSeries (Fin 2) K →+* L) (hφ : φ.comp MvPowerSeries.C = ψ) :
    uT (fun i => φ (MvPowerSeries.X i)) ∣ S.f.map ψ - (S.v.map φ) ^ 2 := by
  have := Polynomial.map_dvd φ S.u1_dvd
  rwa [map_uT, Polynomial.map_sub, Polynomial.map_pow, map_cst_hom ψ φ hφ] at this

/-- **The addition law through a homomorphism** `Φ2 : K⟦s, s'⟧ → L`. -/
theorem law_hom (Φ2 : A2 K →+* L) (hΦ : Φ2.comp MvPowerSeries.C = ψ) (hc1 : Φ2 S.c1 ≠ 0)
    (hc2 : Φ2 S.c2 ≠ 0) :
    S.chi ψ (Φ2.comp ρL.toRingHom) * S.chi ψ (Φ2.comp ρR.toRingHom) =
      S.E0 ψ * S.chi ψ (Φ2.comp S.ρG.toRingHom) := by
  have hcst := map_cst_hom ψ Φ2 hΦ
  have hVu := Polynomial.map_dvd Φ2 S.uL_dvd_V_sub
  have hVu' := Polynomial.map_dvd Φ2 S.uR_dvd_V_sub
  have hWw : S.w.map Φ2 ∣ S.W.map Φ2 + S.V.map Φ2 := by
    rw [← Polynomial.map_add, S.W_add_V, Polynomial.map_mul]; exact dvd_mul_right _ _
  have hWX := Polynomial.map_dvd Φ2 S.X2_dvd_W_add_v0
  have hWu := Polynomial.map_dvd Φ2 S.u2_dvd_vG_add_W
  rw [Polynomial.map_sub] at hVu hVu'
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, hcst] at hWX
  rw [Polynomial.map_add] at hWu
  have hV : (S.V.map Φ2) ^ 2 - S.f.map ψ =
      C (-Φ2 S.c1) * ((uL.map Φ2) * (uR.map Φ2) * S.w.map Φ2) := by
    have := congrArg (Polynomial.map Φ2) S.f_sub_V_sq_eq
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
      hcst] at this
    rw [C_neg]
    linear_combination -this
  have hW : (S.W.map Φ2) ^ 2 - S.f.map ψ =
      C (-Φ2 S.c2) * (S.w.map Φ2 * X ^ 2 * S.u2.map Φ2) := by
    have := congrArg (Polynomial.map Φ2) S.f_sub_W_sq_eq
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, hcst] at this
    rw [C_neg]
    linear_combination -this
  have huL : uL.map Φ2 = uT (fun i => (Φ2.comp ρL.toRingHom) (MvPowerSeries.X i)) := by
    rw [map_uT]; congr 1; funext i
    simp only [Function.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, sb_X]
  have huR : uR.map Φ2 = uT (fun i => (Φ2.comp ρR.toRingHom) (MvPowerSeries.X i)) := by
    rw [map_uT]; congr 1; funext i
    simp only [Function.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, sb_X]
  have hu2 : S.u2.map Φ2 = uT (fun i => (Φ2.comp S.ρG.toRingHom) (MvPowerSeries.X i)) := by
    rw [S.u2_eq, map_uT]; congr 1; funext i
    simp only [Function.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, sb_X]
  have law := mk0_add_law (S.f.map ψ) (neg_ne_zero.mpr hc1) (neg_ne_zero.mpr hc2) ((uT_monic _).map Φ2).ne_zero
    ((uT_monic _).map Φ2).ne_zero (pow_ne_zero 2 X_ne_zero) (S.u2_monic.1.map Φ2).ne_zero
    hVu hVu' hV hWw hWX hW hWu
  rw [mk0_eq_cls _ _ huL, mk0_eq_cls _ _ huR, mk0_eq_cls _ _ hu2] at law
  simpa only [chi, E0, vL, vR, vG, Polynomial.map_map] using law

end Hom

/-! ### Substitutions into `K⟦τ⟧` and the field of fractions -/

section Frac

variable {τ : Type*} [Finite τ]

/-- The field of fractions of `K⟦τ⟧`. -/
abbrev Lf (K : Type*) [Field K] (τ : Type*) := FractionRing (MvPowerSeries τ K)

/-- The class `χ(a)` of the substitution `t ↦ a`, in the class group over `Frac K⟦τ⟧`. -/
noncomputable def chiF [GoodSextic (S.f.map (algebraMap K (Lf K τ)))]
    (a : Fin 2 → MvPowerSeries τ K) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    ClassGroup (CoordRing (S.f.map (algebraMap K (Lf K τ)))) :=
  S.chi (algebraMap K (Lf K τ))
    ((algebraMap (MvPowerSeries τ K) (Lf K τ)).comp (sb a ha).toRingHom)

theorem algebraMap_comp_sb_C {σ : Type*} [Finite σ] (e : σ → MvPowerSeries τ K)
    (he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0) :
    ((algebraMap (MvPowerSeries τ K) (Lf K τ)).comp (sb e he).toRingHom).comp MvPowerSeries.C =
      algebraMap K (Lf K τ) := by
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- The substituted addition series `G(a, b)`. -/
noncomputable def Gs (a b : Fin 2 → MvPowerSeries τ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) : Fin 2 → MvPowerSeries τ K :=
  fun i => sb (Sum.elim a b) (by rintro (j | j) <;> simp [ha, hb]) (S.G i)

theorem Gs_const (a b : Fin 2 → MvPowerSeries τ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff (S.Gs a b ha hb i) = 0 := by
  rw [Gs, constantCoeff_sb, S.G_const]

theorem sb_comp_sb {σ ρ : Type*} [Finite σ] [Finite ρ] (a : σ → MvPowerSeries ρ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (e : ρ → MvPowerSeries τ K)
    (he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0) :
    (sb e he).toRingHom.comp (sb a ha).toRingHom =
      (sb (fun i => sb e he (a i)) (fun i => by rw [constantCoeff_sb, ha])).toRingHom := by
  ext g : 1
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    sb_apply]
  exact MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero he) g

theorem sb_congr {σ : Type*} [Finite σ] {a b : σ → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (h : a = b) :
    (sb a ha).toRingHom = (sb b hb).toRingHom := by
  subst h; rfl

variable [GoodSextic (S.f.map (algebraMap K (Lf K τ)))]

theorem sb_ne_zero {σ : Type*} [Finite σ] (e : σ → MvPowerSeries τ K)
    (he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0) {g : MvPowerSeries σ K}
    (hg : MvPowerSeries.constantCoeff g ≠ 0) :
    algebraMap (MvPowerSeries τ K) (Lf K τ) (sb e he g) ≠ 0 := by
  rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
  intro h0
  apply hg
  rw [← constantCoeff_sb he, h0, map_zero]

/-- **The addition law over `Frac K⟦τ⟧`**: `χ(a) χ(b) = E0 χ(G(a, b))`. -/
theorem law_frac (a b : Fin 2 → MvPowerSeries τ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    S.chiF a ha * S.chiF b hb = S.E0 (algebraMap K (Lf K τ)) *
      S.chiF (S.Gs a b ha hb) (S.Gs_const a b ha hb) := by
  set e : Fin 2 ⊕ Fin 2 → MvPowerSeries τ K := Sum.elim a b with he_def
  have he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0 := by
    rintro (j | j) <;> simp [e, ha, hb]
  set Φ2 := (algebraMap (MvPowerSeries τ K) (Lf K τ)).comp (sb e he).toRingHom with hΦ2
  have law := S.law_hom Φ2 (algebraMap_comp_sb_C e he)
    (sb_ne_zero e he S.c1_ne) (sb_ne_zero e he S.c2_ne)
  have hL : Φ2.comp ρL.toRingHom =
      (algebraMap (MvPowerSeries τ K) (Lf K τ)).comp (sb a ha).toRingHom := by
    rw [hΦ2, RingHom.comp_assoc, sb_comp_sb]
    congr 1
    exact sb_congr _ _ (funext fun i => by rw [sb_X]; rfl)
  have hR : Φ2.comp ρR.toRingHom =
      (algebraMap (MvPowerSeries τ K) (Lf K τ)).comp (sb b hb).toRingHom := by
    rw [hΦ2, RingHom.comp_assoc, sb_comp_sb]
    congr 1
    exact sb_congr _ _ (funext fun i => by rw [sb_X]; rfl)
  have hG : Φ2.comp S.ρG.toRingHom = (algebraMap (MvPowerSeries τ K) (Lf K τ)).comp
      (sb (S.Gs a b ha hb) (S.Gs_const a b ha hb)).toRingHom := by
    rw [hΦ2, RingHom.comp_assoc, sb_comp_sb]
    rfl
  rw [hL, hR, hG] at law
  exact law

omit [GoodSextic (S.f.map (algebraMap K (Lf K τ)))] in
theorem zero_const : ∀ i, MvPowerSeries.constantCoeff ((0 : Fin 2 → MvPowerSeries τ K) i) = 0 :=
  fun i => by rw [Pi.zero_apply, map_zero]

/-- `χ(0) = E0`. -/
theorem chiF_zero : S.chiF (0 : Fin 2 → MvPowerSeries τ K) zero_const =
    S.E0 (algebraMap K (Lf K τ)) := by
  have h0 : ∀ g : MvPowerSeries (Fin 2) K, sb (0 : Fin 2 → MvPowerSeries τ K) zero_const g =
      MvPowerSeries.C (MvPowerSeries.constantCoeff g) := by
    intro g
    rw [sb_apply, MvPowerSeries.subst_zero_eq_C_constantCoeff]
    ext d
    simp [MvPowerSeries.coeff_map]
  have hu : uT (fun i => ((algebraMap (MvPowerSeries τ K) (Lf K τ)).comp
      (sb (0 : Fin 2 → MvPowerSeries τ K) zero_const).toRingHom) (MvPowerSeries.X i)) =
      (X ^ 2 : (Lf K τ)[X]) := by
    rw [← uT_zero]; congr 1; funext i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      sb_X, Pi.zero_apply, map_zero]
  have hv : S.v.map ((algebraMap (MvPowerSeries τ K) (Lf K τ)).comp
      (sb (0 : Fin 2 → MvPowerSeries τ K) zero_const).toRingHom) =
      S.v0.map (algebraMap K (Lf K τ)) := by
    rw [← S.v_map, Polynomial.map_map]
    congr 1
    ext g
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      h0]
    rw [MvPowerSeries.c_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  simp only [chiF, chi]
  rw [hv, E0, ← mk0_eq_cls _ (pow_ne_zero 2 X_ne_zero) hu.symm]

/-- Chart injectivity over `Frac K⟦τ⟧`. -/
theorem eq_of_chiF_eq {a b : Fin 2 → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (h : S.chiF a ha = S.chiF b hb) :
    a = b := by
  have hinj := IsFractionRing.injective (MvPowerSeries τ K) (Lf K τ)
  have ht := eq_of_cls_eq _ (S.chi_dvd _ (algebraMap_comp_sb_C a ha))
    (S.chi_dvd _ (algebraMap_comp_sb_C b hb)) h
  funext i
  apply hinj
  have := congrFun ht i
  simpa [sb_X] using this

end Frac

/-! ### `GoodSextic` over `Frac K⟦τ⟧` -/

section Good

omit [Field K] in
theorem lexOrder_C {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] {K : Type*} [Field K] {c : K}
    (hc : c ≠ 0) : MvPowerSeries.lexOrder (MvPowerSeries.C c : MvPowerSeries σ K) =
      ((toLex (0 : σ →₀ ℕ) : Lex (σ →₀ ℕ)) : WithTop (Lex (σ →₀ ℕ))) := by
  apply le_antisymm
  · exact MvPowerSeries.lexOrder_le_of_coeff_ne_zero (d := 0) (by simpa using hc)
  · rw [MvPowerSeries.le_lexOrder_iff]
    intro d hd
    exfalso
    have h0 : toLex (0 : σ →₀ ℕ) ≤ toLex d := Finsupp.toLex_monotone (zero_le (a := d))
    exact absurd hd (not_lt.mpr (WithTop.coe_le_coe.mpr h0))

omit [Field K] in
/-- If `p² = c q²` in `K⟦σ⟧` with `q ≠ 0`, then `c` is a square (compare lowest lexicographic
terms). -/
theorem isSquare_of_sq_eq_C_mul_sq {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] {K : Type*}
    [Field K] {p q : MvPowerSeries σ K} (c : K) (hq : q ≠ 0)
    (h : p * p = MvPowerSeries.C c * (q * q)) : IsSquare c := by
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  have hp : p ≠ 0 := by
    rintro rfl
    rw [mul_zero, eq_comm] at h
    exact mul_ne_zero (by simpa using hc) (mul_ne_zero hq hq) h
  obtain ⟨e, he⟩ := MvPowerSeries.exists_finsupp_eq_lexOrder_of_ne_zero hp
  obtain ⟨d, hd⟩ := MvPowerSeries.exists_finsupp_eq_lexOrder_of_ne_zero hq
  have h1 : MvPowerSeries.lexOrder (p * p) = ((toLex e + toLex e : Lex (σ →₀ ℕ)) :
      WithTop (Lex (σ →₀ ℕ))) := by
    rw [MvPowerSeries.lexOrder_mul, he, WithTop.coe_add]
  have h2 : MvPowerSeries.lexOrder (MvPowerSeries.C c * (q * q)) =
      ((toLex d + toLex d : Lex (σ →₀ ℕ)) : WithTop (Lex (σ →₀ ℕ))) := by
    rw [MvPowerSeries.lexOrder_mul, MvPowerSeries.lexOrder_mul, lexOrder_C hc, hd,
      WithTop.coe_add, toLex_zero, WithTop.coe_zero, zero_add]
  have h12 : (toLex e + toLex e : Lex (σ →₀ ℕ)) = toLex d + toLex d := by
    rw [h] at h1; exact WithTop.coe_injective (h1.symm.trans h2)
  have hed : e = d := by
    rcases lt_trichotomy (toLex e) (toLex d) with hlt | heq | hlt
    · exact absurd h12 (add_lt_add hlt hlt).ne
    · exact toLex.injective heq
    · exact absurd h12.symm (add_lt_add hlt hlt).ne
  subst hed
  have hc1 := MvPowerSeries.coeff_mul_of_add_lexOrder he he
  have hc2 := MvPowerSeries.coeff_mul_of_add_lexOrder hd hd
  have hcoef := congrArg (MvPowerSeries.coeff (e + e)) h
  rw [hc1, MvPowerSeries.coeff_C_mul, hc2] at hcoef
  have hq0 : MvPowerSeries.coeff e q ≠ 0 := MvPowerSeries.coeff_ne_zero_of_lexOrder hd.symm
  refine ⟨MvPowerSeries.coeff e p / MvPowerSeries.coeff e q, ?_⟩
  field_simp
  linear_combination -hcoef

/-- A non-square of `K` stays a non-square in `Frac K⟦τ⟧` (lowest lexicographic terms). -/
theorem not_isSquare_frac {τ : Type*} [Finite τ] {c : K} (hc : ¬ IsSquare c) :
    ¬ IsSquare (algebraMap K (Lf K τ) c) := by
  classical
  cases nonempty_fintype τ
  let _ : LinearOrder τ := LinearOrder.lift' (Fintype.equivFin τ) (Fintype.equivFin τ).injective
  have : WellFoundedGT τ := Finite.to_wellFoundedGT
  rintro ⟨y, hy⟩
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPowerSeries τ K) y
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hqL : algebraMap (MvPowerSeries τ K) (Lf K τ) q ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hq0
  have hC : algebraMap K (Lf K τ) c =
      algebraMap (MvPowerSeries τ K) (Lf K τ) (MvPowerSeries.C c) := by
    rw [IsScalarTower.algebraMap_apply K (MvPowerSeries τ K) (Lf K τ),
      MvPowerSeries.c_eq_algebraMap]
  rw [hC] at hy
  have h : algebraMap (MvPowerSeries τ K) (Lf K τ) (p * p) =
      algebraMap (MvPowerSeries τ K) (Lf K τ) (MvPowerSeries.C c * (q * q)) := by
    rw [map_mul, map_mul, map_mul, hy]
    field_simp
  exact hc (isSquare_of_sq_eq_C_mul_sq c hq0 (IsFractionRing.injective _ _ h))

theorem goodSextic_frac [CharZero K] [GoodSextic S.f] (τ : Type*) [Finite τ] :
    GoodSextic (S.f.map (algebraMap K (Lf K τ))) :=
  goodSextic_map _ (PerfectField.separable_iff_squarefree.mpr GoodSextic.squarefree)
    GoodSextic.natDegree_eq (GoodSextic.two_ne_zero S.f)
    (not_isSquare_frac GoodSextic.not_isSquare_leadingCoeff)

end Good

/-! ### The axioms -/

section Axioms

variable [CharZero K] [GoodSextic S.f]

omit [CharZero K] [GoodSextic S.f] in
theorem chiF_irrel {τ : Type*} [Finite τ] [GoodSextic (S.f.map (algebraMap K (Lf K τ)))]
    {a b : Fin 2 → MvPowerSeries τ K} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (h : a = b) :
    S.chiF a ha = S.chiF b hb := by
  subst h; rfl

theorem G_add_zero (i : Fin 2) :
    MvPowerSeries.subst (Sum.elim MvPowerSeries.X fun _ ↦ 0 :
      Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2) K) (S.G i) = MvPowerSeries.X i := by
  have := S.goodSextic_frac (Fin 2)
  have hX : ∀ j, MvPowerSeries.constantCoeff
      ((MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) K) j) = 0 := fun j => by simp
  have law := S.law_frac MvPowerSeries.X 0 hX zero_const
  rw [S.chiF_zero, mul_comm] at law
  have h := S.eq_of_chiF_eq _ _ (mul_left_cancel law)
  have := congrFun h i
  simp only [Gs, sb_apply] at this
  exact this.symm

theorem G_zero_add (i : Fin 2) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ 0) MvPowerSeries.X :
      Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2) K) (S.G i) = MvPowerSeries.X i := by
  have := S.goodSextic_frac (Fin 2)
  have hX : ∀ j, MvPowerSeries.constantCoeff
      ((MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) K) j) = 0 := fun j => by simp
  have law := S.law_frac 0 MvPowerSeries.X zero_const hX
  rw [S.chiF_zero] at law
  have h := S.eq_of_chiF_eq _ _ (mul_left_cancel law)
  have := congrFun h i
  simp only [Gs, sb_apply] at this
  exact this.symm

theorem G_comm (i : Fin 2) :
    MvPowerSeries.subst (fun s : Fin 2 ⊕ Fin 2 ↦ (MvPowerSeries.X s.swap : A2 K)) (S.G i) =
      S.G i := by
  have := S.goodSextic_frac (Fin 2 ⊕ Fin 2)
  set a : Fin 2 → A2 K := fun j => MvPowerSeries.X (Sum.inl j)
  set b : Fin 2 → A2 K := fun j => MvPowerSeries.X (Sum.inr j)
  have ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0 := fun j => by simp [a]
  have hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0 := fun j => by simp [b]
  have l1 := S.law_frac a b ha hb
  have l2 := S.law_frac b a hb ha
  rw [mul_comm, l2] at l1
  have h := S.eq_of_chiF_eq _ _ (mul_left_cancel l1)
  have := congrFun h i
  simp only [Gs, sb_apply] at this
  have e1 : (Sum.elim b a : Fin 2 ⊕ Fin 2 → A2 K) = fun s => MvPowerSeries.X s.swap := by
    funext s; rcases s with j | j <;> rfl
  have e2 : (Sum.elim a b : Fin 2 ⊕ Fin 2 → A2 K) = MvPowerSeries.X := by
    funext s; rcases s with j | j <;> rfl
  rw [e1, e2, MvPowerSeries.subst_self] at this
  exact this

theorem G_assoc (i : Fin 2) :
    MvPowerSeries.subst (FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.assocLeftFam S.G) (S.G i) =
      MvPowerSeries.subst (FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.assocRightFam S.G) (S.G i) := by
  have := S.goodSextic_frac (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
  set a : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K := fun j => MvPowerSeries.X (Sum.inl j)
  set b : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K :=
    fun j => MvPowerSeries.X (Sum.inr (Sum.inl j))
  set c : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K :=
    fun j => MvPowerSeries.X (Sum.inr (Sum.inr j))
  have ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0 := fun j => by simp [a]
  have hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0 := fun j => by simp [b]
  have hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0 := fun j => by simp [c]
  have l1 := S.law_frac a b ha hb
  have l2 := S.law_frac (S.Gs a b ha hb) c (S.Gs_const a b ha hb) hc
  have l3 := S.law_frac b c hb hc
  have l4 := S.law_frac a (S.Gs b c hb hc) ha (S.Gs_const b c hb hc)
  set E := S.E0 (algebraMap K (Lf K (Fin 2 ⊕ Fin 2 ⊕ Fin 2)))
  have key : E * (E * S.chiF (S.Gs (S.Gs a b ha hb) c (S.Gs_const a b ha hb) hc)
      (S.Gs_const _ _ _ _)) =
      E * (E * S.chiF (S.Gs a (S.Gs b c hb hc) ha (S.Gs_const b c hb hc))
        (S.Gs_const _ _ _ _)) := by
    rw [← l2, ← l4, ← mul_assoc, ← l1, mul_assoc, l3, mul_left_comm]
  have h := S.eq_of_chiF_eq _ _ (mul_left_cancel (mul_left_cancel key))
  have := congrFun h i
  simp only [Gs, sb_apply] at this
  have eL : (Sum.elim (S.Gs a b ha hb) c) = FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.assocLeftFam S.G := by
    funext s
    rcases s with j | j
    · simp only [Gs, sb_apply, FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.assocLeftFam, Sum.elim_inl]; rfl
    · rfl
  have eR : (Sum.elim a (S.Gs b c hb hc)) = FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.assocRightFam S.G := by
    funext s
    rcases s with j | j
    · rfl
    · simp only [Gs, sb_apply, FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.assocRightFam, Sum.elim_inr]; rfl
  rwa [eL, eR] at this

/-- **The formal group law of the chart at `E0`**: `G` is a commutative two-dimensional formal
group law over `K`. -/
noncomputable def fgl : FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw K (Fin 2) where
  F := S.G
  zero_constantCoeff := S.G_const
  add_zero' := S.G_add_zero
  zero_add' := S.G_zero_add
  comm' := S.G_comm
  assoc' := S.G_assoc

theorem fgl_F : S.fgl.F = S.G := rfl

end Axioms

end FurioLombardo.Vendor.Toolbox.G2Formal.Setup
