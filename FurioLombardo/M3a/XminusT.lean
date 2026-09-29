import Mathlib
import FurioLombardo.M3a.BaseChange

/-!
# The `x - T` map (lane M3a)

For `f` with `GoodSextic f`, `L = K[T]/(f)` (`AdjoinRoot f`):

* `H f = L^× / K^× (L^×)²`, the target of the `x - T` map;
* `muIdeal f I`: the class of `N(I)(T)` (the generator of the relative norm evaluated at `T`), for
  `I` coprime to `(Y)`; `isUnit_mk_generator`: then it is a unit of `L`;
* `mu f : Pic f →* H f`, the unique hom with `mu (mk0 I) = muIdeal I` for `I` coprime to `(Y)`
  (moving lemma, `exists_classGroup_lift_coprime`); `muJ f` its restriction to `Jac f`;
* `mu_sq`: `μ` kills squares (the easy direction `μ(2A) = 0`, over any field, in particular over
  `k_v`);
* `Hmap φ f`, `mu_picMap`: `μ` commutes with base change.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The subgroup `K^× (L^×)²` of `L^×`, where `L = K[T]/(f)`. -/
noncomputable def sqClass (f : K[X]) : Subgroup (AdjoinRoot f)ˣ :=
  (Units.map (algebraMap K (AdjoinRoot f)).toMonoidHom).range ⊔
    (powMonoidHom 2 : (AdjoinRoot f)ˣ →* (AdjoinRoot f)ˣ).range

/-- The target `L^× / K^× (L^×)²` of the `x - T` map. -/
abbrev H (f : K[X]) : Type _ := (AdjoinRoot f)ˣ ⧸ sqClass f

open Classical in
/-- The `x - T` value of an ideal `I`: the class of `N(I)(T)`, when this is a unit of `L`. -/
noncomputable def muIdeal (f : K[X]) [GoodSextic f] (I : Ideal (CoordRing f)) : H f :=
  if h : IsUnit (AdjoinRoot.mk f (Submodule.IsPrincipal.generator (Ideal.relNorm K[X] I))) then
    QuotientGroup.mk h.unit else 1

/-- The base change `K[T]/(f) → K'[T]/(f^φ)`. -/
noncomputable def etaleMap {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) :
    AdjoinRoot f →+* AdjoinRoot (f.map φ) :=
  AdjoinRoot.map φ f (f.map φ) dvd_rfl

end FurioLombardo.M3a.Genus2

theorem FurioLombardo.M3a.Genus2.span_Yc_ne_bot {K : Type*} [Field K] (f : K[X]) [GoodSextic f] : Ideal.span {Yc f} ≠ ⊥ := by
  have hYc_ne_zero : Yc f ≠ 0 := by
    rw [← basis_one]
    exact (basis f).ne_zero 1
  intro h
  apply hYc_ne_zero
  exact (Ideal.span_singleton_eq_bot.mp h)

theorem FurioLombardo.M3a.Genus2.etaleMap_mk {K : Type*} [Field K] {K' : Type*} [Field K']
    (φ : K →+* K') (f p : K[X]) :
    etaleMap φ f (AdjoinRoot.mk f p) = AdjoinRoot.mk (f.map φ) (p.map φ) := by
  rw [etaleMap, AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq,
    Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]

theorem FurioLombardo.M3a.Genus2.isUnit_mk_generator {K : Type*} [Field K] (f : K[X])
    [GoodSextic f] (I : Ideal (CoordRing f)) (hI : I ⊔ Ideal.span {Yc f} = ⊤) :
    IsUnit (AdjoinRoot.mk f (Submodule.IsPrincipal.generator (Ideal.relNorm K[X] I))) := by
  have h1 : (1 : CoordRing f) ∈ I ⊔ Ideal.span {Yc f} := by rw [hI]; exact Submodule.mem_top
  obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp h1
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hev : evT f a = 1 := by
    have := congrArg (evT f) hay
    rwa [map_add, map_mul, evT_Yc, mul_zero, add_zero, map_one] at this
  have hn : Algebra.norm K[X] a ∈ Ideal.relNorm K[X] I := Ideal.norm_mem_relNorm _ _ ha
  rw [Submodule.IsPrincipal.mem_iff_generator_dvd] at hn
  obtain ⟨d, hd⟩ := hn
  have hmk : AdjoinRoot.mk f (Algebra.norm K[X] a) = 1 := by
    rw [mk_norm_eq_evT_sq, hev, one_pow]
  rw [hd, map_mul] at hmk
  exact IsUnit.of_mul_eq_one _ hmk

theorem FurioLombardo.M3a.Genus2.muIdeal_mul {K : Type*} [Field K] (f : K[X]) [GoodSextic f] (I I' : Ideal (CoordRing f))
    (hI : I ⊔ Ideal.span {Yc f} = ⊤) (hI' : I' ⊔ Ideal.span {Yc f} = ⊤) :
    muIdeal f (I * I') = muIdeal f I * muIdeal f I' := by
  have hII' : I * I' ⊔ Ideal.span {Yc f} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hI hI' ⊢
    exact hI.mul_left hI'
  have hu := isUnit_mk_generator f I hI
  have hu' := isUnit_mk_generator f I' hI'
  have hu'' := isUnit_mk_generator f (I * I') hII'
  unfold muIdeal
  rw [dif_pos hu, dif_pos hu', dif_pos hu'', ← QuotientGroup.mk_mul, QuotientGroup.eq]
  set g := Submodule.IsPrincipal.generator (Ideal.relNorm K[X] I)
  set g' := Submodule.IsPrincipal.generator (Ideal.relNorm K[X] I')
  set G := Submodule.IsPrincipal.generator (Ideal.relNorm K[X] (I * I'))
  have hassoc : Associated G (g * g') := by
    rw [← Ideal.span_singleton_eq_span_singleton, Ideal.span_singleton_generator, map_mul,
      ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_generator,
      Ideal.span_singleton_generator]
  obtain ⟨w, hw⟩ := hassoc
  obtain ⟨r, hr, hrw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  have hkey : AdjoinRoot.mk f G * algebraMap K (AdjoinRoot f) r =
      AdjoinRoot.mk f g * AdjoinRoot.mk f g' := by
    rw [← map_mul, ← hw, map_mul, ← hrw, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  apply Subgroup.mem_sup_left
  refine ⟨hr.unit, ?_⟩
  ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_mul,
    IsUnit.unit_spec]
  rw [← hkey, ← mul_assoc, Units.inv_mul_of_eq hu''.unit_spec.symm, one_mul]


theorem FurioLombardo.M3a.Genus2.muIdeal_span {K : Type*} [Field K] (f : K[X]) [GoodSextic f] (x : CoordRing f) (hx : x ≠ 0)
    (hxY : Ideal.span {x} ⊔ Ideal.span {Yc f} = ⊤) : muIdeal f (Ideal.span {x}) = 1 := by
  have h1 : (1 : CoordRing f) ∈ Ideal.span {x} ⊔ Ideal.span {Yc f} := by
    rw [hxY]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hev : evT f a * evT f x = 1 := by
    have := congrArg (evT f) hyz
    rwa [map_add, map_mul, map_mul, evT_Yc, mul_zero, add_zero, map_one] at this
  have hux : IsUnit (evT f x) := IsUnit.of_mul_eq_one_right _ hev
  have hN : Ideal.relNorm K[X] (Ideal.span {x}) = Ideal.span {Algebra.norm K[X] x} := by
    rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm]
  set g := Submodule.IsPrincipal.generator (Ideal.relNorm K[X] (Ideal.span {x}))
  have hassoc : Associated g (Algebra.norm K[X] x) := by
    rw [← Ideal.span_singleton_eq_span_singleton, Ideal.span_singleton_generator, hN]
  obtain ⟨w, hw⟩ := hassoc
  obtain ⟨r, hr, hrw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  have hkey : AdjoinRoot.mk f g * algebraMap K (AdjoinRoot f) r = evT f x ^ 2 := by
    rw [← mk_norm_eq_evT_sq, ← hw, map_mul, ← hrw, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  have hg : IsUnit (AdjoinRoot.mk f g) :=
    isUnit_of_mul_isUnit_left (hkey ▸ hux.pow 2)
  unfold muIdeal
  rw [dif_pos hg, QuotientGroup.eq_one_iff]
  have hgu : hg.unit = (hux.unit ^ 2) * (Units.map (algebraMap K (AdjoinRoot f)).toMonoidHom
      hr.unit)⁻¹ := by
    ext
    simp only [IsUnit.unit_spec, Units.val_mul, Units.val_pow_eq_pow_val, RingHom.toMonoidHom_eq_coe,
      Units.coe_map_inv, MonoidHom.coe_coe]
    rw [← hkey, mul_assoc, ← map_mul, hr.mul_val_inv, map_one, mul_one]
  rw [hgu]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hux.unit, rfl⟩)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left ⟨hr.unit, rfl⟩))

theorem FurioLombardo.M3a.Genus2.sqClass_le_comap {K : Type*} [Field K] {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) :
    sqClass f ≤ (sqClass (f.map φ)).comap (Units.map (etaleMap φ f).toMonoidHom) := by
  unfold sqClass
  apply sup_le
  · intro x hx
    rw [Subgroup.mem_comap]
    rcases MonoidHom.mem_range.mp hx with ⟨u, rfl⟩
    have hmap : (Units.map (etaleMap φ f).toMonoidHom) (Units.map (algebraMap K (AdjoinRoot f)).toMonoidHom u) =
        Units.map (algebraMap K' (AdjoinRoot (f.map φ))).toMonoidHom (Units.map φ.toMonoidHom u) := by
      calc
        (Units.map (etaleMap φ f).toMonoidHom) (Units.map (algebraMap K (AdjoinRoot f)).toMonoidHom u)
            = ((Units.map (etaleMap φ f).toMonoidHom).comp (Units.map (algebraMap K (AdjoinRoot f)).toMonoidHom)) u := rfl
        _ = Units.map ((etaleMap φ f).toMonoidHom.comp (algebraMap K (AdjoinRoot f)).toMonoidHom) u := by
          rw [← Units.map_comp]
        _ = Units.map (algebraMap K' (AdjoinRoot (f.map φ))).toMonoidHom (Units.map φ.toMonoidHom u) := by
          ext
          simp [AdjoinRoot.algebraMap_eq, etaleMap, AdjoinRoot.map_of]
    rw [hmap]
    apply Subgroup.mem_sup_left
    apply MonoidHom.mem_range.mpr
    exact ⟨Units.map φ.toMonoidHom u, rfl⟩
  · intro x hx
    rw [Subgroup.mem_comap]
    rcases MonoidHom.mem_range.mp hx with ⟨w, hw⟩
    have hx' : x = w ^ 2 := by
      simpa [powMonoidHom] using hw.symm
    rw [hx']
    have hmap : Units.map (etaleMap φ f).toMonoidHom (w ^ 2) = (Units.map (etaleMap φ f).toMonoidHom w) ^ 2 := by
      simp
    rw [hmap]
    apply Subgroup.mem_sup_right
    apply MonoidHom.mem_range.mpr
    exact ⟨Units.map (etaleMap φ f).toMonoidHom w, rfl⟩

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The base change of the `x - T` target. -/
noncomputable def Hmap {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) :
    H f →* H (f.map φ) :=
  QuotientGroup.map (sqClass f) (sqClass (f.map φ)) (Units.map (etaleMap φ f).toMonoidHom)
    (sqClass_le_comap φ f)

/-- The `x - T` map `μ : Pic f → L^× / K^× (L^×)²`. -/
noncomputable def mu (f : K[X]) [GoodSextic f] : Pic f →* H f :=
  Classical.choose (exists_classGroup_lift_coprime (span_Yc_ne_bot f) (muIdeal f) (muIdeal_mul f)
    (muIdeal_span f))

theorem mu_mk0 (f : K[X]) [GoodSextic f] (I : (Ideal (CoordRing f))⁰)
    (hI : (I : Ideal (CoordRing f)) ⊔ Ideal.span {Yc f} = ⊤) :
    mu f (ClassGroup.mk0 I) = muIdeal f I :=
  Classical.choose_spec (exists_classGroup_lift_coprime (span_Yc_ne_bot f) (muIdeal f)
    (muIdeal_mul f) (muIdeal_span f)) I hI

end FurioLombardo.M3a.Genus2

theorem FurioLombardo.M3a.Genus2.mu_sq {K : Type*} [Field K] (f : K[X]) [GoodSextic f] (c : Pic f) : mu f (c ^ 2) = 1 := by
  rw [(mu f).map_pow c 2]
  refine QuotientGroup.induction_on (mu f c) ?_
  intro u
  rw [← QuotientGroup.mk_pow]
  have : (sqClass f).Normal := inferInstance
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_sup_right
  apply MonoidHom.mem_range.mpr
  exact ⟨u, rfl⟩

theorem FurioLombardo.M3a.Genus2.mu_picMap {K : Type*} [Field K] {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f]
    [GoodSextic (f.map φ)] (c : Pic f) : mu (f.map φ) (picMap φ f c) = Hmap φ f (mu f c) := by
  obtain ⟨I, rfl, hI⟩ := exists_mk0_eq_sup_eq_top c (span_Yc_ne_bot f)
  have hne : (I : Ideal (CoordRing f)).map (baseChange φ f) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (baseChange_injective φ f)).not.mpr
      (nonZeroDivisors.ne_zero I.2)
  set J : (Ideal (CoordRing (f.map φ)))⁰ := ⟨_, mem_nonZeroDivisors_of_ne_zero hne⟩ with hJdef
  have hJ : (J : Ideal (CoordRing (f.map φ))) = (I : Ideal (CoordRing f)).map (baseChange φ f) :=
    rfl
  have hJY : (J : Ideal (CoordRing (f.map φ))) ⊔ Ideal.span {Yc (f.map φ)} = ⊤ := by
    have := congrArg (Ideal.map (baseChange φ f)) hI
    rwa [Ideal.map_sup, Ideal.map_span, Set.image_singleton, baseChange_Yc, Ideal.map_top] at this
  rw [picMap_mk0 φ f I J hJ, mu_mk0 _ J hJY, mu_mk0 f I hI]
  have hu := isUnit_mk_generator f I hI
  have hu' := isUnit_mk_generator (f.map φ) J hJY
  unfold muIdeal
  rw [dite_cond_eq_true (eq_true hu), dite_cond_eq_true (eq_true hu'), Hmap, QuotientGroup.map_mk, QuotientGroup.eq]
  set g := Submodule.IsPrincipal.generator (Ideal.relNorm K[X] (I : Ideal (CoordRing f)))
  set g' := Submodule.IsPrincipal.generator (Ideal.relNorm K'[X] (J : Ideal (CoordRing (f.map φ))))
  have hJn : Ideal.relNorm K'[X] (J : Ideal (CoordRing (f.map φ))) = Ideal.span {g.map φ} := by
    rw [hJ, relNorm_map_baseChange, ← Ideal.span_singleton_generator
      (Ideal.relNorm K[X] (I : Ideal (CoordRing f))), Ideal.map_span, Set.image_singleton]
    rfl
  have hassoc : Associated g' (g.map φ) := by
    rw [← Ideal.span_singleton_eq_span_singleton, Ideal.span_singleton_generator, hJn]
  obtain ⟨w, hw⟩ := hassoc
  obtain ⟨r, hr, hrw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  have hkey : etaleMap φ f (AdjoinRoot.mk f g) =
      AdjoinRoot.mk (f.map φ) g' * algebraMap K' (AdjoinRoot (f.map φ)) r := by
    rw [etaleMap_mk, ← hw, map_mul, ← hrw, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  apply Subgroup.mem_sup_left
  refine ⟨hr.unit, ?_⟩
  ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_mul,
    IsUnit.unit_spec]
  rw [hkey, ← mul_assoc, Units.inv_mul_of_eq hu'.unit_spec.symm, one_mul]

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The `x - T` map on `A(K)`. -/
noncomputable def muJ (f : K[X]) [GoodSextic f] : Jac f →* H f := (mu f).comp (Jac f).subtype

/-- `μ` on `A(K)` kills squares. -/
theorem muJ_sq (f : K[X]) [GoodSextic f] (Q : Jac f) : muJ f (Q ^ 2) = 1 := by
  change mu f ((Q : Pic f) ^ 2) = 1
  exact mu_sq f Q

/-- `μ` on `A(K)` commutes with the localisation `jacMap`. -/
theorem muJ_jacMap {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) [GoodSextic f]
    [GoodSextic (f.map φ)] (Q : Jac f) : muJ (f.map φ) (jacMap φ f Q) = Hmap φ f (muJ f Q) :=
  mu_picMap φ f Q

end FurioLombardo.M3a.Genus2
