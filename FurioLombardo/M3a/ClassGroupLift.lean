import Mathlib
import FurioLombardo.M3a.Moving

/-!
# Homomorphisms out of the class group of a Dedekind domain (lane M3a)

* `exists_classGroup_lift`: a monoid hom on nonzero ideals that kills principal ideals factors
  through `ClassGroup.mk0`.
* `exists_classGroup_lift_coprime`: a function on ideals that is multiplicative on ideals coprime
  to a fixed nonzero ideal `J` and trivial on principal ideals with a generator coprime to `J`
  induces a hom on the class group (through the moving lemma of `Moving.lean`).
-/

open scoped nonZeroDivisors

namespace FurioLombardo.M3a

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A monoid hom on nonzero ideals killing principal ideals factors through the class group. -/
theorem exists_classGroup_lift
    {G : Type*} [CommGroup G] (g : (Ideal R)⁰ →* G)
    (hg : ∀ I : (Ideal R)⁰, (I : Ideal R).IsPrincipal → g I = 1) :
    ∃ φ : ClassGroup R →* G, ∀ I : (Ideal R)⁰, φ (ClassGroup.mk0 I) = g I := by
  classical
  have hspan : ∀ x : R, x ≠ 0 → Ideal.span {x} ∈ (Ideal R)⁰ := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  have hconst : ∀ I J : (Ideal R)⁰, ClassGroup.mk0 I = ClassGroup.mk0 J → g I = g J := by
    intro I J h
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    have h1 : (⟨_, hspan x hx⟩ : (Ideal R)⁰) * I = ⟨_, hspan y hy⟩ * J := Subtype.ext hxy
    have h2 := congrArg g h1
    rwa [map_mul, map_mul, hg ⟨_, hspan x hx⟩ ⟨⟨x, rfl⟩⟩, hg ⟨_, hspan y hy⟩ ⟨⟨y, rfl⟩⟩, one_mul,
      one_mul] at h2
  let rep : ClassGroup R → (Ideal R)⁰ := fun c => (ClassGroup.mk0_surjective c).choose
  have hrep : ∀ c, ClassGroup.mk0 (rep c) = c := fun c =>
    (ClassGroup.mk0_surjective c).choose_spec
  refine ⟨{ toFun := fun c => g (rep c), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · change g (rep 1) = 1
    rw [hconst (rep 1) 1 (by rw [hrep, map_one]), map_one]
  · intro c d
    rw [← map_mul, hconst (rep (c * d)) (rep c * rep d) (by rw [hrep, map_mul, hrep, hrep])]
  · intro I
    exact hconst _ _ (hrep _)

/-- A function on ideals, multiplicative on ideals coprime to `J` and trivial on principal ideals
with a generator coprime to `J`, induces a hom on the class group, determined by its values on
the representatives coprime to `J`. -/
theorem exists_classGroup_lift_coprime {J : Ideal R} (hJ : J ≠ ⊥) {G : Type*} [CommGroup G]
    (g : Ideal R → G)
    (hmul : ∀ I I' : Ideal R, I ⊔ J = ⊤ → I' ⊔ J = ⊤ → g (I * I') = g I * g I')
    (hprin : ∀ x : R, x ≠ 0 → Ideal.span {x} ⊔ J = ⊤ → g (Ideal.span {x}) = 1) :
    ∃ φ : ClassGroup R →* G, ∀ I : (Ideal R)⁰, (I : Ideal R) ⊔ J = ⊤ →
      φ (ClassGroup.mk0 I) = g I := by
  classical
  have hconst : ∀ I I' : (Ideal R)⁰, (I : Ideal R) ⊔ J = ⊤ → (I' : Ideal R) ⊔ J = ⊤ →
      ClassGroup.mk0 I = ClassGroup.mk0 I' → g I = g I' := by
    intro I I' hI hI' h
    obtain ⟨x, y, hx, hy, hxJ, hyJ, hxy⟩ := exists_coprime_generators hJ hI hI' h
    have h2 := congrArg g hxy
    rwa [hmul _ _ hxJ hI, hmul _ _ hyJ hI', hprin x hx hxJ, hprin y hy hyJ, one_mul,
      one_mul] at h2
  have hcop : ∀ A B : Ideal R, A ⊔ J = ⊤ → B ⊔ J = ⊤ → A * B ⊔ J = ⊤ := by
    intro A B hA hB
    rw [← Ideal.isCoprime_iff_sup_eq] at hA hB ⊢
    exact hA.mul_left hB
  let rep : ClassGroup R → (Ideal R)⁰ := fun c => (exists_mk0_eq_sup_eq_top c hJ).choose
  have hrep : ∀ c, ClassGroup.mk0 (rep c) = c := fun c =>
    (exists_mk0_eq_sup_eq_top c hJ).choose_spec.1
  have hrepJ : ∀ c, (rep c : Ideal R) ⊔ J = ⊤ := fun c =>
    (exists_mk0_eq_sup_eq_top c hJ).choose_spec.2
  have htop : ((1 : (Ideal R)⁰) : Ideal R) ⊔ J = ⊤ := by
    rw [OneMemClass.coe_one, Ideal.one_eq_top, top_sup_eq]
  have hg1 : g ((1 : (Ideal R)⁰) : Ideal R) = 1 := by
    have h1 : (1 : Ideal R) = Ideal.span {1} := by rw [Ideal.one_eq_top, Ideal.span_singleton_one]
    rw [OneMemClass.coe_one, h1]
    exact hprin 1 one_ne_zero (by rw [Ideal.span_singleton_one, top_sup_eq])
  refine ⟨{ toFun := fun c => g (rep c), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · change g (rep 1) = 1
    rw [hconst (rep 1) 1 (hrepJ 1) htop (by rw [hrep, map_one]), hg1]
  · intro c d
    rw [← hmul _ _ (hrepJ c) (hrepJ d)]
    have := hconst (rep (c * d)) (rep c * rep d) (hrepJ _)
      (by rw [Submonoid.coe_mul]; exact hcop _ _ (hrepJ c) (hrepJ d))
      (by rw [hrep, map_mul, hrep, hrep])
    rwa [Submonoid.coe_mul] at this
  · intro I hI
    exact hconst _ _ (hrepJ _) hI (hrep _)

end FurioLombardo.M3a
