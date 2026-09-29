import Mathlib

/-!
# Degrees of ideals of `K[X]` (lane M3a)

`K[X]` is a principal ideal domain; the degree of an ideal is the degree of its generator. It is
additive on nonzero ideals and equals `natDegree p` on `span {p}`.
-/

namespace FurioLombardo.M3a.Genus2

open Polynomial

variable {K : Type*} [Field K]

/-- The degree of an ideal of `K[X]`: the degree of a generator. -/
noncomputable def idealDeg (J : Ideal K[X]) : ℕ := (Submodule.IsPrincipal.generator J).natDegree

theorem natDegree_generator_span_singleton (p : K[X]) :
    (Submodule.IsPrincipal.generator (Ideal.span {p})).natDegree = p.natDegree :=
  natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (Submodule.IsPrincipal.associated_generator_span_self p))

theorem idealDeg_span_singleton (p : K[X]) : idealDeg (Ideal.span {p}) = p.natDegree :=
  natDegree_generator_span_singleton p

theorem natDegree_generator_mul {J J' : Ideal K[X]} (hJ : J ≠ ⊥) (hJ' : J' ≠ ⊥) :
    (Submodule.IsPrincipal.generator (J * J')).natDegree =
      (Submodule.IsPrincipal.generator J).natDegree +
        (Submodule.IsPrincipal.generator J').natDegree := by
  set g := Submodule.IsPrincipal.generator J
  set g' := Submodule.IsPrincipal.generator J'
  have hg : g ≠ 0 := fun h => hJ ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J).mpr h)
  have hg' : g' ≠ 0 :=
    fun h => hJ' ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J').mpr h)
  have hprod : J * J' = Ideal.span {g * g'} := by
    rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_generator,
      Ideal.span_singleton_generator]
  rw [hprod, natDegree_generator_span_singleton, natDegree_mul hg hg']

theorem idealDeg_mul {J J' : Ideal K[X]} (hJ : J ≠ ⊥) (hJ' : J' ≠ ⊥) :
    idealDeg (J * J') = idealDeg J + idealDeg J' :=
  natDegree_generator_mul hJ hJ'

end FurioLombardo.M3a.Genus2
