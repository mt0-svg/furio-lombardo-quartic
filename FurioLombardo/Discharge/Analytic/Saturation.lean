import Mathlib
import FurioLombardo.M4.Lattice
import FurioLombardo.M4.Hypotheses
import FurioLombardo.M3a.StollSat

/-!
# The saturation of a span, as a submodule

`HSat Λ S a b` (FurioLombardo.M4.Hypotheses) and `Saturated Λ S` (FurioLombardo.M3a.Hypotheses) are not facts about
the Jacobian: they say what `S` is. For every `Λ`, `a`, `b` the submodule `satOf Λ a b` of the `x ∈ Λ` with
`2^m x ∈ span {a, b}` for some `m` satisfies `IsSatOf Λ (satOf Λ a b) a b` (`isSatOf_satOf`), and it is the only
submodule that does (`eq_satOf`). So both hypotheses are discharged by choosing `S := satOf Λ a b`, and then
`a, b ∈ S` as soon as `a, b ∈ Λ` (`left_mem_satOf`, `right_mem_satOf`: the fields `mem_a`, `mem_b` of
`FurioLombardo.M3a.Route.Inputs`).
-/

namespace FurioLombardo.Discharge.Analytic

open FurioLombardo.M4

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

/-- The saturation in `Λ` of the span of `a` and `b` at the prime 2: the `x ∈ Λ` with `2^m x ∈ span {a, b}` for
some `m`. -/
def satOf (Λ : Submodule ℤ_[2] V) (a b : V) : Submodule ℤ_[2] V where
  carrier := {x | x ∈ Λ ∧ ∃ m : ℕ, (2 : ℤ_[2]) ^ m • x ∈ Submodule.span ℤ_[2] {a, b}}
  add_mem' := by
    rintro x y ⟨hx, m, hm⟩ ⟨hy, n, hn⟩
    refine ⟨Λ.add_mem hx hy, m + n, ?_⟩
    rw [smul_add, pow_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hm
    · rw [mul_smul]
      exact Submodule.smul_mem _ _ hn
  zero_mem' := ⟨Λ.zero_mem, 0, by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, m, hm⟩
    refine ⟨Λ.smul_mem c hx, m, ?_⟩
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hm

theorem mem_satOf {Λ : Submodule ℤ_[2] V} {a b x : V} :
    x ∈ satOf Λ a b ↔ x ∈ Λ ∧ ∃ m : ℕ, (2 : ℤ_[2]) ^ m • x ∈ Submodule.span ℤ_[2] {a, b} :=
  Iff.rfl

/-- `satOf Λ a b` is the saturation of `span {a, b}` in `Λ` in the sense of lane M4. -/
theorem isSatOf_satOf (Λ : Submodule ℤ_[2] V) (a b : V) : IsSatOf Λ (satOf Λ a b) a b :=
  fun _ => Iff.rfl

/-- The saturation is unique: any `S` with `IsSatOf Λ S a b` is `satOf Λ a b`. -/
theorem eq_satOf {Λ S : Submodule ℤ_[2] V} {a b : V} (h : IsSatOf Λ S a b) : S = satOf Λ a b := by
  ext x
  exact h x

/-- **HSat discharged**: the hypothesis `HSat` of lane M4 holds for `S := satOf Λ a b`. -/
theorem hSat_satOf (Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (a b : Fin 6 → ℤ_[2]) :
    HSat Λ (satOf Λ a b) a b :=
  isSatOf_satOf Λ a b

/-- **Saturated discharged** (lane M3a's `Saturated`, same body as lane M4's): `satOf Λ a b` is saturated in `Λ`. -/
theorem saturated_satOf (Λ : Submodule ℤ_[2] V) (a b : V) :
    FurioLombardo.M3a.Saturated Λ (satOf Λ a b) := by
  have h := saturated_of_isSatOf (isSatOf_satOf Λ a b)
  exact ⟨h.1, h.2⟩

/-- `a ∈ satOf Λ a b` when `a ∈ Λ`. -/
theorem left_mem_satOf {Λ : Submodule ℤ_[2] V} {a : V} (b : V) (ha : a ∈ Λ) : a ∈ satOf Λ a b :=
  ⟨ha, 0, by simpa using Submodule.subset_span (Set.mem_insert a {b})⟩

/-- `b ∈ satOf Λ a b` when `b ∈ Λ`. -/
theorem right_mem_satOf {Λ : Submodule ℤ_[2] V} (a : V) {b : V} (hb : b ∈ Λ) : b ∈ satOf Λ a b :=
  ⟨hb, 0, by simpa using Submodule.subset_span (Set.mem_insert_of_mem a (Set.mem_singleton b))⟩

end FurioLombardo.Discharge.Analytic
