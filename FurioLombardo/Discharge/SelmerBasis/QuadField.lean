import Mathlib

/-!
# Quadratic extensions of a complete ultrametric field, with the spectral norm

For a complete ultrametric nontrivially normed field `K` and `a b : K` with `X² - b X - a`
irreducible (`Fact (∀ r, r ^ 2 ≠ a + b * r)`), `QF K a b` is the field `QuadraticAlgebra K a b`
with the spectral norm of the extension: a complete ultrametric nontrivially normed field, proper
when `K` is, whose norm extends the norm of `K` (`norm_algebraMap`) and satisfies
`‖z‖ ^ 2 = ‖N z‖` (`norm_sq`). These are the quadratic components of the local algebras
`K_w[T]/(f_w)` at the places of the Selmer bound. The type
synonym keeps the spectral norm away from other uses of `QuadraticAlgebra`, as `M4Cert.Kv` does
for `AdjoinRoot`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (a b : K)

/-- `K(√·)` as `QuadraticAlgebra K a b`, carrying the spectral norm. -/
def QF : Type _ := QuadraticAlgebra K a b

namespace QF

variable [Fact (∀ r : K, r ^ 2 ≠ a + b * r)]

noncomputable instance : Field (QF K a b) := inferInstanceAs (Field (QuadraticAlgebra K a b))

noncomputable instance : Algebra K (QF K a b) := inferInstanceAs (Algebra K (QuadraticAlgebra K a b))

instance : FiniteDimensional K (QF K a b) :=
  inferInstanceAs (Module.Finite K (QuadraticAlgebra K a b))

instance : Algebra.IsAlgebraic K (QF K a b) := Algebra.IsAlgebraic.of_finite K (QF K a b)

noncomputable instance : NontriviallyNormedField (QF K a b) :=
  spectralNorm.nontriviallyNormedField K (QF K a b)

noncomputable instance : NormedAlgebra K (QF K a b) where
  toAlgebra := inferInstance
  norm_smul_le r x := (spectralNorm.normedAlgebra K (QF K a b)).norm_smul_le r x

instance : CompleteSpace (QF K a b) := FiniteDimensional.complete K (QF K a b)

instance : IsUltrametricDist (QF K a b) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm

instance [ProperSpace K] : ProperSpace (QF K a b) := FiniteDimensional.proper K (QF K a b)

/-- The element `⟨x, y⟩ = x + y ω` of `QF K a b`. -/
def mk (x y : K) : QF K a b := (⟨x, y⟩ : QuadraticAlgebra K a b)

/-- The norm `N ⟨x, y⟩ = x² + b x y - a y²` of `QuadraticAlgebra`. -/
noncomputable def qnorm (z : QF K a b) : K := QuadraticAlgebra.norm (z : QuadraticAlgebra K a b)

theorem norm_algebraMap (x : K) : ‖algebraMap K (QF K a b) x‖ = ‖x‖ := spectralNorm_extends x

section Conj

variable {K a b}

/-- Conjugation as a `K`-algebra automorphism of `QF K a b`. -/
noncomputable def conj : QF K a b ≃ₐ[K] QF K a b :=
  AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut (QuadraticAlgebra K a b)))
    (fun r => by
      show star (algebraMap K (QuadraticAlgebra K a b) r) = algebraMap K (QuadraticAlgebra K a b) r
      ext <;> simp)

theorem norm_conj (z : QF K a b) : ‖conj z‖ = ‖z‖ :=
  (spectralNorm_eq_of_equiv (K := K) (L := QF K a b) conj z).symm

end Conj

/-- **The spectral norm of a quadratic extension**: `‖z‖ ^ 2 = ‖N z‖` (conjugation is an isometry,
prior-art round r7, code/formal-proof/qf_norm_sq_probe.lean). -/
theorem norm_sq (z : QF K a b) : ‖z‖ ^ 2 = ‖qnorm K a b z‖ := by
  have h : algebraMap K (QF K a b) (qnorm K a b z) = z * conj z :=
    QuadraticAlgebra.algebraMap_norm_eq_mul_star (z : QuadraticAlgebra K a b)
  rw [← norm_algebraMap K a b (qnorm K a b z), h, norm_mul, norm_conj, sq]

end QF

end FurioLombardo.Discharge.SelmerBasis
