import FurioLombardo.Discharge.SelmerBasis.QuadField

/-! Probe: `QF.norm_sq` of QuadField.lean by the conjugation route,
`spectralNorm_eq_of_equiv` with the conjugation of `QuadraticAlgebra` as a `K`-algebra
automorphism, and `QuadraticAlgebra.algebraMap_norm_eq_mul_star`. The statement is the one of
QuadField.lean, renamed `norm_sq'`. -/

namespace FurioLombardo.Discharge.SelmerBasis.QF

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] {a b : K}
variable [Fact (∀ r : K, r ^ 2 ≠ a + b * r)]

/-- Conjugation as a `K`-algebra automorphism of `QF K a b`. -/
noncomputable def conj : QF K a b ≃ₐ[K] QF K a b :=
  AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut (QuadraticAlgebra K a b)))
    (fun r => by
      show star (algebraMap K (QuadraticAlgebra K a b) r) = algebraMap K (QuadraticAlgebra K a b) r
      ext <;> simp)

theorem norm_conj (z : QF K a b) : ‖conj z‖ = ‖z‖ :=
  (spectralNorm_eq_of_equiv (K := K) (L := QF K a b) conj z).symm

theorem norm_sq' (z : QF K a b) : ‖z‖ ^ 2 = ‖qnorm K a b z‖ := by
  have h : algebraMap K (QF K a b) (qnorm K a b z) = z * conj z :=
    QuadraticAlgebra.algebraMap_norm_eq_mul_star (z : QuadraticAlgebra K a b)
  rw [← norm_algebraMap K a b (qnorm K a b z), h, norm_mul, norm_conj, sq]

end FurioLombardo.Discharge.SelmerBasis.QF

#print axioms FurioLombardo.Discharge.SelmerBasis.QF.norm_sq'
