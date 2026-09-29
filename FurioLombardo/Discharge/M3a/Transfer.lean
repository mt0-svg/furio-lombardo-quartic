import Mathlib
import FurioLombardo.M3a.Sections

/-!
# Changing the matrices of the quadrics

`DPoint L M1 M2 M3 δ` only sees the quadratic forms `p ↦ p ⬝ᵥ (M_i *ᵥ p)`. Lanes use different
matrices for the same Bruin quadrics (WP2's symmetric `Bruin.Mmat i`, lane M4 certificate's upper
triangular `BQ i`). If the forms agree, points transfer (`transferD`, keeping the point
below and the coordinates `r`, `s`), and so do M3a's `Descent` and `TwistConclusion`
(`descent_congr`, `twistConclusion_congr`).
-/

namespace FurioLombardo.Discharge.M3a

open FurioLombardo.M3a Matrix

variable {L : Type*} [Field L] {M1 M2 M3 N1 N2 N3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

/-- Same quadratic forms. -/
def SameForms (M1 M2 M3 N1 N2 N3 : Matrix (Fin 3) (Fin 3) L) : Prop :=
  ∀ p : Fin 3 → L, p ⬝ᵥ (M1 *ᵥ p) = p ⬝ᵥ (N1 *ᵥ p) ∧ p ⬝ᵥ (M2 *ᵥ p) = p ⬝ᵥ (N2 *ᵥ p) ∧
    p ⬝ᵥ (M3 *ᵥ p) = p ⬝ᵥ (N3 *ᵥ p)

theorem SameForms.symm (h : SameForms M1 M2 M3 N1 N2 N3) : SameForms N1 N2 N3 M1 M2 M3 :=
  fun p => ⟨(h p).1.symm, (h p).2.1.symm, (h p).2.2.symm⟩

/-- A point of `D_δ` for the matrices `M_i` is a point for any matrices `N_i` with the same
forms. -/
def transferD (h : SameForms M1 M2 M3 N1 N2 N3) (x : DPoint L M1 M2 M3 δ) :
    DPoint L N1 N2 N3 δ where
  p := x.p
  r := x.r
  s := x.s
  ne_zero := x.ne_zero
  eq1 := by rw [← (h x.p).1]; exact x.eq1
  eq2 := by rw [← (h x.p).2.1]; exact x.eq2
  eq3 := by rw [← (h x.p).2.2]; exact x.eq3

theorem over_transferD [Algebra ℚ L] (h : SameForms M1 M2 M3 N1 N2 N3)
    (x : DPoint L M1 M2 M3 δ) (a b c : ℚ) : (transferD h x).Over a b c ↔ x.Over a b c :=
  Iff.rfl

theorem descent_congr {k : Type*} [Field k] [Algebra ℚ k]
    {M1 M2 M3 N1 N2 N3 : Matrix (Fin 3) (Fin 3) k} {δ0 δ1 : k}
    (h : SameForms M1 M2 M3 N1 N2 N3) (hD : Descent k M1 M2 M3 δ0 δ1) :
    Descent k N1 N2 N3 δ0 δ1 := by
  intro x y z hne hF
  rcases hD x y z hne hF with ⟨d, hd⟩ | ⟨d, hd⟩
  · exact Or.inl ⟨transferD h d, hd⟩
  · exact Or.inr ⟨transferD h d, hd⟩

theorem twistConclusion_congr {k : Type*} [Field k] [Algebra ℚ k]
    {M1 M2 M3 N1 N2 N3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    (h : SameForms M1 M2 M3 N1 N2 N3) (hT : TwistConclusion k N1 N2 N3 δ Pa Pb) :
    TwistConclusion k M1 M2 M3 δ Pa Pb :=
  fun d x y z hd => hT (transferD h d) x y z hd

end FurioLombardo.Discharge.M3a
