import Mathlib

/-!
# Frozen statement: Conjecture 1.6 of Furio and Lombardo

Source: `PROBLEM.md`, and Furio and Lombardo, "On 7-adic Galois representations for elliptic
curves over Q", arXiv 2507.17967v3, Conjecture 1.6 (`conj: XE3` in the LaTeX source):

  The set of rational points of the curve
  C : x^4 + 3x^3y - 3x^2yz - 3x^2z^2 + 6xy^3 - 6xy^2z + 3xyz^2 - 2xz^3 + 4y^4 + 2y^3z - 5yz^3 = 0
  is C(Q) = {[0 : 0 : 1], [1 : 1 : 1], [2 : 0 : 1], [-1 : 0 : 1]}.

A rational point of the projective plane is a nonzero triple of rationals up to a nonzero
rational factor. `FurioLombardo.Conjecture` says: a nonzero rational triple lies on C if and only
if it is a nonzero multiple of one of the four listed triples. The direction "if" (the four points
are on C) is a finite check, proved below; the open part is "only if", stated separately as
`FurioLombardo.OnlyFourPoints`. `conjecture_iff_onlyFourPoints` records that they are equivalent.
-/

namespace FurioLombardo

/-- The quartic form defining C, term by term as in the paper. -/
def F {R : Type*} [CommRing R] (x y z : R) : R :=
  x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3
    + 4*y^4 + 2*y^3*z - 5*y*z^3

/-- The four listed points `[0:0:1], [1:1:1], [2:0:1], [-1:0:1]`, as representative triples
`(x, y, z)`. -/
def listed : List (ℚ × ℚ × ℚ) := [(0, 0, 1), (1, 1, 1), (2, 0, 1), (-1, 0, 1)]

/-- `(x, y, z)` represents the same projective point as `P`: it is `c • P` for a nonzero rational
`c`. -/
def SameProjPoint (x y z : ℚ) (P : ℚ × ℚ × ℚ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ x = c * P.1 ∧ y = c * P.2.1 ∧ z = c * P.2.2

/-- Conjecture 1.6: for every rational triple `(x, y, z) ≠ (0, 0, 0)` (a point of `P²(ℚ)`),
the point lies on C (`F x y z = 0`) exactly when it is one of the four listed points. -/
def Conjecture : Prop :=
  ∀ x y z : ℚ, (x, y, z) ≠ (0, 0, 0) →
    (F x y z = 0 ↔ ∃ P ∈ listed, SameProjPoint x y z P)

/-- The open part: every rational point of C is one of the four. -/
def OnlyFourPoints : Prop :=
  ∀ x y z : ℚ, (x, y, z) ≠ (0, 0, 0) → F x y z = 0 → ∃ P ∈ listed, SameProjPoint x y z P

/-- The known direction: the four listed points lie on C (F is homogeneous of degree 4). -/
theorem listed_on_C (x y z : ℚ) (P : ℚ × ℚ × ℚ) (hP : P ∈ listed)
    (h : SameProjPoint x y z P) : F x y z = 0 := by
  obtain ⟨c, -, rfl, rfl, rfl⟩ := h
  simp only [listed, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl <;> simp [F] <;> ring

theorem conjecture_iff_onlyFourPoints : Conjecture ↔ OnlyFourPoints := by
  constructor
  · intro h x y z h0 hF
    exact (h x y z h0).1 hF
  · intro h x y z h0
    exact ⟨h x y z h0, fun ⟨P, hP, hs⟩ => listed_on_C x y z P hP hs⟩

end FurioLombardo
