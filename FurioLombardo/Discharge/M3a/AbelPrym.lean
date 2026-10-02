import Mathlib
import FurioLombardo.M3a.Sections
import FurioLombardo.Discharge.M3a.Reduction

/-!
# Bruin's Abel-Prym map on the ideal class model (WP4 of the M3a discharge)

Bruin, arXiv math/0408069, section 6 (Lemma 6.1, Proposition 6.2), in the form of
code/earlier-computations/abel_prym_lib.gp. Setting: a field `L`, three ternary quadratic forms
`Q_i(p) = p ⬝ M_i p`, and `D_δ : Q1 = δ r², Q2 = δ r s, Q3 = δ s²` in `P⁴` (points `(p, r, s)`, type
`DPoint`). For a point `P` of `D_δ`:

* `T` is a second point of the tangent line of `D_δ` at `P` (`polarD i P T = 0`, `T ∉ L P`);
* `a_i = quadD i T` (apm_lib's `T QD_i T`) and `U = t² + 2 (a₂/a₃) t + a₁/a₃` (`bruinU`);
* at a root `t₀` of `U`, with `G = diag(M1 + 2 t₀ M2 + t₀² M3, -δ)` (`gram`), `a = (p, r + t₀ s)`,
  `b = (T_p, T_r + t₀ T_s)` (`plk`) and `A = a bᵀ - b aᵀ` (`plucker`), the ruling coordinate `Y`
  satisfies `G A G = Y ⋆A` (`hodge` is apm_lib's `apm_star`); `V` interpolates `Y` at the roots,
  which is the identity `G A G ≡ V ⋆A` modulo `U` in `L[t]`.

`Cert M1 M2 M3 δ f x` is the certificate of this construction at `x`: the tangent vector `T`,
the rank 3 condition (the tangent map `W ↦ (polarD i x W)_i` is onto, so the tangent line is
unique), `a₃ ≠ 0`, `V` of degree `< 2`, the ruling identity modulo `U`, an entry of `⋆A` that is a
unit modulo `U` (so the identity determines `V`), and `U ∣ V² - f`. Any two certificates at the
same point have the same `U` and `V` (`Cert.bruinU_eq`, `Cert.V_eq`). `bruinPhi` is the class of
the Mumford ideal `⟨U, Y - V⟩` of any certificate, and `1` at points without a certificate;
`bruinPhi_eq_of_cert` gives its value at a point with an explicit certificate. A certificate at
`x` gives one at `ι x` with `(U, -V)` (`Cert.inv`), so `bruinPhi (ι x) = (bruinPhi x)⁻¹` at every
point (`bruinPhi_inv`, from M3a's `mk0_mumford_neg`).

`phiRev` is the same construction for the swapped data `(M3, M2, M1)` at `(p, s, r)`. Under
`t = 1/t'`, `M1 + 2t M2 + t² M3 = t² (M3 + 2t' M2 + t'² M1)`, so the swapped curve is the reversed
model `Y'² = f^rev(t') = t'⁶ f(1/t')` of `Y² = f(t) = -δ det(M1 + 2t M2 + t² M3)`, and the swapped
construction is apm_lib's output transported by `(t, Y) ↦ (1/t, Y/t³)`
(checked on the known lifts by code/genus2-curves/abel_prym_explore.gp).
-/

open Polynomial Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.M3a.AbelPrym

variable {L : Type*} [Field L]

/-- Vectors of the ambient space of `D_δ`: coordinates `(x, y, z)`, `r`, `s`. -/
abbrev V5 (L : Type*) [Field L] := (Fin 3 → L) × L × L

section Forms

variable (M : Fin 3 → Matrix (Fin 3) (Fin 3) L) (δ : L)

/-- The quadrics `Q_i - δ (r², r s, s²)_i` of `D_δ` (apm_lib's `QD_i`), `M = ![M1, M2, M3]`. -/
def quadD (i : Fin 3) (W : V5 L) : L :=
  W.1 ⬝ᵥ (M i *ᵥ W.1) - δ * ![W.2.1 ^ 2, W.2.1 * W.2.2, W.2.2 ^ 2] i

/-- The polar form of `quadD i`: the derivative of `quadD i` at `P` in the direction `W`. -/
def polarD (i : Fin 3) (P W : V5 L) : L :=
  (P.1 ⬝ᵥ (M i *ᵥ W.1) + W.1 ⬝ᵥ (M i *ᵥ P.1)) -
    δ * ![2 * (P.2.1 * W.2.1), P.2.1 * W.2.2 + P.2.2 * W.2.1, 2 * (P.2.2 * W.2.2)] i

theorem polarD_comm (i : Fin 3) (P W : V5 L) : polarD M δ i P W = polarD M δ i W P := by
  unfold polarD
  rw [add_comm (P.1 ⬝ᵥ (M i *ᵥ W.1))]
  congr 2
  fin_cases i <;> simp [mul_comm]; ring

theorem polarD_add (i : Fin 3) (P W W' : V5 L) :
    polarD M δ i P (W + W') = polarD M δ i P W + polarD M δ i P W' := by
  simp only [polarD, Prod.fst_add, Prod.snd_add, mulVec_add, dotProduct_add, add_dotProduct]
  fin_cases i <;> simp <;> ring

theorem polarD_smul (i : Fin 3) (P W : V5 L) (c : L) :
    polarD M δ i P (c • W) = c * polarD M δ i P W := by
  simp only [polarD, Prod.smul_fst, Prod.smul_snd, mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  fin_cases i <;> simp <;> ring

theorem polarD_self (i : Fin 3) (P : V5 L) : polarD M δ i P P = 2 * quadD M δ i P := by
  unfold polarD quadD
  fin_cases i <;> simp <;> ring

/-- `quadD i (c T + d P) = c² quadD i T + c d polarD i P T + d² quadD i P`. -/
theorem quadD_add_smul (i : Fin 3) (T P : V5 L) (c d : L) :
    quadD M δ i (c • T + d • P) = c ^ 2 * quadD M δ i T + c * d * polarD M δ i P T +
      d ^ 2 * quadD M δ i P := by
  simp only [quadD, polarD, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
    mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  fin_cases i <;> simp <;> ring

/-- The tangent map `W ↦ (polarD i P W)_i`, whose kernel is the tangent space at `P`. -/
def tangentMap (P : V5 L) : V5 L →ₗ[L] (Fin 3 → L) where
  toFun W i := polarD M δ i P W
  map_add' W W' := by funext i; exact polarD_add M δ i P W W'
  map_smul' c W := by funext i; simp [polarD_smul]

theorem tangentMap_apply (P W : V5 L) (i : Fin 3) :
    tangentMap M δ P W i = polarD M δ i P W := rfl

end Forms

/-! ## The tangent line is unique when the tangent forms have rank 3 -/

theorem finrank_V5 : Module.finrank L (V5 L) = 5 := by
  simp [Module.finrank_prod]

/-- Rank-nullity: if `Φ : L⁵ → L³` is surjective and `T, P` are independent in its kernel, the
kernel is spanned by `T` and `P`. -/
theorem exists_eq_of_rank (Φ : V5 L →ₗ[L] (Fin 3 → L)) (hsurj : Function.Surjective Φ)
    {T P : V5 L} (hT : Φ T = 0) (hP : Φ P = 0)
    (hind : LinearIndependent L ![T, P]) {W : V5 L} (hW : Φ W = 0) :
    ∃ c d : L, W = c • T + d • P := by
  have hrange : Module.finrank L (LinearMap.range Φ) = 3 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]; simp
  have hker : Module.finrank L (LinearMap.ker Φ) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrange, finrank_V5] at this; omega
  have hle : Submodule.span L (Set.range ![T, P]) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · simpa using hT
    · simpa using hP
  have hspan : Module.finrank L (Submodule.span L (Set.range ![T, P])) = 2 := by
    rw [finrank_span_eq_card hind]; simp
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan, hker])
  have hWmem : W ∈ Submodule.span L (Set.range ![T, P]) := by
    rw [heq]; exact hW
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hWmem
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp

/-! ## Points of `D_δ` -/

variable {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

/-- The coordinates `(p, r, s)` of a point of `D_δ`. -/
def pt (x : DPoint L M1 M2 M3 δ) : V5 L := (x.p, x.r, x.s)

theorem quadD_pt (x : DPoint L M1 M2 M3 δ) (i : Fin 3) :
    quadD ![M1, M2, M3] δ i (pt x) = 0 := by
  fin_cases i
  · simp [quadD, pt, x.eq1]
  · simp [quadD, pt, x.eq2]
  · simp [quadD, pt, x.eq3]

/-- The point `(p, s, r)` of `D_δ` for the swapped forms `(Q3, Q2, Q1)`. -/
def swapPt (x : DPoint L M1 M2 M3 δ) : DPoint L M3 M2 M1 δ where
  p := x.p
  r := x.s
  s := x.r
  ne_zero := x.ne_zero
  eq1 := x.eq3
  eq2 := by rw [x.eq2, mul_comm x.r]
  eq3 := x.eq1

theorem swapPt_inv (x : DPoint L M1 M2 M3 δ) : swapPt x.inv = (swapPt x).inv := rfl

/-! ## The polynomial layer -/

section Poly

variable (M1 M2 M3 δ)

/-- The pencil `M1 + 2t M2 + t² M3` over `L[t]`. -/
noncomputable def pencil : Matrix (Fin 3) (Fin 3) L[X] :=
  Matrix.of fun a b => C (M1 a b) + 2 * X * C (M2 a b) + X ^ 2 * C (M3 a b)

/-- apm_lib's `G = diag(M1 + 2t M2 + t² M3, -δ)`. -/
noncomputable def gram : Matrix (Fin 4) (Fin 4) L[X] :=
  !![pencil M1 M2 M3 0 0, pencil M1 M2 M3 0 1, pencil M1 M2 M3 0 2, 0;
     pencil M1 M2 M3 1 0, pencil M1 M2 M3 1 1, pencil M1 M2 M3 1 2, 0;
     pencil M1 M2 M3 2 0, pencil M1 M2 M3 2 1, pencil M1 M2 M3 2 2, 0;
     0, 0, 0, -C δ]

/-- apm_lib's `U = t² + 2 (a₂/a₃) t + a₁/a₃` with `a_i = quadD i T`. -/
noncomputable def bruinU (T : V5 L) : L[X] :=
  X ^ 2 + C (2 * quadD ![M1, M2, M3] δ 1 T / quadD ![M1, M2, M3] δ 2 T) * X +
    C (quadD ![M1, M2, M3] δ 0 T / quadD ![M1, M2, M3] δ 2 T)

end Poly

/-- The projection `(x, y, z, r + t s)` of a vector from the vertex `(0 : 0 : 0 : -t : 1)`. -/
noncomputable def plk (W : V5 L) : Fin 4 → L[X] :=
  ![C (W.1 0), C (W.1 1), C (W.1 2), C W.2.1 + X * C W.2.2]

/-- The Plücker matrix `a bᵀ - b aᵀ` of the plane spanned by `a` and `b`. -/
def plucker {R : Type*} [CommRing R] (a b : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  vecMulVec a b - vecMulVec b a

/-- The Hodge star on `4 × 4` antisymmetric matrices, `(⋆A)_{ij} = Σ_{k<l} ε_{ijkl} A_{kl}`
(apm_lib's `apm_star`). -/
def hodge {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, A 2 3, A 3 1, A 1 2;
     -A 2 3, 0, A 0 3, A 2 0;
     -A 3 1, -A 0 3, 0, A 0 1;
     -A 1 2, -A 2 0, -A 0 1, 0]

theorem hodge_smul {R : Type*} [CommRing R] (r : R) (A : Matrix (Fin 4) (Fin 4) R) :
    hodge (r • A) = r • hodge A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hodge]

theorem degree_lin_lt (a b : L) : (C a * X + C b).degree < 2 :=
  lt_of_le_of_lt (degree_add_le _ _)
    (max_lt (lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num))
      (lt_of_le_of_lt degree_C_le (by norm_num)))

variable (M1 M2 M3 δ) in
theorem bruinU_monic (T : V5 L) : (bruinU M1 M2 M3 δ T).Monic := by
  unfold bruinU
  rw [add_assoc]
  exact monic_X_pow_add (degree_lin_lt _ _)

variable (M1 M2 M3 δ) in
theorem bruinU_natDegree (T : V5 L) : (bruinU M1 M2 M3 δ T).natDegree = 2 := by
  unfold bruinU
  rw [add_assoc, natDegree_add_eq_left_of_degree_lt]
  · simp
  · rw [degree_X_pow]; exact degree_lin_lt _ _

variable (M1 M2 M3 δ) in
theorem bruinU_degree (T : V5 L) : (bruinU M1 M2 M3 δ T).degree = 2 := by
  rw [degree_eq_natDegree (bruinU_monic M1 M2 M3 δ T).ne_zero, bruinU_natDegree]; rfl

/-- `a₃ U = a₁ + 2 a₂ t + a₃ t²`. -/
theorem C_mul_bruinU {T : V5 L} (h : quadD ![M1, M2, M3] δ 2 T ≠ 0) :
    C (quadD ![M1, M2, M3] δ 2 T) * bruinU M1 M2 M3 δ T =
      C (quadD ![M1, M2, M3] δ 0 T) + C (2 * quadD ![M1, M2, M3] δ 1 T) * X +
        C (quadD ![M1, M2, M3] δ 2 T) * X ^ 2 := by
  unfold bruinU
  have e1 : quadD ![M1, M2, M3] δ 2 T * (2 * quadD ![M1, M2, M3] δ 1 T / quadD ![M1, M2, M3] δ 2 T)
      = 2 * quadD ![M1, M2, M3] δ 1 T := by field_simp
  have e0 : quadD ![M1, M2, M3] δ 2 T * (quadD ![M1, M2, M3] δ 0 T / quadD ![M1, M2, M3] δ 2 T) =
      quadD ![M1, M2, M3] δ 0 T := by field_simp
  rw [mul_add, mul_add, ← mul_assoc, ← map_mul, e1, ← map_mul, e0]
  ring

/-! ## The certificate -/

variable (M1 M2 M3 δ) in
/-- A certificate of Bruin's construction at the point `x` of `D_δ`, for the curve `Y² = f`
(`f = -δ det(M1 + 2t M2 + t² M3)` in the application). -/
structure Cert (f : L[X]) (x : DPoint L M1 M2 M3 δ) where
  /-- a second point of the tangent line at `x` -/
  T : V5 L
  tangent : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0
  /-- the three tangent forms at `x` are independent (`D_δ` is smooth at `x`) -/
  rank : Function.Surjective (tangentMap ![M1, M2, M3] δ (pt x))
  indep : LinearIndependent L ![T, pt x]
  a3_ne : quadD ![M1, M2, M3] δ 2 T ≠ 0
  /-- the interpolation of the ruling coordinate `Y` at the roots of `U` -/
  V : L[X]
  degree_V : V.degree < 2
  ruling : ∀ i j, bruinU M1 M2 M3 δ T ∣
    (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j -
      V * hodge (plucker (plk (pt x)) (plk T)) i j
  unit : ∃ i j, ∃ w : L[X],
    bruinU M1 M2 M3 δ T ∣ w * hodge (plucker (plk (pt x)) (plk T)) i j - 1
  sq : bruinU M1 M2 M3 δ T ∣ V ^ 2 - f

namespace Cert

variable {f : L[X]} {x : DPoint L M1 M2 M3 δ}

theorem tangentMap_T (c : Cert M1 M2 M3 δ f x) :
    tangentMap ![M1, M2, M3] δ (pt x) c.T = 0 := by
  funext i; exact c.tangent i

theorem tangentMap_pt (x : DPoint L M1 M2 M3 δ) :
    tangentMap ![M1, M2, M3] δ (pt x) (pt x) = 0 := by
  funext i
  rw [tangentMap_apply, polarD_self, quadD_pt, mul_zero]; rfl

/-- Every tangent vector at `x` is `a T + b x`. -/
theorem tline (c : Cert M1 M2 M3 δ f x) {W : V5 L}
    (hW : ∀ i, polarD ![M1, M2, M3] δ i (pt x) W = 0) : ∃ a b : L, W = a • c.T + b • pt x :=
  exists_eq_of_rank (tangentMap ![M1, M2, M3] δ (pt x)) c.rank c.tangentMap_T
    (tangentMap_pt x) c.indep (funext hW)

/-- The tangent vectors of two certificates: `T' = a T + b x` with `a ≠ 0`. -/
theorem exists_smul (c c' : Cert M1 M2 M3 δ f x) :
    ∃ a b : L, a ≠ 0 ∧ c'.T = a • c.T + b • pt x := by
  obtain ⟨a, b, h⟩ := c.tline c'.tangent
  refine ⟨a, b, fun ha => ?_, h⟩
  have := (LinearIndependent.pair_iff.mp c'.indep) 1 (-b) (by rw [h, ha]; simp)
  exact one_ne_zero this.1

theorem quadD_T (c c' : Cert M1 M2 M3 δ f x) {a b : L} (h : c'.T = a • c.T + b • pt x)
    (i : Fin 3) : quadD ![M1, M2, M3] δ i c'.T = a ^ 2 * quadD ![M1, M2, M3] δ i c.T := by
  rw [h, quadD_add_smul, c.tangent, quadD_pt]; ring

/-- Two certificates at the same point have the same `U`. -/
theorem bruinU_eq (c c' : Cert M1 M2 M3 δ f x) :
    bruinU M1 M2 M3 δ c'.T = bruinU M1 M2 M3 δ c.T := by
  obtain ⟨a, b, ha, h⟩ := exists_smul c c'
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  unfold bruinU
  rw [quadD_T c c' h 0, quadD_T c c' h 1, quadD_T c c' h 2, mul_left_comm 2 (a ^ 2),
    mul_div_mul_left _ _ ha2, mul_div_mul_left _ _ ha2]

theorem plk_add_smul (T P : V5 L) (a b : L) (k : Fin 4) :
    plk (a • T + b • P) k = C a * plk T k + C b * plk P k := by
  fin_cases k <;> simp [plk] <;> ring

theorem plucker_T (c c' : Cert M1 M2 M3 δ f x) {a b : L} (h : c'.T = a • c.T + b • pt x) :
    plucker (plk (pt x)) (plk c'.T) = C a • plucker (plk (pt x)) (plk c.T) := by
  refine Matrix.ext fun k l => ?_
  simp only [plucker, Matrix.sub_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, h,
    plk_add_smul]
  ring

/-- Two certificates at the same point have the same `V`. -/
theorem V_eq (c c' : Cert M1 M2 M3 δ f x) : c'.V = c.V := by
  obtain ⟨a, b, ha, h⟩ := exists_smul c c'
  obtain ⟨i, j, w, hw⟩ := c.unit
  have h1 := c.ruling i j
  have h2 := c'.ruling i j
  rw [bruinU_eq c c', plucker_T c c' h, hodge_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h2
  have hu : IsUnit (C a) := isUnit_C.mpr (Ne.isUnit ha)
  have h2' : bruinU M1 M2 M3 δ c.T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk c.T) * gram M1 M2 M3 δ) i j -
        c'.V * hodge (plucker (plk (pt x)) (plk c.T)) i j :=
    hu.dvd_mul_left.mp (by convert h2 using 1; ring)
  have h3 : bruinU M1 M2 M3 δ c.T ∣
      (c'.V - c.V) * hodge (plucker (plk (pt x)) (plk c.T)) i j := by
    have := dvd_sub h1 h2'
    convert this using 1; ring
  have h4 : bruinU M1 M2 M3 δ c.T ∣ c'.V - c.V := by
    have e : c'.V - c.V = w * ((c'.V - c.V) * hodge (plucker (plk (pt x)) (plk c.T)) i j) -
        (c'.V - c.V) * (w * hodge (plucker (plk (pt x)) (plk c.T)) i j - 1) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right h3 w) (dvd_mul_of_dvd_right hw _)
  have hdeg : (c'.V - c.V).degree < (bruinU M1 M2 M3 δ c.T).degree := by
    rw [bruinU_degree]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt c'.degree_V c.degree_V)
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt h4 hdeg)

/-- The factorization `V² - f = U w` of a certificate. -/
theorem sq_eq (c : Cert M1 M2 M3 δ f x) :
    c.V ^ 2 - f = bruinU M1 M2 M3 δ c.T * (dvd_iff_exists_eq_mul_right.mp c.sq).choose :=
  (dvd_iff_exists_eq_mul_right.mp c.sq).choose_spec

/-- The point `[⟨U, Y - V⟩]` of `Jac f` given by a certificate. -/
noncomputable def cls [GoodSextic f] (c : Cert M1 M2 M3 δ f x) : Jac f :=
  mumfordJac f (bruinU_monic M1 M2 M3 δ c.T) (by rw [bruinU_natDegree]; exact even_two) c.sq_eq
    (exists_coprime_of_squarefree GoodSextic.squarefree c.sq_eq)

theorem coe_cls [GoodSextic f] (c : Cert M1 M2 M3 δ f x) :
    (c.cls : Pic f) =
      ClassGroup.mk0 (mumford0 f (bruinU_monic M1 M2 M3 δ c.T).ne_zero c.V) := rfl

theorem cls_eq [GoodSextic f] (c c' : Cert M1 M2 M3 δ f x) : c'.cls = c.cls := by
  apply Subtype.ext
  rw [coe_cls, coe_cls]
  congr 1
  apply Subtype.ext
  change mumford f (bruinU M1 M2 M3 δ c'.T) c'.V = mumford f (bruinU M1 M2 M3 δ c.T) c.V
  rw [bruinU_eq c c', V_eq c c']

end Cert

/-! ## The covering involution -/

/-- The involution `(p, r, s) ↦ (p, -r, -s)` of the ambient space. -/
def iotaV (W : V5 L) : V5 L := (W.1, -W.2.1, -W.2.2)

theorem pt_inv (x : DPoint L M1 M2 M3 δ) : pt x.inv = iotaV (pt x) := rfl

@[simp] theorem iotaV_iotaV (W : V5 L) : iotaV (iotaV W) = W := by
  simp [iotaV]

theorem quadD_iotaV (M : Fin 3 → Matrix (Fin 3) (Fin 3) L) (δ : L) (i : Fin 3) (W : V5 L) :
    quadD M δ i (iotaV W) = quadD M δ i W := by
  fin_cases i <;> simp [quadD, iotaV]

theorem polarD_iotaV (M : Fin 3 → Matrix (Fin 3) (Fin 3) L) (δ : L) (i : Fin 3) (P W : V5 L) :
    polarD M δ i (iotaV P) W = polarD M δ i P (iotaV W) := by
  fin_cases i <;> simp [polarD, iotaV]

theorem polarD_iotaV_iotaV (M : Fin 3 → Matrix (Fin 3) (Fin 3) L) (δ : L) (i : Fin 3)
    (P W : V5 L) : polarD M δ i (iotaV P) (iotaV W) = polarD M δ i P W := by
  rw [polarD_iotaV, iotaV_iotaV]

/-- `iotaV` as a linear map. -/
def iotaL : V5 L →ₗ[L] V5 L where
  toFun := iotaV
  map_add' W W' := by simp [iotaV]; constructor <;> ring
  map_smul' c W := by simp [iotaV]

theorem iotaL_injective : Function.Injective (iotaL : V5 L →ₗ[L] V5 L) := fun W W' h => by
  rw [← iotaV_iotaV W, ← iotaV_iotaV W']
  exact congrArg iotaV h

theorem bruinU_iotaV (T : V5 L) : bruinU M1 M2 M3 δ (iotaV T) = bruinU M1 M2 M3 δ T := by
  simp only [bruinU, quadD_iotaV]

/-- `diag(1, 1, 1, -1)`. -/
noncomputable def sgn4 : Matrix (Fin 4) (Fin 4) L[X] := diagonal ![1, 1, 1, -1]

theorem plk_iotaV (W : V5 L) : plk (iotaV W) = sgn4 *ᵥ plk W := by
  funext k
  fin_cases k <;> simp [plk, iotaV, sgn4, mulVec_diagonal] <;> ring

theorem plucker_iotaV (P T : V5 L) :
    plucker (plk (iotaV P)) (plk (iotaV T)) = sgn4 * plucker (plk P) (plk T) * sgn4 := by
  refine Matrix.ext fun k l => ?_
  rw [plk_iotaV, plk_iotaV]
  fin_cases k <;> fin_cases l <;>
    simp [plucker, sgn4, vecMulVec_apply, mulVec_diagonal, diagonal_mul, mul_diagonal] <;> ring

theorem gram_sgn4 : gram M1 M2 M3 δ * sgn4 = sgn4 * gram M1 M2 M3 δ := by
  refine Matrix.ext fun k l => ?_
  fin_cases k <;> fin_cases l <;> simp [gram, sgn4, diagonal_mul, mul_diagonal]

theorem gram_mul_sgn4 (A : Matrix (Fin 4) (Fin 4) L[X]) :
    gram M1 M2 M3 δ * (sgn4 * A * sgn4) * gram M1 M2 M3 δ =
      sgn4 * (gram M1 M2 M3 δ * A * gram M1 M2 M3 δ) * sgn4 := by
  calc gram M1 M2 M3 δ * (sgn4 * A * sgn4) * gram M1 M2 M3 δ
      = (gram M1 M2 M3 δ * sgn4) * A * (sgn4 * gram M1 M2 M3 δ) := by
        simp only [Matrix.mul_assoc]
    _ = (sgn4 * gram M1 M2 M3 δ) * A * (gram M1 M2 M3 δ * sgn4) := by rw [gram_sgn4]
    _ = sgn4 * (gram M1 M2 M3 δ * A * gram M1 M2 M3 δ) * sgn4 := by simp only [Matrix.mul_assoc]

theorem sgn4_entry (A : Matrix (Fin 4) (Fin 4) L[X]) (i j : Fin 4) :
    (sgn4 * A * sgn4 : Matrix (Fin 4) (Fin 4) L[X]) i j =
      ![1, 1, 1, -1] i * ![1, 1, 1, -1] j * A i j := by
  simp only [sgn4, diagonal_mul, mul_diagonal]; ring

theorem hodge_sgn4 (A : Matrix (Fin 4) (Fin 4) L[X]) (i j : Fin 4) :
    hodge (sgn4 * A * sgn4 : Matrix (Fin 4) (Fin 4) L[X]) i j =
      -(![1, 1, 1, -1] i * ![1, 1, 1, -1] j * hodge A i j) := by
  fin_cases i <;> fin_cases j <;> simp [hodge, sgn4_entry]

theorem sgn_sq (i : Fin 4) : (![1, 1, 1, -1] i : L[X]) * ![1, 1, 1, -1] i = 1 := by
  fin_cases i <;> simp

namespace Cert

variable {f : L[X]} {x : DPoint L M1 M2 M3 δ}

/-- A certificate at `x` gives one at `ι x`, with the same `U` and `-V`. -/
noncomputable def inv (c : Cert M1 M2 M3 δ f x) : Cert M1 M2 M3 δ f x.inv where
  T := iotaV c.T
  tangent i := by rw [pt_inv, polarD_iotaV_iotaV]; exact c.tangent i
  rank v := by
    obtain ⟨W, hW⟩ := c.rank v
    refine ⟨iotaV W, ?_⟩
    funext i
    rw [tangentMap_apply, pt_inv, polarD_iotaV_iotaV, ← tangentMap_apply, hW]
  indep := by
    have h := c.indep.map' iotaL (LinearMap.ker_eq_bot.mpr iotaL_injective)
    have e : (iotaL ∘ ![c.T, pt x]) = ![iotaV c.T, pt x.inv] := by
      funext k; fin_cases k <;> rfl
    rwa [e] at h
  a3_ne := by rw [quadD_iotaV]; exact c.a3_ne
  V := -c.V
  degree_V := by rw [degree_neg]; exact c.degree_V
  ruling i j := by
    rw [bruinU_iotaV, pt_inv, plucker_iotaV, gram_mul_sgn4, sgn4_entry, hodge_sgn4]
    have := dvd_mul_of_dvd_right (c.ruling i j) (![1, 1, 1, -1] i * ![1, 1, 1, -1] j)
    convert this using 1; ring
  unit := by
    obtain ⟨i, j, w, hw⟩ := c.unit
    refine ⟨i, j, -(![1, 1, 1, -1] i * ![1, 1, 1, -1] j * w), ?_⟩
    rw [bruinU_iotaV, pt_inv, plucker_iotaV, hodge_sgn4]
    convert hw using 1
    have hi := sgn_sq (L := L) i
    have hj := sgn_sq (L := L) j
    linear_combination (w * hodge (plucker (plk (pt x)) (plk c.T)) i j) * (![1, 1, 1, -1] j *
      ![1, 1, 1, -1] j) * hi + (w * hodge (plucker (plk (pt x)) (plk c.T)) i j) * hj
  sq := by rw [bruinU_iotaV, neg_sq]; exact c.sq

theorem inv_T (c : Cert M1 M2 M3 δ f x) : c.inv.T = iotaV c.T := rfl

theorem inv_V (c : Cert M1 M2 M3 δ f x) : c.inv.V = -c.V := rfl

/-- **The covering involution acts as `-1`**: `[⟨U, Y + V⟩] = [⟨U, Y - V⟩]⁻¹`
(M3a's `mk0_mumford_neg`). -/
theorem cls_inv [GoodSextic f] (c : Cert M1 M2 M3 δ f x) : c.inv.cls = c.cls⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, coe_cls, coe_cls]
  have e := mk0_mumford_neg f (bruinU_monic M1 M2 M3 δ c.T) c.sq_eq
    (exists_coprime_of_squarefree GoodSextic.squarefree c.sq_eq)
  rw [← e]
  congr 1
  apply Subtype.ext
  change mumford f (bruinU M1 M2 M3 δ (iotaV c.T)) (-c.V) = mumford f (bruinU M1 M2 M3 δ c.T) (-c.V)
  rw [bruinU_iotaV]

end Cert

/-! ## The map -/

variable (M1 M2 M3 δ) in
/-- Bruin's Abel-Prym map `D_δ → Jac(Y² = f)` in the chart of the pencil `M1 + 2t M2 + t² M3`:
the class `[⟨U, Y - V⟩]` of any certificate, `1` at points without a certificate. -/
noncomputable def bruinPhi (f : L[X]) [GoodSextic f] (x : DPoint L M1 M2 M3 δ) : Jac f :=
  open Classical in
  if h : Nonempty (Cert M1 M2 M3 δ f x) then h.some.cls else 1

theorem bruinPhi_eq_of_cert {f : L[X]} [GoodSextic f] {x : DPoint L M1 M2 M3 δ}
    (c : Cert M1 M2 M3 δ f x) : bruinPhi M1 M2 M3 δ f x = c.cls := by
  unfold bruinPhi
  rw [dite_cond_eq_true (eq_true ⟨c⟩)]
  exact Cert.cls_eq _ _

theorem bruinPhi_of_not {f : L[X]} [GoodSextic f] {x : DPoint L M1 M2 M3 δ}
    (h : IsEmpty (Cert M1 M2 M3 δ f x)) : bruinPhi M1 M2 M3 δ f x = 1 := by
  unfold bruinPhi
  rw [dite_cond_eq_false (eq_false (not_nonempty_iff.mpr h))]

/-- **`φ ∘ ι = -φ`** at every point of `D_δ`. -/
theorem bruinPhi_inv {f : L[X]} [GoodSextic f] (x : DPoint L M1 M2 M3 δ) :
    bruinPhi M1 M2 M3 δ f x.inv = (bruinPhi M1 M2 M3 δ f x)⁻¹ := by
  rcases isEmpty_or_nonempty (Cert M1 M2 M3 δ f x) with h | h
  · have h' : IsEmpty (Cert M1 M2 M3 δ f x.inv) :=
      ⟨fun c' => h.false (DPoint.inv_inv x ▸ c'.inv)⟩
    rw [bruinPhi_of_not h, bruinPhi_of_not h', inv_one]
  · obtain ⟨c⟩ := h
    rw [bruinPhi_eq_of_cert c, bruinPhi_eq_of_cert c.inv, Cert.cls_inv]

variable (M1 M2 M3 δ) in
/-- The Abel-Prym map on the reversed model: Bruin's construction for the swapped forms
`(Q3, Q2, Q1)` at `(p, s, r)`, with values in `Jac f` for `f = -δ det(M3 + 2t M2 + t² M1)`, the
reversal of `-δ det(M1 + 2t M2 + t² M3)`. Proposition 3.4 of the paper. -/
noncomputable def phiRev (f : L[X]) [GoodSextic f] (x : DPoint L M1 M2 M3 δ) : Jac f :=
  bruinPhi M3 M2 M1 δ f (swapPt x)

theorem phiRev_eq_of_cert {f : L[X]} [GoodSextic f] {x : DPoint L M1 M2 M3 δ}
    (c : Cert M3 M2 M1 δ f (swapPt x)) : phiRev M1 M2 M3 δ f x = c.cls :=
  bruinPhi_eq_of_cert c

/-- **`φ ∘ ι = -φ`** for the Abel-Prym map on the reversed model. -/
theorem phiRev_inv {f : L[X]} [GoodSextic f] (x : DPoint L M1 M2 M3 δ) :
    phiRev M1 M2 M3 δ f x.inv = (phiRev M1 M2 M3 δ f x)⁻¹ := by
  unfold phiRev
  rw [swapPt_inv, bruinPhi_inv]

end FurioLombardo.Discharge.M3a.AbelPrym
