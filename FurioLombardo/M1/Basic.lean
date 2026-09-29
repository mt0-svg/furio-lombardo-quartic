import Mathlib

/-!
# Lane M1: the field K21 and kernel-computable integer list polynomials

`K21 = ℚ[X]/(f)` for the monic degree 21 polynomial `f` of code/earlier-computations/bruin_form.gp
(variable `b` there), `θ` the class of `X`. This file is the shared definition of K21 for the furio
Lean lanes (board post of 2026-09-27): `FurioLombardo.M1.K21`, `FurioLombardo.M1.θ`, `𝓞 K21`.

A polynomial is a coefficient list, constant term first; `evalL t l` evaluates it by Horner's
rule in any commutative ring. The list operations below are run by the kernel (`decide +kernel`);
the lemmas of `FurioLombardo.M1.ListPoly` say that evaluation turns them into ring operations.
-/

namespace FurioLombardo.M1

open Polynomial

/-! ## Integer list polynomials -/

/-- Horner evaluation of an integer coefficient list (constant term first) at `t`. -/
def evalL {R : Type*} [CommRing R] (t : R) : List ℤ → R
  | [] => 0
  | a :: l => (a : R) + t * evalL t l

/-- Coefficientwise sum. -/
def addL : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

/-- Scalar multiple. -/
def smulL (c : ℤ) (l : List ℤ) : List ℤ := l.map (fun a => c * a)

/-- Difference. -/
def subL (l m : List ℤ) : List ℤ := addL l (smulL (-1) m)

/-- Product. -/
def mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: l, m => addL (smulL a m) (0 :: mulL l m)

/-- `X * r` reduced once modulo the monic `X ^ gl.length + gl` (`gl` = lower coefficients): when `r`
has length `gl.length`, the top coefficient of `0 :: r` is folded back using `X ^ n = -gl`. -/
def mulXL (gl r : List ℤ) : List ℤ :=
  if r.length = gl.length then addL (0 :: r.dropLast) (smulL (-(r.getLastD 0)) gl) else 0 :: r

/-- Reduction modulo the monic `X ^ gl.length + gl` (Horner scheme from the top). -/
def redL (gl : List ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: l => addL [a] (mulXL gl (redL gl l))

/-- Every coefficient is zero. -/
def allZeroL : List ℤ → Bool
  | [] => true
  | a :: l => a == 0 && allZeroL l

/-- Every coefficient is divisible by `m`. -/
def allDvdL (m : ℤ) : List ℤ → Bool
  | [] => true
  | a :: l => a % m == 0 && allDvdL m l

/-- The Mathlib polynomial with coefficient list `l`. -/
noncomputable def ofListL : List ℤ → ℤ[X]
  | [] => 0
  | a :: l => C a + X * ofListL l

/-! ## The polynomial f and the field K21 -/

/-- The coefficients of `f`, constant term first (degree 21, monic). -/
def fL : List ℤ :=
  [-4, 28, -112, 252, -336, 28, 560, -1072, 1008, -280, -770, 980, -609, 175, 2, 98, -84, 0, 0,
    14, -7, 1]

/-- The lower coefficients of `f` (`f = X ^ 21 + fLow`), the modulus format of `redL`. -/
def fLow : List ℤ := fL.dropLast

/-- The defining polynomial of K21 (`K21` in code/earlier-computations/bruin_form.gp). -/
noncomputable def fZ : ℤ[X] :=
  X ^ 21 - 7 * X ^ 20 + 14 * X ^ 19 - 84 * X ^ 16 + 98 * X ^ 15 + 2 * X ^ 14 + 175 * X ^ 13
    - 609 * X ^ 12 + 980 * X ^ 11 - 770 * X ^ 10 - 280 * X ^ 9 + 1008 * X ^ 8 - 1072 * X ^ 7
    + 560 * X ^ 6 + 28 * X ^ 5 - 336 * X ^ 4 + 252 * X ^ 3 - 112 * X ^ 2 + 28 * X - 4

/-- `f` over `ℚ`. -/
noncomputable def fQ : ℚ[X] := fZ.map (Int.castRingHom ℚ)

/-! ### Irreducibility of `f` (generalized Eisenstein criterion at 7)

`fZ ≡ qZ ^ 7 mod 7` with `qZ = X^3 + 2X^2 - X - 4` irreducible modulo 7 (no root), and
`fZ mod qZ = 182196 X^2 + 520632 X - 955220` is not zero modulo 49 (`182196 ≡ 14 mod 49`). The
proof is the one of lane M2 (lean/FurioLombardo/M2/Field.lean), copied here so that the shared
definition of K21 carries no hypothesis. -/

/-- The cubic with `fZ ≡ qZ ^ 7 mod 7`. -/
noncomputable def qZ : ℤ[X] := X ^ 3 + 2 * X ^ 2 - X - 4

/-- `(fZ - qZ ^ 7) / 7`. -/
noncomputable def hZ : ℤ[X] :=
  -3 * X ^ 20 - 9 * X ^ 19 - 24 * X ^ 18 + 25 * X ^ 17 + 238 * X ^ 16 + 427 * X ^ 15
    - 446 * X ^ 14 - 2388 * X ^ 13 - 1957 * X ^ 12 + 4835 * X ^ 11 + 9586 * X ^ 10
    - 589 * X ^ 9 - 17562 * X ^ 8 - 12601 * X ^ 7 + 14196 * X ^ 6 + 21300 * X ^ 5
    - 1264 * X ^ 4 - 15068 * X ^ 3 - 5136 * X ^ 2 + 4100 * X + 2340

/-- The quotient of `fZ` by `qZ`. -/
noncomputable def sZ : ℤ[X] :=
  X ^ 18 - 9 * X ^ 17 + 33 * X ^ 16 - 71 * X ^ 15 + 139 * X ^ 14 - 301 * X ^ 13 + 555 * X ^ 12
    - 853 * X ^ 11 + 1232 * X ^ 10 - 1706 * X ^ 9 + 2212 * X ^ 8 - 1972 * X ^ 7 - 948 * X ^ 6
    + 9780 * X ^ 5 - 29468 * X ^ 4 + 65484 * X ^ 3 - 121288 * X ^ 2 + 189852 * X - 238804

/-- The remainder of `fZ` by `qZ`. -/
noncomputable def rZ : ℤ[X] := 182196 * X ^ 2 + 520632 * X - 955220

theorem fZ_eq_q7 : fZ = qZ ^ 7 + 7 * hZ := by
  unfold fZ qZ hZ; ring

theorem fZ_eq_qs_r : fZ = qZ * sZ + rZ := by
  unfold fZ qZ sZ rZ; ring

theorem fZ_natDegree : fZ.natDegree = 21 := by unfold fZ; compute_degree!

theorem fZ_monic : fZ.Monic := by unfold fZ; monicity!

theorem qZ_monic : qZ.Monic := by unfold qZ; monicity!

theorem qZ_natDegree : qZ.natDegree = 3 := by unfold qZ; compute_degree!

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem qZ_map7_irreducible : Irreducible (qZ.map (algebraMap ℤ (ZMod 7))) := by
  have hq : qZ.map (algebraMap ℤ (ZMod 7)) = X ^ 3 + 2 * X ^ 2 - X - 4 := by simp [qZ]
  rw [hq]
  have hdeg : (X ^ 3 + 2 * X ^ 2 - X - 4 : (ZMod 7)[X]).natDegree = 3 := by compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x ↦ ?_
  simp only [IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_ofNat]
  revert x; decide

theorem fZ_map7 : fZ.map (algebraMap ℤ (ZMod 7)) =
    C (algebraMap ℤ (ZMod 7) fZ.leadingCoeff) * (qZ.map (algebraMap ℤ (ZMod 7))) ^ 7 := by
  rw [fZ_monic.leadingCoeff, map_one, C_1, one_mul, fZ_eq_q7, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_mul]
  have : (7 : ℤ[X]).map (algebraMap ℤ (ZMod 7)) = 0 := by
    rw [show (7 : ℤ[X]) = C 7 from rfl, Polynomial.map_C]
    simp only [map_ofNat]
    exact CharP.ofNat_eq_zero' _ 7 7 (by norm_num)
  rw [this, zero_mul, add_zero]

theorem rZ_degree_lt : rZ.degree < qZ.degree := by
  rw [Polynomial.degree_eq_natDegree qZ_monic.ne_zero, qZ_natDegree]; unfold rZ; compute_degree!

theorem fZ_modByMonic : fZ %ₘ qZ = rZ :=
  (Polynomial.div_modByMonic_unique sZ rZ qZ_monic ⟨by rw [fZ_eq_qs_r]; ring, rZ_degree_lt⟩).2

theorem fZ_irreducible : Irreducible fZ := by
  refine generalizedEisenstein (K := ZMod 7) (q := qZ) (p := 7) qZ_map7_irreducible qZ_monic
    fZ_monic.isPrimitive (by rw [fZ_natDegree]; norm_num) ?_ fZ_map7 ?_
  · rw [fZ_monic.leadingCoeff]; simp
  · rw [fZ_modByMonic, CharP.ker_intAlgebraMap_eq_span 7, Ideal.span_singleton_pow]
    intro h
    have h2 := congrArg (fun g => g.coeff 2) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
    have : rZ.coeff 2 = 182196 := by unfold rZ; simp [coeff_X]
    rw [this] at h2
    norm_num at h2

theorem fQ_irreducible : Irreducible fQ := by
  have := (fZ_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp fZ_irreducible
  rwa [algebraMap_int_eq] at this

instance fact_irreducible_fQ : Fact (Irreducible fQ) := ⟨fQ_irreducible⟩

/-- The degree 21 field `K21 = ℚ[X]/(f)`. -/
abbrev K21 : Type := AdjoinRoot fQ

/-- The class of `X` in `K21` (the root `b` of the PARI scripts). -/
noncomputable def θ : K21 := AdjoinRoot.root fQ

end FurioLombardo.M1
