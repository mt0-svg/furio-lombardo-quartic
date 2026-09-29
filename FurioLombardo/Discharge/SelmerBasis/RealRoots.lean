import FurioLombardo.Discharge.SelmerBasis.PlaceReal
import FurioLombardo.Discharge.SelmerBasis.RealRootData

/-!
# The real roots of `fRev 0` at the real places 5 and 6 (`realEmb 0`, `realEmb 1`)

Places 5 and 6 of sb_3_places are `realEmb 0` and `realEmb 1` (code/selmer-local-conditions/real_roots.gp).
Over `L42 = K21(ω)`, `ω² = ε`, `h 0 = hp · conj(hp)` with `hp = X² + (p0 + p1 ω) X + (r0 + r1 ω)`
(data RealRootData.lean, four kernel identities). At a real embedding `σ` with `t = √σ(ε)` this gives
`h^σ = g₊ g₋`, `g± = X² + (p0 ± t p1) X + (r0 ± t r1)`, with discriminants `(A ± t B) / D²` whose
product is `σ(N Δ) / D⁴ < 0`. So exactly one factor, the one with the sign `ς = sign σ(B)`, has real
roots, and the other is positive. The signs of `q 0` and `h 0` at five rational separators (kernel
sign certificates) place the two roots of `q^σ` and the two real roots of `h^σ`:
layout `(q, h, q, h)` at place 5 and `(h, q, h, q)` at place 6 (referee F5).
-/

namespace FurioLombardo.Discharge.SelmerBasis.RealRoots

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3b
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin
  FurioLombardo.Discharge.SelmerBasis.RealRootData

/-! ## Signs at one real embedding -/

/-- The refined root interval `(lo k / Dr2, hi k / Dr2)` of `realEmb k`. -/
def lo (k : Fin 3) : ℤ := rA2.getD k 0
def hi (k : Fin 3) : ℤ := rB2.getD k 0

theorem Dr2_pos : 0 < Dr2 := by decide

theorem ck_bracket2 : ∀ k : Fin 3, bracketL Dr2 fL (lo k) (hi k) = true := by decide +kernel

theorem ck_inside2 : ∀ k : Fin 3, rtA k * (Dr2 : ℤ) < lo k * Dr ∧ hi k * Dr < rtB k * Dr2 := by
  decide

theorem ck_disjoint : ∀ i j : Fin 3, i ≠ j → rtB i ≤ rtA j ∨ rtB j ≤ rtA i := by decide

theorem rootR_mem2 (k : Fin 3) : (lo k : ℝ) / Dr2 < rootR k ∧ rootR k < (hi k : ℝ) / Dr2 := by
  obtain ⟨x, h1, h2, hx⟩ := exists_root_of_bracketL Dr2_pos (ck_bracket2 k)
  obtain ⟨k', rfl⟩ := eq_rootR hx
  have hD : (0 : ℝ) < Dr := by exact_mod_cast Dr_pos
  have hD2 : (0 : ℝ) < Dr2 := by exact_mod_cast Dr2_pos
  -- `rootR k'` lies in the old interval of `k`
  obtain ⟨i1, i2⟩ := ck_inside2 k
  have a1 : (rtA k : ℝ) / Dr < rootR k' := by
    refine lt_trans ?_ h1
    rw [div_lt_div_iff₀ hD hD2]
    exact_mod_cast i1
  have a2 : rootR k' < (rtB k : ℝ) / Dr := by
    refine lt_trans h2 ?_
    rw [div_lt_div_iff₀ hD2 hD]
    exact_mod_cast i2
  obtain ⟨b1, b2, -⟩ := rootR_spec k'
  have hk : k' = k := by
    by_contra hne
    rcases ck_disjoint k k' (Ne.symm hne) with h | h
    · have : (rtB k : ℝ) / Dr ≤ (rtA k' : ℝ) / Dr :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le
      linarith
    · have : (rtB k' : ℝ) / Dr ≤ (rtA k : ℝ) / Dr :=
        div_le_div_of_nonneg_right (by exact_mod_cast h) hD.le
      linarith
  subst hk
  exact ⟨h1, h2⟩

/-- Sign certificate of the element with zk coordinates `a` on the refined interval of `realEmb k`. -/
def elemCertAt (a : List ℤ) (s : ℤ) (k : Fin 3) : Bool :=
  signCert s [lo k, hi k] [(Dr2 : ℤ), (Dr2 : ℤ)] (combo a zkNum)

theorem elemAt_sign {a : List ℤ} {s : ℤ} {k : Fin 3} (h : elemCertAt a s k = true) :
    0 < (s : ℝ) * realEmb k (zkE a) := by
  rw [realEmb_zkE]
  have h1 := signCert_Ioo Dr2_pos h (rootR_mem2 k).1 (rootR_mem2 k).2
  have hDz : (0 : ℝ) < (Dz : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (by decide : 0 < Dz))
  calc (0 : ℝ) < (Dz : ℝ)⁻¹ * ((s : ℝ) * evalL (rootR k) (combo a zkNum)) := mul_pos hDz h1
    _ = _ := by ring

theorem pos_of_cert {a : List ℤ} {k : Fin 3} (h : elemCertAt a 1 k = true) :
    0 < realEmb k (zkE a) := by
  simpa using elemAt_sign h

theorem neg_of_cert {a : List ℤ} {k : Fin 3} (h : elemCertAt a (-1) k = true) :
    realEmb k (zkE a) < 0 := by
  have := elemAt_sign h
  push_cast at this
  linarith

/-! ## Kernel identities -/

def epsE : KE := .lin epsL
def P0E : KE := .lin rhP0
def P1E : KE := .lin rhP1
def R0E : KE := .lin rhR0
def R1E : KE := .lin rhR1
/-- `rhDen² Δ₀ = P0² + ε P1² - 4 rhDen R0`. -/
def AE : KE := .sub (.add (.mul P0E P0E) (.mul epsE (.mul P1E P1E))) (.mul (.int (4 * rhDen)) R0E)
/-- `rhDen² Δ₁ = 2 P0 P1 - 4 rhDen R1`. -/
def BE : KE := .sub (.mul (.int 2) (.mul P0E P1E)) (.mul (.int (4 * rhDen)) R1E)

theorem ck_h3 : checkK 2048 (.sub (.mul (.int rhDen) (hE 0 3))
    (.mul (.int (2 * hDenN 0)) P0E)) = true := by decide +kernel

theorem ck_h2 : checkK 2048 (.sub (.mul (.int (rhDen * rhDen)) (hE 0 2))
    (.mul (.int (hDenN 0)) (.add (.mul (.int (2 * rhDen)) R0E)
      (.sub (.mul P0E P0E) (.mul epsE (.mul P1E P1E)))))) = true := by decide +kernel

theorem ck_h1 : checkK 2048 (.sub (.mul (.int (rhDen * rhDen)) (hE 0 1))
    (.mul (.int (hDenN 0)) (.sub (.mul (.int 2) (.mul P0E R0E))
      (.mul (.int 2) (.mul epsE (.mul P1E R1E)))))) = true := by decide +kernel

theorem ck_h0 : checkK 2048 (.sub (.mul (.int (rhDen * rhDen)) (hE 0 0))
    (.mul (.int (hDenN 0)) (.sub (.mul R0E R0E) (.mul epsE (.mul R1E R1E))))) = true := by
  decide +kernel

theorem ck_D1 : checkK 2048 (.sub (.lin rhD1) BE) = true := by decide +kernel

theorem ck_N : checkK 2048 (.sub (.lin rhN) (.sub (.mul AE AE) (.mul epsE (.mul BE BE)))) = true := by
  decide +kernel

/-! ## Separators -/

def sn (k i : ℕ) : ℤ := (sepN.getD k []).getD i 0
def sd (k i : ℕ) : ℤ := (sepD.getD k []).getD i 1
def sQ (k i : ℕ) : List ℤ := (sepQ.getD k []).getD i []
def sH (k i : ℕ) : List ℤ := (sepH.getD k []).getD i []

/-- `d² qDen q 0 (n / d)`. -/
def qsE (k i : ℕ) : KE :=
  .add (.add (.mul (.int (sd k i * sd k i)) (qE 0 0)) (.mul (.int (sn k i * sd k i)) (qE 0 1)))
    (.int (qDenN 0 * sn k i * sn k i))

/-- `d⁴ hDen h 0 (n / d)`. -/
def hsE (k i : ℕ) : KE :=
  .add (.add (.add (.add (.mul (.int (sd k i ^ 4)) (hE 0 0))
    (.mul (.int (sn k i * sd k i ^ 3)) (hE 0 1))) (.mul (.int (sn k i ^ 2 * sd k i ^ 2)) (hE 0 2)))
    (.mul (.int (sn k i ^ 3 * sd k i)) (hE 0 3))) (.int (hDenN 0 * sn k i ^ 4))

theorem ck_sepQ : ∀ k : Fin 2, ∀ i : Fin 5, checkK 2048 (.sub (qsE k i) (.lin (sQ k i))) = true := by
  decide +kernel

theorem ck_sepH : ∀ k : Fin 2, ∀ i : Fin 5, checkK 2048 (.sub (hsE k i) (.lin (sH k i))) = true := by
  decide +kernel

theorem sd_pos : ∀ k : Fin 2, ∀ i : Fin 5, 0 < sd k i := by decide

/-! ## Sign certificates at places 5 (`realEmb 0`) and 6 (`realEmb 1`) -/

/-- Signs of `q 0` at the separators. -/
def sgnQ : Fin 2 → Fin 5 → ℤ := ![![1, -1, -1, 1, 1], ![1, 1, -1, -1, 1]]
/-- Signs of `h 0` at the separators. -/
def sgnH : Fin 2 → Fin 5 → ℤ := ![![1, 1, -1, -1, 1], ![1, -1, -1, 1, 1]]
/-- The sign `ς` of `σ(Δ₁)`. -/
def sgnB : Fin 2 → ℤ := ![-1, 1]

theorem ck_sgnQ : ∀ k : Fin 2, ∀ i : Fin 5, elemCertAt (sQ k i) (sgnQ k i) (Fin.castSucc k) = true := by
  decide +kernel

theorem ck_sgnH : ∀ k : Fin 2, ∀ i : Fin 5, elemCertAt (sH k i) (sgnH k i) (Fin.castSucc k) = true := by
  decide +kernel

theorem ck_sgnB : ∀ k : Fin 2, elemCertAt rhD1 (sgnB k) (Fin.castSucc k) = true := by
  decide +kernel

theorem ck_sgnN : ∀ k : Fin 2, elemCertAt rhN (-1) (Fin.castSucc k) = true := by
  decide +kernel

/-! ## Real quadratics -/

theorem quad_split {B C a : ℝ} (ha : a ^ 2 + B * a + C < 0) :
    ∃ u v : ℝ, u < a ∧ a < v ∧ ∀ x, x ^ 2 + B * x + C = (x - u) * (x - v) := by
  have hD : 0 < B ^ 2 - 4 * C := by nlinarith [sq_nonneg (2 * a + B)]
  set s := Real.sqrt (B ^ 2 - 4 * C) with hs
  have hs2 : s * s = B ^ 2 - 4 * C := Real.mul_self_sqrt hD.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  refine ⟨(-B - s) / 2, (-B + s) / 2, ?_, ?_, fun x => by linear_combination (1 / 4 : ℝ) * hs2⟩
  · nlinarith [sq_nonneg (2 * a + B + s)]
  · nlinarith [sq_nonneg (2 * a + B - s)]

theorem quad_pos {B C : ℝ} (hd : B ^ 2 - 4 * C < 0) (x : ℝ) : 0 < x ^ 2 + B * x + C := by
  nlinarith [sq_nonneg (2 * x + B)]

/-- Two monic real quadratics with the signs `(+, -, -, +)` at `s0, s1, s2, s3` and at
`s1, s2, s3, s4` have interlaced roots. -/
theorem interlace {B1 C1 B2 C2 s0 s1 s2 s3 s4 : ℝ} (h01 : s0 < s1) (h12 : s1 < s2) (h23 : s2 < s3)
    (h34 : s3 < s4)
    (a0 : 0 < s0 ^ 2 + B1 * s0 + C1) (a1 : s1 ^ 2 + B1 * s1 + C1 < 0)
    (a2 : s2 ^ 2 + B1 * s2 + C1 < 0) (a3 : 0 < s3 ^ 2 + B1 * s3 + C1)
    (b1 : 0 < s1 ^ 2 + B2 * s1 + C2) (b2 : s2 ^ 2 + B2 * s2 + C2 < 0)
    (b3 : s3 ^ 2 + B2 * s3 + C2 < 0) (b4 : 0 < s4 ^ 2 + B2 * s4 + C2) :
    ∃ x1 x2 y1 y2 : ℝ, s0 < x1 ∧ x1 < s1 ∧ s1 < y1 ∧ y1 < s2 ∧ s2 < x2 ∧ x2 < s3 ∧ s3 < y2 ∧
      y2 < s4 ∧ (∀ x, x ^ 2 + B1 * x + C1 = (x - x1) * (x - x2)) ∧
      (∀ x, x ^ 2 + B2 * x + C2 = (x - y1) * (x - y2)) := by
  obtain ⟨u, v, hu, hv, huv⟩ := quad_split a1
  obtain ⟨u', v', hu', hv', huv'⟩ := quad_split b2
  rw [huv] at a0 a2 a3
  rw [huv'] at b1 b3 b4
  have c1 : s0 < u := by
    by_contra h
    push Not at h
    nlinarith
  have c2 : s2 < v := by
    by_contra h
    push Not at h
    nlinarith
  have c3 : v < s3 := by
    by_contra h
    push Not at h
    nlinarith
  have d1 : s1 < u' := by
    by_contra h
    push Not at h
    nlinarith
  have d2 : s3 < v' := by
    by_contra h
    push Not at h
    nlinarith
  have d3 : v' < s4 := by
    by_contra h
    push Not at h
    nlinarith
  exact ⟨u, v, u', v', c1, hu, d1, hu', c2, c3, d2, d3, huv, huv'⟩

end FurioLombardo.Discharge.SelmerBasis.RealRoots
