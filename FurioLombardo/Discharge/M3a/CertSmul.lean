import Mathlib
import FurioLombardo.Discharge.M3a.AbelPrymRuling

/-!
# Rescaling a point of `D_δ`

`(p, r, s)` and `(a p, a r, a s)` for `a ≠ 0` are the same point of `D_δ` in the weighted projective
space, and Bruin's construction does not see the difference: a certificate at `x` is one at the
rescaled point with the same `T` and `V` (`Cert.smul`, the ruling and unit conditions scale by `a`),
so `bruinPhi` and `phiRev` take the same value at both (`bruinPhi_smul`, `phiRev_smul`). Lane
lean-m4box uses it for `hLog`: the image in `D_δ(K_v)` of a lift is a rescaling of the point over
`pKv d X`.
-/

open Polynomial Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.M3a.AbelPrym

variable {L : Type*} [Field L] {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

/-- The point `(a p, a r, a s)` of `D_δ`. -/
def smulPt (a : L) (ha : a ≠ 0) (x : DPoint L M1 M2 M3 δ) : DPoint L M1 M2 M3 δ where
  p := a • x.p
  r := a * x.r
  s := a * x.s
  ne_zero := smul_ne_zero ha x.ne_zero
  eq1 := by
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct, x.eq1, smul_eq_mul, smul_eq_mul]; ring
  eq2 := by
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct, x.eq2, smul_eq_mul, smul_eq_mul]; ring
  eq3 := by
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct, x.eq3, smul_eq_mul, smul_eq_mul]; ring

theorem pt_smulPt (a : L) (ha : a ≠ 0) (x : DPoint L M1 M2 M3 δ) :
    pt (smulPt a ha x) = a • pt x := rfl

theorem swapPt_smulPt (a : L) (ha : a ≠ 0) (x : DPoint L M1 M2 M3 δ) :
    swapPt (smulPt a ha x) = smulPt a ha (swapPt x) := rfl

theorem smulPt_inv_smulPt (a : L) (ha : a ≠ 0) (x : DPoint L M1 M2 M3 δ) :
    smulPt a⁻¹ (inv_ne_zero ha) (smulPt a ha x) = x := by
  cases x
  simp [smulPt, inv_smul_smul₀ ha, inv_mul_cancel_left₀ ha]

/-! ## The certificate at the rescaled point -/

theorem rank_smul {P : V5 L} (a : L) (ha : a ≠ 0)
    (h : Function.Surjective (tangentMap ![M1, M2, M3] δ P)) :
    Function.Surjective (tangentMap ![M1, M2, M3] δ (a • P)) := by
  intro w
  rcases h (a⁻¹ • w) with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  ext i
  calc
    tangentMap ![M1, M2, M3] δ (a • P) W i = polarD ![M1, M2, M3] δ i (a • P) W := by
      rw [tangentMap_apply]
    _ = polarD ![M1, M2, M3] δ i W (a • P) := by rw [polarD_comm]
    _ = a * polarD ![M1, M2, M3] δ i W P := by rw [polarD_smul]
    _ = a * polarD ![M1, M2, M3] δ i P W := by rw [polarD_comm]
    _ = a * (tangentMap ![M1, M2, M3] δ P W) i := by rw [tangentMap_apply]
    _ = a * ((a⁻¹ • w) i) := by rw [hW]
    _ = a * (a⁻¹ * w i) := by rw [Pi.smul_apply, smul_eq_mul]
    _ = (a * a⁻¹) * w i := by ring
    _ = 1 * w i := by field_simp [ha]
    _ = w i := by simp

theorem indep_smul {T P : V5 L} {a : L} (ha : a ≠ 0) (h : LinearIndependent L ![T, P]) :
    LinearIndependent L ![T, a • P] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  have hzero : s • T + (t * a) • P = 0 := by
    calc
      s • T + (t * a) • P = s • T + t • (a • P) := by simp [smul_smul]
      _ = 0 := hst
  rcases h s (t * a) hzero with ⟨hs, hta⟩
  have ht : t = 0 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hta with (h' | h')
    · exact h'
    · exact (ha h').elim
  exact ⟨hs, ht⟩

theorem plk_smul (a : L) (W : V5 L) :
    plk (a • W) = C a • plk W := by
  funext k
  fin_cases k <;> dsimp [plk] <;> simp [map_mul] <;> try ring

theorem plucker_smul_left (a : L) (u v : Fin 4 → L[X]) :
    plucker (C a • u) v = C a • plucker u v := by
  ext i j
  simp [plucker, Matrix.smul_vecMulVec, Matrix.smul_apply, smul_eq_mul, mul_sub]

theorem ruling_smul {x : DPoint L M1 M2 M3 δ} {T : V5 L} {V : L[X]} {a : L} (ha : a ≠ 0)
    (i j : Fin 4)
    (h : bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j -
        V * hodge (plucker (plk (pt x)) (plk T)) i j) :
    bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt (smulPt a ha x))) (plk T) * gram M1 M2 M3 δ) i j -
        V * hodge (plucker (plk (pt (smulPt a ha x))) (plk T)) i j := by
  have hpt : pt (smulPt a ha x) = a • pt x := pt_smulPt a ha x
  have hplk : plk (pt (smulPt a ha x)) = C a • plk (pt x) := by
    rw [hpt, plk_smul]
  have hplucker : plucker (plk (pt (smulPt a ha x))) (plk T) = C a • plucker (plk (pt x)) (plk T) := by
    rw [hplk, plucker_smul_left]
  have hhodge' : hodge (C a • plucker (plk (pt x)) (plk T)) = C a • hodge (plucker (plk (pt x)) (plk T)) := by
    rw [hodge_smul]
  rw [hplucker, hhodge']
  have h_expr : (gram M1 M2 M3 δ * (C a • plucker (plk (pt x)) (plk T)) * gram M1 M2 M3 δ) i j -
      V * ((C a • hodge (plucker (plk (pt x)) (plk T)))) i j =
      C a * ((gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j -
        V * hodge (plucker (plk (pt x)) (plk T)) i j) := by
    calc
      (gram M1 M2 M3 δ * (C a • plucker (plk (pt x)) (plk T)) * gram M1 M2 M3 δ) i j -
          V * ((C a • hodge (plucker (plk (pt x)) (plk T)))) i j
          = ((C a • (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ)) i j) -
              V * ((C a • hodge (plucker (plk (pt x)) (plk T)))) i j := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (C a * (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j) -
          V * (C a * hodge (plucker (plk (pt x)) (plk T)) i j) := by
        simp [Matrix.smul_apply, smul_eq_mul]
      _ = C a * (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j -
          C a * (V * hodge (plucker (plk (pt x)) (plk T)) i j) := by ring
      _ = C a * ((gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j -
          V * hodge (plucker (plk (pt x)) (plk T)) i j) := by ring
  rw [h_expr]
  exact Dvd.dvd.mul_left h (C a)

theorem unit_smul {x : DPoint L M1 M2 M3 δ} {T : V5 L} {a : L} (ha : a ≠ 0)
    (h : ∃ i j, ∃ w : L[X], bruinU M1 M2 M3 δ T ∣ w * hodge (plucker (plk (pt x)) (plk T)) i j - 1) :
    ∃ i j, ∃ w : L[X], bruinU M1 M2 M3 δ T ∣
      w * hodge (plucker (plk (pt (smulPt a ha x))) (plk T)) i j - 1 := by
  obtain ⟨i, j, w, hw⟩ := h
  have hpt : pt (smulPt a ha x) = a • pt x := pt_smulPt a ha x
  have hplk : plk (pt (smulPt a ha x)) = C a • plk (pt x) := by
    rw [hpt]
    exact plk_smul a (pt x)
  have hplucker : plucker (plk (pt (smulPt a ha x))) (plk T) = C a • plucker (plk (pt x)) (plk T) := by
    rw [hplk]
    exact plucker_smul_left a (plk (pt x)) (plk T)
  have hhodge : hodge (plucker (plk (pt (smulPt a ha x))) (plk T)) = C a • hodge (plucker (plk (pt x)) (plk T)) := by
    rw [hplucker]
    exact hodge_smul (C a) (plucker (plk (pt x)) (plk T))
  have h_entry : hodge (plucker (plk (pt (smulPt a ha x))) (plk T)) i j =
      C a * hodge (plucker (plk (pt x)) (plk T)) i j := by
    rw [hhodge, Matrix.smul_apply, smul_eq_mul]
  refine ⟨i, j, C a⁻¹ * w, ?_⟩
  rw [h_entry]
  have h_eq : (C a⁻¹ * w) * (C a * hodge (plucker (plk (pt x)) (plk T)) i j) - 1 =
      w * hodge (plucker (plk (pt x)) (plk T)) i j - 1 := by
    calc
      (C a⁻¹ * w) * (C a * hodge (plucker (plk (pt x)) (plk T)) i j) - 1
          = (C a⁻¹ * C a) * (w * hodge (plucker (plk (pt x)) (plk T)) i j) - 1 := by ring
      _ = C (a⁻¹ * a) * (w * hodge (plucker (plk (pt x)) (plk T)) i j) - 1 := by rw [← C_mul]
      _ = C 1 * (w * hodge (plucker (plk (pt x)) (plk T)) i j) - 1 := by rw [inv_mul_cancel₀ ha]
      _ = w * hodge (plucker (plk (pt x)) (plk T)) i j - 1 := by simp
  rw [h_eq]
  exact hw

/-- A certificate at `x` is a certificate at `(a p, a r, a s)`, with the same `T` and `V`. -/
noncomputable def Cert.smul {f : L[X]} {x : DPoint L M1 M2 M3 δ} (c : Cert M1 M2 M3 δ f x) (a : L)
    (ha : a ≠ 0) : Cert M1 M2 M3 δ f (smulPt a ha x) where
  T := c.T
  tangent i := by
    rw [pt_smulPt, polarD_comm, polarD_smul, polarD_comm, c.tangent i, mul_zero]
  rank := by rw [pt_smulPt]; exact rank_smul a ha c.rank
  indep := by rw [pt_smulPt]; exact indep_smul ha c.indep
  a3_ne := c.a3_ne
  V := c.V
  degree_V := c.degree_V
  ruling i j := ruling_smul ha i j (c.ruling i j)
  unit := unit_smul ha c.unit
  sq := c.sq

theorem Cert.cls_smul {f : L[X]} [GoodSextic f] {x : DPoint L M1 M2 M3 δ} (c : Cert M1 M2 M3 δ f x)
    (a : L) (ha : a ≠ 0) : (c.smul a ha).cls = c.cls := rfl

/-- **`bruinPhi` does not see the rescaling.** -/
theorem bruinPhi_smul {f : L[X]} [GoodSextic f] (a : L) (ha : a ≠ 0) (x : DPoint L M1 M2 M3 δ) :
    bruinPhi M1 M2 M3 δ f (smulPt a ha x) = bruinPhi M1 M2 M3 δ f x := by
  rcases isEmpty_or_nonempty (Cert M1 M2 M3 δ f x) with hx | ⟨c⟩
  · have hx' : IsEmpty (Cert M1 M2 M3 δ f (smulPt a ha x)) := by
      refine ⟨fun c' => ?_⟩
      have h := Cert.smul c' a⁻¹ (inv_ne_zero ha)
      rw [smulPt_inv_smulPt a ha x] at h
      exact hx.elim h
    rw [bruinPhi_of_not hx, bruinPhi_of_not hx']
  · rw [bruinPhi_eq_of_cert (Cert.smul c.some a ha), bruinPhi_eq_of_cert c.some,
      ← Cert.cls_smul c.some a ha]

theorem phiRev_smul {f : L[X]} [GoodSextic f] (a : L) (ha : a ≠ 0) (x : DPoint L M1 M2 M3 δ) :
    phiRev M1 M2 M3 δ f (smulPt a ha x) = phiRev M1 M2 M3 δ f x := by
  unfold phiRev
  rw [swapPt_smulPt]
  exact bruinPhi_smul a ha (swapPt x)

end FurioLombardo.Discharge.M3a.AbelPrym
