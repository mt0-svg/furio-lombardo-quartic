import Mathlib
import FurioLombardo.Discharge.M3a.CertMap
import FurioLombardo.Discharge.M3a.Assembly
import FurioLombardo.Discharge.M4Box.DiscRoot
import FurioLombardo.Discharge.Analytic.Saturation
import FurioLombardo.M4.Instances

/-!
# `lamD` at the known lifts (lane lean-m4box, `hKn`)

The centre `Xi` of a tail box of disc `d` is the parameter of the image of a known lift `x_i`:
`pKv d Xi` is the image of `x_i.p` (the root `discY d Xi` is `0`). The point of `D_δ(K_v)` over it
on the branch of the box is then the image of `x_i` or of its inverse (`lamD_mem`), and `φ_v` at the
image of `x_i` is the image of `φ(x_i)` (`phiV_mapPt`, from the base change of Bruin's certificates).
So `lamD` at the centre is `± log φ(x_i) - log φ(x_a)`, which lies in `satOf Λ (log φ(x_a))
(log φ(x_b))` once both logarithms lie in `Λ` (`hKnown_0`, `hKnown_1`). No branch has to be
computed: both signs are in the saturation.
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.Analytic (satOf left_mem_satOf right_mem_satOf)
open FurioLombardo.Discharge.M3a (logPhi)
open FurioLombardo.Discharge.M3a.AbelPrym (mapPt phiRev_map)
open FurioLombardo.Discharge.M3a.Bruin (fRev Mmat δ phiK x0 x1 x2 x3 goodSextic_fRev_Kv phiRev_eq_cls)

namespace FurioLombardo.Discharge.M4Box

attribute [local instance] goodSextic_fRev_Kv

/-! ## `φ_v` and `lamPt` at the image of a point of `D_δ(K21)` -/

theorem mapσ_eq_mapPt {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {d : K21} (x : DPoint K21 M1 M2 M3 d) :
    DPoint.mapσ x = mapPt σ x := rfl

/-- **`φ_v` at the image of `x` is the image of `φ(x)`.** -/
theorem phiV_mapPt (k : Fin 2) (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    phiV k (mapPt σ x) = jacMap σ (fRev k) (phiK k x) := by
  obtain ⟨c, -⟩ := phiRev_eq_cls k x
  exact phiRev_map σ c

theorem lamPt_mapPt (k : Fin 2) (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    lamPt k (mapPt σ x) =
      logPhi σ (fRev k) (phiK k) (lam k) x - logPhi σ (fRev k) (phiK k) (lam k) (xa k) := by
  unfold lamPt
  rw [phiV_mapPt, map_sub]

theorem lamPt_mapPt_inv (k : Fin 2) (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) :
    lamPt k (mapPt σ x).inv =
      -logPhi σ (fRev k) (phiK k) (lam k) x - logPhi σ (fRev k) (phiK k) (lam k) (xa k) := by
  unfold lamPt
  dsimp [phiV]
  have h := FurioLombardo.Discharge.M3a.AbelPrym.phiRev_inv (x := mapPt σ x) (f := (fRev k).map σ)
  have h2 := phiV_mapPt (k := k) (x := x)
  dsimp [phiV] at h2
  rw [h, h2, ofMul_inv, map_sub, map_neg]

/-- **`lamD` over the image of `x`**: the point on the branch is the image of `x` or of `x.inv`. -/
theorem lamD_mem (k : Fin 2) {S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {d : ℕ} {X : ℤ_[2]}
    (x : DPoint K21 (Mmat 0) (Mmat 1) (Mmat 2) (δ k)) (hp : pKv d X = (mapPt σ x).p)
    (h1 : lamPt k (mapPt σ x) ∈ S) (h2 : lamPt k (mapPt σ x).inv ∈ S) : lamD k d X ∈ S := by
  unfold lamD
  split
  · exact S.zero_mem
  · rename_i e
    split_ifs with h
    · set y := h.choose with hy_def
      have hy_spec := h.choose_spec
      have hy_p : y.p = pKv d X := hy_spec.1
      have hy_p' : y.p = (mapPt σ x).p := hy_p.trans hp
      have h_cases := eq_or_eq_neg_of_p_eq (σδ_ne_zero k)
        FurioLombardo.Discharge.M3a.Bruin.two_ne_zero_Kv y (mapPt σ x) hy_p'
      rcases h_cases with (⟨hr, hs⟩ | ⟨hr, hs⟩)
      · have hy_eq : y = mapPt σ x := DPoint.ext' hy_p' hr hs
        rw [hy_eq]
        exact h1
      · have hy_eq : y = (mapPt σ x).inv :=
          DPoint.ext' (y := (mapPt σ x).inv) hy_p' hr hs
        rw [hy_eq]
        exact h2
    · exact S.zero_mem

/-! ## The centres of the tail boxes -/

theorem discY_eq_zero {d : ℕ} (hd : IsDisc d) {X : ℤ_[2]} (h : G1 d X 0 = 0) : discY d X = 0 :=
  ((discY_spec hd X).2 0 ((G1_eq_zero_iff hd X 0).mpr h)).symm

theorem discY_x0 : discY 1 ((0 : ℤ) : ℤ_[2]) = 0 := by
  apply discY_eq_zero
  · unfold IsDisc; simp
  · unfold G1; norm_num

theorem pKv_x0 : pKv 1 ((0 : ℤ) : ℤ_[2]) = (mapPt σ x0).p := by
  unfold pKv
  rw [discY_x0]
  unfold mapPt
  ext i
  fin_cases i <;> simp [discPt, x0, map_one]

theorem discY_x2 : discY 1 ((1 : ℤ) : ℤ_[2]) = 0 := by
  apply discY_eq_zero
  · unfold IsDisc; simp
  · unfold G1; norm_num

theorem pKv_x2 : pKv 1 ((1 : ℤ) : ℤ_[2]) = (mapPt σ x2).p := by
  unfold pKv
  rw [discY_x2]
  unfold mapPt
  ext i
  fin_cases i <;> simp [discPt, x2, map_one, map_ofNat]

theorem discY_x1 : discY 3 ((0 : ℤ) : ℤ_[2]) = 0 := by
  apply discY_eq_zero
  · unfold IsDisc; simp
  · unfold G1; norm_num

theorem pKv_x1 : pKv 3 ((0 : ℤ) : ℤ_[2]) = (mapPt σ x1).p := by
  unfold pKv
  rw [discY_x1]
  unfold mapPt
  ext i
  fin_cases i <;> simp [discPt, x1, map_one]

theorem discY_x3 : discY 2 ((-1 : ℤ) : ℤ_[2]) = 0 := by
  apply discY_eq_zero
  · unfold IsDisc; simp
  · unfold G1; norm_num

theorem pKv_x3 : pKv 2 ((-1 : ℤ) : ℤ_[2]) = (mapPt σ x3).p := by
  unfold pKv
  rw [discY_x3]
  unfold mapPt
  ext i
  fin_cases i <;> simp [discPt, x3, map_one, map_ofNat]
  norm_num

/-! ## `HKnown` for the two twists -/

/-- **`HKnown` for the twist `δ0`** (tails at `x2` and `x0`). -/
theorem hKnown_0 (Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2]))
    (ha : logPhi σ (fRev 0) (phiK 0) (lam 0) x0 ∈ Λ) (hb : logPhi σ (fRev 0) (phiK 0) (lam 0) x2 ∈ Λ) :
    FurioLombardo.M4.HKnown FurioLombardo.M4.T0.data
      (satOf Λ (logPhi σ (fRev 0) (phiK 0) (lam 0) x0) (logPhi σ (fRev 0) (phiK 0) (lam 0) x2))
      (lamD 0) := by
  have hA := left_mem_satOf (logPhi σ (fRev 0) (phiK 0) (lam 0) x2) ha
  have hB := right_mem_satOf (logPhi σ (fRev 0) (phiK 0) (lam 0) x0) hb
  intro t ht
  have ht' : t ∈ FurioLombardo.M4.T0.tails := ht
  simp only [FurioLombardo.M4.T0.tails, List.mem_cons, List.not_mem_nil, or_false] at ht'
  rcases ht' with rfl | rfl
  · exact lamD_mem 0 x2 pKv_x2 (by rw [lamPt_mapPt]; exact Submodule.sub_mem _ hB hA)
      (by rw [lamPt_mapPt_inv]; exact Submodule.sub_mem _ (Submodule.neg_mem _ hB) hA)
  · exact lamD_mem 0 x0 pKv_x0 (by rw [lamPt_mapPt]; exact Submodule.sub_mem _ hA hA)
      (by rw [lamPt_mapPt_inv]; exact Submodule.sub_mem _ (Submodule.neg_mem _ hA) hA)

/-- **`HKnown` for the twist `δ1`** (tails at `x1` and `x3`). -/
theorem hKnown_1 (Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2]))
    (ha : logPhi σ (fRev 1) (phiK 1) (lam 1) x1 ∈ Λ) (hb : logPhi σ (fRev 1) (phiK 1) (lam 1) x3 ∈ Λ) :
    FurioLombardo.M4.HKnown FurioLombardo.M4.T1.data
      (satOf Λ (logPhi σ (fRev 1) (phiK 1) (lam 1) x1) (logPhi σ (fRev 1) (phiK 1) (lam 1) x3))
      (lamD 1) := by
  have hA := left_mem_satOf (logPhi σ (fRev 1) (phiK 1) (lam 1) x3) ha
  have hB := right_mem_satOf (logPhi σ (fRev 1) (phiK 1) (lam 1) x1) hb
  intro t ht
  have ht' : t ∈ FurioLombardo.M4.T1.tails := ht
  simp only [FurioLombardo.M4.T1.tails, List.mem_cons, List.not_mem_nil, or_false] at ht'
  rcases ht' with rfl | rfl
  · exact lamD_mem 1 x1 pKv_x1 (by rw [lamPt_mapPt]; exact Submodule.sub_mem _ hA hA)
      (by rw [lamPt_mapPt_inv]; exact Submodule.sub_mem _ (Submodule.neg_mem _ hA) hA)
  · exact lamD_mem 1 x3 pKv_x3 (by rw [lamPt_mapPt]; exact Submodule.sub_mem _ hB hA)
      (by rw [lamPt_mapPt_inv]; exact Submodule.sub_mem _ (Submodule.neg_mem _ hB) hA)

end FurioLombardo.Discharge.M4Box
