import FurioLombardo.Discharge.SelmerSpan.ApproxT
import FurioLombardo.Discharge.SelmerSpan.DData
import FurioLombardo.Discharge.M3a.LocalLead

/-!
# The local divisors `D_1, ..., D_7` at `v` (lane SelmerSpan)

For each twist `k` and `i`, `Dpt k i` is the point `[⟨U, Y - V⟩]` of `Jac g`, `g = (fRev k)^σ`
(the reversed model of the M3a discharge over lane M4Cert's `K_v`), where

* `U = X² + σ(p) X + σ(r)` with `p = u1/u0`, `r = 1/u0 ∈ K21` exact: the reversal of the `u_i` of lane
  M4's basis (code/earlier-computations/local_images_twist<k>_e3.bin, generator
  code/local-group/local_divisors_data.gp);
* `V = b X + c` the square root of `g` modulo `U` (`Mumford.lean`, `sq_sub_eq`) built from two
  square roots in `K_v`: `n² = Z0² - p Z1 Z0 + r Z1²` and `a² = 2 Z0 - p Z1 + 2 n`, `Z1 X + Z0 = 4 (g mod U)`,
  each given by Hensel's lemma at a certificate (`exists_sqrt`); the certificates fix the signs so
  that `V` is the `v_i` of lane M4 (checked in PARI to `π^75` at least, `approx_n`, `approx_a`).

Main results: `muJ_Dpt`, the `x - T` image of `Dpt k i` is the class of `U(T)` in `H g`; `Dpt_mumford`,
the underlying class is the Mumford ideal of `(U, V)`. Every kernel condition is one
`decide +kernel` (`dOK`, `fOK`).
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin

namespace FurioLombardo.Discharge.SelmerSpan

attribute [local instance] goodSextic_fRev_Kv

/-! ## Data accessors -/

def pLi (k i : ℕ) : List ℤ := (pData.getD k []).getD i []
def rLi (k i : ℕ) : List ℤ := (rData.getD k []).getD i []
def pMi (k i : ℕ) : ℕ := (pDen.getD k []).getD i 1
def rMi (k i : ℕ) : ℕ := (rDen.getD k []).getD i 1
def pJ (k i : ℕ) : ℕ := ((pJO.getD k []).getD i []).getD 0 0
def pO (k i : ℕ) : ℕ := ((pJO.getD k []).getD i []).getD 1 1
def rJ (k i : ℕ) : ℕ := ((rJO.getD k []).getD i []).getD 0 0
def rO (k i : ℕ) : ℕ := ((rJO.getD k []).getD i []).getD 1 1
def pOI (k i : ℕ) : ℤ := (pOi.getD k []).getD i 1
def rOI (k i : ℕ) : ℤ := (rOi.getD k []).getD i 1

/-- The Hensel data `(b1, s1, b2, s2)`. -/
def hensD (k i : ℕ) : T3 × ℕ × T3 × ℕ := (hens.getD k []).getD i ((0, 0, 0), 0, (0, 0, 0), 0)
def hb1 (k i : ℕ) : T3 := (hensD k i).1
def hs1 (k i : ℕ) : ℕ := (hensD k i).2.1
def hb2 (k i : ℕ) : T3 := (hensD k i).2.2.1
def hs2 (k i : ℕ) : ℕ := (hensD k i).2.2.2

/-- Precision of the first square root. -/
def P1 (k i : ℕ) : ℕ := Pv - (hs1 k i + 2)

/-- Precision of the second square root. -/
def P2 (k i : ℕ) : ℕ := P1 k i - (hs2 k i + 2)

/-- zk coordinates of `4 fRev_j` (lane M3a discharge's `FnData`, reversed). -/
def FL (k j : ℕ) : List ℤ := (FnData.getD k []).getD (6 - j) []

/-! ## Global elements -/

/-- `p = u1 / u0`. -/
noncomputable def pG (k i : ℕ) : K21 := ((pMi k i : ℕ) : K21)⁻¹ * zkE (pLi k i)

/-- `r = 1 / u0`. -/
noncomputable def rG (k i : ℕ) : K21 := ((rMi k i : ℕ) : K21)⁻¹ * zkE (rLi k i)

/-- `4 fRev_j`. -/
noncomputable def FG (k j : ℕ) : K21 := zkE (FL k j)

theorem fRev_coeff (k : Fin 2) {j : ℕ} (hj : j ≤ 6) : (fRev k).coeff j = (4 : K21)⁻¹ * FG k j := by
  rw [fRev, coeff_pQ]
  congr 1
  interval_cases j <;> rfl

/-! ## Residues and the kernel checks -/

def tp (k i : ℕ) : T3 := sQres (pLi k i) (pJ k i) (pOI k i) Pv
def tr (k i : ℕ) : T3 := sQres (rLi k i) (rJ k i) (rOI k i) Pv
def tF (k j : ℕ) : T3 := sQres (FL k j) 0 1 Pv

def tZ1 (k i : ℕ) : T3 :=
  divR1T Pv (tp k i) (tr k i) (tF k 1) (tF k 2) (tF k 3) (tF k 4) (tF k 5) (tF k 6)

def tZ0 (k i : ℕ) : T3 :=
  divR0T Pv (tp k i) (tr k i) (tF k 0) (tF k 2) (tF k 3) (tF k 4) (tF k 5) (tF k 6)

def tN (k i : ℕ) : T3 := nTT Pv (tp k i) (tr k i) (tZ1 k i) (tZ0 k i)

def tA (k i : ℕ) : T3 := aTT (P1 k i) (tp k i) (tZ1 k i) (tZ0 k i) (hb1 k i)

/-- The kernel conditions for `D_i`: the atoms `p`, `r`, the two Hensel certificates, `N ≠ 0`,
`a ≠ 0`. -/
def DOK (k i : ℕ) : Prop :=
  SQok (pLi k i) (pMi k i) (pJ k i) (pO k i) (pOI k i) Pv ∧
  SQok (rLi k i) (rMi k i) (rJ k i) (rO k i) (rOI k i) Pv ∧
  modT (mulZ (hb1 k i) (hb1 k i)) Pv = modT (tN k i) Pv ∧ LowOK (hb1 k i) (hs1 k i) ∧
  2 * hs1 k i + 4 ≤ Pv ∧ modT (tN k i) Pv ≠ modT (0, 0, 0) Pv ∧
  modT (mulZ (hb2 k i) (hb2 k i)) (P1 k i) = modT (tA k i) (P1 k i) ∧ LowOK (hb2 k i) (hs2 k i) ∧
  2 * hs2 k i + 4 ≤ P1 k i ∧ modT (hb2 k i) (P2 k i) ≠ modT (0, 0, 0) (P2 k i)

instance (k i : ℕ) : Decidable (DOK k i) := by unfold DOK; infer_instance

/-- The atoms `4 fRev_j`. -/
def FOK (k : ℕ) : Prop := ∀ j : Fin 7, SQok (FL k j) 1 0 1 1 Pv

instance (k : ℕ) : Decidable (FOK k) := by unfold FOK; infer_instance

theorem fOK : ∀ k : Fin 2, FOK k := by decide +kernel

theorem dOK : ∀ k : Fin 2, ∀ i : Fin 7, DOK k i := by decide +kernel

/-! ## Local elements -/

/-- `σ(4 fRev_j)`. -/
noncomputable def Fv (k j : ℕ) : Kv := σ (FG k j)

/-- `Z1 = 4 z1`, `z1 X + z0 = g mod U`. -/
noncomputable def Z1v (k i : ℕ) : Kv :=
  divR1 (σ (pG k i)) (σ (rG k i)) (Fv k 0) (Fv k 1) (Fv k 2) (Fv k 3) (Fv k 4) (Fv k 5) (Fv k 6)

/-- `Z0 = 4 z0`. -/
noncomputable def Z0v (k i : ℕ) : Kv :=
  divR0 (σ (pG k i)) (σ (rG k i)) (Fv k 0) (Fv k 1) (Fv k 2) (Fv k 3) (Fv k 4) (Fv k 5) (Fv k 6)

/-- `Z0² - p Z1 Z0 + r Z1² = 16 Res(U, z1 X + z0)`. -/
noncomputable def Nv (k i : ℕ) : Kv :=
  Z0v k i ^ 2 - σ (pG k i) * Z1v k i * Z0v k i + σ (rG k i) * Z1v k i ^ 2

theorem approx_p (k : Fin 2) (i : Fin 7) : Approx (σ (pG k i)) (tp k i) Pv :=
  approx_σ_atom (dOK k i).1

theorem approx_r (k : Fin 2) (i : Fin 7) : Approx (σ (rG k i)) (tr k i) Pv :=
  approx_σ_atom (dOK k i).2.1

theorem approx_F (k : Fin 2) (j : Fin 7) : Approx (Fv k j) (tF k j) Pv := by
  have h := approx_σ_atom (fOK k j)
  rw [show Fv k j = σ (((1 : ℕ) : K21)⁻¹ * zkE (FL k j)) by simp [Fv, FG]]
  exact h

theorem approx_Z1 (k : Fin 2) (i : Fin 7) : Approx (Z1v k i) (tZ1 k i) Pv :=
  approx_divR1 (approx_p k i) (approx_r k i) (approx_F k 1) (approx_F k 2) (approx_F k 3)
    (approx_F k 4) (approx_F k 5) (approx_F k 6)

theorem approx_Z0 (k : Fin 2) (i : Fin 7) : Approx (Z0v k i) (tZ0 k i) Pv :=
  approx_divR0 (approx_p k i) (approx_r k i) (approx_F k 0) (approx_F k 2) (approx_F k 3)
    (approx_F k 4) (approx_F k 5) (approx_F k 6)

theorem approx_N (k : Fin 2) (i : Fin 7) : Approx (Nv k i) (tN k i) Pv :=
  approx_nTT (approx_p k i) (approx_r k i) (approx_Z1 k i) (approx_Z0 k i)

theorem Nv_ne_zero (k : Fin 2) (i : Fin 7) : Nv k i ≠ 0 :=
  ne_zero_of_approx (approx_N k i) (dOK k i).2.2.2.2.2.1

theorem exists_n (k : Fin 2) (i : Fin 7) : ∃ n : Kv, n ^ 2 = Nv k i ∧ Approx n (hb1 k i) (P1 k i) :=
  exists_sqrt (approx_N k i) (dOK k i).2.2.1 (dOK k i).2.2.2.1 (dOK k i).2.2.2.2.1

/-- The square root `n` of `Nv` (sign fixed by the certificate). -/
noncomputable def nv (k : Fin 2) (i : Fin 7) : Kv := (exists_n k i).choose

theorem nv_sq (k : Fin 2) (i : Fin 7) : nv k i ^ 2 = Nv k i := (exists_n k i).choose_spec.1

theorem approx_n (k : Fin 2) (i : Fin 7) : Approx (nv k i) (hb1 k i) (P1 k i) :=
  (exists_n k i).choose_spec.2

theorem P1_le (k i : ℕ) : P1 k i ≤ Pv := Nat.sub_le _ _

theorem exists_a (k : Fin 2) (i : Fin 7) :
    ∃ a : Kv, a ^ 2 = 2 * Z0v k i - σ (pG k i) * Z1v k i + 2 * nv k i ∧
      Approx a (hb2 k i) (P2 k i) :=
  exists_sqrt (approx_aTT ((approx_p k i).mono (P1_le k i)) ((approx_Z1 k i).mono (P1_le k i))
      ((approx_Z0 k i).mono (P1_le k i)) (approx_n k i))
    (dOK k i).2.2.2.2.2.2.1 (dOK k i).2.2.2.2.2.2.2.1 (dOK k i).2.2.2.2.2.2.2.2.1

/-- The second square root `a` (sign fixed by the certificate). -/
noncomputable def av (k : Fin 2) (i : Fin 7) : Kv := (exists_a k i).choose

theorem av_sq (k : Fin 2) (i : Fin 7) :
    av k i ^ 2 = 2 * Z0v k i - σ (pG k i) * Z1v k i + 2 * nv k i := (exists_a k i).choose_spec.1

theorem approx_a (k : Fin 2) (i : Fin 7) : Approx (av k i) (hb2 k i) (P2 k i) :=
  (exists_a k i).choose_spec.2

theorem av_ne_zero (k : Fin 2) (i : Fin 7) : av k i ≠ 0 :=
  ne_zero_of_approx (approx_a k i) (dOK k i).2.2.2.2.2.2.2.2.2

/-! ## The Mumford data -/

/-- `U = X² + σ(p) X + σ(r)`. -/
noncomputable def Uv (k : Fin 2) (i : Fin 7) : Kv[X] := quad (σ (pG k i)) (σ (rG k i))

/-- `V = b X + c`. -/
noncomputable def Vv (k : Fin 2) (i : Fin 7) : Kv[X] :=
  C (sqB (Z1v k i) (av k i)) * X + C (sqC (σ (pG k i)) (Z1v k i) (av k i))

/-- The quotient of `g` by `U`. -/
noncomputable def Qv (k : Fin 2) (i : Fin 7) : Kv[X] :=
  divQ (σ (pG k i)) (σ (rG k i)) (Fv k 0 / 4) (Fv k 1 / 4) (Fv k 2 / 4) (Fv k 3 / 4) (Fv k 4 / 4)
    (Fv k 5 / 4) (Fv k 6 / 4)

/-- `W = (V² - g) / U`. -/
noncomputable def Wv (k : Fin 2) (i : Fin 7) : Kv[X] := C (sqB (Z1v k i) (av k i) ^ 2) - Qv k i

theorem four_ne_zero_Kv : (4 : Kv) ≠ 0 := by
  have h := two_ne_zero_Kv
  have : (4 : Kv) = 2 * 2 := by norm_num
  rw [this]; exact mul_ne_zero h h

theorem g_coeff (k : Fin 2) {j : ℕ} (hj : j ≤ 6) : ((fRev k).map σ).coeff j = Fv k j / 4 := by
  rw [coeff_map, fRev_coeff k hj, map_mul, map_inv₀, map_ofNat, Fv, div_eq_inv_mul]

theorem g_eq (k : Fin 2) :
    (fRev k).map σ = C (Fv k 6 / 4) * X ^ 6 + C (Fv k 5 / 4) * X ^ 5 + C (Fv k 4 / 4) * X ^ 4 +
      C (Fv k 3 / 4) * X ^ 3 + C (Fv k 2 / 4) * X ^ 2 + C (Fv k 1 / 4) * X + C (Fv k 0 / 4) := by
  have hdeg : ((fRev k).map σ).natDegree ≤ 6 := (GoodSextic.natDegree_eq (f := (fRev k).map σ)).le
  conv_lhs => rw [eq_sextic_of_natDegree_le hdeg]
  rw [g_coeff k (by norm_num), g_coeff k (by norm_num), g_coeff k (by norm_num),
    g_coeff k (by norm_num), g_coeff k (by norm_num), g_coeff k (by norm_num),
    g_coeff k (by norm_num)]

theorem divR1_quarter (p r g0 g1 g2 g3 g4 g5 g6 : Kv) :
    divR1 p r (g0 / 4) (g1 / 4) (g2 / 4) (g3 / 4) (g4 / 4) (g5 / 4) (g6 / 4) =
      divR1 p r g0 g1 g2 g3 g4 g5 g6 / 4 := by
  simp only [divR1, divW]; ring

theorem divR0_quarter (p r g0 g1 g2 g3 g4 g5 g6 : Kv) :
    divR0 p r (g0 / 4) (g1 / 4) (g2 / 4) (g3 / 4) (g4 / 4) (g5 / 4) (g6 / 4) =
      divR0 p r g0 g1 g2 g3 g4 g5 g6 / 4 := by
  simp only [divR0, divW]; ring

/-- `g = U Q + (Z1/4) X + Z0/4`. -/
theorem g_div (k : Fin 2) (i : Fin 7) :
    (fRev k).map σ = Uv k i * Qv k i + (C (Z1v k i / 4) * X + C (Z0v k i / 4)) := by
  rw [g_eq k, sextic_eq (σ (pG k i)) (σ (rG k i)), divR1_quarter, divR0_quarter]
  rfl

/-- **`V² - g = U W`.** -/
theorem hw (k : Fin 2) (i : Fin 7) : Vv k i ^ 2 - (fRev k).map σ = Uv k i * Wv k i := by
  have hs := sq_sub_eq (r := σ (rG k i)) two_ne_zero_Kv (nv_sq k i) (av_sq k i) (av_ne_zero k i)
  have hg := g_div k i
  calc Vv k i ^ 2 - (fRev k).map σ
      = (Vv k i ^ 2 - (C (Z1v k i / 4) * X + C (Z0v k i / 4))) - Uv k i * Qv k i := by
        rw [hg]; ring
    _ = Uv k i * Wv k i := by
        rw [Vv, hs, Wv, Uv]; ring

/-- `U` is coprime to `g`. -/
theorem isCoprime_U (k : Fin 2) (i : Fin 7) : IsCoprime (Uv k i) ((fRev k).map σ) := by
  have hρ : (Z0v k i / 4) ^ 2 - σ (pG k i) * (Z1v k i / 4) * (Z0v k i / 4) +
      σ (rG k i) * (Z1v k i / 4) ^ 2 ≠ 0 := by
    have e : (Z0v k i / 4) ^ 2 - σ (pG k i) * (Z1v k i / 4) * (Z0v k i / 4) +
        σ (rG k i) * (Z1v k i / 4) ^ 2 = Nv k i * (4⁻¹) ^ 2 := by
      rw [Nv]; ring
    rw [e]
    exact mul_ne_zero (Nv_ne_zero k i) (pow_ne_zero 2 (inv_ne_zero four_ne_zero_Kv))
  have h := isCoprime_quad_lin hρ
  rw [g_div k i]
  have h' : IsCoprime (Uv k i) (C (Z1v k i / 4) * X + C (Z0v k i / 4) + Uv k i * Qv k i) :=
    IsCoprime.add_mul_left_right h (Qv k i)
  rw [add_comm]
  exact h'

/-! ## The points -/

/-- **The local divisor `D_(i+1)` of twist `k` as a point of `A(K_v) = Jac g`.** -/
noncomputable def Dpt (k : Fin 2) (i : Fin 7) : Additive (Jac ((fRev k).map σ)) :=
  Additive.ofMul (mumfordJac ((fRev k).map σ) (quad_monic _ _) (quad_even _ _) (hw k i)
    (exists_coprime_of_squarefree GoodSextic.squarefree (hw k i)))

/-- The class underlying `Dpt k i` is the Mumford ideal `⟨U, Y - V⟩`. -/
theorem Dpt_mumford (k : Fin 2) (i : Fin 7) :
    ((Additive.toMul (Dpt k i) : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) =
      ClassGroup.mk0 (mumford0 ((fRev k).map σ) (quad_monic (σ (pG k i)) (σ (rG k i))).ne_zero
        (Vv k i)) := rfl

/-- `U(T)` is a unit of `K_v[T]/(g)`. -/
theorem isUnit_U (k : Fin 2) (i : Fin 7) : IsUnit (AdjoinRoot.mk ((fRev k).map σ) (Uv k i)) :=
  isUnit_mk_of_isCoprime (isCoprime_U k i)

/-- **`μ_v(D_i) = [U_i(T)]`.** -/
theorem muJ_Dpt (k : Fin 2) (i : Fin 7) :
    muJ ((fRev k).map σ) (Additive.toMul (Dpt k i)) =
      (QuotientGroup.mk (isUnit_U k i).unit : H ((fRev k).map σ)) :=
  muJ_mumfordJac _ (quad_monic _ _) (quad_even _ _) (hw k i)
    (exists_coprime_of_squarefree GoodSextic.squarefree (hw k i)) (isCoprime_U k i)

end FurioLombardo.Discharge.SelmerSpan
