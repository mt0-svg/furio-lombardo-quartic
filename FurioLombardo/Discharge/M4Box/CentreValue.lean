import Mathlib
import FurioLombardo.Discharge.M4Box.PtValue
import FurioLombardo.Discharge.M4Box.AbelPrymSpec
import FurioLombardo.Discharge.M4Box.AbelPrymRel
import FurioLombardo.Discharge.M4Box.DiscRoot
import FurioLombardo.Discharge.M4Cert.Bridge

/-!
# The values of `lamD` at the centres of the constant boxes (lane lean-m4box, `hCe`)

At the centre `c` of a constant box of disc `d`, `lamD k d c = lam (φ_v(x) - φ(x_a))` for the point `x`
of `D_δ(K_v)` over `pKv d c` on the branch of the box (`M4Log.lamD_eq`). The certificate:

* `apInBall`: balls of the input of the Abel-Prym program at `x`, from the root `Y ≡ Y0 mod 2^N` of
  `G1 d c Y = 0` (an integer check), the square root of `Q1/δ` (or `Q3/δ`) near the reference root of the
  box, and `x.s = Q2 / (δ x.r)` (or `x.r = Q2 / (δ x.s)`); `exists_of_apInBall` gives the point `x`, on
  the branch, with its input in the balls;
* the ball run of `apPhi` and `rel_apPhi`, `phiV_eq_cls` (the exact run gives the pair of `φ_v(x)`);
* the chain and `finalOK` of `lamK_of_cert` against `c.y + la`, the ball of `lam φ(x_a)` from `hBP`
  (`la`, `qa ≥ c.q`) giving the ball `c.y` of the difference (`hCentre_of_ok`).
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith
open FurioLombardo.Discharge.M3a.AbelPrym (swapPt phiRev_eq_of_cert pencil)
open FurioLombardo.Discharge.M3a.Bruin (fRev Mmat δ QcL dL Mmat_symm phiK x0 x1)

namespace FurioLombardo.Discharge.M4Box

/-! ## The exact run at a point of `D_δ(K_v)` -/

/-- The input of the program for `phiV k x`: the swapped forms at `(p, s, r)`. -/
noncomputable def apInV (k : Fin 2) (x : DPtKv k) : APIn Kv :=
  APIn.ofPoint ((Mmat 2).map σ) ((Mmat 1).map σ) ((Mmat 0).map σ) (σ (δ k)) (swapPt x)

theorem Mmat_map_symm (i : Fin 3) : ((Mmat i).map σ)ᵀ = (Mmat i).map σ := by
  rw [← Matrix.transpose_map, Mmat_symm]

theorem fRev_map_det (k : Fin 2) :
    (fRev k).map σ =
      -C (σ (δ k)) * (pencil ((Mmat 2).map σ) ((Mmat 1).map σ) ((Mmat 0).map σ)).det := by
  rw [FurioLombardo.Discharge.M3a.Bruin.fRev_eq_det_swap k]
  simp only [Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_C]
  have h := RingHom.map_det (Polynomial.mapRingHom σ) (pencil (Mmat 2) (Mmat 1) (Mmat 0))
  calc
    -C (σ (δ k)) * map σ (pencil (Mmat 2) (Mmat 1) (Mmat 0)).det
        = -C (σ (δ k)) * ((Polynomial.mapRingHom σ) ((pencil (Mmat 2) (Mmat 1) (Mmat 0)).det)) := rfl
    _ = -C (σ (δ k)) * (((Polynomial.mapRingHom σ).mapMatrix (pencil (Mmat 2) (Mmat 1) (Mmat 0))).det) := by
      rw [h]
    _ = -C (σ (δ k)) * (pencil ((Mmat 2).map σ) ((Mmat 1).map σ) ((Mmat 0).map σ)).det := by
      have hmatrix : (Polynomial.mapRingHom σ).mapMatrix (pencil (Mmat 2) (Mmat 1) (Mmat 0)) =
          pencil ((Mmat 2).map σ) ((Mmat 1).map σ) ((Mmat 0).map σ) := by
        refine Matrix.ext fun a b => ?_
        rw [RingHom.mapMatrix_apply, Matrix.map_apply]
        simp [Polynomial.mapRingHom, pencil, Matrix.of_apply, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      rw [hmatrix]

/-- **The exact run gives the pair of `φ_v(x)`.** -/
theorem phiV_eq_cls (k : Fin 2) (x : DPtKv k) {prm : APPrm} {m : Mum Kv}
    (h : apPhi (fieldOps Kv) prm (apInV k x) = some m) :
    m.OnCurve ((fRev k).map σ) ∧
      m.cls ((fRev k).map σ) = ((phiV k x : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) := by
  obtain ⟨c, hU, hV⟩ := apPhi_cert (Mmat_map_symm 2) (Mmat_map_symm 1) (Mmat_map_symm 0)
    FurioLombardo.Discharge.M3a.Bruin.two_ne_zero_Kv (σδ_ne_zero k) (fRev_map_det k) (swapPt x) h
  refine ⟨?_, ?_⟩
  · have hs := c.sq
    rw [hU, hV] at hs
    rw [Mum.OnCurve, ← dvd_neg, neg_sub]
    exact hs
  · have e : phiV k x = c.cls := phiRev_eq_of_cert c
    rw [e, FurioLombardo.Discharge.M3a.AbelPrym.Cert.coe_cls]
    exact mk0_mumford_eq _ _ hU.symm hV.symm

/-- **The certificate of `lamK (φ_v(x))`** from balls of the input of the program at `x`. -/
theorem lamK_phiV_of_cert (kk : Fin 2) (x : DPtKv kk) {k : Ctx} (hk : k.Ok) {xb : APIn Ball}
    (hx : APIn.Rel (fun a b => Ball.Mem b a) (apInV kk x) xb) {prm : APPrm} {mB : Mum Ball}
    (hphi : apPhi (ballOpsF k) prm xb = some mB)
    {F g : Sext Ball} {b : Ball} {E R : Mum Ball} {A : Mat2 Ball} {sB : N3} {eB J Dd : ℕ}
    {l : Fin 6 → ℤ} {q : ℕ}
    (hF : FvBall k kk = some F) (hg : gBall k F = some g) (hb : bKBall k kk g sB eB = some b)
    (hE : E0Ball k kk g b = some E) (hA : AmatBall k kk g b = some A)
    (hR : drun (ballOpsF k) g mB E (chainSteps J) mB = some R)
    (hfin : finalOK k A b kk (IntModelKv.aa kk) (M0 kk) R J Dd l q = true) (j : Fin 2) :
    ‖lamK kk (Additive.ofMul (phiV kk x)) j‖ ≤ 1 ∧
      ‖lamK kk (Additive.ofMul (phiV kk x)) j - evZ (lTriple l j)‖ ≤ ‖pv‖ ^ (3 * q) := by
  obtain ⟨m, hm, hmB⟩ := rel_apPhi (rel_ballOpsF hk) prm hx mB hphi
  obtain ⟨hon, hcls⟩ := phiV_eq_cls kk x hm
  exact lamK_of_cert kk (X := Additive.ofMul (phiV kk x)) hon hcls hk hF hg hb hE hA hmB hR hfin j

/-! ## The balls of the input -/

theorem rel_discPtO {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop} (h : Ops.Rel o p R)
    (d : ℕ) {X Y : A} {X' Y' : B} (hX : R X X') (hY : R Y Y') :
    Trip.Rel R (discPtO o d X Y) (discPtO p d X' Y') := by
  unfold discPtO
  split_ifs with h1 h2 h3 h4 h5
  · -- d = 1
    exact ⟨h.mul (h.ofInt 2) hX, h.mul (h.ofInt 2) hY, h.ofInt 1⟩
  · -- d = 2
    exact ⟨h.add (h.ofInt 1) (h.mul (h.ofInt 2) hX), h.mul (h.ofInt 2) hY, h.ofInt 1⟩
  · -- d = 3
    exact ⟨h.add (h.ofInt 1) (h.mul (h.ofInt 2) hX), h.add (h.ofInt 1) (h.mul (h.ofInt 2) hY), h.ofInt 1⟩
  · -- d = 4
    exact ⟨h.mul (h.ofInt 2) hX, h.ofInt 1, h.mul (h.ofInt 2) hY⟩
  · -- d = 5
    exact ⟨h.add (h.ofInt 1) (h.mul (h.ofInt 2) hX), h.ofInt 1, h.mul (h.ofInt 2) hY⟩
  · -- d ∉ {1,2,3,4,5}
    exact ⟨h.ofInt 0, h.ofInt 0, h.ofInt 0⟩

theorem discPtO_field (d : ℕ) (X Y : Kv) :
    discPtO (fieldOps Kv) d X Y = (discPt d X Y 0, discPt d X Y 1, discPt d X Y 2) := by
  unfold discPtO discPt
  split_ifs <;> simp [fieldOps]

theorem mem_mBall {k : Ctx} (hk : k.Ok) (i : Fin 3) {m : Sym3 Ball} (h : mBall k i = some m) :
    Sym3.Rel (fun a b => Ball.Mem b a) (Sym3.ofMatrix ((Mmat i).map σ)) m := by
  -- Extract the six sigQ equalities from h
  have h_sigQ : (sigQ k (QcL i 0) 1 = some m.a00) ∧
      (sigQ k (QcL i 1) 2 = some m.a01) ∧
      (sigQ k (QcL i 2) 2 = some m.a02) ∧
      (sigQ k (QcL i 3) 1 = some m.a11) ∧
      (sigQ k (QcL i 4) 2 = some m.a12) ∧
      (sigQ k (QcL i 5) 1 = some m.a22) := by
    -- Expand mBall at h
    simp [mBall] at h
    -- Peel the six binds
    rcases Option.bind_eq_some_iff.mp h with ⟨a00, h00, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨a01, h01, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨a02, h02, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨a11, h11, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨a12, h12, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨a22, h22, h⟩
    -- Now h : pure ⟨a00, a01, a02, a11, a12, a22⟩ = some m
    -- So ⟨a00, ..., a22⟩ = m
    obtain rfl := Option.some_inj.mp h
    exact ⟨h00, h01, h02, h11, h12, h22⟩
  rcases h_sigQ with ⟨h00, h01, h02, h11, h12, h22⟩
  -- Apply mem_sigQ to each
  have hm00 := mem_sigQ hk h00
  have hm01 := mem_sigQ hk h01
  have hm02 := mem_sigQ hk h02
  have hm11 := mem_sigQ hk h11
  have hm12 := mem_sigQ hk h12
  have hm22 := mem_sigQ hk h22
  -- Now we need to match the goal entries with hm00..hm22
  -- The goal is Sym3.Rel (fun a b => Ball.Mem b a) (Sym3.ofMatrix ((Mmat i).map σ)) m
  -- which expands to six Ball.Mem statements
  -- hm00 : m.a00.Mem (σ ((1 : K21)⁻¹ * zkE (QcL i 0)))
  -- Goal component 1: Ball.Mem m.a00 (σ (Mmat i 0 0))
  -- We show these are equal by expanding definitions
  have h00' : Ball.Mem m.a00 (σ (Mmat i 0 0)) := by
    simpa [Mmat, FurioLombardo.Discharge.M3a.Bruin.Qc] using hm00
  have h01' : Ball.Mem m.a01 (σ (Mmat i 0 1)) := by
    simpa [Mmat, FurioLombardo.Discharge.M3a.Bruin.Qc, div_eq_mul_inv, mul_comm] using hm01
  have h02' : Ball.Mem m.a02 (σ (Mmat i 0 2)) := by
    simpa [Mmat, FurioLombardo.Discharge.M3a.Bruin.Qc, div_eq_mul_inv, mul_comm] using hm02
  have h11' : Ball.Mem m.a11 (σ (Mmat i 1 1)) := by
    simpa [Mmat, FurioLombardo.Discharge.M3a.Bruin.Qc] using hm11
  have h12' : Ball.Mem m.a12 (σ (Mmat i 1 2)) := by
    simpa [Mmat, FurioLombardo.Discharge.M3a.Bruin.Qc, div_eq_mul_inv, mul_comm] using hm12
  have h22' : Ball.Mem m.a22 (σ (Mmat i 2 2)) := by
    simpa [Mmat, FurioLombardo.Discharge.M3a.Bruin.Qc] using hm22
  -- Now unfold Sym3.Rel and Sym3.ofMatrix to combine the six
  unfold Sym3.Rel Sym3.ofMatrix
  simp [Matrix.map_apply]
  exact ⟨h00', h01', h02', h11', h12', h22'⟩

/-- The root `discY d c` from an integer approximation. -/
theorem approx_discY {d : ℕ} (hd : IsDisc d) (c : ℕ) {Y0 : ℤ} {N : ℕ}
    (hY : (2 : ℤ) ^ N ∣ G1 d (c : ℤ) Y0) :
    Approx (toKv (discY d (c : ℤ_[2]))) (Y0, 0, 0) N := by
  have hdiscY_spec := (discY_spec hd (c : ℤ_[2])).1
  have hG1_zero : G1 d ((c : ℤ_[2])) (discY d ((c : ℤ_[2]))) = 0 := by
    rw [← (G1_eq_zero_iff hd ((c : ℤ_[2])) (discY d ((c : ℤ_[2])))).mp]
    simpa using hdiscY_spec
  have hG1_sub_eq : G1 d ((c : ℤ_[2])) (discY d ((c : ℤ_[2]))) - G1 d ((c : ℤ_[2])) ((Y0 : ℤ) : ℤ_[2]) =
      ((discY d ((c : ℤ_[2]))) - ((Y0 : ℤ) : ℤ_[2])) * Hd d ((c : ℤ_[2])) (discY d ((c : ℤ_[2]))) ((Y0 : ℤ) : ℤ_[2]) :=
    G1_sub hd ((c : ℤ_[2])) (discY d ((c : ℤ_[2]))) ((Y0 : ℤ) : ℤ_[2])
  rw [hG1_zero, zero_sub] at hG1_sub_eq
  have hunit : IsUnit (Hd d ((c : ℤ_[2])) (discY d ((c : ℤ_[2]))) ((Y0 : ℤ) : ℤ_[2])) :=
    isUnit_Hd hd ((c : ℤ_[2])) (discY d ((c : ℤ_[2]))) ((Y0 : ℤ) : ℤ_[2])
  have hY' : (2 : ℤ_[2]) ^ N ∣ ((G1 d (c : ℤ) Y0 : ℤ) : ℤ_[2]) := by
    rwa [two_pow_dvd_intCast_iff]
  have hG1_cast : ((G1 d (c : ℤ) Y0 : ℤ) : ℤ_[2]) = G1 d ((c : ℤ) : ℤ_[2]) ((Y0 : ℤ) : ℤ_[2]) :=
    map_G1 (Int.castRingHom ℤ_[2]) hd (c : ℤ) Y0
  have hY_cast : (2 : ℤ_[2]) ^ N ∣ G1 d ((c : ℤ) : ℤ_[2]) ((Y0 : ℤ) : ℤ_[2]) := by
    rwa [← hG1_cast]
  have hY_neg : (2 : ℤ_[2]) ^ N ∣ -(G1 d ((c : ℤ) : ℤ_[2]) ((Y0 : ℤ) : ℤ_[2])) :=
    (dvd_neg).mpr hY_cast
  have hY_discY : (2 : ℤ_[2]) ^ N ∣ (discY d ((c : ℤ) : ℤ_[2])) - ((Y0 : ℤ) : ℤ_[2]) := by
    have hG1_sub_eq' : -G1 d ((c : ℤ) : ℤ_[2]) ((Y0 : ℤ) : ℤ_[2]) =
        ((discY d ((c : ℤ) : ℤ_[2])) - ((Y0 : ℤ) : ℤ_[2])) * Hd d ((c : ℤ) : ℤ_[2]) (discY d ((c : ℤ) : ℤ_[2])) ((Y0 : ℤ) : ℤ_[2]) := by
      simpa using hG1_sub_eq
    have htemp : (2 : ℤ_[2]) ^ N ∣ ((discY d ((c : ℤ) : ℤ_[2])) - ((Y0 : ℤ) : ℤ_[2])) *
        Hd d ((c : ℤ) : ℤ_[2]) (discY d ((c : ℤ) : ℤ_[2])) ((Y0 : ℤ) : ℤ_[2]) := by
      rw [← hG1_sub_eq']
      simpa using hY_neg
    exact ((IsUnit.dvd_mul_right hunit).mp htemp)
  simpa [sub_eq_add_neg, add_comm, add_left_comm] using approx_toKv hY_discY

/-- The point `pKv d X` lies on `C`. -/
theorem F_pKv {d : ℕ} (hd : IsDisc d) (X : ℤ_[2]) :
    FurioLombardo.F (pKv d X 0) (pKv d X 1) (pKv d X 2) = 0 := by
  simp only [pKv]
  rw [← map_F]
  rw [(discY_spec hd X).1]
  simp

/-- The value of the quadratic form of a symmetric matrix read as a `Sym3`. -/
theorem quad_ofMatrix {M : Matrix (Fin 3) (Fin 3) Kv} (hM : Mᵀ = M) (p : Fin 3 → Kv) :
    Sym3.quad (fieldOps Kv) (Sym3.ofMatrix M) (p 0) (p 1) (p 2) = p ⬝ᵥ (M *ᵥ p) := by
  obtain ⟨a10, a20, a21⟩ := sym_entries hM
  simp only [Sym3.quad, Sym3.mulVec, Sym3.ofMatrix, fieldOps, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  rw [a10, a20, a21]

/-- Bruin's identity `Q1 Q3 = Q2²` at a point of `C(K_v)`. -/
theorem quad_rel_Kv (p : Fin 3 → Kv) (hF : FurioLombardo.F (p 0) (p 1) (p 2) = 0) :
    (p ⬝ᵥ ((Mmat 0).map σ *ᵥ p)) * (p ⬝ᵥ ((Mmat 2).map σ *ᵥ p)) =
      (p ⬝ᵥ ((Mmat 1).map σ *ᵥ p)) ^ 2 := by
  rw [quad_eq (qFormData_Mmat 0), quad_eq (qFormData_Mmat 1), quad_eq (qFormData_Mmat 2)]
  have h := onE_zero
  simp only [onE, List.forall_mem_cons, evK_sub, evK_add, evK_mul, evK_lin, evK_int, Int.cast_one,
    Int.cast_ofNat, Int.cast_neg] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -⟩ := h
  have g0 := congrArg σ h0
  have g1 := congrArg σ h1
  have g2 := congrArg σ h2
  have g3 := congrArg σ h3
  have g4 := congrArg σ h4
  have g5 := congrArg σ h5
  have g6 := congrArg σ h6
  have g7 := congrArg σ h7
  have g8 := congrArg σ h8
  have g9 := congrArg σ h9
  have g10 := congrArg σ h10
  have g11 := congrArg σ h11
  have g12 := congrArg σ h12
  have g13 := congrArg σ h13
  have g14 := congrArg σ h14
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, map_zero] at g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14
  have key : qvalK (fun i j => σ (zkE (qzk 0 i j))) p * qvalK (fun i j => σ (zkE (qzk 2 i j))) p -
      qvalK (fun i j => σ (zkE (qzk 1 i j))) p ^ 2 = σ (zkE czk) * FurioLombardo.F (p 0) (p 1) (p 2) := by
    simp only [qvalK, FurioLombardo.F]
    linear_combination p 0 ^ 4 * g0 + p 0 ^ 3 * p 1 * g1 + p 0 ^ 3 * p 2 * g2 +
      p 0 ^ 2 * p 1 ^ 2 * g3 + p 0 ^ 2 * p 1 * p 2 * g4 + p 0 ^ 2 * p 2 ^ 2 * g5 +
      p 0 * p 1 ^ 3 * g6 + p 0 * p 1 ^ 2 * p 2 * g7 + p 0 * p 1 * p 2 ^ 2 * g8 + p 0 * p 2 ^ 3 * g9 +
      p 1 ^ 4 * g10 + p 1 ^ 3 * p 2 * g11 + p 1 ^ 2 * p 2 ^ 2 * g12 + p 1 * p 2 ^ 3 * g13 +
      p 2 ^ 4 * g14
  rw [hF, mul_zero] at key
  linear_combination key

/-! ## The point of `D_δ(K_v)` of the certificate -/

theorem pKv_ne_zero {d : ℕ} (hd : IsDisc d) (X : ℤ_[2]) : pKv d X ≠ 0 := by
  intro h
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · have h2 := congrFun h 2
    simp [pKv, discPt, toKv] at h2
  · have h2 := congrFun h 2
    simp [pKv, discPt, toKv] at h2
  · have h2 := congrFun h 2
    simp [pKv, discPt, toKv] at h2
  · have h1 := congrFun h 1
    simp [pKv, discPt, toKv] at h1
  · have h1 := congrFun h 1
    simp [pKv, discPt, toKv] at h1

theorem mem_dl {k : Ctx} (hk : k.Ok) (kk : Fin 2) {dl : Ball} (h : sigQ k (dL kk) 1 = some dl) :
    dl.Mem (σ (δ kk)) := by
  have h1 := mem_sigQ hk h
  simpa [FurioLombardo.Discharge.M3a.Bruin.δ, Nat.cast_one, inv_one, one_mul] using h1

theorem mem_discPtO {k : Ctx} (hk : k.Ok) {d : ℕ} (hd : IsDisc d) (c : ℕ) {Y0 : ℤ} {N : ℕ}
    (hY : (2 : ℤ) ^ N ∣ G1 d (c : ℤ) Y0) :
    Trip.Rel (fun a b => Ball.Mem b a)
      (pKv d (c : ℤ_[2]) 0, pKv d (c : ℤ_[2]) 1, pKv d (c : ℤ_[2]) 2)
      (discPtO (ballOpsF k) d ((ballOpsF k).ofInt c) (Ball.ofApprox k (Y0, 0, 0) N)) := by
  have hX : ((ballOpsF k).ofInt c).Mem (((c : ℤ) : Kv)) := (rel_ballOpsF hk).ofInt c
  have hY : (Ball.ofApprox k (Y0, 0, 0) N).Mem (toKv (discY d (c : ℤ_[2]))) :=
    Ball.mem_ofApprox hk (approx_discY hd c hY)
  have h := rel_discPtO (rel_ballOpsF hk) d hX hY
  have hleft : discPtO (fieldOps Kv) d ((c : ℤ) : Kv) (toKv (discY d (c : ℤ_[2]))) =
      (pKv d (c : ℤ_[2]) 0, pKv d (c : ℤ_[2]) 1, pKv d (c : ℤ_[2]) 2) := by
    rw [discPtO_field]
    simp [pKv, map_discPt, toKv, map_natCast, Int.cast_natCast]
  rw [hleft] at h
  exact h

theorem mem_quad_of {k : Ctx} (hk : k.Ok) (i : Fin 3) {m : Sym3 Ball} (hm : mBall k i = some m)
    {p : Fin 3 → Kv} {w : Ball × Ball × Ball}
    (hw : Trip.Rel (fun a b => Ball.Mem b a) (p 0, p 1, p 2) w) :
    (Sym3.quad (ballOpsF k) m w.1 w.2.1 w.2.2).Mem (p ⬝ᵥ ((Mmat i).map σ *ᵥ p)) := by
  have h := rel_quad (rel_ballOpsF hk) (mem_mBall hk i hm) hw.1 hw.2.1 hw.2.2
  rwa [quad_ofMatrix (Mmat_map_symm i)] at h

theorem mem_inv_of {k : Ctx} (hk : k.Ok) {b b' : Ball} {x : Kv} (hx : b.Mem x)
    (h : (ballOpsF k).inv b = some b') : x ≠ 0 ∧ b'.Mem x⁻¹ := by
  obtain ⟨y, hy, hm⟩ := (rel_ballOpsF hk).inv hx h
  obtain ⟨hx0, rfl⟩ := fieldOps_inv_eq_some hy
  exact ⟨hx0, hm⟩

theorem mem_rho {k : Ctx} (hk : k.Ok) {e : BranchBox} (he : e.e = 0) :
    (Ball.ofApprox k e.rho k.P).Mem (rhoK e) := by
  apply Ball.mem_ofApprox hk
  rw [rhoK, he, pow_zero, div_one]
  exact approx_evZ e.rho k.P

theorem norm_sub_lt_add_of_lt {y ρ : Kv} (h : ‖y - ρ‖ < ‖2 * ρ‖) : ‖y - ρ‖ < ‖y + ρ‖ := by
  have e : y + ρ = 2 * ρ + (y - ρ) := by ring
  rw [e, norm_add_eq_left_of_lt h]
  exact h

theorem eq_mul_sq_of_sq {L : Type*} [Field L] {δ y Q : L} (hδ : δ ≠ 0) (h : y ^ 2 = Q * δ⁻¹) :
    Q = δ * y ^ 2 := by
  rw [h, mul_comm Q, ← mul_assoc, mul_inv_cancel₀ hδ, one_mul]

theorem eq_mul_mul_inv {L : Type*} [Field L] {δ y Q : L} (hδ : δ ≠ 0) (hy : y ≠ 0) :
    Q = δ * (y * (Q * δ⁻¹ * y⁻¹)) := by
  field_simp [hδ, hy]

theorem eq_mul_inv_mul {L : Type*} [Field L] {δ y Q : L} (hδ : δ ≠ 0) (hy : y ≠ 0) :
    Q = δ * (Q * δ⁻¹ * y⁻¹ * y) := by
  field_simp [hδ, hy]

theorem eq_mul_sq_of_rel {L : Type*} [Field L] {δ y A B C : L} (hδ : δ ≠ 0) (hy : y ≠ 0)
    (h1 : A = δ * y ^ 2) (h : A * C = B ^ 2) : C = δ * (B * δ⁻¹ * y⁻¹) ^ 2 := by
  rw [h1] at h
  field_simp [hδ, hy]
  calc
    C * δ * y ^ 2 = (δ * y ^ 2) * C := by ring
    _ = B ^ 2 := h

/-- The point over `p` with `r = y` and `s = Q2 / (δ y)`. -/
noncomputable def ptR (kk : Fin 2) {p : Fin 3 → Kv} (hp : p ≠ 0)
    (hF : FurioLombardo.F (p 0) (p 1) (p 2) = 0) {y : Kv} (hy : y ≠ 0)
    (h1 : y ^ 2 = p ⬝ᵥ ((Mmat 0).map σ *ᵥ p) * (σ (δ kk))⁻¹) : DPtKv kk where
  p := p
  r := y
  s := p ⬝ᵥ ((Mmat 1).map σ *ᵥ p) * (σ (δ kk))⁻¹ * y⁻¹
  ne_zero := hp
  eq1 := eq_mul_sq_of_sq (σδ_ne_zero kk) h1
  eq2 := eq_mul_mul_inv (σδ_ne_zero kk) hy
  eq3 := eq_mul_sq_of_rel (σδ_ne_zero kk) hy (eq_mul_sq_of_sq (σδ_ne_zero kk) h1) (quad_rel_Kv p hF)

/-- The point over `p` with `s = y` and `r = Q2 / (δ y)`. -/
noncomputable def ptS (kk : Fin 2) {p : Fin 3 → Kv} (hp : p ≠ 0)
    (hF : FurioLombardo.F (p 0) (p 1) (p 2) = 0) {y : Kv} (hy : y ≠ 0)
    (h3 : y ^ 2 = p ⬝ᵥ ((Mmat 2).map σ *ᵥ p) * (σ (δ kk))⁻¹) : DPtKv kk where
  p := p
  r := p ⬝ᵥ ((Mmat 1).map σ *ᵥ p) * (σ (δ kk))⁻¹ * y⁻¹
  s := y
  ne_zero := hp
  eq1 := eq_mul_sq_of_rel (σδ_ne_zero kk) hy (eq_mul_sq_of_sq (σδ_ne_zero kk) h3)
    (by rw [mul_comm]; exact quad_rel_Kv p hF)
  eq2 := eq_mul_inv_mul (σδ_ne_zero kk) hy
  eq3 := eq_mul_sq_of_sq (σδ_ne_zero kk) h3

/-- **The point of the certificate.** -/
theorem exists_of_apInBall {k : Ctx} (hk : k.Ok) (kk : Fin 2) {d c : ℕ} (hd : IsDisc d) {Y0 : ℤ}
    {N : ℕ} (hY : (2 : ℤ) ^ N ∣ G1 d (c : ℤ) Y0) {e : BranchBox} (he : e.e = 0) {sR : N3} {eR : ℕ}
    {xb : APIn Ball} (h : apInBall k kk d c Y0 N e sR eR = some xb) :
    ∃ x : DPtKv kk, x.p = pKv d (c : ℤ_[2]) ∧ BranchOK e x ∧
      APIn.Rel (fun a b => Ball.Mem b a) (apInV kk x) xb := by
  have hp := pKv_ne_zero hd (c : ℤ_[2])
  have hF := F_pKv hd (c : ℤ_[2])
  have hw := mem_discPtO hk hd c hY
  have hrho := mem_rho hk (k := k) he
  unfold apInBall at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨m0, hm0, m1, hm1, m2, hm2, dl, hdl, idl, hidl, h⟩ := h
  have hdl' := mem_dl hk kk hdl
  obtain ⟨-, hidl'⟩ := mem_inv_of hk hdl' hidl
  have hq0 := (rel_ballOpsF hk).mul (mem_quad_of hk 0 hm0 hw) hidl'
  have hq1 := (rel_ballOpsF hk).mul (mem_quad_of hk 1 hm1 hw) hidl'
  have hq2 := (rel_ballOpsF hk).mul (mem_quad_of hk 2 hm2 hw) hidl'
  have hm0' := mem_mBall hk 0 hm0
  have hm1' := mem_mBall hk 1 hm1
  have hm2' := mem_mBall hk 2 hm2
  split_ifs at h with hwh
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    split_ifs at h with hnear
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨ir, hir, rfl⟩ := h
    obtain ⟨y, hy2, hy⟩ := Ball.exists_mem_sqrt hk hq0 hr
    obtain ⟨hy0, hiy⟩ := mem_inv_of hk hy hir
    refine ⟨ptR kk hp hF hy0 hy2, rfl, ?_, ?_⟩
    · simp only [BranchOK, hwh, ite_true]
      exact norm_sub_lt_add_of_lt (Ball.norm_sub_lt_of_nearOK hk hy hrho hnear)
    · exact ⟨hm2', hm1', hm0', hdl', hw.1, hw.2.1, hw.2.2, (rel_ballOpsF hk).mul hq1 hiy, hy⟩
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, h⟩ := h
    split_ifs at h with hnear
    simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨is, his, rfl⟩ := h
    obtain ⟨y, hy2, hy⟩ := Ball.exists_mem_sqrt hk hq2 hs
    obtain ⟨hy0, hiy⟩ := mem_inv_of hk hy his
    refine ⟨ptS kk hp hF hy0 hy2, rfl, ?_, ?_⟩
    · simp only [BranchOK, hwh, Bool.false_eq_true, ite_false]
      exact norm_sub_lt_add_of_lt (Ball.norm_sub_lt_of_nearOK hk hy hrho hnear)
    · exact ⟨hm2', hm1', hm0', hdl', hw.1, hw.2.1, hw.2.2, hy, (rel_ballOpsF hk).mul hq1 hiy⟩

/-! ## The centres -/

/-- The certificate of the centre of the constant box `c` of twist `kk`: the box is in the branch
table, and the point `x` over the centre on its branch has `lamK (φ_v(x))` in the ball of `c.y + la`. -/
def CentreOK (kk : Fin 2) (la : Fin 6 → ℤ) (qa : ℕ) (c : FurioLombardo.M4.CBox) : Prop :=
  c.q ≤ qa ∧ ∃ e ∈ branchTable kk, e.disc = c.disc ∧ e.c = c.c ∧ e.s = c.s ∧
    ∃ x : DPtKv kk, x.p = pKv c.disc (c.c : ℤ_[2]) ∧ BranchOK e x ∧
      ∀ j, ‖lamK kk (Additive.ofMul (phiV kk x)) j - evZ (lTriple (c.y + la) j)‖ ≤ ‖pv‖ ^ (3 * c.q)

/-- **`CentreOK` from the ball run.** -/
theorem centreOK_of_run (kk : Fin 2) {la : Fin 6 → ℤ} {qa : ℕ} {c : FurioLombardo.M4.CBox}
    {e : BranchBox} (hbox : e ∈ branchTable kk ∧ e.disc = c.disc ∧ e.c = c.c ∧ e.s = c.s ∧ e.e = 0)
    (hq : c.q ≤ qa) (hd : IsDisc c.disc) {Y0 : ℤ} {N : ℕ} (hY : (2 : ℤ) ^ N ∣ G1 c.disc (c.c : ℤ) Y0)
    {k : Ctx} (hk : k.Ok) {sR : N3} {eR : ℕ} {xb : APIn Ball}
    (hin : apInBall k kk c.disc c.c Y0 N e sR eR = some xb) {prm : APPrm} {mB : Mum Ball}
    (hphi : apPhi (ballOpsF k) prm xb = some mB)
    {F g : Sext Ball} {b : Ball} {E R : Mum Ball} {A : Mat2 Ball} {sB : N3} {eB J Dd : ℕ}
    (hF : FvBall k kk = some F) (hg : gBall k F = some g) (hb : bKBall k kk g sB eB = some b)
    (hE : E0Ball k kk g b = some E) (hA : AmatBall k kk g b = some A)
    (hR : drun (ballOpsF k) g mB E (chainSteps J) mB = some R)
    (hfin : finalOK k A b kk (IntModelKv.aa kk) (M0 kk) R J Dd (c.y + la) c.q = true) :
    CentreOK kk la qa c := by
  obtain ⟨he, hed, hec, hes, he0⟩ := hbox
  obtain ⟨x, hxp, hxb, hxr⟩ := exists_of_apInBall hk kk hd hY he0 hin
  refine ⟨hq, e, he, hed, hec, hes, x, hxp, hxb, fun j => ?_⟩
  exact (lamK_phiV_of_cert kk x hk hxr hphi hF hg hb hE hA hR hfin j).2

theorem lTriple_add (l l' : Fin 6 → ℤ) (j : Fin 2) :
    evZ (lTriple (l + l') j) = evZ (lTriple l j) + evZ (lTriple l' j) := by
  simp only [lTriple, evZ, Pi.add_apply, Int.cast_add]
  ring

/-- **`HCentre` from the certificates of the centres** and the ball `(la, qa)` of `lam φ(x_a)`. -/
theorem hCentre_of_ok (kk : Fin 2) (D : FurioLombardo.M4.TwistData) (hI : LamInt kk)
    (hla : ∀ j, ‖lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j -
      evZ (lTriple D.la j)‖ ≤ ‖pv‖ ^ (3 * D.qa))
    (h : ∀ c ∈ D.constant, CentreOK kk D.la D.qa c) :
    FurioLombardo.M4.HCentre D (lamD kk) := by
  intro c hc
  rcases h c hc with ⟨hq, e, he, hed, hec, hes, x, hxp, hxb, hx⟩
  have hbox : boxAt kk c.disc (c.c : ℤ_[2]) = some e := by
    apply boxAt_eq_of_mem he
    · exact hed
    · rw [hec, hes]
      exact ⟨0, by simp⟩
  have hlamD : lamD kk c.disc (c.c : ℤ_[2]) = lamPt kk x := by
    apply lamD_eq hbox x hxp hxb
  rw [hlamD]
  apply dvdV_of_norm_toKv2_le
  intro j
  have htarget : toKv2 (lamPt kk x - FurioLombardo.M4.icast c.y) j =
      lamK kk (Additive.ofMul (phiV kk x)) j - lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j -
      evZ (lTriple c.y j) := by
    calc
      toKv2 (lamPt kk x - FurioLombardo.M4.icast c.y) j
          = (toKv2 (lamPt kk x) - toKv2 (FurioLombardo.M4.icast c.y)) j := by rw [map_sub]
      _ = toKv2 (lamPt kk x) j - toKv2 (FurioLombardo.M4.icast c.y) j := by rw [Pi.sub_apply]
      _ = toKv2 (lam kk (Additive.ofMul (phiV kk x) - Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk))))) j -
          toKv2 (FurioLombardo.M4.icast c.y) j := rfl
      _ = toKv2 ((lam kk (Additive.ofMul (phiV kk x))) - (lam kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))))) j -
          toKv2 (FurioLombardo.M4.icast c.y) j := by rw [map_sub]
      _ = (toKv2 (lam kk (Additive.ofMul (phiV kk x))) - toKv2 (lam kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))))) j -
          toKv2 (FurioLombardo.M4.icast c.y) j := by rw [map_sub]
      _ = (toKv2 (lam kk (Additive.ofMul (phiV kk x))) j - toKv2 (lam kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk))))) j) -
          toKv2 (FurioLombardo.M4.icast c.y) j := by rw [Pi.sub_apply]
      _ = (lamK kk (Additive.ofMul (phiV kk x)) j - lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j) -
          toKv2 (FurioLombardo.M4.icast c.y) j := by rw [lam_toKv2 kk hI, lam_toKv2 kk hI]
      _ = (lamK kk (Additive.ofMul (phiV kk x)) j - lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j) -
          evZ (lTriple c.y j) := by rw [toKv2_icast]
  rw [htarget]
  have hA : ‖lamK kk (Additive.ofMul (phiV kk x)) j - evZ (lTriple (c.y + D.la) j)‖ ≤ ‖pv‖ ^ (3 * c.q) := hx j
  have hB : ‖lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)‖ ≤ ‖pv‖ ^ (3 * D.qa) := hla j
  have hpow : ‖pv‖ ^ (3 * D.qa) ≤ ‖pv‖ ^ (3 * c.q) := by
    have hpos : 0 ≤ ‖pv‖ := norm_nonneg _
    have hle1 : ‖pv‖ ≤ 1 := norm_pv_le_one
    have hmul : 3 * c.q ≤ 3 * D.qa := by omega
    exact pow_le_pow_of_le_one hpos hle1 hmul
  have hB' : ‖lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)‖ ≤ ‖pv‖ ^ (3 * c.q) :=
    le_trans hB hpow
  have hsum : evZ (lTriple (c.y + D.la) j) = evZ (lTriple c.y j) + evZ (lTriple D.la j) := lTriple_add c.y D.la j
  rw [hsum] at hA
  have htarget2 : lamK kk (Additive.ofMul (phiV kk x)) j - lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple c.y j) =
      (lamK kk (Additive.ofMul (phiV kk x)) j - (evZ (lTriple c.y j) + evZ (lTriple D.la j))) -
      (lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)) := by
    ring
  rw [htarget2]
  have hmax : ‖(lamK kk (Additive.ofMul (phiV kk x)) j - (evZ (lTriple c.y j) + evZ (lTriple D.la j))) -
      (lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j))‖ ≤
      max ‖lamK kk (Additive.ofMul (phiV kk x)) j - (evZ (lTriple c.y j) + evZ (lTriple D.la j))‖
          ‖lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)‖ := by
    have h := IsUltrametricDist.norm_add_le_max
      (lamK kk (Additive.ofMul (phiV kk x)) j - (evZ (lTriple c.y j) + evZ (lTriple D.la j)))
      (-(lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)))
    have hsub : (lamK kk (Additive.ofMul (phiV kk x)) j - (evZ (lTriple c.y j) + evZ (lTriple D.la j))) +
        (-(lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j))) =
        (lamK kk (Additive.ofMul (phiV kk x)) j - (evZ (lTriple c.y j) + evZ (lTriple D.la j))) -
        (lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)) := by
      ring
    have hnorm : ‖-(lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j))‖ =
        ‖lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)‖ := by
      rw [norm_neg]
    rw [hsub, hnorm] at h
    exact h
  have hmax' : max ‖lamK kk (Additive.ofMul (phiV kk x)) j - (evZ (lTriple c.y j) + evZ (lTriple D.la j))‖
      ‖lamK kk (Additive.ofMul (jacMap σ (fRev kk) (phiK kk (xa kk)))) j - evZ (lTriple D.la j)‖ ≤ ‖pv‖ ^ (3 * c.q) := by
    exact max_le hA hB'
  exact le_trans hmax hmax'

end FurioLombardo.Discharge.M4Box
