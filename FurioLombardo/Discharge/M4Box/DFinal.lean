import Mathlib
import FurioLombardo.Discharge.M4Box.DInput
import FurioLombardo.Discharge.M4Box.Coord

/-!
# The value certificate of `lamK k (D_i)` (lane lean-m4box)

From a successful ball run of the chain `2^J N D_i + E0` (`drun` on `ballOpsF`, inputs `DBall`,
`E0Ball`, `gBall`), the final checks `finalOK` (depth `Dd` of the chart coordinates, the branch
conditions of `lamK_Dpt_sub_le`, and the balls `lamBall` of the two coordinates of `lamK k (D_i)`
against the lattice data) give `‖lamK k (D_i) j‖ ≤ 1` and `‖lamK k (D_i) j - l_i(j)‖ ≤ ‖pv‖^(3 q_i)`
(`lamK_Dpt_of_cert`), hence `HBallD` (`hBallD_of_values`).
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith
open FurioLombardo.Discharge.M3a.Bruin (fRev goodSextic_fRev_Kv)

namespace FurioLombardo.Discharge.M4Box

/-! ## The final checks -/

/-! ## Soundness -/

set_option maxHeartbeats 400000 in
theorem mem_lamBall {k : Ctx} (hk : k.Ok) (kk : Fin 2) {A : Mat2 Ball}
    (hA : A.a00.Mem (Amat kk 0 0) ∧ A.a01.Mem (Amat kk 0 1) ∧ A.a10.Mem (Amat kk 1 0) ∧
      A.a11.Mem (Amat kk 1 1))
    {R : Mum Ball} {Rx : Mum Kv} (hR : Mum.Rel (fun x b => b.Mem x) Rx R) {J Err : ℕ} {lam : Kv}
    (j : Fin 2)
    (hlam : ‖((2 ^ J * dN : ℕ) : Kv) * lam - (Amat kk *ᵥ Rx.chartT (aK kk)) j‖ ≤ ‖pv‖ ^ Err)
    {lb : Ball} (h : lamBall k A kk R J Err j = some lb) : lb.Mem lam := by
  unfold lamBall shiftB at h
  generalize hN : (2 ^ J * dN : ℕ) = N at h hlam
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨i, hi, h_eq⟩ := h
  -- h_eq : (ballOpsF k).mul i ... = lb (already simplified by simp)
  let s := shiftB k kk R
  let x := if j = 0 then (ballOpsF k).add ((ballOpsF k).mul A.a00 s.u1) ((ballOpsF k).mul A.a01 s.u0)
    else (ballOpsF k).add ((ballOpsF k).mul A.a10 s.u1) ((ballOpsF k).mul A.a11 s.u0)
  set M' := ((N : ℕ) : ℤ) with hM'
  have hNkv : (M' : Kv) = ((N : ℕ) : Kv) := by simp [hM']
  have hmem_ofInt : ((ballOpsF k).ofInt M').Mem (M' : Kv) :=
    Ball.mem_ofInt hk M'
  have hi' : (ballOpsF k).inv ((ballOpsF k).ofInt M') = some i := by
    simpa [hM'] using hi
  have hinv := (rel_ballOpsF hk).inv hmem_ofInt hi'
  obtain ⟨i', hi', hi_mem⟩ := hinv
  have hinv_eq := fieldOps_inv_eq_some hi'
  rcases hinv_eq with ⟨hM'_ne_zero, hi'_eq⟩
  -- The shift relation
  -- Try to use the shift relation without the expensive ha proof
  -- Let's create ha using a simpler approach
  have ha : ((ballOpsF k).ofInt (kk : ℤ)).Mem ((fieldOps Kv).ofInt (kk : ℤ)) := by
    dsimp [ballOpsF, fieldOps]
    exact Ball.mem_ofInt hk (kk : ℤ)
  have hs_rel := (rel_ballOpsF hk).shift ha hR
  rcases hs_rel with ⟨hs_u0_mem, hs_u1_mem, hs_v0_mem, hs_v1_mem⟩
  -- Now handle the coordinate j
  fin_cases j
  · -- j = 0: x simplifies to the first branch
    dsimp [x] at h_eq
    have hx_mem : x.Mem ((Amat kk *ᵥ Rx.chartT (aK kk)) 0) := by
      have h_mul1 := (rel_ballOpsF hk).mul hA.1 hs_u1_mem
      have h_mul2 := (rel_ballOpsF hk).mul hA.2.1 hs_u0_mem
      have h_add := (rel_ballOpsF hk).add h_mul1 h_mul2
      rw [Mum.chartT_eq_shift (aK kk) Rx]
      simp [Matrix.mulVec]
      simp [fieldOps, aK, Mum.shift]
      exact h_add
    have herr_mem : (Ball.errB k Err).Mem ((M' : Kv) * lam - (Amat kk *ᵥ Rx.chartT (aK kk)) 0) := by
      rw [hNkv]
      exact Ball.mem_errB hlam
    have h_add_mem : ((ballOpsF k).add x (Ball.errB k Err)).Mem ((M' : Kv) * lam) := by
      have h_add := (rel_ballOpsF hk).add hx_mem herr_mem
      simpa [fieldOps, x, add_comm, sub_add_cancel] using h_add
    have h_mul_mem : ((ballOpsF k).mul i ((ballOpsF k).add x (Ball.errB k Err))).Mem
        ((M' : Kv)⁻¹ * ((M' : Kv) * lam)) := by
      have h_mul := (rel_ballOpsF hk).mul hi_mem h_add_mem
      simpa [fieldOps, hi'_eq] using h_mul
    have h_target : ((ballOpsF k).mul i ((ballOpsF k).add x (Ball.errB k Err))).Mem lam := by
      have h_eq : (M' : Kv)⁻¹ * ((M' : Kv) * lam) = lam := by
        rw [← mul_assoc, inv_mul_cancel₀ hM'_ne_zero, one_mul]
      rw [h_eq] at h_mul_mem
      exact h_mul_mem
    dsimp [x] at h_target
    rw [← h_eq]
    exact h_target
  · -- j = 1: x simplifies to the second branch
    dsimp [x] at h_eq
    have hx_mem : x.Mem ((Amat kk *ᵥ Rx.chartT (aK kk)) 1) := by
      have h_mul1 := (rel_ballOpsF hk).mul hA.2.2.1 hs_u1_mem
      have h_mul2 := (rel_ballOpsF hk).mul hA.2.2.2 hs_u0_mem
      have h_add := (rel_ballOpsF hk).add h_mul1 h_mul2
      rw [Mum.chartT_eq_shift (aK kk) Rx]
      simp [Matrix.mulVec]
      simp [fieldOps, aK, Mum.shift]
      exact h_add
    have herr_mem : (Ball.errB k Err).Mem ((M' : Kv) * lam - (Amat kk *ᵥ Rx.chartT (aK kk)) 1) := by
      rw [hNkv]
      exact Ball.mem_errB hlam
    have h_add_mem : ((ballOpsF k).add x (Ball.errB k Err)).Mem ((M' : Kv) * lam) := by
      have h_add := (rel_ballOpsF hk).add hx_mem herr_mem
      simpa [fieldOps, x, add_comm, sub_add_cancel] using h_add
    have h_mul_mem : ((ballOpsF k).mul i ((ballOpsF k).add x (Ball.errB k Err))).Mem
        ((M' : Kv)⁻¹ * ((M' : Kv) * lam)) := by
      have h_mul := (rel_ballOpsF hk).mul hi_mem h_add_mem
      simpa [fieldOps, hi'_eq] using h_mul
    have h_target : ((ballOpsF k).mul i ((ballOpsF k).add x (Ball.errB k Err))).Mem lam := by
      have h_eq : (M' : Kv)⁻¹ * ((M' : Kv) * lam) = lam := by
        rw [← mul_assoc, inv_mul_cancel₀ hM'_ne_zero, one_mul]
      rw [h_eq] at h_mul_mem
      exact h_mul_mem
    dsimp [x] at h_target
    rw [← h_eq]
    exact h_target

theorem lamOK_sound {k : Ctx} (hk : k.Ok) {lb : Ball} {x : Kv} (hx : lb.Mem x) {lt : T3} {q : ℕ}
    (h : lamOK k lb lt q = true) : ‖x‖ ≤ 1 ∧ ‖x - evZ lt‖ ≤ ‖pv‖ ^ (3 * q) := by
  simp only [lamOK, Bool.and_eq_true] at h
  have h1 : ‖x‖ ≤ 1 := by
    have := Ball.norm_le_of_normLe hk hx h.1
    simpa [pow_zero] using this
  have h2 : ‖x - evZ lt‖ ≤ ‖pv‖ ^ (3 * q) := by
    have mem_sub : (lb.sub k (Ball.ofApprox k lt k.P)).Mem (x - evZ lt) :=
      Ball.mem_sub hk hx (Ball.mem_ofApprox hk (approx_evZ lt k.P))
    exact Ball.norm_le_of_normLe hk mem_sub h.2
  exact And.intro h1 h2

theorem lamCheck_eq_true {k : Ctx} {A : Mat2 Ball} {a : ℕ} {R : Mum Ball} {J Err : ℕ} {j : Fin 2}
    {l : Fin 6 → ℤ} {q : ℕ} (h : lamCheck k A a R J Err j l q = true) :
    ∃ lb, lamBall k A a R J Err j = some lb ∧ lamOK k lb (lTriple l j) q = true :=
  -- by the library lemma, not by reduction: checking `(match some lb with ..) = lamOK ..` by
  -- unfolding reaches the ball arithmetic of `lamOK` and exhausts memory
  (Option.any_eq_true _ _).mp h

theorem chartW_coeff_zero_shift {K : Type*} [Field K] (a : K) (D : Mum K) :
    (D.chartW a).coeff 0 = (Mum.shift (fieldOps K) a D).v0 := by
  simp [Mum.chartW, Mum.shift, fieldOps, coeff_add, coeff_X_zero, coeff_C_zero]

theorem chartW_coeff_one_shift {K : Type*} [Field K] (a : K) (D : Mum K) :
    (D.chartW a).coeff 1 = (Mum.shift (fieldOps K) a D).v1 := by
  simp [Mum.chartW, Mum.shift, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]

/-- **The certificate of one point `D_i`.** -/
theorem lamK_Dpt_of_cert (kk : Fin 2) (i : Fin 7) {k : Ctx} (hk : k.Ok) {F g : Sext Ball} {b : Ball}
    {E D R : Mum Ball} {A : Mat2 Ball} {sN sA sB : N3} {eN eA eB J Dd : ℕ} {l : Fin 6 → ℤ} {q : ℕ}
    (hF : FvBall k kk = some F) (hg : gBall k F = some g) (hb : bKBall k kk g sB eB = some b)
    (hE : E0Ball k kk g b = some E) (hA : AmatBall k kk g b = some A)
    (hD : DBall k kk i F sN eN sA eA = some D)
    (hR : drun (ballOpsF k) g D E (chainSteps J) D = some R)
    (hfin : finalOK k A b kk (IntModelKv.aa kk) (M0 kk) R J Dd l q = true) (j : Fin 2) :
    ‖lamK kk (SelmerSpan.Dpt kk i) j‖ ≤ 1 ∧
      ‖lamK kk (SelmerSpan.Dpt kk i) j - evZ (lTriple l j)‖ ≤ ‖pv‖ ^ (3 * q) := by
  have hFm := mem_FvBall hk hF
  have hgm := mem_gBall hk kk hFm hg
  have hbm := mem_bKBall hk kk hgm hb
  have hEm := mem_E0Ball hk kk hgm hbm hE
  have hAm := mem_AmatBall hk kk hgm hbm hA
  have hDm := mem_DBall hk kk i hFm hD
  have hrel := Ops.Rel.drun (rel_ballOpsF hk) hgm hDm hEm (chainSteps J) hDm
  obtain ⟨Rx, hRx, hRR⟩ := hrel R hR
  have hs : Mum.Rel (fun x b => b.Mem x) (Mum.shift (fieldOps Kv) (aK kk) Rx) (shiftB k kk R) := by
    have h0 := Ops.Rel.shift (rel_ballOpsF hk) ((rel_ballOpsF hk).ofInt ((kk : ℕ) : ℤ)) hRR
    have e : (fieldOps Kv).ofInt ((kk : ℕ) : ℤ) = aK kk := by simp [fieldOps, aK]
    rw [e] at h0
    exact h0
  obtain ⟨hs0, hs1, hs2, hs3⟩ := hs
  simp only [finalOK, Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨⟨⟨⟨⟨⟨⟨hM, h7⟩, ht1⟩, ht0⟩, hw0⟩, hw1⟩, hl0⟩, hl1⟩ := hfin
  have ht : ∀ j, ‖Rx.chartT (aK kk) j‖ ≤ ‖pv‖ ^ Dd := by
    intro j
    rw [Mum.chartT_eq_shift]
    fin_cases j
    · exact Ball.norm_le_of_normLe hk hs1 ht1
    · exact Ball.norm_le_of_normLe hk hs0 ht0
  have hw0' : ‖(Rx.chartW (aK kk)).coeff 0 - bK kk‖ < ‖2 * bK kk‖ := by
    rw [chartW_coeff_zero_shift]
    exact Ball.norm_sub_lt_of_nearOK hk hs2 hbm hw0
  have hw1' : ‖(Rx.chartW (aK kk)).coeff 1‖ * ‖pv‖ ^ IntModelKv.aa kk ≤ ‖bK kk‖ := by
    rw [chartW_coeff_one_shift]
    exact Ball.norm_mul_le_of_normLeMul hk hs3 hbm hw1
  have hlam := lamK_Dpt_sub_le kk i J hRx hM h7 ht hw0' hw1' j
  -- `j` stays a variable and becomes a literal only inside `hlj`: after `fin_cases j`, checking
  -- the hypotheses at `⟨0, _⟩` against the goal unfolds the ball arithmetic and exhausts memory
  have hlj : lamCheck k A kk R J (2 * Dd - M0 kk - 3) j l q = true := by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · exact hl0
    · exact hl1
  obtain ⟨lb, hl, hok⟩ := lamCheck_eq_true hlj
  exact lamOK_sound hk (mem_lamBall hk kk hAm hRR j hlam hl) hok

/-! ## From the values to `HBallD` -/

theorem toKv2_icast (l : Fin 6 → ℤ) (j : Fin 2) :
    toKv2 (FurioLombardo.M4.icast l) j = evZ (lTriple l j) := by
  rw [toKv2_apply]
  simp only [evQ, evZ, lTriple, FurioLombardo.M4.icast, PadicInt.coe_intCast, map_intCast]

/-- **`HBallD` from the value bounds.** -/
theorem hBallD_of_values (kk : Fin 2) (D : FurioLombardo.M4.TwistData) (hI : LamInt kk)
    (h : ∀ i j, ‖lamK kk (SelmerSpan.Dpt kk i) j - evZ (lTriple (D.lD i) j)‖ ≤ ‖pv‖ ^ (3 * D.qD i)) :
    FurioLombardo.M4.HBallD D (fun i => lam kk (SelmerSpan.Dpt kk i)) := by
  intro i
  apply dvdV_of_norm_toKv2_le
  intro j
  rw [map_sub, lam_toKv2 kk hI, Pi.sub_apply, toKv2_icast]
  exact h i j

end FurioLombardo.Discharge.M4Box
