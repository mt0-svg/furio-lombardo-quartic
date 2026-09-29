import Mathlib
import FurioLombardo.Discharge.KvArith.Comp.DCert
import FurioLombardo.Discharge.KvArith.BallOps
import FurioLombardo.Discharge.KvArith.DChain
import FurioLombardo.Discharge.KvArith.Comp.DRun
import FurioLombardo.Discharge.SelmerSpan.Mumford
import FurioLombardo.Discharge.R7.ConcreteKv

/-!
# Soundness of the input and output programs of the D_i value certificate (lane lean-kv-arith)

For the programs of `Comp/DCert.lean`: the relational lemmas (`Ops.Rel.divR1`, ..., `Ops.Rel.sqC`),
their values over a field (`fieldOps_divR1`, ...: the expressions of `SelmerSpan.Dpt` and of the
translate `F(X + a)`), the three ball comparisons (`Ball.norm_sub_lt_of_nearOK`,
`Ball.norm_le_of_normLe`, `Ball.norm_mul_le_of_normLeMul`), the error ball `Ball.mem_errB`, the
identification of square roots (`eq_of_sq_eq_of_norm_sub_lt`, `Ball.eq_of_nearOK`). The splitting
of a chain run (`drun_append`) is in `Comp/DRun.lean`.
-/

namespace FurioLombardo.Discharge.KvArith

open Polynomial FurioLombardo.Discharge.M4Cert

/-! ## Relational lemmas -/

section Rel

variable {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}

theorem Ops.Rel.divR1 (h : Ops.Rel o p R) {x0 x1 x2 x3 x4 x5 x6 x7 x8 : A}
    {y0 y1 y2 y3 y4 y5 y6 y7 y8 : B} (h0 : R x0 y0) (h1 : R x1 y1) (h2 : R x2 y2) (h3 : R x3 y3)
    (h4 : R x4 y4) (h5 : R x5 y5) (h6 : R x6 y6) (h7 : R x7 y7) (h8 : R x8 y8) :
    R (o.divR1 x0 x1 x2 x3 x4 x5 x6 x7 x8) (p.divR1 y0 y1 y2 y3 y4 y5 y6 y7 y8) := by
  have w4 := h8
  have w3 := h.sub h7 (h.mul h0 w4)
  have w2 := h.sub (h.sub h6 (h.mul h0 w3)) (h.mul h1 w4)
  have w1 := h.sub (h.sub h5 (h.mul h0 w2)) (h.mul h1 w3)
  have w0 := h.sub (h.sub h4 (h.mul h0 w1)) (h.mul h1 w2)
  exact h.sub (h.sub h3 (h.mul h0 w0)) (h.mul h1 w1)

theorem Ops.Rel.divR0 (h : Ops.Rel o p R) {x0 x1 x2 x3 x4 x5 x6 x7 x8 : A}
    {y0 y1 y2 y3 y4 y5 y6 y7 y8 : B} (h0 : R x0 y0) (h1 : R x1 y1) (h2 : R x2 y2) (h3 : R x3 y3)
    (h4 : R x4 y4) (h5 : R x5 y5) (h6 : R x6 y6) (h7 : R x7 y7) (h8 : R x8 y8) :
    R (o.divR0 x0 x1 x2 x3 x4 x5 x6 x7 x8) (p.divR0 y0 y1 y2 y3 y4 y5 y6 y7 y8) := by
  have w4 := h8
  have w3 := h.sub h7 (h.mul h0 w4)
  have w2 := h.sub (h.sub h6 (h.mul h0 w3)) (h.mul h1 w4)
  have w1 := h.sub (h.sub h5 (h.mul h0 w2)) (h.mul h1 w3)
  have w0 := h.sub (h.sub h4 (h.mul h0 w1)) (h.mul h1 w2)
  exact h.sub h2 (h.mul h1 w0)

theorem Ops.Rel.normN (h : Ops.Rel o p R) {x0 x1 x2 x3 : A} {y0 y1 y2 y3 : B} (h0 : R x0 y0)
    (h1 : R x1 y1) (h2 : R x2 y2) (h3 : R x3 y3) :
    R (o.normN x0 x1 x2 x3) (p.normN y0 y1 y2 y3) := by
  unfold Ops.normN
  exact h.add (h.sub (h.mul h3 h3) (h.mul (h.mul h0 h2) h3)) (h.mul h1 (h.mul h2 h2))

theorem Ops.Rel.normA (h : Ops.Rel o p R) {x0 x1 x2 x3 : A} {y0 y1 y2 y3 : B} (h0 : R x0 y0)
    (h1 : R x1 y1) (h2 : R x2 y2) (h3 : R x3 y3) :
    R (o.normA x0 x1 x2 x3) (p.normA y0 y1 y2 y3) := by
  unfold Ops.normA
  exact h.add (h.sub (h.mul (h.ofInt 2) h2) (h.mul h0 h1)) (h.mul (h.ofInt 2) h3)

theorem Ops.Rel.sqB (h : Ops.Rel o p R) {x0 x1 : A} {y0 y1 : B} (h0 : R x0 y0) (h1 : R x1 y1) :
    OptRel R (o.sqB x0 x1) (p.sqB y0 y1) := by
  unfold Ops.sqB
  apply OptRel.bind
  · intro b' hb'
    exact h.inv (h.mul (h.ofInt 2) h1) hb'
  · intro a b hab c hc
    have hc' : c = p.mul y0 b := by
      simpa using hc.symm
    subst hc'
    refine ⟨o.mul x0 a, rfl, h.mul h0 hab⟩

theorem Ops.Rel.sqC (h : Ops.Rel o p R) {x0 x1 x2 : A} {y0 y1 y2 : B} (h0 : R x0 y0)
    (h1 : R x1 y1) (h2 : R x2 y2) :
    OptRel R (o.sqC x0 x1 x2) (p.sqC y0 y1 y2) := by
  simp [Ops.sqC]
  have h_inv4 : OptRel R (o.inv (o.ofInt 4)) (p.inv (p.ofInt 4)) := by
    intro b hb
    have h_inv := h.inv (h.ofInt 4) hb
    rcases h_inv with ⟨a, ha, hR⟩
    exact ⟨a, ha, hR⟩
  have h_inv2 : OptRel R (o.inv (o.ofInt 2)) (p.inv (p.ofInt 2)) := by
    intro b hb
    have h_inv := h.inv (h.ofInt 2) hb
    rcases h_inv with ⟨a, ha, hR⟩
    exact ⟨a, ha, hR⟩
  have h_pure (i4 : A) (j4 : B) (i2 : A) (j2 : B) (hi4 : R i4 j4) (hi2 : R i2 j2) :
      OptRel R (pure (o.add (o.mul x1 i4) (o.mul (o.mul x2 x0) i2)))
        (pure (p.add (p.mul y1 j4) (p.mul (p.mul y2 y0) j2))) := by
    intro c hc
    simp at hc
    subst hc
    refine ⟨o.add (o.mul x1 i4) (o.mul (o.mul x2 x0) i2), rfl, ?_⟩
    exact h.add (h.mul h1 hi4) (h.mul (h.mul h2 h0) hi2)
  refine (h_inv4.bind ?_)
  intro a b hR_ab
  refine (h_inv2.bind ?_)
  intro i2 j2 hR_i2j2
  exact h_pure a b i2 j2 hR_ab hR_i2j2

theorem Ops.Rel.transC0 (h : Ops.Rel o p R) (a : ℤ) {F : Sext A} {F' : Sext B}
    (hF : Sext.Rel R F F') : R (o.transC0 a F) (p.transC0 a F') := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hF
  unfold Ops.transC0
  exact h.add (h.add (h.add (h.add (h.add (h.add h0 (h.mul (h.ofInt a) h1)) (h.mul (h.ofInt (a ^ 2)) h2)) (h.mul (h.ofInt (a ^ 3)) h3)) (h.mul (h.ofInt (a ^ 4)) h4)) (h.mul (h.ofInt (a ^ 5)) h5)) (h.mul (h.ofInt (a ^ 6)) h6)

theorem Ops.Rel.transC1 (h : Ops.Rel o p R) (a : ℤ) {F : Sext A} {F' : Sext B}
    (hF : Sext.Rel R F F') : R (o.transC1 a F) (p.transC1 a F') := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hF
  unfold Ops.transC1
  exact h.add (h.add (h.add (h.add (h.add h1 (h.mul (h.ofInt (2 * a)) h2)) (h.mul (h.ofInt (3 * a ^ 2)) h3)) (h.mul (h.ofInt (4 * a ^ 3)) h4)) (h.mul (h.ofInt (5 * a ^ 4)) h5)) (h.mul (h.ofInt (6 * a ^ 5)) h6)

end Rel

/-! ## Values over a field -/

section Field

variable {F : Type*} [Field F]

theorem fieldOps_divR1 (p r g0 g1 g2 g3 g4 g5 g6 : F) :
    (fieldOps F).divR1 p r g0 g1 g2 g3 g4 g5 g6 = SelmerSpan.divR1 p r g0 g1 g2 g3 g4 g5 g6 := by
  rfl

theorem fieldOps_divR0 (p r g0 g1 g2 g3 g4 g5 g6 : F) :
    (fieldOps F).divR0 p r g0 g1 g2 g3 g4 g5 g6 = SelmerSpan.divR0 p r g0 g1 g2 g3 g4 g5 g6 := by
  simp only [Ops.divR0, Ops.divW, SelmerSpan.divR0, SelmerSpan.divW, fieldOps]

theorem fieldOps_normN (p r Z1 Z0 : F) :
    (fieldOps F).normN p r Z1 Z0 = Z0 ^ 2 - p * Z1 * Z0 + r * Z1 ^ 2 := by
  simp only [Ops.normN, fieldOps]; ring

theorem fieldOps_normA (p Z1 Z0 n : F) :
    (fieldOps F).normA p Z1 Z0 n = 2 * Z0 - p * Z1 + 2 * n := by
  simp only [Ops.normA, fieldOps]
  push_cast
  ring

theorem fieldOps_sqB {Z1 a b : F} (h : (fieldOps F).sqB Z1 a = some b) :
    b = SelmerSpan.sqB Z1 a := by
  simp only [Ops.sqB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨i, hi, rfl⟩ := h
  obtain ⟨hne, rfl⟩ := fieldOps_inv_eq_some hi
  simp [fieldOps, SelmerSpan.sqB, div_eq_mul_inv]

theorem fieldOps_sqC {p a b c : F} (h : (fieldOps F).sqC p a b = some c) :
    c = a / 4 + b * p / 2 := by
  unfold Ops.sqC at h
  simp [fieldOps] at h
  split_ifs at h
  · simp at h
  · simp at h
  · simp at h
  · have h_eq := Option.some.inj (by
      simpa using h)
    rw [← h_eq]
    simp [div_eq_mul_inv]

theorem fieldOps_transC0 (a : ℤ) {g : F[X]} (hg : g.natDegree ≤ 6) :
    (fieldOps F).transC0 a (Sext.ofPoly g) = (g.comp (X + C (a : F))).coeff 0 := by
  have hg_lt : g.natDegree < 7 := by omega
  have h_right : (g.comp (X + C (a : F))).coeff 0 = g.eval (a : F) := by
    calc
      (g.comp (X + C (a : F))).coeff 0 = Polynomial.eval 0 (g.comp (X + C (a : F))) := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
      _ = g.eval (Polynomial.eval 0 (X + C (a : F))) := by rw [Polynomial.eval_comp]
      _ = g.eval ((Polynomial.eval 0 X) + (Polynomial.eval 0 (C (a : F)))) := by rw [Polynomial.eval_add]
      _ = g.eval (0 + (a : F)) := by simp
      _ = g.eval (a : F) := by simp
  have h_left : (fieldOps F).transC0 a (Sext.ofPoly g) = g.eval (a : F) := by
    simp [Ops.transC0, Sext.ofPoly, fieldOps, Polynomial.eval_eq_sum_range' hg_lt]
    simp [Finset.sum_range_succ]
    ring
  rw [h_left, h_right]

theorem fieldOps_transC1 (a : ℤ) {g : F[X]} (hg : g.natDegree ≤ 6) :
    (fieldOps F).transC1 a (Sext.ofPoly g) = (g.comp (X + C (a : F))).coeff 1 := by
  have hcoeff7 : g.coeff 7 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hsum := FurioLombardo.Discharge.R7.ConcreteKv.coeff_comp_X_add_C g (a : F) (by omega) 1
  rw [hsum]
  simp [Ops.transC1, Sext.ofPoly, fieldOps, Finset.sum_range_succ, Nat.choose_one_right, hcoeff7]
  push_cast
  ring

end Field

/-! ## Ball comparisons -/

/-- Two square roots closer than `‖2y‖` are equal. -/
theorem eq_of_sq_eq_of_norm_sub_lt {K : Type*} [NormedField K] {x y : K} (h2 : x ^ 2 = y ^ 2)
    (h : ‖x - y‖ < ‖2 * y‖) : x = y := by
  have hprod : (x - y) * (x + y) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp hprod with (hsub | hadd)
  · exact sub_eq_zero.mp hsub
  · have hx_eq_neg_y : x = -y := by
      calc
        x = (x + y) - y := by ring
        _ = 0 - y := by rw [hadd]
        _ = -y := by simp
    have hsub' : x - y = -(2 * y) := by
      linear_combination hx_eq_neg_y
    have hnorm : ‖x - y‖ = ‖2 * y‖ := by
      calc
        ‖x - y‖ = ‖-(2 * y)‖ := by rw [hsub']
        _ = ‖2 * y‖ := by rw [norm_neg]
    exact (lt_irrefl _ (h.trans_eq hnorm.symm)).elim

section Balls

variable {k : Ctx}

theorem Ball.mem_errB {x : Kv} {R : ℕ} (hx : ‖x‖ ≤ ‖pv‖ ^ R) : (Ball.errB k R).Mem x := by
  refine ⟨?_, ?_⟩
  · simpa [Ball.errB, ApproxP, evN] using hx
  · simp [Ball.errB, evN]

theorem Ball.norm_le_of_normLe (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) {n : ℕ}
    (h : b.normLe k n = true) : ‖x‖ ≤ ‖pv‖ ^ n := by
  rcases hx with ⟨hx_approx, hx_center⟩
  have h_bound : n + 3 * b.e ≤ min (vN k b.c) b.r := by
    simpa [Ball.normLe, decide_eq_true_eq] using h
  have hn_le_vN : n + 3 * b.e ≤ vN k b.c :=
    le_trans h_bound (min_le_left _ _)
  have hn_le_r : n + 3 * b.e ≤ b.r :=
    le_trans h_bound (min_le_right _ _)
  have h_mul_bound : ‖(2 : Kv) ^ b.e * x‖ ≤ ‖pv‖ ^ (n + 3 * b.e) :=
    norm_le_pv_of_sub hx_approx (norm_evN_le hk b.c) hn_le_r hn_le_vN
  rw [norm_mul] at h_mul_bound
  rw [norm_two_pow_Kv b.e] at h_mul_bound
  rw [pow_add] at h_mul_bound
  have h_pv_pow_pos : 0 < ‖pv‖ ^ (3 * b.e) :=
    pow_pos norm_pv_pos _
  rw [mul_comm (‖pv‖ ^ n) (‖pv‖ ^ (3 * b.e))] at h_mul_bound
  exact le_of_mul_le_mul_left h_mul_bound h_pv_pow_pos

theorem Ball.norm_sub_lt_of_nearOK (hk : k.Ok) {bx bY : Ball} {x y : Kv} (hx : bx.Mem x)
    (hy : bY.Mem y) (h : Ball.nearOK k bx bY = true) : ‖x - y‖ < ‖2 * y‖ := by
  simp only [Ball.nearOK, Bool.and_eq_true, decide_eq_true_eq] at h
  let d := Ball.sub k bx bY
  let t := Ball.mul k (Ball.ofInt k 2) bY
  have hd : d.Mem (x - y) := Ball.mem_sub hk hx hy
  have ht : t.Mem ((2 : Kv) * y) := by
    simpa [t] using Ball.mem_mul hk (Ball.mem_ofInt hk (2 : ℤ)) hy
  have hnz : t.nz k = true := h.1
  have hlt : vN k t.c + 3 * d.e < min (vN k d.c) d.r + 3 * t.e := h.2
  set P := ‖pv‖ with hP
  have hP_pos : 0 < P := norm_pv_pos
  set m := min (vN k d.c) d.r with hm
  set vt := vN k t.c with hvt
  have hnorm_sub_le : ‖(2 : Kv) ^ d.e * (x - y)‖ ≤ P ^ m := by
    have hx_sub_y : ‖(2 : Kv) ^ d.e * (x - y) - evN d.c‖ ≤ P ^ d.r := hd.1
    have hy_bound : ‖evN d.c‖ ≤ P ^ (vN k d.c) := by
      simpa [hP] using norm_evN_le hk d.c
    have hi : m ≤ d.r := min_le_right _ _
    have hj : m ≤ vN k d.c := min_le_left _ _
    simpa [hP] using norm_le_pv_of_sub hx_sub_y hy_bound hi hj
  have hl : ‖x - y‖ * P ^ (3 * d.e) ≤ P ^ m := by
    have h_eq : ‖(2 : Kv) ^ d.e * (x - y)‖ = ‖x - y‖ * P ^ (3 * d.e) := by
      calc
        ‖(2 : Kv) ^ d.e * (x - y)‖ = ‖(2 : Kv) ^ d.e‖ * ‖x - y‖ := by rw [norm_mul]
        _ = P ^ (3 * d.e) * ‖x - y‖ := by rw [norm_two_pow_Kv, hP]
        _ = ‖x - y‖ * P ^ (3 * d.e) := by ring
    rw [h_eq] at hnorm_sub_le
    exact hnorm_sub_le
  have hnorm_2y_eq : ‖(2 : Kv) ^ t.e * ((2 : Kv) * y)‖ = P ^ vt := by
    simpa [hP, hvt] using Ball.norm_eq_of_nz hk ht hnz
  have hr : ‖(2 : Kv) * y‖ * P ^ (3 * t.e) = P ^ vt := by
    calc
      ‖(2 : Kv) * y‖ * P ^ (3 * t.e) = ‖(2 : Kv) * y‖ * ‖(2 : Kv) ^ t.e‖ := by rw [norm_two_pow_Kv, hP]
      _ = ‖(2 : Kv) ^ t.e * ((2 : Kv) * y)‖ := by simp [norm_mul, mul_comm]
      _ = P ^ vt := hnorm_2y_eq
  have hQ_pos : 0 < P ^ (3 * d.e + 3 * t.e) := pow_pos hP_pos _
  have h1 : ‖x - y‖ * P ^ (3 * d.e + 3 * t.e) ≤ P ^ (m + 3 * t.e) := by
    calc
      ‖x - y‖ * P ^ (3 * d.e + 3 * t.e) = ‖x - y‖ * (P ^ (3 * d.e) * P ^ (3 * t.e)) := by rw [pow_add]
      _ = (‖x - y‖ * P ^ (3 * d.e)) * P ^ (3 * t.e) := by ring
      _ ≤ P ^ m * P ^ (3 * t.e) := mul_le_mul_of_nonneg_right hl (pow_nonneg (norm_nonneg _) _)
      _ = P ^ (m + 3 * t.e) := by rw [pow_add]
  have h2 : P ^ (m + 3 * t.e) < P ^ (vt + 3 * d.e) := by
    have h_lt : vt + 3 * d.e < m + 3 * t.e := hlt
    exact pv_pow_lt_pv_pow h_lt
  have h3 : P ^ (vt + 3 * d.e) = ‖(2 : Kv) * y‖ * P ^ (3 * d.e + 3 * t.e) := by
    calc
      P ^ (vt + 3 * d.e) = P ^ vt * P ^ (3 * d.e) := by rw [pow_add]
      _ = (‖(2 : Kv) * y‖ * P ^ (3 * t.e)) * P ^ (3 * d.e) := by rw [← hr]
      _ = ‖(2 : Kv) * y‖ * (P ^ (3 * t.e) * P ^ (3 * d.e)) := by ring
      _ = ‖(2 : Kv) * y‖ * P ^ (3 * t.e + 3 * d.e) := by rw [pow_add]
      _ = ‖(2 : Kv) * y‖ * P ^ (3 * d.e + 3 * t.e) := by ring
  have h_ineq : ‖x - y‖ * P ^ (3 * d.e + 3 * t.e) < ‖(2 : Kv) * y‖ * P ^ (3 * d.e + 3 * t.e) :=
    h1.trans_lt (h2.trans_eq h3)
  have h_goal : ‖x - y‖ * P ^ (3 * d.e + 3 * t.e) < ‖2 * y‖ * P ^ (3 * d.e + 3 * t.e) := by
    simpa using h_ineq
  exact lt_of_mul_lt_mul_right h_goal hQ_pos.le

theorem Ball.norm_mul_le_of_normLeMul (hk : k.Ok) {bx bY : Ball} {x y : Kv} (hx : bx.Mem x)
    (hy : bY.Mem y) {a : ℕ} (h : Ball.normLeMul k bx bY a = true) : ‖x‖ * ‖pv‖ ^ a ≤ ‖y‖ := by
  have h_and : bY.nz k = true ∧ vN k bY.c + 3 * bx.e ≤ min (vN k bx.c) bx.r + a + 3 * bY.e := by
    simpa [Ball.normLeMul] using h
  have h_nz : bY.nz k = true := h_and.1
  have hineq : vN k bY.c + 3 * bx.e ≤ min (vN k bx.c) bx.r + a + 3 * bY.e := h_and.2
  have hx_bound : ‖(2 : Kv) ^ bx.e * x‖ ≤ ‖pv‖ ^ min (vN k bx.c) bx.r :=
    norm_le_pv_of_sub hx.1 (norm_evN_le hk bx.c) (min_le_right _ _) (min_le_left _ _)
  have hy_eq : ‖(2 : Kv) ^ bY.e * y‖ = ‖pv‖ ^ vN k bY.c :=
    Ball.norm_eq_of_nz hk hy h_nz
  have hx_bound' : ‖pv‖ ^ (3 * bx.e) * ‖x‖ ≤ ‖pv‖ ^ min (vN k bx.c) bx.r := by
    calc
      ‖pv‖ ^ (3 * bx.e) * ‖x‖ = ‖(2 : Kv) ^ bx.e‖ * ‖x‖ := by rw [norm_two_pow_Kv]
      _ = ‖(2 : Kv) ^ bx.e * x‖ := by rw [norm_mul]
      _ ≤ ‖pv‖ ^ min (vN k bx.c) bx.r := hx_bound
  have hy_eq' : ‖pv‖ ^ (3 * bY.e) * ‖y‖ = ‖pv‖ ^ vN k bY.c := by
    calc
      ‖pv‖ ^ (3 * bY.e) * ‖y‖ = ‖(2 : Kv) ^ bY.e‖ * ‖y‖ := by rw [norm_two_pow_Kv]
      _ = ‖(2 : Kv) ^ bY.e * y‖ := by rw [norm_mul]
      _ = ‖pv‖ ^ vN k bY.c := hy_eq
  have hpv_pos : 0 < ‖pv‖ := norm_pv_pos
  have hP_pos : 0 < ‖pv‖ ^ (3 * bx.e) * ‖pv‖ ^ (3 * bY.e) := by
    have h1 : 0 < ‖pv‖ ^ (3 * bx.e) := pow_pos hpv_pos _
    have h2 : 0 < ‖pv‖ ^ (3 * bY.e) := pow_pos hpv_pos _
    exact mul_pos h1 h2
  apply le_of_mul_le_mul_right ?_ hP_pos
  calc
    (‖x‖ * ‖pv‖ ^ a) * (‖pv‖ ^ (3 * bx.e) * ‖pv‖ ^ (3 * bY.e))
        = ‖pv‖ ^ (3 * bx.e) * ‖x‖ * ‖pv‖ ^ a * ‖pv‖ ^ (3 * bY.e) := by ring
    _ ≤ (‖pv‖ ^ min (vN k bx.c) bx.r) * ‖pv‖ ^ a * ‖pv‖ ^ (3 * bY.e) := by
      have h_nonneg_a : 0 ≤ ‖pv‖ ^ a := pow_nonneg (norm_nonneg _) _
      have h_mul1 : (‖pv‖ ^ (3 * bx.e) * ‖x‖) * ‖pv‖ ^ a ≤ (‖pv‖ ^ min (vN k bx.c) bx.r) * ‖pv‖ ^ a :=
        mul_le_mul_of_nonneg_right hx_bound' h_nonneg_a
      have h_nonneg_bY : 0 ≤ ‖pv‖ ^ (3 * bY.e) := pow_nonneg (norm_nonneg _) _
      exact mul_le_mul_of_nonneg_right h_mul1 h_nonneg_bY
    _ = (‖pv‖ ^ min (vN k bx.c) bx.r * ‖pv‖ ^ a) * ‖pv‖ ^ (3 * bY.e) := by ring
    _ = ‖pv‖ ^ (min (vN k bx.c) bx.r + a + 3 * bY.e) := by
      rw [← pow_add, ← pow_add]
    _ ≤ ‖pv‖ ^ (vN k bY.c + 3 * bx.e) := pv_pow_le_pv_pow hineq
    _ = ‖pv‖ ^ vN k bY.c * ‖pv‖ ^ (3 * bx.e) := by rw [pow_add]
    _ = (‖pv‖ ^ (3 * bY.e) * ‖y‖) * ‖pv‖ ^ (3 * bx.e) := by rw [hy_eq']
    _ = ‖y‖ * (‖pv‖ ^ (3 * bx.e) * ‖pv‖ ^ (3 * bY.e)) := by ring

theorem Ball.eq_of_nearOK (hk : k.Ok) {bx bY : Ball} {x y : Kv} (hx : bx.Mem x) (hy : bY.Mem y)
    (h2 : x ^ 2 = y ^ 2) (h : Ball.nearOK k bx bY = true) : x = y :=
  eq_of_sq_eq_of_norm_sub_lt h2 (Ball.norm_sub_lt_of_nearOK hk hx hy h)

end Balls

end FurioLombardo.Discharge.KvArith
