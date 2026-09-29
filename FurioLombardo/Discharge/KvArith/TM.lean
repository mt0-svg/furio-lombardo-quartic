import Mathlib
import FurioLombardo.Discharge.KvArith.BallOps
import FurioLombardo.Discharge.KvArith.Comp.TM

/-!
# Taylor models over `K_v` with fixed coefficients (lane lean-kv-arith, D2)

A Taylor model of order `n` over a set `H ⊆ pv^η O_v` (`TCtx.Dom`) is `M = ⟨[C₀, ..., C_l], R⟩`
(balls). `EnclC T H M cs F`: the fixed coefficients `cs` lie in the balls `M.cs`, and for every `h ∈ H`
there is `ρ ∈ R` with `F h = Σ cᵢ hⁱ + h^(n+1) ρ`. `EnclF` forgets `cs`; the pointwise predicate `Encl`
(coefficients depending on `h`, the semantics of code/covering/taylor_model_probe.gp) follows (`EnclF.encl`).
Fixed coefficients give remainders `O(h^(n+1))` uniformly in `h`, as the tail boxes need.

* `TM.add`, `TM.sub`, `TM.neg`: coefficientwise; `TM.mul`: `Ops.conv` of the coefficient balls, truncated
  at degree `n` (so the exact coefficients are `Ops.pmul`), the part of degree `> n` and the products with
  the remainders moved into `R`, `h^j` replaced by the ball `hpw j` of radius `j η`;
* `TM.cst b`: a constant in `b`; `TM.rem b`: `h^(n+1) G(h)` for `G` with values in `b`; `TM.var`: `h`;
* `TM.inv`, `TM.sqrt`, `TM.root`: the coefficients are the formal inverse, square root and implicit root
  (`Ops.invSeries`, `Ops.sqrtSeries`, `Ops.rootSeries` run on balls, which enclose the exact formal series
  of the exact coefficients), so the residual `F P - 1`, `A - P²`, `F(t₀ + t₁ h, P)` is exactly
  `h^(n+1)` times its remainder, and the remainder of the result is that remainder times a ball of
  `1/F`, `1/(r + P)`, `1/G` (`G` the divided difference);
* `TM.ball`, `TM.split`: the ball of `F h`, and `F h = Σ_{i<j} cᵢ hⁱ + h^j q` with `q` in a ball;
  `TM.incl`: inclusion.

`rel_tmOps`: Taylor models follow the pairs (truncated exact series, function) of
`(polyOps (fieldOps Kv) n).prod (funOps H)` along `EnclC`, so every program of `Ops.lean` runs on Taylor
models.
-/

namespace FurioLombardo.Discharge.KvArith

open FurioLombardo.Discharge.M4Cert

/-- `H` lies in `pv^η O_v`. -/
def TCtx.Dom (T : TCtx) (H : Set Kv) : Prop := ∀ h ∈ H, ‖h‖ ≤ ‖pv‖ ^ T.η

/-- **Enclosure with the given fixed coefficients** `cs` of `F` on `H` by `M`. -/
def EnclC (T : TCtx) (H : Set Kv) (M : TM) (cs : List Kv) (F : Kv → Kv) : Prop :=
  List.Forall₂ (fun x b => Ball.Mem b x) cs M.cs ∧
    ∀ h ∈ H, ∃ ρ : Kv, M.R.Mem ρ ∧ F h = (fieldOps Kv).horner cs h + h ^ (T.n + 1) * ρ

/-- **Enclosure with fixed coefficients** of `F` on `H` by `M`. -/
def EnclF (T : TCtx) (H : Set Kv) (M : TM) (F : Kv → Kv) : Prop :=
  ∃ cs : List Kv, EnclC T H M cs F

/-- **Pointwise enclosure** of `F` on `H` by `M` (the coefficients may depend on `h`). -/
def Encl (T : TCtx) (H : Set Kv) (M : TM) (F : Kv → Kv) : Prop :=
  ∀ h ∈ H, ∃ cs : List Kv, List.Forall₂ (fun x b => Ball.Mem b x) cs M.cs ∧
    ∃ ρ : Kv, M.R.Mem ρ ∧ F h = (fieldOps Kv).horner cs h + h ^ (T.n + 1) * ρ

/-! ## Soundness -/

section Sound

variable {T : TCtx} {H : Set Kv}

/-! ### Helpers -/

theorem mem_zeroB (hk : T.k.Ok) : (TM.zeroB T).Mem 0 := by
  have := Ball.mem_ofInt hk 0
  simpa [TM.zeroB] using this

theorem fieldOps_horner_nil' (x : Kv) : (fieldOps Kv).horner [] x = 0 := fieldOps_horner_nil x

theorem mem_hpw' (hk : T.k.Ok) (hH : T.Dom H) {h : Kv} (hh : h ∈ H) (j : ℕ) :
    (TM.hpw T j).Mem (h ^ j) := by
  refine ⟨?_, ?_⟩
  · simp only [TM.hpw, ApproxP, pow_zero, one_mul]
    have e : evN (0, 0, 0) = 0 := by simp [evN]
    rw [e, sub_zero, norm_pow]
    calc ‖h‖ ^ j ≤ (‖pv‖ ^ T.η) ^ j := pow_le_pow_left₀ (norm_nonneg _) (hH h hh) j
      _ = ‖pv‖ ^ (j * T.η) := by rw [← pow_mul, mul_comm]
      _ ≤ ‖pv‖ ^ min (j * T.η) (3 * T.k.P) := pv_pow_le_pv_pow (min_le_left _ _)
  · have e : evN (0, 0, 0) = 0 := by simp [evN]
    simp only [TM.hpw]
    rw [e, norm_zero]
    positivity

theorem mem_pball (hk : T.k.Ok) (hH : T.Dom H) {cs : List Kv} {bs : List Ball}
    (hcs : List.Forall₂ (fun x b => Ball.Mem b x) cs bs) {h : Kv} (hh : h ∈ H) :
    (TM.pball T bs).Mem ((fieldOps Kv).horner cs h) := by
  have h1 := mem_hpw' hk hH hh 1
  rw [pow_one] at h1
  exact (rel_ballOps hk).horner hcs h1

theorem EnclF.encl {M : TM} {F : Kv → Kv} (h : EnclF T H M F) : Encl T H M F := by
  obtain ⟨cs, hcs, hR⟩ := h
  exact fun x hx => ⟨cs, hcs, hR x hx⟩

theorem EnclC.mono {H' : Set Kv} (hH : H' ⊆ H) {M : TM} {cs : List Kv} {F : Kv → Kv}
    (h : EnclC T H M cs F) : EnclC T H' M cs F :=
  ⟨h.1, fun x hx => h.2 x (hH hx)⟩

theorem EnclC.congr {M : TM} {cs : List Kv} {F G : Kv → Kv} (h : EnclC T H M cs F)
    (hFG : ∀ h ∈ H, F h = G h) : EnclC T H M cs G := by
  refine ⟨h.1, fun x hx => ?_⟩
  rw [← hFG x hx]
  exact h.2 x hx

theorem EnclC.cst (hk : T.k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) :
    EnclC T H (TM.cst T b) [x] (fun _ => x) := by
  refine ⟨List.Forall₂.cons hx List.Forall₂.nil, fun h _ => ⟨0, mem_zeroB hk, ?_⟩⟩
  rw [fieldOps_horner_cons, fieldOps_horner_nil]
  ring

theorem EnclC.rem (hk : T.k.Ok) {b : Ball} {G : Kv → Kv} (hG : ∀ h ∈ H, b.Mem (G h)) :
    EnclC T H (TM.rem b) [] (fun h => h ^ (T.n + 1) * G h) := by
  refine ⟨List.Forall₂.nil, fun h hh => ⟨G h, hG h hh, ?_⟩⟩
  rw [fieldOps_horner_nil, zero_add]

theorem EnclC.var (hk : T.k.Ok) : EnclC T H (TM.var T) [0, 1] id := by
  have h1 := Ball.mem_ofInt hk 1
  rw [Int.cast_one] at h1
  refine ⟨List.Forall₂.cons (mem_zeroB hk) (List.Forall₂.cons h1 List.Forall₂.nil),
    fun h _ => ⟨0, mem_zeroB hk, ?_⟩⟩
  rw [fieldOps_horner_cons, fieldOps_horner_cons, fieldOps_horner_nil]
  simp

theorem EnclC.add (hk : T.k.Ok) {M N : TM} {cs ds : List Kv} {F G : Kv → Kv}
    (hF : EnclC T H M cs F) (hG : EnclC T H N ds G) :
    EnclC T H (TM.add T M N) ((fieldOps Kv).zipAdd cs ds) (fun h => F h + G h) := by
  refine ⟨(rel_ballOps hk).zipAdd hF.1 hG.1, fun h hh => ?_⟩
  obtain ⟨ρ, hρ, hFρ⟩ := hF.2 h hh
  obtain ⟨σ, hσ, hGσ⟩ := hG.2 h hh
  refine ⟨ρ + σ, Ball.mem_add hk hρ hσ, ?_⟩
  dsimp only
  rw [fieldOps_horner_zipAdd, hFρ, hGσ]
  ring

theorem EnclC.sub (hk : T.k.Ok) {M N : TM} {cs ds : List Kv} {F G : Kv → Kv}
    (hF : EnclC T H M cs F) (hG : EnclC T H N ds G) :
    EnclC T H (TM.sub T M N) ((fieldOps Kv).zipSub cs ds) (fun h => F h - G h) := by
  refine ⟨(rel_ballOps hk).zipSub hF.1 hG.1, fun h hh => ?_⟩
  obtain ⟨ρ, hρ, hFρ⟩ := hF.2 h hh
  obtain ⟨σ, hσ, hGσ⟩ := hG.2 h hh
  refine ⟨ρ - σ, Ball.mem_sub hk hρ hσ, ?_⟩
  dsimp only
  rw [fieldOps_horner_zipSub, hFρ, hGσ]
  ring

theorem EnclC.neg (hk : T.k.Ok) {M : TM} {cs : List Kv} {F : Kv → Kv} (hF : EnclC T H M cs F) :
    EnclC T H (TM.neg T M) (cs.map Neg.neg) (fun h => -F h) := by
  refine ⟨?_, fun h hh => ?_⟩
  · change List.Forall₂ _ (cs.map Neg.neg) (M.cs.map (Ball.neg T.k))
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hF.1.imp fun {_ _} hx => by simpa [fieldOps] using Ball.mem_neg hk hx
  · obtain ⟨ρ, hρ, hFρ⟩ := hF.2 h hh
    refine ⟨-ρ, Ball.mem_neg hk hρ, ?_⟩
    dsimp only
    rw [fieldOps_horner_eq_polyOf, polyOf_map_neg, Polynomial.eval_neg, ← fieldOps_horner_eq_polyOf,
      hFρ]
    ring

theorem mem_hpw (hk : T.k.Ok) (hH : T.Dom H) {h : Kv} (hh : h ∈ H) (j : ℕ) :
    (TM.hpw T j).Mem (h ^ j) :=
  mem_hpw' hk hH hh j

theorem Encl.mem_ball (hk : T.k.Ok) (hH : T.Dom H) {M : TM} {F : Kv → Kv} (hF : Encl T H M F)
    {h : Kv} (hh : h ∈ H) : (TM.ball T M).Mem (F h) := by
  obtain ⟨cs, hcs, ρ, hρ, hFρ⟩ := hF h hh
  rw [hFρ]
  exact Ball.mem_add hk (mem_pball hk hH hcs hh) (Ball.mem_mul hk (mem_hpw' hk hH hh _) hρ)

section EnclC_mul_aux
open List

theorem EnclC_mul_aux1 {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {n : Nat}
    (h : Forall₂ R l₁ l₂) : Forall₂ R (l₁.take n) (l₂.take n) := by
  induction' n with k ih generalizing l₁ l₂
  · simp
  · cases l₁ with
    | nil =>
      cases l₂ with
      | nil => simp
      | cons b l₂' =>
        cases h
    | cons a l₁' =>
      cases l₂ with
      | nil =>
        cases h
      | cons b l₂' =>
        have h1 : (a :: l₁').take (k + 1) = a :: l₁'.take k := by simp
        have h2 : (b :: l₂').take (k + 1) = b :: l₂'.take k := by simp
        simp [h1, h2]
        cases h with
        | cons hhead htail =>
          exact ⟨hhead, ih htail⟩
end EnclC_mul_aux

theorem EnclC.mul (hk : T.k.Ok) (hH : T.Dom H) {M N : TM} {cs ds : List Kv} {F G : Kv → Kv}
    (hF : EnclC T H M cs F) (hG : EnclC T H N ds G) :
    EnclC T H (TM.mul T M N) ((fieldOps Kv).pmul T.n cs ds) (fun h => F h * G h) := by
  rcases hF with ⟨hFcs, hFrem⟩
  rcases hG with ⟨hGcs, hGrem⟩
  -- First goal: List.Forall₂
  have hconv : List.Forall₂ (fun x b => Ball.Mem b x) ((fieldOps Kv).conv cs ds) ((ballOps T.k).conv M.cs N.cs) := by
    -- from rel_ballOps hk and hFcs, hGcs using Ops.Rel.conv
    exact (rel_ballOps hk).conv hFcs hGcs
  have hpmul : List.Forall₂ (fun x b => Ball.Mem b x) ((fieldOps Kv).pmul T.n cs ds) (((ballOps T.k).conv M.cs N.cs).take (T.n + 1)) := by
    have := EnclC_mul_aux1 (n := T.n + 1) hconv
    simpa [Ops.pmul] using this
  -- Now we need to construct the EnclC
  refine ⟨?_, ?_⟩
  · -- List.Forall₂ part
    -- (TM.mul T M N).cs = ((ballOps T.k).conv M.cs N.cs).take (T.n + 1) by definition
    -- (fieldOps Kv).pmul T.n cs ds = ((fieldOps Kv).conv cs ds).take (T.n + 1) by definition
    simpa [TM.mul, Ops.pmul] using hpmul
  · -- Remainder part
    intro h hh
    rcases hFrem h hh with ⟨ρ, hρM, hFh⟩
    rcases hGrem h hh with ⟨σ, hσN, hGh⟩
    -- hFh : F h = (fieldOps Kv).horner cs h + h ^ (T.n + 1) * ρ
    -- hGh : G h = (fieldOps Kv).horner ds h + h ^ (T.n + 1) * σ
    set P := (fieldOps Kv).horner cs h with hP
    set Q := (fieldOps Kv).horner ds h with hQ
    set drop_conv := ((fieldOps Kv).conv cs ds).drop (T.n + 1) with hdrop_conv
    set ρ' := (fieldOps Kv).horner drop_conv h + ρ * Q + σ * P + h ^ (T.n + 1) * (ρ * σ) with hρ'
    -- Need to show: (TM.mul T M N).R.Mem ρ' and the equation
    have h_eq : F h * G h = (fieldOps Kv).horner ((fieldOps Kv).pmul T.n cs ds) h + h ^ (T.n + 1) * ρ' := by
      calc
        F h * G h = (P + h ^ (T.n + 1) * ρ) * (Q + h ^ (T.n + 1) * σ) := by rw [hFh, hGh, hP, hQ]
        _ = P * Q + h ^ (T.n + 1) * (ρ * Q + σ * P) + h ^ (T.n + 1) * (h ^ (T.n + 1) * (ρ * σ)) := by ring_nf
        _ = P * Q + h ^ (T.n + 1) * (ρ * Q + σ * P + h ^ (T.n + 1) * (ρ * σ)) := by ring_nf
        _ = ((fieldOps Kv).horner ((fieldOps Kv).conv cs ds) h) + h ^ (T.n + 1) * (ρ * Q + σ * P + h ^ (T.n + 1) * (ρ * σ)) := by
          rw [hP, hQ, fieldOps_horner_conv cs ds h]
        _ = (((fieldOps Kv).horner (((fieldOps Kv).conv cs ds).take (T.n + 1)) h) +
             h ^ (T.n + 1) * (fieldOps Kv).horner (((fieldOps Kv).conv cs ds).drop (T.n + 1)) h) +
            h ^ (T.n + 1) * (ρ * Q + σ * P + h ^ (T.n + 1) * (ρ * σ)) := by rw [fieldOps_horner_split ((fieldOps Kv).conv cs ds) (T.n + 1) h]
        _ = (fieldOps Kv).horner (((fieldOps Kv).conv cs ds).take (T.n + 1)) h +
            h ^ (T.n + 1) * ((fieldOps Kv).horner (((fieldOps Kv).conv cs ds).drop (T.n + 1)) h +
            ρ * Q + σ * P + h ^ (T.n + 1) * (ρ * σ)) := by ring
        _ = (fieldOps Kv).horner ((fieldOps Kv).pmul T.n cs ds) h + h ^ (T.n + 1) * ρ' := by
          simp [Ops.pmul, hρ', hdrop_conv]
    -- Now we need to show (TM.mul T M N).R.Mem ρ'
    -- (TM.mul T M N).R = Ball.add T.k R1 R2
    -- where R1 = hi + M.R * pball N.cs
    --       R2 = N.R * pball M.cs + hpw (n+1) * (M.R * N.R)
    --       hi = pball (C.drop (n+1)) and C = (ballOps T.k).conv M.cs N.cs
    -- So we need to decompose ρ' into parts that belong to each sub-ball
    have h_mem : (TM.mul T M N).R.Mem ρ' := by
      dsimp [TM.mul, ρ']
      have h_drop_forall : List.Forall₂ (fun x b => Ball.Mem b x) (((fieldOps Kv).conv cs ds).drop (T.n + 1)) (((ballOps T.k).conv M.cs N.cs).drop (T.n + 1)) :=
        List.forall₂_drop (T.n + 1) hconv
      have hA : (TM.pball T (((ballOps T.k).conv M.cs N.cs).drop (T.n + 1))).Mem ((fieldOps Kv).horner (((fieldOps Kv).conv cs ds).drop (T.n + 1)) h) :=
        mem_pball hk hH h_drop_forall hh
      have hB : (Ball.mul T.k M.R (TM.pball T N.cs)).Mem (ρ * Q) := by
        have hQ : (TM.pball T N.cs).Mem Q := mem_pball hk hH hGcs hh
        exact Ball.mem_mul hk hρM hQ
      have hC : (Ball.mul T.k N.R (TM.pball T M.cs)).Mem (σ * P) := by
        have hP : (TM.pball T M.cs).Mem P := mem_pball hk hH hFcs hh
        exact Ball.mem_mul hk hσN hP
      have hD : (Ball.mul T.k (TM.hpw T (T.n + 1)) (Ball.mul T.k M.R N.R)).Mem (h ^ (T.n + 1) * (ρ * σ)) := by
        have h_hpw : (TM.hpw T (T.n + 1)).Mem (h ^ (T.n + 1)) := mem_hpw hk hH hh (T.n + 1)
        have h_ρσ : (Ball.mul T.k M.R N.R).Mem (ρ * σ) := Ball.mem_mul hk hρM hσN
        exact Ball.mem_mul hk h_hpw h_ρσ
      have hAB : (Ball.add T.k (TM.pball T (((ballOps T.k).conv M.cs N.cs).drop (T.n + 1)))
          (Ball.mul T.k M.R (TM.pball T N.cs))).Mem
          ((fieldOps Kv).horner (((fieldOps Kv).conv cs ds).drop (T.n + 1)) h + ρ * Q) :=
        Ball.mem_add hk hA hB
      have hCD : (Ball.add T.k (Ball.mul T.k N.R (TM.pball T M.cs))
          (Ball.mul T.k (TM.hpw T (T.n + 1)) (Ball.mul T.k M.R N.R))).Mem
          (σ * P + h ^ (T.n + 1) * (ρ * σ)) :=
        Ball.mem_add hk hC hD
      have hABCD : (Ball.add T.k (Ball.add T.k (TM.pball T (((ballOps T.k).conv M.cs N.cs).drop (T.n + 1)))
          (Ball.mul T.k M.R (TM.pball T N.cs)))
          (Ball.add T.k (Ball.mul T.k N.R (TM.pball T M.cs))
            (Ball.mul T.k (TM.hpw T (T.n + 1)) (Ball.mul T.k M.R N.R)))).Mem
          (((fieldOps Kv).horner (((fieldOps Kv).conv cs ds).drop (T.n + 1)) h + ρ * Q) +
            (σ * P + h ^ (T.n + 1) * (ρ * σ))) :=
        Ball.mem_add hk hAB hCD
      simpa [add_comm, add_left_comm, add_assoc] using hABCD
    exact ⟨ρ', h_mem, h_eq⟩

theorem EnclC.trunc (hk : T.k.Ok) (hH : T.Dom H) {M : TM} {cs : List Kv} {F : Kv → Kv}
    (hF : EnclC T H M cs F) : EnclC T H (TM.trunc T M) (cs.take (T.n + 1)) F := by
  refine ⟨List.forall₂_take _ hF.1, fun h hh => ?_⟩
  obtain ⟨ρ, hρ, hFρ⟩ := hF.2 h hh
  refine ⟨(fieldOps Kv).horner (cs.drop (T.n + 1)) h + ρ,
    Ball.mem_add hk (mem_pball hk hH (List.forall₂_drop _ hF.1) hh) hρ, ?_⟩
  rw [hFρ, fieldOps_horner_split cs (T.n + 1) h]
  ring

/-- **Soundness of the inverse**: `F` has no zero on `H`, and the exact formal inverse encloses `1/F`. -/
theorem EnclC.inv (hk : T.k.Ok) (hH : T.Dom H) {M M' : TM} {cs : List Kv} {F : Kv → Kv}
    (hF : EnclC T H M cs F) (h : TM.inv T M = some M') :
    (∀ h ∈ H, F h ≠ 0) ∧ ∃ ds, (fieldOps Kv).invSeries T.n cs = some ds ∧
      EnclC T H M' ds (fun h => (F h)⁻¹) := by
  -- Let M1 be the truncated version
  set M1 := TM.trunc T M with hM1_def
  have hF_trunc : EnclC T H M1 (cs.take (T.n + 1)) F :=
    EnclC.trunc hk hH hF
  -- Save the components of hF_trunc before consuming
  rcases hF_trunc with ⟨h_forall_ball, h_rep_trunc⟩
  -- h_forall_ball : List.Forall₂ (fun x b => Ball.Mem b x) (cs.take (T.n + 1)) M1.cs
  -- h_rep_trunc : ∀ h ∈ H, ∃ ρ : Kv, M1.R.Mem ρ ∧ F h = (fieldOps Kv).horner (cs.take (T.n + 1)) h + h ^ (T.n + 1) * ρ
  -- From h : TM.inv T M = some M', extract the components of the inverse
  have h_inv_eq : TM.inv T M = some M' := h
  unfold TM.inv at h_inv_eq
  dsimp at h_inv_eq
  -- h_inv_eq : ((ballOps T.k).inv (ball T M1)).bind (fun gbi => ...) = some M'
  rcases Option.bind_eq_some_iff.mp h_inv_eq with ⟨gbi, hgbi, h_rest⟩
  -- hgbi : (ballOps T.k).inv (ball T M1) = some gbi
  rcases Option.bind_eq_some_iff.mp h_rest with ⟨ds_ball, hds_ball, hM'⟩
  -- hds_ball : (ballOps T.k).invSeries T.n M1.cs = some ds_ball
  -- hM' : (let E := TM.mul T M1 ⟨ds_ball, TM.zeroB T⟩; some ⟨ds_ball, Ball.neg T.k (Ball.mul T.k E.R gbi)⟩) = some M'
  -- Extract M' = ... from hM'
  have hM'_eq : M' = ⟨ds_ball, Ball.neg T.k (Ball.mul T.k (TM.mul T M1 ⟨ds_ball, TM.zeroB T⟩).R gbi)⟩ := by
    have := (Option.some.inj hM').symm
    simpa [hM1_def] using this
  -- Now we have gbi and ds_ball
  -- Part 1: ∀ h ∈ H, F h ≠ 0, and also save gbi.Mem (F h)⁻¹
  have h_nonzero : ∀ h ∈ H, F h ≠ 0 := by
    intro h hh
    -- From h_rep_trunc, we have the representation of F h
    rcases h_rep_trunc h hh with ⟨ρ, hρ_mem, hF_rep⟩
    -- hF_rep : F h = (fieldOps Kv).horner (cs.take (T.n + 1)) h + h ^ (T.n + 1) * ρ
    -- Use rel_ballOps to get the field inverse
    have h_ball_mem : (TM.ball T M1).Mem (F h) := by
      -- From Encl.mem_ball via EnclF.encl
      have h_enclF : EnclF T H M1 F := ⟨cs.take (T.n + 1), ⟨h_forall_ball, h_rep_trunc⟩⟩
      have h_encl : Encl T H M1 F := EnclF.encl h_enclF
      exact Encl.mem_ball hk hH h_encl hh
    -- Now use rel_ballOps hk to transfer the inverse
    have h_rel := rel_ballOps hk
    -- h_rel : Ops.Rel (fieldOps Kv) (ballOps T.k) (fun x b => b.Mem x)
    -- The inv case: if R x a and p.inv a = some b, then ∃ y, o.inv x = some y ∧ R y b
    rcases h_rel.inv h_ball_mem hgbi with ⟨y, hy_inv, hy_mem⟩
    -- hy_inv : (fieldOps Kv).inv (F h) = some y
    -- hy_mem : gbi.Mem y
    rcases fieldOps_inv_eq_some hy_inv with ⟨hF_ne, hy_eq⟩
    -- hF_ne : F h ≠ 0, hF_ne is exactly what we need
    exact hF_ne
  -- Save the gbi.Mem (F h)⁻¹ fact for later use
  have h_gbi_inv : ∀ h ∈ H, gbi.Mem ((F h)⁻¹) := by
    intro h hh
    rcases h_rep_trunc h hh with ⟨ρ, hρ_mem, hF_rep⟩
    have h_ball_mem : (TM.ball T M1).Mem (F h) := by
      have h_enclF : EnclF T H M1 F := ⟨cs.take (T.n + 1), ⟨h_forall_ball, h_rep_trunc⟩⟩
      have h_encl : Encl T H M1 F := EnclF.encl h_enclF
      exact Encl.mem_ball hk hH h_encl hh
    have h_rel := rel_ballOps hk
    rcases h_rel.inv h_ball_mem hgbi with ⟨y, hy_inv, hy_mem⟩
    rcases fieldOps_inv_eq_some hy_inv with ⟨hF_ne, hy_eq⟩
    rw [← hy_eq]
    exact hy_mem
  -- Part 2: ∃ ds, (fieldOps Kv).invSeries T.n cs = some ds ∧ EnclC T H M' ds (fun h => (F h)⁻¹)
  -- First, get the field inverse series from the ball one using Ops.Rel.invSeries
  have h_invSeries_rel := (rel_ballOps hk).invSeries T.n h_forall_ball
  -- h_invSeries_rel : OptRel (List.Forall₂ (fun x b => b.Mem x)) ((fieldOps Kv).invSeries T.n (cs.take (T.n + 1))) ((ballOps T.k).invSeries T.n M1.cs)
  -- i.e., OptRel ... (some ds_field) (some ds_ball)
  have h_invSeries_rel' : OptRel (List.Forall₂ (fun x b => b.Mem x)) ((fieldOps Kv).invSeries T.n (cs.take (T.n + 1))) (some ds_ball) := by
    rw [← hds_ball]
    exact h_invSeries_rel
  -- From OptRel definition, taking b := ds_ball
  rcases h_invSeries_rel' ds_ball rfl with ⟨ds_field, hds_field, h_forall_field⟩
  -- hds_field : (fieldOps Kv).invSeries T.n (cs.take (T.n + 1)) = some ds_field
  -- h_forall_field : List.Forall₂ (fun x b => b.Mem x) ds_field ds_ball
  -- Now use Ops.invSeries_take to relate to cs
  have hds_field_cs : (fieldOps Kv).invSeries T.n cs = some ds_field := by
    rw [← Ops.invSeries_take (fieldOps Kv) T.n cs]
    exact hds_field
  -- Now we need to show EnclC T H M' ds_field (fun h => (F h)⁻¹)
  -- First, relate M' to ds_ball and ds_field
  -- M' = ⟨ds_ball, Ball.neg T.k (Ball.mul T.k E.R gbi)⟩
  -- where E = TM.mul T M1 ⟨ds_ball, TM.zeroB T⟩
  -- We have List.Forall₂ (fun x b => b.Mem x) ds_field ds_ball
  -- i.e., List.Forall₂ (fun x b => Ball.Mem b x) ds_field ds_ball
  -- For EnclC, we need List.Forall₂ (fun x b => Ball.Mem b x) ds_field M'.cs
  -- Since M'.cs = ds_ball, this is exactly h_forall_field
  have h_forall_encl : List.Forall₂ (fun x b => Ball.Mem b x) ds_field M'.cs := by
    rw [hM'_eq]
    -- Now we need List.Forall₂ (fun x b => Ball.Mem b x) ds_field ds_ball
    -- But h_forall_field is List.Forall₂ (fun x b => b.Mem x) ds_field ds_ball
    -- And b.Mem x = Ball.Mem b x
    simpa using h_forall_field
  -- Now we need the second part of EnclC: for all h ∈ H, ∃ ρ, M'.R.Mem ρ ∧ (F h)⁻¹ = horner ds_field h + h^(n+1) * ρ
  -- Set up E and q
  set E := TM.mul T M1 ⟨ds_ball, TM.zeroB T⟩ with hE_def
  set q := (fieldOps Kv).pmul T.n (cs.take (T.n + 1)) ds_field with hq_def
  -- Reconstruct hF_trunc for EnclC.mul
  have hF_trunc' : EnclC T H M1 (cs.take (T.n + 1)) F := ⟨h_forall_ball, h_rep_trunc⟩
  -- EnclC for ⟨ds_ball, zeroB⟩ with coefficients ds_field and function horner ds_field
  have h_zero : EnclC T H ⟨ds_ball, TM.zeroB T⟩ ds_field (fun h => (fieldOps Kv).horner ds_field h) := by
    refine ⟨?_, ?_⟩
    · -- List.Forall₂ (fun x b => Ball.Mem b x) ds_field ds_ball
      simpa using h_forall_field
    · intro h hh
      refine ⟨0, mem_zeroB hk, ?_⟩
      simp
  -- Multiply: F h * horner ds_field h is enclosed by E with coefficients q
  have h_mul : EnclC T H E q (fun h => F h * (fieldOps Kv).horner ds_field h) :=
    EnclC.mul hk hH hF_trunc' h_zero
  -- From invSeries_spec, get the polynomial relation
  rcases invSeries_spec hds_field with ⟨h_len, h_poly⟩
  -- h_poly : Polynomial.X ^ (T.n + 1) ∣ polyOf (cs.take (T.n + 1)) * polyOf ds_field - 1
  rcases h_poly with ⟨P, hP⟩
  -- hP : polyOf (cs.take (T.n + 1)) * polyOf ds_field - 1 = Polynomial.X ^ (T.n + 1) * P
  -- So polyOf (cs.take (T.n + 1)) * polyOf ds_field = 1 + Polynomial.X ^ (T.n + 1) * P
  have h_poly_prod (h : Kv) : (polyOf (cs.take (T.n + 1)) * polyOf ds_field).eval h = 1 + h ^ (T.n + 1) * P.eval h := by
    have htemp := congrArg (fun p : Polynomial Kv => p.eval h) hP
    -- htemp: (polyOf ... * polyOf ds_field - 1).eval h = (Polynomial.X^(n+1) * P).eval h
    have htemp' := by
      simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one] using htemp
    -- htemp': (polyOf ... * polyOf ds_field).eval h - 1 = h^(n+1) * P.eval h
    calc
      (polyOf (cs.take (T.n + 1)) * polyOf ds_field).eval h
          = ((polyOf (cs.take (T.n + 1)) * polyOf ds_field).eval h - 1) + 1 := by
        rw [sub_add_cancel]
      _ = (h ^ (T.n + 1) * P.eval h) + 1 := by
        rw [Polynomial.eval_mul, htemp']
      _ = 1 + h ^ (T.n + 1) * P.eval h := add_comm _ _
  -- Translate to horner
  have h_horner_prod (h : Kv) : (fieldOps Kv).horner (cs.take (T.n + 1)) h * (fieldOps Kv).horner ds_field h =
      1 + h ^ (T.n + 1) * P.eval h := by
    calc
      (fieldOps Kv).horner (cs.take (T.n + 1)) h * (fieldOps Kv).horner ds_field h
          = ((polyOf (cs.take (T.n + 1))).eval h) * ((polyOf ds_field).eval h) := by
        simp [fieldOps_horner_eq_polyOf]
      _ = (polyOf (cs.take (T.n + 1)) * polyOf ds_field).eval h := by simp
      _ = 1 + h ^ (T.n + 1) * P.eval h := h_poly_prod h
  -- Now prove that polyOf q = 1 using the degree argument
  have h_poly_q_one : Polynomial.X ^ (T.n + 1) ∣ polyOf q - 1 := by
    have h1 : Polynomial.X ^ (T.n + 1) ∣ polyOf q - polyOf (cs.take (T.n + 1)) * polyOf ds_field :=
      X_pow_dvd_polyOf_pmul T.n (cs.take (T.n + 1)) ds_field
    have h2 : Polynomial.X ^ (T.n + 1) ∣ polyOf (cs.take (T.n + 1)) * polyOf ds_field - 1 := by
      rw [hP]
      exact ⟨P, rfl⟩
    have h_sub : polyOf q - 1 = (polyOf q - polyOf (cs.take (T.n + 1)) * polyOf ds_field) +
      (polyOf (cs.take (T.n + 1)) * polyOf ds_field - 1) := by ring
    rw [h_sub]
    exact dvd_add h1 h2
  -- Bound on q.length
  have h_len_q : q.length ≤ T.n + 1 := by
    rw [hq_def]
    -- q = (fieldOps Kv).pmul T.n (cs.take (T.n + 1)) ds_field
    -- = ((fieldOps Kv).conv (cs.take (T.n + 1)) ds_field).take (T.n + 1)
    -- length ≤ T.n+1 by List.length_take_le
    simpa [Ops.pmul] using List.length_take_le ((fieldOps Kv).conv (cs.take (T.n + 1)) ds_field) (T.n + 1)
  -- Therefore degree (polyOf q - 1) < T.n + 1
  have h_deg_q_sub_one : (polyOf q - 1).degree < (T.n + 1 : ℕ) := by
    have h_deg_sub_le : (polyOf q - 1).degree ≤ max (polyOf q).degree (1 : Polynomial Kv).degree :=
      Polynomial.degree_sub_le _ _
    apply lt_of_le_of_lt h_deg_sub_le
    rw [max_lt_iff]
    constructor
    · -- degree (polyOf q) < T.n+1
      have h_deg_q_lt : (polyOf q).degree < (q.length : WithBot ℕ) := degree_polyOf_lt q
      have h_len_q' : (q.length : WithBot ℕ) ≤ (T.n + 1 : ℕ) := by exact_mod_cast h_len_q
      exact lt_of_lt_of_le h_deg_q_lt h_len_q'
    · -- degree 1 < T.n+1
      have hpos : (0 : WithBot ℕ) < (T.n + 1 : ℕ) := by
        refine WithBot.coe_lt_coe.mpr ?_
        have hpos_nat : 0 < T.n + 1 := by omega
        exact hpos_nat
      simpa using hpos
  -- Hence polyOf q = 1
  have h_poly_q_eq_one : polyOf q = 1 := by
    have h_deg_X : ((Polynomial.X : Polynomial Kv) ^ (T.n + 1)).degree = (T.n + 1 : ℕ) := by simp
    have h_deg_q_sub_one' : (polyOf q - 1).degree < ((Polynomial.X : Polynomial Kv) ^ (T.n + 1)).degree := by
      rw [h_deg_X]
      exact h_deg_q_sub_one
    have h_zero : polyOf q - 1 = 0 :=
      Polynomial.eq_zero_of_dvd_of_degree_lt h_poly_q_one h_deg_q_sub_one'
    -- polyOf q - 1 = 0 → polyOf q = 1
    calc
      polyOf q = (polyOf q - 1) + 1 := by ring
      _ = 0 + 1 := by rw [h_zero]
      _ = 1 := by simp
  -- Therefore horner q h = 1
  have h_horner_q (h : Kv) : (fieldOps Kv).horner q h = 1 := by
    rw [fieldOps_horner_eq_polyOf, h_poly_q_eq_one]
    simp
  -- Now prove the second part of EnclC
  have h_encl_second : ∀ h ∈ H, ∃ ρ : Kv, M'.R.Mem ρ ∧ (F h)⁻¹ = (fieldOps Kv).horner ds_field h + h ^ (T.n + 1) * ρ := by
    intro h hh
    -- Get the representation from h_mul
    rcases h_mul with ⟨h_forall_q, h_rep_mul⟩
    rcases h_rep_mul h hh with ⟨ρ_E, hρ_E_mem, h_mul_rep⟩
    -- h_mul_rep : F h * (fieldOps Kv).horner ds_field h = (fieldOps Kv).horner q h + h ^ (T.n + 1) * ρ_E
    -- Get the representation from h_rep_trunc
    rcases h_rep_trunc h hh with ⟨ρ, hρ_mem, hF_rep⟩
    -- hF_rep : F h = (fieldOps Kv).horner (cs.take (T.n + 1)) h + h ^ (T.n + 1) * ρ
    set A := (fieldOps Kv).horner (cs.take (T.n + 1)) h with hA_def
    set B := (fieldOps Kv).horner ds_field h with hB_def
    have hF_rep' : F h = A + h ^ (T.n + 1) * ρ := hF_rep
    have h_mul_rep' : F h * B = (fieldOps Kv).horner q h + h ^ (T.n + 1) * ρ_E := h_mul_rep
    have h_horner_q_h : (fieldOps Kv).horner q h = 1 := h_horner_q h
    have h_horner_prod_h : A * B = 1 + h ^ (T.n + 1) * P.eval h := h_horner_prod h
    have hF_ne : F h ≠ 0 := h_nonzero h hh
    -- From h_horner_q_h and h_mul_rep': F h * B = 1 + h^(n+1) * ρ_E
    have h_mul_eq : F h * B = 1 + h ^ (T.n + 1) * ρ_E := by
      rw [h_horner_q_h] at h_mul_rep'
      exact h_mul_rep'
    -- Define ρ' = -ρ_E * (F h)⁻¹
    set ρ' := -ρ_E * (F h)⁻¹ with hρ'_def
    have h_inv_eq : (F h)⁻¹ = B + h ^ (T.n + 1) * ρ' := by
      rw [hρ'_def]
      -- Goal: (F h)⁻¹ = B + h^(n+1) * (-ρ_E * (F h)⁻¹)
      -- From h_mul_eq: F h * B = 1 + h^(n+1) * ρ_E
      -- So B = (F h)⁻¹ + h^(n+1) * ρ_E * (F h)⁻¹
      have hB : B = (F h)⁻¹ + h ^ (T.n + 1) * ρ_E * (F h)⁻¹ := by
        calc
          B = (F h)⁻¹ * (F h * B) := by field_simp [hF_ne]
          _ = (F h)⁻¹ * (1 + h ^ (T.n + 1) * ρ_E) := by rw [h_mul_eq]
          _ = (F h)⁻¹ + h ^ (T.n + 1) * ρ_E * (F h)⁻¹ := by ring
      -- Now (F h)⁻¹ = B - h^(n+1) * ρ_E * (F h)⁻¹ = B + h^(n+1) * (-ρ_E * (F h)⁻¹)
      rw [hB]
      ring
    -- Now we need M'.R.Mem ρ'
    -- M'.R = Ball.neg T.k (Ball.mul T.k E.R gbi)
    have h_mem : M'.R.Mem ρ' := by
      rw [hM'_eq]
      -- M'.R = Ball.neg T.k (Ball.mul T.k E.R gbi)
      -- Need: (Ball.neg T.k (Ball.mul T.k E.R gbi)).Mem (-ρ_E * (F h)⁻¹)
      -- By Ball.mem_neg hk: follows from (Ball.mul T.k E.R gbi).Mem (ρ_E * (F h)⁻¹)
      -- By Ball.mem_mul hk: follows from E.R.Mem ρ_E and gbi.Mem (F h)⁻¹
      have h_mem_mul : (Ball.mul T.k E.R gbi).Mem (ρ_E * (F h)⁻¹) :=
        Ball.mem_mul hk hρ_E_mem (h_gbi_inv h hh)
      have h_mem_neg : (Ball.neg T.k (Ball.mul T.k E.R gbi)).Mem (-(ρ_E * (F h)⁻¹)) :=
        Ball.mem_neg hk h_mem_mul
      -- -(ρ_E * (F h)⁻¹) = (-ρ_E) * (F h)⁻¹ = -ρ_E * (F h)⁻¹ = ρ'
      simpa [hρ'_def, neg_mul] using h_mem_neg
    -- Return the result
    refine ⟨ρ', h_mem, h_inv_eq⟩
  -- Combine the two parts
  refine ⟨h_nonzero, ds_field, hds_field_cs, ?_⟩
  refine ⟨h_forall_encl, h_encl_second⟩

theorem forall₂_headD_mem (hk : T.k.Ok) {cs : List Kv} {bs : List Ball}
    (h : List.Forall₂ (fun x b => Ball.Mem b x) cs bs) :
    (bs.headD (TM.zeroB T)).Mem (cs.headD 0) := by
  cases h with
  | nil => exact mem_zeroB hk
  | cons hx _ => exact hx

theorem EnclC.poly (hk : T.k.Ok) {cs : List Kv} {bs : List Ball}
    (h : List.Forall₂ (fun x b => Ball.Mem b x) cs bs) :
    EnclC T H ⟨bs, TM.zeroB T⟩ cs (fun x => (fieldOps Kv).horner cs x) :=
  ⟨h, fun x _ => ⟨0, mem_zeroB hk, by ring⟩⟩

open Polynomial in
theorem fieldOps_horner_eq_zero_of_dvd {K : Type*} [Field K] {n : ℕ} {cs : List K}
    (hl : cs.length ≤ n + 1) (hd : X ^ (n + 1) ∣ polyOf cs) (x : K) :
    (fieldOps K).horner cs x = 0 := by
  rw [fieldOps_horner_eq_polyOf, polyOf_eq_zero_of_dvd hl hd, eval_zero]

theorem sqrt_branch_eq {r P A e ρ : Kv} (hr : r ^ 2 = A) (hA : A - P ^ 2 = e * ρ) (hne : r + P ≠ 0) :
    r = P + e * (ρ * (r + P)⁻¹) := by
  field_simp
  linear_combination hr + hA

open Polynomial in
/-- The exact residual of a formal square root has no polynomial part. -/
theorem horner_zipSub_pmul_eq_zero {n : ℕ} {cs ps : List Kv}
    (hdvd : X ^ (n + 1) ∣ polyOf (cs.take (n + 1)) - polyOf ps ^ 2) (x : Kv) :
    (fieldOps Kv).horner ((fieldOps Kv).zipSub (cs.take (n + 1)) ((fieldOps Kv).pmul n ps ps)) x = 0 := by
  refine fieldOps_horner_eq_zero_of_dvd (n := n) ?_ ?_ x
  · refine le_trans (length_zipSub_le _ _ _) (max_le ?_ (length_pmul_le _ _ _ _))
    exact List.length_take_le _ _
  · rw [polyOf_zipSub]
    have h2 := X_pow_dvd_polyOf_pmul n ps ps
    have e : polyOf (cs.take (n + 1)) - polyOf ((fieldOps Kv).pmul n ps ps) =
        (polyOf (cs.take (n + 1)) - polyOf ps ^ 2) -
          (polyOf ((fieldOps Kv).pmul n ps ps) - polyOf ps * polyOf ps) := by ring
    rw [e]
    exact dvd_sub hdvd h2

/-- **Soundness of the square root**: roots exist in `rb` on `H`, and every branch with values in
`rb` is enclosed, with the same fixed coefficients. -/
theorem EnclC.sqrt (hk : T.k.Ok) (hH : T.Dom H) {M M' : TM} {cs : List Kv} {rb : Ball} {s : N3}
    {es : ℕ} {A : Kv → Kv} (hA : EnclC T H M cs A) (h : TM.sqrt T M s es = some (M', rb)) :
    (∀ h ∈ H, ∃ y : Kv, y ^ 2 = A h ∧ rb.Mem y) ∧
      ∃ ps : List Kv, ∀ r : Kv → Kv, (∀ h ∈ H, r h ^ 2 = A h ∧ rb.Mem (r h)) → EnclC T H M' ps r := by
  unfold TM.sqrt at h
  obtain ⟨r0, hr0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rb', hrb', h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨psB, hpsB, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨di, hdi, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hA1 := EnclC.trunc hk hH hA
  refine ⟨fun x hx => Ball.exists_mem_sqrt hk (Encl.mem_ball hk hH (EnclF.encl ⟨_, hA1⟩) hx) hrb', ?_⟩
  obtain ⟨p0, hp0, hp0m⟩ := Ball.exists_mem_sqrt hk (forall₂_headD_mem hk hA1.1) hr0
  obtain ⟨ps, hps, hpsF⟩ := Ops.Rel.sqrtSeries (rel_ballOps hk) T.n hA1.1 hp0m psB hpsB
  obtain ⟨-, -, hdvd⟩ := sqrtSeries_spec hp0 hps
  refine ⟨ps, fun r hr => ⟨hpsF, fun x hx => ?_⟩⟩
  have hP : EnclC T H ⟨psB, TM.zeroB T⟩ ps (fun x => (fieldOps Kv).horner ps x) := EnclC.poly hk hpsF
  have hD := EnclC.sub hk hA1 (EnclC.mul hk hH hP hP)
  obtain ⟨ρ, hρ, hρeq⟩ := hD.2 x hx
  rw [horner_zipSub_pmul_eq_zero hdvd x, zero_add] at hρeq
  have hmem := Ball.mem_add hk (hr x hx).2 (Encl.mem_ball hk hH (EnclF.encl ⟨ps, hP⟩) hx)
  obtain ⟨y, hy, hym⟩ := (rel_ballOps hk).inv hmem hdi
  obtain ⟨hne, rfl⟩ := fieldOps_inv_eq_some hy
  refine ⟨ρ * (r x + (fieldOps Kv).horner ps x)⁻¹, Ball.mem_mul hk hρ hym, ?_⟩
  exact sqrt_branch_eq (hr x hx).1 (by rw [← hρeq]; ring) hne

/-- The part of degree at least `j`, with the fixed coefficients below `j`. -/
theorem EnclC.split (hk : T.k.Ok) (hH : T.Dom H) {M : TM} {cs : List Kv} {F : Kv → Kv}
    (hF : EnclC T H M cs F) {j : ℕ} (hj : j ≤ T.n + 1) {h : Kv} (hh : h ∈ H) :
    ∃ q : Kv, (TM.split T j M).Mem q ∧ F h = (fieldOps Kv).horner (cs.take j) h + h ^ j * q := by
  obtain ⟨ρ, hρ, hFρ⟩ := hF.2 h hh
  refine ⟨(fieldOps Kv).horner (cs.drop j) h + h ^ (T.n + 1 - j) * ρ,
    Ball.mem_add hk (mem_pball hk hH (List.forall₂_drop _ hF.1) hh)
      (Ball.mem_mul hk (mem_hpw' hk hH hh _) hρ), ?_⟩
  rw [hFρ, fieldOps_horner_split cs j h]
  have e : h ^ (T.n + 1) = h ^ j * h ^ (T.n + 1 - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [e]
  ring

/-- The first two fixed coefficients and the ball of the rest: `F h = c₀ + h c₁ + h² S(h)` with `c₀, c₁`
in the first two coefficient balls and `S(h)` in `TM.split T 2 M` (the form of the tail boxes). -/
theorem EnclF.split2 (hk : T.k.Ok) (hH : T.Dom H) {M : TM} {F : Kv → Kv} (hF : EnclF T H M F)
    (hn : 1 ≤ T.n) {b0 b1 : Ball} {bs : List Ball} (hM : M.cs = b0 :: b1 :: bs) :
    ∃ c0 c1 : Kv, b0.Mem c0 ∧ b1.Mem c1 ∧
      ∀ h ∈ H, ∃ S : Kv, (TM.split T 2 M).Mem S ∧ F h = c0 + h * c1 + h ^ 2 * S := by
  obtain ⟨cs, hcs, hR⟩ := hF
  rw [hM] at hcs
  obtain ⟨c0, c1, cs', h0, h1, -, rfl⟩ : ∃ c0 c1 cs', b0.Mem c0 ∧ b1.Mem c1 ∧
      List.Forall₂ (fun x b => Ball.Mem b x) cs' bs ∧ cs = c0 :: c1 :: cs' := by
    cases hcs with
    | cons h0 hcs' =>
      cases hcs' with
      | cons h1 hbs => exact ⟨_, _, _, h0, h1, hbs, rfl⟩
  refine ⟨c0, c1, h0, h1, fun h hh => ?_⟩
  obtain ⟨S, hS, hFS⟩ := EnclC.split (j := 2) hk hH ⟨by rw [hM]; exact hcs, hR⟩ (by omega) hh
  refine ⟨S, hS, ?_⟩
  rw [hFS]
  simp only [List.take_succ_cons, List.take_zero, Ops.horner, List.foldr, Ops.zero, fieldOps,
    Int.cast_zero]
  ring

section EnclC_of_incl_aux
lemma EnclC_of_incl_aux1 {T : TCtx} {hk : T.k.Ok} {cs : List Kv} {Mcs M'cs : List Ball}
    (hFcs : List.Forall₂ (fun x b => Ball.Mem b x) cs Mcs)
    (hlen : Mcs.length = M'cs.length) (hall : ∀ a b, (a, b) ∈ Mcs.zip M'cs → Ball.incl T.k a b = true) :
    List.Forall₂ (fun x b => Ball.Mem b x) cs M'cs := by
  revert M'cs hlen hall
  match hFcs with
  | List.Forall₂.nil =>
      intro M'cs hlen hall
      have hnil : M'cs = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using hlen.symm
      rw [hnil]
      exact List.Forall₂.nil
  | List.Forall₂.cons (a := x) (b := b_val) (l₁ := xs) (l₂ := bs_val) hx hFcs_tail =>
      intro M'cs hlen hall
      cases M'cs with
      | nil => simp at hlen
      | cons b_head cs_tail' =>
        have hlen_tail : bs_val.length = cs_tail'.length := by
          simpa using hlen
        have hhead_incl : Ball.incl T.k b_val b_head = true := by
          have mem_zip : (b_val, b_head) ∈ (b_val :: bs_val).zip (b_head :: cs_tail') := by
            simp
          exact hall b_val b_head mem_zip
        have hhead_mem : Ball.Mem b_head x := Ball.mem_of_incl hk hx hhead_incl
        have hall_tail : ∀ a b, (a, b) ∈ bs_val.zip cs_tail' → Ball.incl T.k a b = true := by
          intro a' b' hmem
          have mem_zip : (a', b') ∈ (b_val :: bs_val).zip (b_head :: cs_tail') := by
            simp [hmem]
          exact hall a' b' mem_zip
        have htail := EnclC_of_incl_aux1 (hk := hk) hFcs_tail hlen_tail hall_tail
        exact List.Forall₂.cons hhead_mem htail
end EnclC_of_incl_aux

/-- **Inclusion**: a certificate Taylor model containing the computed one. -/
theorem EnclC.of_incl (hk : T.k.Ok) {M M' : TM} {cs : List Kv} {F : Kv → Kv}
    (hF : EnclC T H M cs F) (h : TM.incl T M M' = true) : EnclC T H M' cs F := by
  rcases hF with ⟨hFcs, hFh⟩
  have hparts : ((M.cs.length = M'.cs.length) ∧ (∀ a b, (a, b) ∈ M.cs.zip M'.cs → Ball.incl T.k a b = true)) ∧ (Ball.incl T.k M.R M'.R = true) := by
    simpa [TM.incl, Bool.and_eq_true] using h
  rcases hparts with ⟨⟨hlen, hall⟩, hRincl⟩
  have hFcs' : List.Forall₂ (fun x b => Ball.Mem b x) cs M'.cs :=
    EnclC_of_incl_aux1 (hk := hk) hFcs hlen hall
  have hFh' : ∀ h ∈ H, ∃ ρ : Kv, M'.R.Mem ρ ∧ F h = (fieldOps Kv).horner cs h + h ^ (T.n + 1) * ρ := by
    intro hh hH
    rcases hFh hh hH with ⟨ρ, hρ_mem, hρ_eq⟩
    refine ⟨ρ, Ball.mem_of_incl hk hρ_mem hRincl, hρ_eq⟩
  exact And.intro hFcs' hFh'

/-- **Soundness of Taylor model arithmetic**: Taylor models follow the pairs (exact truncated series,
function). -/
theorem rel_tmOps (hk : T.k.Ok) (hH : T.Dom H) :
    Ops.Rel ((polyOps (fieldOps Kv) T.n).prod (funOps H)) (tmOps T)
      (fun cF M => EnclC T H M cF.1 cF.2) := by
  refine
    { add := ?_
      sub := ?_
      neg := ?_
      mul := ?_
      inv := ?_
      ofInt := ?_ }
  · -- add
    intro x y a b hx hy
    -- hx : EnclC T H a x.1 x.2
    -- hy : EnclC T H b y.1 y.2
    -- Goal: EnclC T H (TM.add T a b) ((fieldOps Kv).zipAdd x.1 y.1) (fun h => x.2 h + y.2 h)
    exact EnclC.add hk hx hy
  · -- sub
    intro x y a b hx hy
    exact EnclC.sub hk hx hy
  · -- neg
    intro x a hx
    exact EnclC.neg hk hx
  · -- mul
    intro x y a b hx hy
    exact EnclC.mul hk hH hx hy
  · -- inv
    intro x a b hx hM
    -- hx : EnclC T H a x.1 x.2
    -- hM : (tmOps T).inv a = some b
    rcases EnclC.inv hk hH hx hM with ⟨hne, ds, hds, henc⟩
    -- hne : ∀ h ∈ H, x.2 h ≠ 0
    -- hds : (fieldOps Kv).invSeries T.n x.1 = some ds
    -- henc : EnclC T H b ds (fun h => (x.2 h)⁻¹)
    refine ⟨(ds, fun h => (x.2 h)⁻¹), ?_, ?_⟩
    · -- ((polyOps (fieldOps Kv) T.n).prod (funOps H)).inv x = some (ds, fun h => (x.2 h)⁻¹)
      dsimp [Ops.inv, polyOps, Ops.prod, funOps]
      have hpos : ∀ h ∈ H, ¬x.2 h = 0 := by
        intro h hh
        exact hne h hh
      rw [hds, if_pos hpos]
    · -- EnclC T H b ds (fun h => (x.2 h)⁻¹)
      exact henc
  · -- ofInt
    intro z
    -- Goal: EnclC T H ((tmOps T).ofInt z) (((polyOps (fieldOps Kv) T.n).prod (funOps H)).ofInt z).1
    --   (((polyOps (fieldOps Kv) T.n).prod (funOps H)).ofInt z).2
    -- i.e., EnclC T H (TM.cst T (Ball.ofInt T.k z)) [(z : Kv)] (fun _ => (z : Kv))
    have h_mem : (Ball.ofInt T.k z).Mem (z : Kv) := Ball.mem_ofInt hk z
    exact EnclC.cst hk h_mem

/-- Taylor models evaluate `hornerZ2`: exact truncated coefficients, pointwise values. -/
theorem EnclC_hornerZ2 (hk : T.k.Ok) (hH : T.Dom H) (F : List (List ℤ)) {M N : TM} {cs ds : List Kv}
    {f g : Kv → Kv} (hM : EnclC T H M cs f) (hN : EnclC T H N ds g) :
    EnclC T H ((tmOps T).hornerZ2 F M N) ((polyOps (fieldOps Kv) T.n).hornerZ2 F cs ds)
      (fun x => (fieldOps Kv).hornerZ2 F (f x) (g x)) := by
  have h1 : EnclC T H ((tmOps T).hornerZ2 F M N)
      (((polyOps (fieldOps Kv) T.n).prod (funOps H)).hornerZ2 F (cs, f) (ds, g)).1
      (((polyOps (fieldOps Kv) T.n).prod (funOps H)).hornerZ2 F (cs, f) (ds, g)).2 :=
    (rel_tmOps hk hH).hornerZ2 F (x := (cs, f)) (y := (ds, g)) hM hN
  have e1 : (((polyOps (fieldOps Kv) T.n).prod (funOps H)).hornerZ2 F (cs, f) (ds, g)).1 =
      (polyOps (fieldOps Kv) T.n).hornerZ2 F cs ds :=
    (rel_prod_fst (polyOps (fieldOps Kv) T.n) (funOps (K := Kv) H)).hornerZ2 F rfl rfl
  have e2 : (((polyOps (fieldOps Kv) T.n).prod (funOps H)).hornerZ2 F (cs, f) (ds, g)).2 =
      (funOps H).hornerZ2 F f g :=
    (rel_prod_snd (polyOps (fieldOps Kv) T.n) (funOps (K := Kv) H)).hornerZ2 F rfl rfl
  rw [e1, e2] at h1
  exact h1.congr fun x hx => (rel_fieldOps_funOps (K := Kv) hx).hornerZ2 F rfl rfl

theorem root_branch_eq {Φ0 Φu P u e ρ G : Kv} (hΦu : Φu = 0) (hΦ0 : Φ0 = e * ρ)
    (hsub : Φ0 - Φu = (P - u) * G) (hG : G ≠ 0) : u = P + e * (-(ρ * G⁻¹)) := by
  subst hΦu
  field_simp
  linear_combination hsub - hΦ0

/-- **The point of a disc**: the root `u(h) ∈ U` of `F(t₀ + t₁ h, Y)` on `H`, for a root `y₀` of
`F(t₀, Y)` in the ball `y0B`. -/
theorem EnclC.root (hk : T.k.Ok) (hH : T.Dom H) {F : List (List ℤ)} {t0B t1B y0B U : Ball} {M : TM}
    {t0 t1 y0 : Kv} (ht0 : t0B.Mem t0) (ht1 : t1B.Mem t1) (hy0 : y0B.Mem y0)
    (hF0 : (fieldOps Kv).hornerZ2 F t0 y0 = 0) {u : Kv → Kv}
    (hu : ∀ h ∈ H, (fieldOps Kv).hornerZ2 F (t0 + t1 * h) (u h) = 0 ∧ U.Mem (u h))
    (h : TM.root T F t0B t1B y0B U = some M) : EnclF T H M u := by
  unfold TM.root at h
  obtain ⟨psB, hpsB, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g, hg, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [pure, Option.some.injEq] at h
  subst h
  obtain ⟨ps, hps, hpsF⟩ := Ops.Rel.rootSeries (rel_ballOps hk) T.n F ht0 ht1 hy0 psB hpsB
  obtain ⟨-, -, hdvd⟩ := rootSeries_spec hF0 hps
  have hTt : EnclC T H ⟨[t0B, t1B], TM.zeroB T⟩ [t0, t1] (fun x => t0 + t1 * x) :=
    ⟨List.Forall₂.cons ht0 (List.Forall₂.cons ht1 List.Forall₂.nil), fun x _ =>
      ⟨0, mem_zeroB hk, by rw [fieldOps_horner_cons, fieldOps_horner_cons, fieldOps_horner_nil]; ring⟩⟩
  have hP : EnclC T H ⟨psB, TM.zeroB T⟩ ps (fun x => (fieldOps Kv).horner ps x) := EnclC.poly hk hpsF
  have hQ := EnclC_hornerZ2 hk hH F hTt hP
  refine ⟨ps, hpsF, fun x hx => ?_⟩
  obtain ⟨ρ, hρ, hρeq⟩ := hQ.2 x hx
  have hz : (fieldOps Kv).horner ((polyOps (fieldOps Kv) T.n).hornerZ2 F [t0, t1] ps) x = 0 := by
    refine fieldOps_horner_eq_zero_of_dvd (n := T.n) (length_polyOps_hornerZ2_le _ _ _ _ _) ?_ x
    have h1 := X_pow_dvd_polyOf_hornerZ2 T.n F [t0, t1] ps
    have hTP : polyOf [t0, t1] = Polynomial.C t0 + Polynomial.C t1 * Polynomial.X := by
      rw [polyOf_cons, polyOf_cons, polyOf_nil]; ring
    rw [hTP] at h1
    have e := dvd_add h1 hdvd
    rwa [sub_add_cancel] at e
  rw [hz, zero_add] at hρeq
  have hmT := Encl.mem_ball hk hH (EnclF.encl ⟨_, hTt⟩) hx
  have hmP := Encl.mem_ball hk hH (EnclF.encl ⟨_, hP⟩) hx
  obtain ⟨y, hy, hym⟩ := (rel_ballOps hk).inv ((rel_ballOps hk).ddZ2 F hmT hmP (hu x hx).2) hg
  obtain ⟨hne, rfl⟩ := fieldOps_inv_eq_some hy
  refine ⟨-(ρ * ((fieldOps Kv).ddZ2 F (t0 + t1 * x) ((fieldOps Kv).horner ps x) (u x))⁻¹),
    Ball.mem_neg hk (Ball.mem_mul hk hρ hym), ?_⟩
  refine root_branch_eq (hu x hx).1 hρeq ?_ hne
  beta_reduce
  rw [fieldOps_hornerZ2_eq_ringOps, fieldOps_hornerZ2_eq_ringOps, fieldOps_ddZ2_eq_ringOps]
  exact hornerZ2_sub_hornerZ2 F _ _ _

end Sound

end FurioLombardo.Discharge.KvArith
