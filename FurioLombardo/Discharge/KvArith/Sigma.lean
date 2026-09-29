import Mathlib
import FurioLombardo.Discharge.KvArith.BallOps

/-!
# Certified images `σ(zkE a)` at high precision (lane lean-kv-arith, D1 inputs)

M4Cert gives `θ⋆` (the root of K21's defining polynomial in `K_v` that defines `σ`) only within `2^-33`
of `θ0`. `thetaHi` is a better approximation, certified to `thetaR` `π`-adic digits (`mem_thetaBall`: Hensel
at `thetaHi` by ball evaluation of `f` and `f'`, then Hensel uniqueness near `θ0` identifies the root with
`θ⋆`). `sigmaBall k a` is the ball of `σ(zkE a) = Dz⁻¹ Σ (combo a)ⱼ θ⋆ʲ` (`M4Cert.σ_zkE`).
-/

namespace FurioLombardo.Discharge.KvArith

open FurioLombardo.Discharge.M4Cert FurioLombardo.M1

/-- An approximation of `θ⋆` at 1200 bits (code/local-group/theta_high_precision.gp, .out). -/
def thetaHi : N3 :=
  (3126025863883078896197580051153772851814853071277812387867964688282618951171238316643205702559609062814121471625997621916764899463309536960213382244414980565411533613896278994190738197827280582672308859363793071428972874586538632151046151504507757301212880613026788922090894347509015847125584065202230750963010225192407743123621991053800337455424365216541463417,
    16067018296217761567975199555298377725748526527155192803330171690055620964579708259158103948685317474535460710234557881136798903109888920956522225186333970067303303920297078179865271571445488305135584265368863922892070601444600775802973141217906165462272423708164926643421439191807661250438110359265175712970623277960983153031364005558251074596661412950424143150,
    7308304836297202255059053212817707697122229273174647002698146780241464687801933338832539430841104667086757264711372910063924841140794176797169699998637029949440325899599588610577770609887279620265792295509607012765042838611963954393507902835874828465731685230064553783430583549925615714828516349422580612377428095635537806663913585681001717739900362982490210296)

/-- The certified `π`-adic precision of `thetaHi`. -/
def thetaR : ℕ := 3583

/-- The ball of `θ⋆` in the context `k`. -/
def thetaBall (k : Ctx) : Ball :=
  let c := redN k thetaHi; ⟨c, 0, min thetaR (3 * k.P), vN k c⟩

/-- The root check of a triple `th` near `θ0`: `th ≡ θ0 (mod 2^33)` coordinatewise; the ball of
`f(th)` has scale 0 and radius and centre valuation at least `R`; the ball of `f'(th)` has scale 0 and a
certified nonzero centre of valuation `d`. -/
def rootCheck (k : Ctx) (th : N3) (R d : Nat) : Bool :=
  let t := Ball.ofN k th
  let fb := (ballOps k).hornerZ fL t
  let db := (ballOps k).hornerZ (dL fL) t
  ((th.1 : ℤ) - θ0.1) % 2 ^ 33 == 0 && ((th.2.1 : ℤ) - θ0.2.1) % 2 ^ 33 == 0 &&
    ((th.2.2 : ℤ) - θ0.2.2) % 2 ^ 33 == 0 &&
    fb.e == 0 && decide (R ≤ fb.r) && decide (R ≤ vN k fb.c) &&
    db.e == 0 && db.nz k && vN k db.c == d

/-- The context of the certificate of `thetaHi`. -/
def kTheta : Ctx := Ctx.ofP 1200

/-- The certificate of `thetaHi` (`f(thetaHi) ≡ 0 mod 2^1200`, `v(f'(thetaHi)) = 17`). -/
def thetaCheck : Bool := rootCheck kTheta thetaHi 3600 17

set_option maxRecDepth 100000 in
theorem thetaCheck_eq : thetaCheck = true := by decide +kernel

theorem fieldOps_hornerZ_eq_evalL (cs : List ℤ) (x : Kv) : (fieldOps Kv).hornerZ cs x = evalL x cs := by
  induction cs with
  | nil => simp [Ops.hornerZ, Ops.zero, fieldOps, evalL]
  | cons c cs ih =>
    simp only [Ops.hornerZ, List.foldr] at ih ⊢
    rw [ih]; simp [fieldOps, evalL]

/-- The ball of a Horner evaluation at an element of a ball. -/
theorem mem_hornerZ {k : Ctx} (hk : k.Ok) (cs : List ℤ) {b : Ball} {x : Kv} (hx : b.Mem x) :
    ((ballOps k).hornerZ cs b).Mem (evalL x cs) := by
  rw [← fieldOps_hornerZ_eq_evalL]
  exact (rel_ballOps hk).hornerZ cs hx

/-- **Soundness of the root check**: `‖θ⋆ - evN th‖ ≤ ‖pv‖^(R - d)`. -/
theorem rootCheck_sound {k : Ctx} (hk : k.Ok) {th : N3} {R d : ℕ} (hd : d < 99)
    (h : rootCheck k th R d = true) : ‖θstar - evN th‖ ≤ ‖pv‖ ^ (R - d) := by
  simp only [rootCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hfe⟩, hfr⟩, hfv⟩, hde⟩, hdnz⟩, hdv⟩ := h
  set z := evN th
  have ht := Ball.mem_ofN hk th
  have hfb := mem_hornerZ hk fL ht
  have hdb := mem_hornerZ hk (dL fL) ht
  set fb := (ballOps k).hornerZ fL (Ball.ofN k th)
  set db := (ballOps k).hornerZ (dL fL) (Ball.ofN k th)
  -- `‖f(z)‖ ≤ ‖pv‖^R` and `‖f'(z)‖ = ‖pv‖^d`
  have hfz : ‖fK.eval z‖ ≤ ‖pv‖ ^ R := by
    rw [fK_eval]
    exact Ball.norm_le_of_mem_vN hk hfb hfe hfv hfr
  have hdz : ‖fK.derivative.eval z‖ = ‖pv‖ ^ d := by
    rw [fK_derivative_eval, ← hdv]
    have := Ball.norm_eq_of_nz hk hdb hdnz
    rwa [hde, pow_zero, one_mul] at this
  -- `z ≡ θ0 ≡ θ⋆ (mod 2^33)`
  have hz0 : ‖z - evZ θ0‖ ≤ (2⁻¹ : ℝ) ^ 33 := by
    rw [show z = evZ (t3OfN th) from evN_eq_evZ th, ← evZ_sub]
    exact norm_evZ_le_of_dvd _ _
      ⟨Int.dvd_of_emod_eq_zero h1, Int.dvd_of_emod_eq_zero h2, Int.dvd_of_emod_eq_zero h3⟩
  have he99 : ‖z - θstar‖ ≤ ‖pv‖ ^ 99 := by
    rw [show (99 : ℕ) = 3 * 33 by norm_num, norm_pv_pow_three_mul]
    rw [show z - θstar = (z - evZ θ0) - (θstar - evZ θ0) by ring]
    exact (norm_sub_le_max_u _ _).trans (max_le hz0 norm_θstar_sub)
  have key := norm_eval_sub_eval_sub_le fK fK_coeff_le (norm_evN_le_one th) (norm_evN_le_one th)
    norm_θstar_le_one
  rw [fK_θstar, sub_zero, sub_self, norm_zero] at key
  set e := ‖z - θstar‖
  have he0 : 0 ≤ e := norm_nonneg _
  have hmax : max 0 ‖θstar - z‖ = e := by rw [norm_sub_rev]; exact max_eq_right he0
  rw [hmax] at key
  have hpd : 0 < ‖pv‖ ^ d := pow_pos norm_pv_pos _
  -- `‖f'(z)‖ e ≤ max ‖f(z)‖ e²`
  have hde' : ‖pv‖ ^ d * e ≤ max ‖fK.eval z‖ (e * e) := by
    rw [← hdz, ← norm_mul]
    rw [show fK.derivative.eval z * (z - θstar) =
      fK.eval z - (fK.eval z - fK.derivative.eval z * (z - θstar)) by ring]
    exact (norm_sub_le_max_u _ _).trans (max_le_max le_rfl key)
  rw [norm_sub_rev]
  rcases le_total ‖fK.eval z‖ (e * e) with hc | hc
  · rw [max_eq_right hc] at hde'
    have : e = 0 := by
      by_contra hne
      have hpos : 0 < e := lt_of_le_of_ne he0 (Ne.symm hne)
      have h1 : ‖pv‖ ^ d ≤ e := le_of_mul_le_mul_right hde' hpos
      have h2 : e < ‖pv‖ ^ d := he99.trans_lt (pv_pow_lt_pv_pow hd)
      linarith
    show e ≤ _
    rw [this]; positivity
  · rw [max_eq_left hc] at hde'
    show e ≤ _
    rcases Nat.lt_or_ge R d with hRd | hRd
    · rw [show R - d = 0 by omega, pow_zero]
      exact he99.trans (pow_le_one₀ (norm_nonneg _) norm_pv_le_one')
    · have h3 : ‖pv‖ ^ d * e ≤ ‖pv‖ ^ d * ‖pv‖ ^ (R - d) := by
        rw [← pow_add, Nat.add_sub_cancel' hRd]; exact hde'.trans hfz
      exact le_of_mul_le_mul_left h3 hpd

theorem mem_thetaBall {k : Ctx} (hk : k.Ok) : (thetaBall k).Mem θstar := by
  have h := rootCheck_sound (Ctx.ofP_ok 1200) (by norm_num) thetaCheck_eq
  have hr := approxP_redN hk thetaHi
  simp only [ApproxP] at hr
  refine ⟨?_, norm_evN_le hk _⟩
  simp only [thetaBall, ApproxP, pow_zero, one_mul]
  exact norm_sub_le_pv h hr (min_le_left _ _) (min_le_right _ _)

/-- The ball of `σ(zkE a)`. -/
def sigmaBall (k : Ctx) (a : List ℤ) : Option Ball := do
  let dzi ← (ballOps k).inv (Ball.ofInt k (Dz : ℤ))
  pure (Ball.mul k dzi ((ballOps k).hornerZ (Kron.combo a zkNum) (thetaBall k)))

theorem mem_sigmaBall {k : Ctx} (hk : k.Ok) {a : List ℤ} {b : Ball} (h : sigmaBall k a = some b) :
    b.Mem (σ (zkE a)) := by
  simp only [sigmaBall, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨dzi, hdzi, rfl⟩ := h
  obtain ⟨y, hy, hym⟩ := (rel_ballOps hk).inv (Ball.mem_ofInt hk (Dz : ℤ)) hdzi
  obtain ⟨-, rfl⟩ := fieldOps_inv_eq_some hy
  rw [σ_zkE, show ((Dz : ℕ) : Kv) = (((Dz : ℕ) : ℤ) : Kv) by push_cast; rfl]
  exact Ball.mem_mul hk hym (mem_hornerZ hk _ (mem_thetaBall hk))

end FurioLombardo.Discharge.KvArith
