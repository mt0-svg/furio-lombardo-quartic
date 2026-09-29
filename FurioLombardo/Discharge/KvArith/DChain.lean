import Mathlib
import FurioLombardo.Discharge.KvArith.Cantor
import FurioLombardo.Discharge.KvArith.Comp.DChain

/-!
# The chain of the D_i values: soundness (lane lean-kv-arith)

* `Ops.Rel.dstep`, `Ops.Rel.drun`: a successful run on a related carrier (balls) forces the exact run to
  succeed, related step by step;
* over a field, for a `GoodSextic` curve: `dstep_spec`, `drun_spec`: the pairs stay on the curve and
  `[R] = [D]^m [E0]^e` with `(m, e)` updated by `dcoef`;
* `dcoef_chainSteps`: after `chainSteps J` from `R = D`, `[R] = [D]^(2^J N) [E0]`.
-/

namespace FurioLombardo.Discharge.KvArith

open Polynomial FurioLombardo.M3a FurioLombardo.M3a.Genus2

section Rel

variable {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}

theorem Ops.Rel.dstep (h : Ops.Rel o p R) {f : Sext A} {f' : Sext B} (hf : Sext.Rel R f f')
    {D E0 X : Mum A} {D' E0' X' : Mum B} (hD : Mum.Rel R D D') (hE : Mum.Rel R E0 E0')
    (hX : Mum.Rel R X X') (s : ℕ) :
    OptRel (Mum.Rel R) (KvArith.dstep o f D E0 X s) (KvArith.dstep p f' D' E0' X' s) := by
  unfold KvArith.dstep
  cases s with
  | zero =>
      -- s = 0: cantorDbl
      simpa using Ops.Rel.cantorDbl h hf hX
  | succ s =>
      cases s with
      | zero =>
          -- s = 1: cantorAdd o f X D
          simpa using Ops.Rel.cantorAdd h hf hX hD
      | succ s =>
          cases s with
          | zero =>
              -- s = 2: cantorAdd o f X E0
              simpa using Ops.Rel.cantorAdd h hf hX hE
          | succ _ =>
              -- s >= 3: cantorAdd o f X (Mum.neg o E0)
              have hneg : Mum.Rel R (Mum.neg o E0) (Mum.neg p E0') := Ops.Rel.mumNeg h hE
              simpa using Ops.Rel.cantorAdd h hf hX hneg

theorem Ops.Rel.drun (h : Ops.Rel o p R) {f : Sext A} {f' : Sext B} (hf : Sext.Rel R f f')
    {D E0 : Mum A} {D' E0' : Mum B} (hD : Mum.Rel R D D') (hE : Mum.Rel R E0 E0') (ss : List ℕ)
    {X : Mum A} {X' : Mum B} (hX : Mum.Rel R X X') :
    OptRel (Mum.Rel R) (KvArith.drun o f D E0 ss X) (KvArith.drun p f' D' E0' ss X') := by
  induction ss generalizing X X' with
  | nil =>
    simp only [KvArith.drun]
    intro b hb
    cases hb
    exact ⟨X, rfl, hX⟩
  | cons s ss ih =>
    simp only [KvArith.drun]
    apply OptRel.bind
    · exact h.dstep hf hD hE hX s
    · intro Y Z hY
      exact ih hY

end Rel

section Field

variable {K : Type*} [Field K]

/-- The class of `-E0` is the inverse class. -/
theorem mumNeg_cls (fp : K[X]) [GoodSextic fp] {E : Mum K} (hE : E.OnCurve fp) :
    (Mum.neg (fieldOps K) E).cls fp = (E.cls fp)⁻¹ := by
  have h := mumNeg_spec fp hE
  rcases h with ⟨honcurve, hprod⟩
  exact eq_inv_of_mul_eq_one_right hprod

theorem dstep_spec (fp : K[X]) [GoodSextic fp] {D E0 X Y : Mum K} (hD : D.OnCurve fp)
    (hE : E0.OnCurve fp) (hX : X.OnCurve fp) {m e : ℤ}
    (hcls : X.cls fp = D.cls fp ^ m * E0.cls fp ^ e) {s : ℕ}
    (h : dstep (fieldOps K) (Sext.ofPoly fp) D E0 X s = some Y) :
    Y.OnCurve fp ∧ Y.cls fp = D.cls fp ^ (dcoef1 (m, e) s).1 * E0.cls fp ^ (dcoef1 (m, e) s).2 := by
  match s with
  | 0 =>
    unfold dstep at h
    have hspec := cantorDbl_spec fp hX h
    rcases hspec with ⟨hYcurve, hYcls⟩
    refine ⟨hYcurve, ?_⟩
    have hcalc : (D.cls fp ^ m * E0.cls fp ^ e) * (D.cls fp ^ m * E0.cls fp ^ e) =
                D.cls fp ^ (2 * m) * E0.cls fp ^ (2 * e) := by
      calc
        (D.cls fp ^ m * E0.cls fp ^ e) * (D.cls fp ^ m * E0.cls fp ^ e) =
          (D.cls fp ^ m * D.cls fp ^ m) * (E0.cls fp ^ e * E0.cls fp ^ e) := by
            simp [mul_comm, mul_assoc, mul_left_comm]
        _ = D.cls fp ^ (m + m) * E0.cls fp ^ (e + e) := by simp [zpow_add]
        _ = D.cls fp ^ (2 * m) * E0.cls fp ^ (2 * e) := by simp [two_mul]
    rw [hcls] at hYcls
    rw [hcalc] at hYcls
    rw [← hYcls]
    rfl
  | 1 =>
    unfold dstep at h
    have hspec := cantorAdd_spec fp hX hD h
    rcases hspec with ⟨hYcurve, hYcls⟩
    refine ⟨hYcurve, ?_⟩
    rw [hcls] at hYcls
    have hcalc : (D.cls fp ^ m * E0.cls fp ^ e) * D.cls fp =
                D.cls fp ^ (m + 1) * E0.cls fp ^ e := by
      calc
        (D.cls fp ^ m * E0.cls fp ^ e) * D.cls fp =
          D.cls fp ^ m * (E0.cls fp ^ e * D.cls fp) := by rw [mul_assoc]
        _ = D.cls fp ^ m * (D.cls fp * E0.cls fp ^ e) := by rw [mul_comm (E0.cls fp ^ e) (D.cls fp)]
        _ = (D.cls fp ^ m * D.cls fp) * E0.cls fp ^ e := by rw [mul_assoc]
        _ = D.cls fp ^ (m + 1) * E0.cls fp ^ e := by simp [zpow_add_one]
    rw [hcalc] at hYcls
    rw [← hYcls]
    rfl
  | 2 =>
    unfold dstep at h
    have hspec := cantorAdd_spec fp hX hE h
    rcases hspec with ⟨hYcurve, hYcls⟩
    refine ⟨hYcurve, ?_⟩
    rw [hcls] at hYcls
    have hcalc : (D.cls fp ^ m * E0.cls fp ^ e) * E0.cls fp =
                D.cls fp ^ m * E0.cls fp ^ (e + 1) := by
      calc
        (D.cls fp ^ m * E0.cls fp ^ e) * E0.cls fp =
          D.cls fp ^ m * (E0.cls fp ^ e * E0.cls fp) := by rw [mul_assoc]
        _ = D.cls fp ^ m * E0.cls fp ^ (e + 1) := by simp [zpow_add_one]
    rw [hcalc] at hYcls
    rw [← hYcls]
    rfl
  | s+3 =>
    unfold dstep at h
    have hnegOnCurve := (mumNeg_spec fp hE).1
    have hspec := cantorAdd_spec fp hX hnegOnCurve h
    rcases hspec with ⟨hYcurve, hYcls⟩
    refine ⟨hYcurve, ?_⟩
    have hneg_cls : (Mum.neg (fieldOps K) E0).cls fp = (E0.cls fp)⁻¹ := mumNeg_cls fp hE
    rw [hcls, hneg_cls] at hYcls
    have hcalc : (D.cls fp ^ m * E0.cls fp ^ e) * (E0.cls fp)⁻¹ =
                D.cls fp ^ m * E0.cls fp ^ (e - 1) := by
      calc
        (D.cls fp ^ m * E0.cls fp ^ e) * (E0.cls fp)⁻¹ =
          D.cls fp ^ m * (E0.cls fp ^ e * (E0.cls fp)⁻¹) := by rw [mul_assoc]
        _ = D.cls fp ^ m * E0.cls fp ^ (e - 1) := by simp [zpow_sub_one]
    rw [hcalc] at hYcls
    rw [← hYcls]
    rfl

theorem drun_spec (fp : K[X]) [GoodSextic fp] {D E0 : Mum K} (hD : D.OnCurve fp)
    (hE : E0.OnCurve fp) (ss : List ℕ) {X Y : Mum K} (hX : X.OnCurve fp) {m e : ℤ}
    (hcls : X.cls fp = D.cls fp ^ m * E0.cls fp ^ e)
    (h : drun (fieldOps K) (Sext.ofPoly fp) D E0 ss X = some Y) :
    Y.OnCurve fp ∧ Y.cls fp = D.cls fp ^ (dcoef ss (m, e)).1 * E0.cls fp ^ (dcoef ss (m, e)).2 := by
  revert h hX hcls
  induction ss generalizing X m e Y with
  | nil =>
    intro h_oncurve h_cls h_drun
    -- h_drun : drun ... [] X = some Y
    -- drun ... [] X reduces to some X, so some X = some Y, hence X = Y
    have h_eq : (X : Mum K) = Y := by
      simpa [drun] using h_drun
    subst h_eq
    simp [dcoef]
    exact And.intro h_oncurve h_cls
  | cons s ss ih =>
    intro h_oncurve h_cls h_drun
    -- h_drun : drun ... (s :: ss) X = some Y
    -- drun ... (s :: ss) X = (dstep ... X s).bind (drun ... ss)
    have h_drun' : (dstep (fieldOps K) (Sext.ofPoly fp) D E0 X s).bind
      (drun (fieldOps K) (Sext.ofPoly fp) D E0 ss) = some Y := by
      simpa [drun] using h_drun
    rcases Option.bind_eq_some_iff.mp h_drun' with ⟨X1, hX1, hrest⟩
    have hspec := dstep_spec fp hD hE h_oncurve h_cls hX1
    rcases hspec with ⟨hX1curve, hX1cls⟩
    have ih_res := ih (X := X1) (Y := Y) (m := (dcoef1 (m, e) s).1) (e := (dcoef1 (m, e) s).2)
      hX1curve hX1cls hrest
    rcases ih_res with ⟨hYcurve, hYcls⟩
    simpa [dcoef] using And.intro hYcurve hYcls

end Field

theorem dcoef_append (l₁ l₂ : List ℕ) (me : ℤ × ℤ) : dcoef (l₁ ++ l₂) me = dcoef l₂ (dcoef l₁ me) := by
  induction l₁ generalizing me with
  | nil => rfl
  | cons s ss ih =>
    simp [List.cons_append, dcoef]
    exact ih (dcoef1 me s)

theorem dcoef_mulSteps : dcoef mulSteps (1, 0) = ((dN : ℤ), 0) := by
  decide

theorem dcoef_tailSteps (J : ℕ) (m : ℤ) : dcoef (tailSteps J) (m, 1) = (2 ^ J * m, 1) := by
  induction J with
  | zero =>
      simp [tailSteps, dcoef]
  | succ J ih =>
      rw [tailSteps, dcoef_append, ih]
      simp [dcoef, dcoef1]
      ring

theorem dcoef_chainSteps (J : ℕ) : dcoef (chainSteps J) (1, 0) = (2 ^ J * (dN : ℤ), 1) := by
  calc
    dcoef (chainSteps J) (1, 0) = dcoef (mulSteps ++ [2] ++ tailSteps J) (1, 0) := by rfl
    _ = dcoef (tailSteps J) (dcoef (mulSteps ++ [2]) (1, 0)) := by rw [dcoef_append]
    _ = dcoef (tailSteps J) (dcoef [2] (dcoef mulSteps (1, 0))) := by rw [dcoef_append]
    _ = dcoef (tailSteps J) (dcoef [2] ((dN : ℤ), 0)) := by rw [dcoef_mulSteps]
    _ = dcoef (tailSteps J) (dcoef1 ((dN : ℤ), 0) 2) := by rfl
    _ = dcoef (tailSteps J) ((dN : ℤ), 0 + 1) := by rfl
    _ = dcoef (tailSteps J) ((dN : ℤ), 1) := by norm_num
    _ = (2 ^ J * (dN : ℤ), 1) := by rw [dcoef_tailSteps J (dN : ℤ)]

/-- **The class of the chain end**: from `R = D`, `[R_J] = [D]^(2^J N) [E0]`. -/
theorem drun_chainSteps_cls {K : Type*} [Field K] (fp : K[X]) [GoodSextic fp] {D E0 Y : Mum K}
    (hD : D.OnCurve fp) (hE : E0.OnCurve fp) (J : ℕ)
    (h : drun (fieldOps K) (Sext.ofPoly fp) D E0 (chainSteps J) D = some Y) :
    Y.OnCurve fp ∧ Y.cls fp = D.cls fp ^ (2 ^ J * dN) * E0.cls fp := by
  have hcls_start : D.cls fp = D.cls fp ^ (1 : ℤ) * E0.cls fp ^ (0 : ℤ) := by
    simp
  have hspec := drun_spec fp hD hE (chainSteps J) hD hcls_start h
  rcases hspec with ⟨hYcurve, hYcls⟩
  have hYcls' : Y.cls fp = D.cls fp ^ (2 ^ J * (dN : ℤ)) * E0.cls fp ^ (1 : ℤ) := by
    simpa [dcoef_chainSteps J] using hYcls
  have hcast : ((2 ^ J * dN : ℕ) : ℤ) = 2 ^ J * (dN : ℤ) := by
    push_cast
    ring
  have hYcls'' : Y.cls fp = D.cls fp ^ (2 ^ J * dN) * E0.cls fp := by
    rw [hYcls']
    rw [← hcast]
    rw [zpow_natCast]
    rw [zpow_one]
  exact And.intro hYcurve hYcls''

end FurioLombardo.Discharge.KvArith
