import FurioLombardo.Discharge.SelmerBasis.PlaceWModel
import FurioLombardo.Discharge.SelmerBasis.Spanning
import FurioLombardo.Discharge.SelmerBasis.LocalGlue

/-!
# Elements at a w-place: the expressions certified by `certOK`, and the rows over three components

For the model `(E, M, S)` of PlaceWModel.lean:

* `X0L M t`, `X1L M t`: the coordinates of `iL (evL t)` on `1, Y` (`iL_evL`);
* `X0N E M S t b`, `X1N E M S t b`: those of `iL (evL t.1) ± iL (evL t.2) · s0`, within
  `‖al‖^(S.n - e - j)` of `iN b (evN t)` (`norm_iN_evN_sub`), `s0 = toF s00 s01` the approximation of `sF`;
* `kapX E i`: `al` (`i = 0`) or `1 + al^i`, the scalars `dyGen (σ al) i` (`evK_kapX`).

The expressions mirror code/selmer-local-conditions/local_data_w6.gp (`X0L`, `X1L`, `X0N`, `X1N`, `KAPX`) node for node: the
precision of a `checkK` depends on the shape of the expression.

The rows over three components and the standard basis are in PlaceWRows.lean.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis.Tower

/-! ## The expressions -/

/-- The coordinate on `1` of `iL (evL t)`. -/
def X0L (M : LModel) (t : LC) : KE := .add t.1 (.mul t.2 (.lin M.y))

/-- The coordinate on `Y` of `iL (evL t)`. -/
def X1L (M : LModel) (t : LC) : KE := .mul t.2 (.lin M.c)

/-- The coordinate on `1` of `iL (evL t.1) ± iL (evL t.2) · s0`. -/
def X0N (E : EisData) (M : LModel) (S : SqrtData) (t : NC) (b : Bool) : KE :=
  let R : KE := .add (.mul (X0L M t.2) (.lin S.s00)) (.mul (.mul (X1L M t.2) (.lin S.s01)) (.lin E.A))
  if b then .add (X0L M t.1) R else .sub (X0L M t.1) R

/-- The coordinate on `Y` of `iL (evL t.1) ± iL (evL t.2) · s0`. -/
def X1N (E : EisData) (M : LModel) (S : SqrtData) (t : NC) (b : Bool) : KE :=
  let R : KE := .add (.add (.mul (X0L M t.2) (.lin S.s01)) (.mul (X1L M t.2) (.lin S.s00)))
    (.mul (.mul (X1L M t.2) (.lin S.s01)) (.lin E.B))
  if b then .add (X1L M t.1) R else .sub (X1L M t.1) R

/-- `al` for `i = 0`, `1 + al^i` for `i ≥ 1`. -/
def kapX (E : EisData) (i : ℕ) : KE := if i = 0 then .lin E.al else .add (.int 1) (.lin (E.alP i))

section Model

variable {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw]
  {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r)]
  {M : LModel}

theorem iL_evL (hM : M.ok E = true) (t : LC) :
    iL σ E M hM (evL t) = toF σ E (evK (X0L M t)) (evK (X1L M t)) := by
  rw [iL_apply]
  rfl

theorem norm_iN_evN_sub [ProperSpace Kw] (hW : WPlace σ E) (hM : M.ok E = true) {S : SqrtData}
    (hS : S.ok E M = true) (b : Bool) (t : NC) :
    ‖iN σ E M hW hM S hS b (evN t) - toF σ E (evK (X0N E M S t b)) (evK (X1N E M S t b))‖ ≤
      ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  set s0 := toF σ E (zkE S.s00) (zkE S.s01)
  set sg : CF σ E := if b then 1 else -1 with hsg
  have hX : toF σ E (evK (X0N E M S t b)) (evK (X1N E M S t b)) =
      iL σ E M hM (evL t.1) + sg * (iL σ E M hM (evL t.2) * s0) := by
    rw [iL_evL, iL_evL, toF_mul]
    cases b <;>
      simp only [X0N, X1N, hsg, ite_true, ite_false, Bool.false_eq_true, evK_add, evK_sub, evK_mul,
        evK_lin, toF_eq, map_add, map_sub, map_mul] <;> ring
  have hN : iN σ E M hW hM S hS b (evN t) =
      iL σ E M hM (evL t.1) + sg * (iL σ E M hM (evL t.2) * sF σ E M hW hM S hS) := by
    rw [iN_apply]
    have him : (evN t).im = 2 * evL t.2 := by
      rw [two_mul]
      ext <;> simp [evN, evL, two_mul]
    rw [show (evN t).re = evL t.1 from rfl, him, map_mul, map_ofNat]
    have h2 := two_ne_zero_CF hW
    field_simp
    rw [hsg]
    ring
  rw [hN, hX]
  have hsg1 : ‖sg‖ = 1 := by rw [hsg]; split_ifs <;> simp
  have hL : ‖iL σ E M hM (evL t.2)‖ ≤ 1 := by
    rw [iL_evL]; exact norm_toF_le_one hW _ _
  calc ‖iL σ E M hM (evL t.1) + sg * (iL σ E M hM (evL t.2) * sF σ E M hW hM S hS) -
        (iL σ E M hM (evL t.1) + sg * (iL σ E M hM (evL t.2) * s0))‖
      = ‖sg‖ * (‖iL σ E M hM (evL t.2)‖ * ‖sF σ E M hW hM S hS - s0‖) := by
        rw [← norm_mul, ← norm_mul]; congr 1; ring
    _ ≤ 1 * (1 * ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j)) := by
        rw [hsg1]
        gcongr
        exact sF_near hW hM hS
    _ = _ := by ring

theorem evK_kapX (hW : WPlace σ E) {i : ℕ} (hi : i < E.alPow.length) :
    σ (evK (kapX E i)) = dyGen (σ (zkE E.al)) i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [kapX, dyGen]
  · simp only [kapX, dyGen, hi0.ne', ite_false, evK_add, evK_int, evK_lin, Int.cast_one, map_add,
      map_one, EisData.ok_alP hW.ok i hi, map_pow]

theorem toF_int_zero (u : K21) : toF σ E u (evK (.int 0)) = algebraMap Kw (CF σ E) (σ u) := by
  simp [toF_eq]

theorem bF_ne_zero (hW : WPlace σ E) (i : ℕ) : bF σ E i ≠ 0 := by
  have one_add_ne : ∀ z : CF σ E, ‖z‖ < 1 → 1 + z ≠ 0 := by
    intro z hz h
    have : z = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hz
    exact lt_irrefl _ hz
  have hY := norm_cY_lt_one hW
  unfold bF
  split_ifs with h0 h5
  · intro h
    have hp : 0 < ‖cY σ E‖ := qfE_Y_pos hW.unif hW.norm_A hW.norm_B
    rw [h, norm_zero] at hp
    exact lt_irrefl _ hp
  · have h2 : ‖(2 : Kw)‖ < 1 := by
      rcases hW.res 2 (by rw [hW.two]; exact pow_le_one₀ (norm_nonneg _) hW.unif.norm_lt_one.le)
        with h | h
      · exact h
      · norm_num at h
    have h4 : ‖(4 : CF σ E)‖ < 1 := by
      rw [show (4 : CF σ E) = algebraMap Kw (CF σ E) 4 from (map_ofNat _ 4).symm,
        QF.norm_algebraMap, show (4 : Kw) = 2 * 2 by norm_num, norm_mul]
      calc ‖(2 : Kw)‖ * ‖(2 : Kw)‖ < 1 * 1 := mul_lt_mul'' h2 h2 (norm_nonneg _) (norm_nonneg _)
        _ = 1 := one_mul 1
    rw [show (5 : CF σ E) = 1 + 4 by norm_num]
    exact one_add_ne _ h4
  · refine one_add_ne _ ?_
    rw [norm_mul, norm_pow, norm_tC hW]
    calc ‖σ (zkE E.al)‖ ^ (i - 1) * ‖cY σ E‖ ≤ 1 * ‖cY σ E‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hW.unif.norm_lt_one.le)
            (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hY

end Model

end FurioLombardo.Discharge.SelmerBasis
