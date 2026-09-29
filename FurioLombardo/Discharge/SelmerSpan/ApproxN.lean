import FurioLombardo.Discharge.SelmerSpan.ApproxT
import FurioLombardo.Discharge.SelmerSpan.Sigma

/-!
# Residues in `K_v(ω)` and `K_v(ω)(x0)` (lane SelmerSpan)

For `N = QuadraticAlgebra K_v δ 0` (`ω² = δ`) and `M = QuadraticAlgebra N (-P0) (-P1)` (`x0² = -P0 - P1 x0`),
residues modulo `2^P` of the coordinates: pairs of triples for `N` (`ApproxN`), pairs of pairs for `M`
(`ApproxM`), with sums, products, norms and traces (`approx_mulNT`, `approx_normNT`, `approx_mulMT`,
`approx_normMT`, `approx_trMT`), selections `x ^ (if b then 1 else 0)` and their products over `Fin 7`, the
scaling by `4^(-b)` (`approx_scT`), and the non-square certificates of `N` (`not_isSquare_of_NCertOK`: the
norm is not a square in `K_v`, or lane M3a's `ZOK`).
-/

namespace FurioLombardo.Discharge.SelmerSpan

open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M3a.Bruin

/-! ## Scaling by `4^(-b)` -/

/-- `t / 4^b` on residues modulo `2^P` (precision `P - 2b`). -/
def scT (P b : ℕ) (t : T3) : T3 := divT (modT t P) (2 ^ (2 * b))

/-- The kernel condition of `approx_scT`. -/
def ScOK (P b : ℕ) (t : T3) : Prop := DvdT (modT t P) (2 ^ (2 * b)) ∧ 2 * b ≤ P

instance (P b : ℕ) (t : T3) : Decidable (ScOK P b t) := by unfold ScOK; infer_instance

theorem approx_scT {x : Kv} {t : T3} {P b : ℕ} (hx : Approx x t P) (h : ScOK P b t) :
    Approx (x / 2 ^ (2 * b)) (scT P b t) (P - 2 * b) := by
  have h1 : Approx x (modT t P) (P - 2 * b + 2 * b) := by
    rw [Nat.sub_add_cancel h.2]; exact hx.reduce
  exact approx_div h1 h.1

theorem div_four_pow_eq (x : Kv) (b : ℕ) : x / 2 ^ (2 * b) = x * ((2 ^ b : Kv)⁻¹) ^ 2 := by
  rw [div_eq_mul_inv, pow_mul', inv_pow]

/-! ## Selections -/

/-- `t` or `1`. -/
def selT (b : Bool) (t : T3) : T3 := if b then t else (1, 0, 0)

/-- The exponent `0` or `1`. -/
def bexp (b : Bool) : ℕ := if b then 1 else 0

theorem approx_one (P : ℕ) : Approx (1 : Kv) (1, 0, 0) P := by
  have h := approx_cT 1 P
  rw [Int.cast_one] at h
  exact h

theorem approx_selT {x : Kv} {t : T3} {P : ℕ} (hx : Approx x t P) (b : Bool) :
    Approx (x ^ bexp b) (selT b t) P := by
  cases b
  · simpa [bexp, selT] using approx_one P
  · simpa [bexp, selT] using hx

/-- The product of the selected residues over `Fin 7`, in the order of `Fin.prod_univ_seven`. -/
def prod7T (P : ℕ) (bs : List Bool) (t : ℕ → T3) : T3 :=
  mulT P (mulT P (mulT P (mulT P (mulT P (mulT P (selT (bs.getD 0 false) (t 0))
    (selT (bs.getD 1 false) (t 1))) (selT (bs.getD 2 false) (t 2))) (selT (bs.getD 3 false) (t 3)))
    (selT (bs.getD 4 false) (t 4))) (selT (bs.getD 5 false) (t 5))) (selT (bs.getD 6 false) (t 6))

theorem approx_prod7T {x : Fin 7 → Kv} {t : ℕ → T3} {P : ℕ} (hx : ∀ i : Fin 7, Approx (x i) (t i) P)
    (bs : List Bool) :
    Approx (∏ i : Fin 7, x i ^ bexp (bs.getD i false)) (prod7T P bs t) P := by
  rw [Fin.prod_univ_seven]
  exact approx_mulT (approx_mulT (approx_mulT (approx_mulT (approx_mulT (approx_mulT
    (approx_selT (hx 0) _) (approx_selT (hx 1) _)) (approx_selT (hx 2) _)) (approx_selT (hx 3) _))
    (approx_selT (hx 4) _)) (approx_selT (hx 5) _)) (approx_selT (hx 6) _)

/-! ## `N = K_v(ω)` -/

section N

variable {δ : Kv}

/-- Residues of the two coordinates. -/
def ApproxN (z : QuadraticAlgebra Kv δ 0) (t : T3 × T3) (P : ℕ) : Prop :=
  Approx z.re t.1 P ∧ Approx z.im t.2 P

def addNT (P : ℕ) (u w : T3 × T3) : T3 × T3 := (addT P u.1 w.1, addT P u.2 w.2)

def subNT (P : ℕ) (u w : T3 × T3) : T3 × T3 := (subT P u.1 w.1, subT P u.2 w.2)

def mulNT (P : ℕ) (dl : T3) (u w : T3 × T3) : T3 × T3 :=
  (addT P (mulT P u.1 w.1) (mulT P dl (mulT P u.2 w.2)), addT P (mulT P u.1 w.2) (mulT P u.2 w.1))

/-- The product by an element of `K_v`. -/
def scNT (P : ℕ) (c : T3) (u : T3 × T3) : T3 × T3 := (mulT P c u.1, mulT P c u.2)

/-- The norm to `K_v`. -/
def normNT (P : ℕ) (dl : T3) (u : T3 × T3) : T3 := subT P (mulT P u.1 u.1) (mulT P dl (mulT P u.2 u.2))

variable {u w : QuadraticAlgebra Kv δ 0} {tu tw : T3 × T3} {dl : T3} {P : ℕ}

theorem ApproxN.mono (h : ApproxN u tu P) {Q : ℕ} (hQ : Q ≤ P) : ApproxN u tu Q :=
  ⟨h.1.mono hQ, h.2.mono hQ⟩

theorem approx_addNT (hu : ApproxN u tu P) (hw : ApproxN w tw P) : ApproxN (u + w) (addNT P tu tw) P :=
  ⟨approx_addT hu.1 hw.1, approx_addT hu.2 hw.2⟩

theorem approx_subNT (hu : ApproxN u tu P) (hw : ApproxN w tw P) : ApproxN (u - w) (subNT P tu tw) P :=
  ⟨approx_subT hu.1 hw.1, approx_subT hu.2 hw.2⟩

theorem approx_mulNT (hd : Approx δ dl P) (hu : ApproxN u tu P) (hw : ApproxN w tw P) :
    ApproxN (u * w) (mulNT P dl tu tw) P := by
  constructor
  · have e : (u * w).re = u.re * w.re + δ * (u.im * w.im) := by
      rw [QuadraticAlgebra.re_mul]; ring
    rw [e]
    exact approx_addT (approx_mulT hu.1 hw.1) (approx_mulT hd (approx_mulT hu.2 hw.2))
  · have e : (u * w).im = u.re * w.im + u.im * w.re := by
      rw [QuadraticAlgebra.im_mul]; ring
    rw [e]
    exact approx_addT (approx_mulT hu.1 hw.2) (approx_mulT hu.2 hw.1)

theorem approx_scNT {c : Kv} {tc : T3} (hc : Approx c tc P) (hu : ApproxN u tu P) :
    ApproxN (algebraMap Kv (QuadraticAlgebra Kv δ 0) c * u) (scNT P tc tu) P := by
  constructor
  · have e : (algebraMap Kv (QuadraticAlgebra Kv δ 0) c * u).re = c * u.re := by
      simp [QuadraticAlgebra.algebraMap_eq]
    rw [e]; exact approx_mulT hc hu.1
  · have e : (algebraMap Kv (QuadraticAlgebra Kv δ 0) c * u).im = c * u.im := by
      simp [QuadraticAlgebra.algebraMap_eq]
    rw [e]; exact approx_mulT hc hu.2

theorem approx_normNT (hd : Approx δ dl P) (hu : ApproxN u tu P) :
    Approx (QuadraticAlgebra.norm u) (normNT P dl tu) P := by
  have e : QuadraticAlgebra.norm u = u.re * u.re - δ * (u.im * u.im) := by
    rw [QuadraticAlgebra.norm_def]; ring
  rw [e]
  exact approx_subT (approx_mulT hu.1 hu.1) (approx_mulT hd (approx_mulT hu.2 hu.2))

theorem approx_mkN {x y : Kv} {tx ty : T3} (hx : Approx x tx P) (hy : Approx y ty P) :
    ApproxN (⟨x, y⟩ : QuadraticAlgebra Kv δ 0) (tx, ty) P := ⟨hx, hy⟩

/-- Scaling of both coordinates by `4^(-b)`. -/
def scN (P b : ℕ) (t : T3 × T3) : T3 × T3 := (scT P b t.1, scT P b t.2)

def ScNOK (P b : ℕ) (t : T3 × T3) : Prop := ScOK P b t.1 ∧ ScOK P b t.2

instance (P b : ℕ) (t : T3 × T3) : Decidable (ScNOK P b t) := by unfold ScNOK; infer_instance

theorem approx_scN {b : ℕ} (hu : ApproxN u tu P) (h : ScNOK P b tu) :
    ApproxN (algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹) * u) (scN P b tu)
      (P - 2 * b) := by
  constructor
  · have e : (algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹) * u).re =
        u.re / 2 ^ (2 * b) := by
      simp [QuadraticAlgebra.algebraMap_eq, div_eq_inv_mul]
    rw [e]; exact approx_scT hu.1 h.1
  · have e : (algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹) * u).im =
        u.im / 2 ^ (2 * b) := by
      simp [QuadraticAlgebra.algebraMap_eq, div_eq_inv_mul]
    rw [e]; exact approx_scT hu.2 h.2

/-- `t` or `1`. -/
def selNT (b : Bool) (t : T3 × T3) : T3 × T3 := if b then t else ((1, 0, 0), (0, 0, 0))

theorem approx_zero (P : ℕ) : Approx (0 : Kv) (0, 0, 0) P := by
  have h := approx_cT 0 P
  rw [Int.cast_zero] at h
  exact h

theorem approx_selNT (hu : ApproxN u tu P) (b : Bool) : ApproxN (u ^ bexp b) (selNT b tu) P := by
  cases b
  · refine ⟨?_, ?_⟩
    · rw [show (u ^ bexp false).re = 1 by simp [bexp, QuadraticAlgebra.re_one]]; exact approx_one P
    · rw [show (u ^ bexp false).im = 0 by simp [bexp, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]]; exact approx_zero P
  · simpa [bexp, selNT] using hu

def prod7NT (P : ℕ) (dl : T3) (bs : List Bool) (t : ℕ → T3 × T3) : T3 × T3 :=
  mulNT P dl (mulNT P dl (mulNT P dl (mulNT P dl (mulNT P dl (mulNT P dl (selNT (bs.getD 0 false) (t 0))
    (selNT (bs.getD 1 false) (t 1))) (selNT (bs.getD 2 false) (t 2))) (selNT (bs.getD 3 false) (t 3)))
    (selNT (bs.getD 4 false) (t 4))) (selNT (bs.getD 5 false) (t 5))) (selNT (bs.getD 6 false) (t 6))

theorem approx_prod7NT {x : Fin 7 → QuadraticAlgebra Kv δ 0} {t : ℕ → T3 × T3} (hd : Approx δ dl P)
    (hx : ∀ i : Fin 7, ApproxN (x i) (t i) P) (bs : List Bool) :
    ApproxN (∏ i : Fin 7, x i ^ bexp (bs.getD i false)) (prod7NT P dl bs t) P := by
  rw [Fin.prod_univ_seven]
  exact approx_mulNT hd (approx_mulNT hd (approx_mulNT hd (approx_mulNT hd (approx_mulNT hd
    (approx_mulNT hd (approx_selNT (hx 0) _) (approx_selNT (hx 1) _)) (approx_selNT (hx 2) _))
    (approx_selNT (hx 3) _)) (approx_selNT (hx 4) _)) (approx_selNT (hx 5) _)) (approx_selNT (hx 6) _)

/-! ## Non-squares of `N` -/

/-- A non-square certificate: `(0, _, _, _, i, j, _, _)`, the norm fails `SqTest _ i j 0`, or
`(1, b, r, P, ip, jp, im, jm)`, lane M3a's `ZOK`. -/
abbrev NCert := ℕ × T3 × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

def NCertOK (M : ℕ) (dl : T3) (t : T3 × T3) (c : NCert) : Prop :=
  (c.1 = 0 ∧ SqTest (normNT M dl t) c.2.2.2.2.1 c.2.2.2.2.2.1 0 M) ∨
  (c.1 = 1 ∧ ZOK t.1 (normNT M dl t) c.2.1 M c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1
    c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2)

instance (M : ℕ) (dl : T3) (t : T3 × T3) (c : NCert) : Decidable (NCertOK M dl t c) := by
  unfold NCertOK; infer_instance

theorem not_isSquare_of_NCertOK {M : ℕ} {c : NCert} (hd : Approx δ dl M) (hu : ApproxN u tu M)
    (h : NCertOK M dl tu c) : ¬ IsSquare u := by
  have hN := approx_normNT hd hu
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · rintro hsq
    obtain ⟨r, hr⟩ := hsq.map (QuadraticAlgebra.norm (R := Kv) (a := δ) (b := 0))
    exact not_sq_of_sqTest hN h r (by rw [hr]; ring)
  · have hP : c.2.2.2.1 ≤ M := by
      obtain ⟨-, -, -, -, h5, -, -⟩ := h; omega
    have h0 : Approx u.re tu.1 c.2.2.2.1 := hu.1.mono hP
    have hN' : Approx (u.re ^ 2 - δ * u.im ^ 2) (normNT M dl tu) M := by
      rw [show u.re ^ 2 - δ * u.im ^ 2 = QuadraticAlgebra.norm u by
        rw [QuadraticAlgebra.norm_def]; ring]
      exact hN
    have := not_isSquare_of_ZOK h0 hN' h
    exact this

end N

/-! ## `M = N(x0)`, `x0² = -P0 - P1 x0` -/

section M

variable {δ : Kv} {P0 P1 : QuadraticAlgebra Kv δ 0}

/-- Residues of the four coordinates. -/
def ApproxM (z : QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1)) (t : (T3 × T3) × (T3 × T3))
    (P : ℕ) : Prop :=
  ApproxN z.re t.1 P ∧ ApproxN z.im t.2 P

def mulMT (P : ℕ) (dl : T3) (t0 t1 : T3 × T3) (u w : (T3 × T3) × (T3 × T3)) : (T3 × T3) × (T3 × T3) :=
  (subNT P (mulNT P dl u.1 w.1) (mulNT P dl t0 (mulNT P dl u.2 w.2)),
    subNT P (addNT P (mulNT P dl u.1 w.2) (mulNT P dl u.2 w.1)) (mulNT P dl t1 (mulNT P dl u.2 w.2)))

/-- The norm to `N`: `re² - P1 re im + P0 im²`. -/
def normMT (P : ℕ) (dl : T3) (t0 t1 : T3 × T3) (u : (T3 × T3) × (T3 × T3)) : T3 × T3 :=
  addNT P (subNT P (mulNT P dl u.1 u.1) (mulNT P dl t1 (mulNT P dl u.1 u.2)))
    (mulNT P dl t0 (mulNT P dl u.2 u.2))

/-- The trace to `N`: `2 re - P1 im`. -/
def trMT (P : ℕ) (dl : T3) (t1 : T3 × T3) (u : (T3 × T3) × (T3 × T3)) : T3 × T3 :=
  subNT P (scNT P (cT 2) u.1) (mulNT P dl t1 u.2)

variable {u w : QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1)} {tu tw : (T3 × T3) × (T3 × T3)}
  {dl : T3} {t0 t1 : T3 × T3} {P : ℕ}

theorem ApproxM.mono (h : ApproxM u tu P) {Q : ℕ} (hQ : Q ≤ P) : ApproxM u tu Q :=
  ⟨h.1.mono hQ, h.2.mono hQ⟩

theorem approx_mulMT (hd : Approx δ dl P) (h0 : ApproxN P0 t0 P) (h1 : ApproxN P1 t1 P)
    (hu : ApproxM u tu P) (hw : ApproxM w tw P) : ApproxM (u * w) (mulMT P dl t0 t1 tu tw) P := by
  constructor
  · have e : (u * w).re = u.re * w.re - P0 * (u.im * w.im) := by
      rw [QuadraticAlgebra.re_mul]; ring
    rw [e]
    exact approx_subNT (approx_mulNT hd hu.1 hw.1) (approx_mulNT hd h0 (approx_mulNT hd hu.2 hw.2))
  · have e : (u * w).im = u.re * w.im + u.im * w.re - P1 * (u.im * w.im) := by
      rw [QuadraticAlgebra.im_mul]; ring
    rw [e]
    exact approx_subNT (approx_addNT (approx_mulNT hd hu.1 hw.2) (approx_mulNT hd hu.2 hw.1))
      (approx_mulNT hd h1 (approx_mulNT hd hu.2 hw.2))

theorem approx_normMT (hd : Approx δ dl P) (h0 : ApproxN P0 t0 P) (h1 : ApproxN P1 t1 P)
    (hu : ApproxM u tu P) : ApproxN (QuadraticAlgebra.norm u) (normMT P dl t0 t1 tu) P := by
  have e : QuadraticAlgebra.norm u = u.re * u.re - P1 * (u.re * u.im) + P0 * (u.im * u.im) := by
    rw [QuadraticAlgebra.norm_def]; ring
  rw [e]
  exact approx_addNT (approx_subNT (approx_mulNT hd hu.1 hu.1)
    (approx_mulNT hd h1 (approx_mulNT hd hu.1 hu.2))) (approx_mulNT hd h0 (approx_mulNT hd hu.2 hu.2))

theorem approx_trMT (hd : Approx δ dl P) (h1 : ApproxN P1 t1 P) (hu : ApproxM u tu P) :
    ApproxN (QuadraticAlgebra.trace u) (trMT P dl t1 tu) P := by
  have e : QuadraticAlgebra.trace u = algebraMap Kv (QuadraticAlgebra Kv δ 0) 2 * u.re - P1 * u.im := by
    rw [QuadraticAlgebra.trace_def, ← map_ofNat (algebraMap Kv (QuadraticAlgebra Kv δ 0)) 2]; ring
  rw [e]
  exact approx_subNT (approx_scNT (approx_two P) hu.1) (approx_mulNT hd h1 hu.2)

/-- Scaling of the four coordinates by `4^(-b)`. -/
def scM (P b : ℕ) (t : (T3 × T3) × (T3 × T3)) : (T3 × T3) × (T3 × T3) := (scN P b t.1, scN P b t.2)

def ScMOK (P b : ℕ) (t : (T3 × T3) × (T3 × T3)) : Prop := ScNOK P b t.1 ∧ ScNOK P b t.2

instance (P b : ℕ) (t : (T3 × T3) × (T3 × T3)) : Decidable (ScMOK P b t) := by
  unfold ScMOK; infer_instance

theorem approx_scM {b : ℕ} (hu : ApproxM u tu P) (h : ScMOK P b tu) :
    ApproxM (algebraMap (QuadraticAlgebra Kv δ 0) (QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1))
      (algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹)) * u) (scM P b tu) (P - 2 * b) := by
  constructor
  · have e : (algebraMap (QuadraticAlgebra Kv δ 0) (QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1))
        (algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹)) * u).re =
        algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹) * u.re := by
      simp [QuadraticAlgebra.algebraMap_eq]
    rw [e]; exact approx_scN hu.1 h.1
  · have e : (algebraMap (QuadraticAlgebra Kv δ 0) (QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1))
        (algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹)) * u).im =
        algebraMap Kv (QuadraticAlgebra Kv δ 0) ((2 ^ (2 * b) : Kv)⁻¹) * u.im := by
      simp [QuadraticAlgebra.algebraMap_eq]
    rw [e]; exact approx_scN hu.2 h.2

def selMT (b : Bool) (t : (T3 × T3) × (T3 × T3)) : (T3 × T3) × (T3 × T3) :=
  if b then t else (((1, 0, 0), (0, 0, 0)), ((0, 0, 0), (0, 0, 0)))

theorem approx_selMT (hu : ApproxM u tu P) (b : Bool) : ApproxM (u ^ bexp b) (selMT b tu) P := by
  cases b
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [show (u ^ bexp false).re.re = 1 by simp [bexp, QuadraticAlgebra.re_one]]; exact approx_one P
    · rw [show (u ^ bexp false).re.im = 0 by simp [bexp, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]]; exact approx_zero P
    · rw [show (u ^ bexp false).im.re = 0 by simp [bexp, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]]; exact approx_zero P
    · rw [show (u ^ bexp false).im.im = 0 by simp [bexp, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]]; exact approx_zero P
  · simpa [bexp, selMT] using hu

def prod7MT (P : ℕ) (dl : T3) (t0 t1 : T3 × T3) (bs : List Bool) (t : ℕ → (T3 × T3) × (T3 × T3)) :
    (T3 × T3) × (T3 × T3) :=
  mulMT P dl t0 t1 (mulMT P dl t0 t1 (mulMT P dl t0 t1 (mulMT P dl t0 t1 (mulMT P dl t0 t1
    (mulMT P dl t0 t1 (selMT (bs.getD 0 false) (t 0)) (selMT (bs.getD 1 false) (t 1)))
    (selMT (bs.getD 2 false) (t 2))) (selMT (bs.getD 3 false) (t 3))) (selMT (bs.getD 4 false) (t 4)))
    (selMT (bs.getD 5 false) (t 5))) (selMT (bs.getD 6 false) (t 6))

theorem approx_prod7MT {x : Fin 7 → QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1)}
    {t : ℕ → (T3 × T3) × (T3 × T3)} (hd : Approx δ dl P) (h0 : ApproxN P0 t0 P) (h1 : ApproxN P1 t1 P)
    (hx : ∀ i : Fin 7, ApproxM (x i) (t i) P) (bs : List Bool) :
    ApproxM (∏ i : Fin 7, x i ^ bexp (bs.getD i false)) (prod7MT P dl t0 t1 bs t) P := by
  rw [Fin.prod_univ_seven]
  have m := fun {a b : QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1)} {ta tb} =>
    @approx_mulMT δ P0 P1 a b ta tb dl t0 t1 P hd h0 h1
  exact m (m (m (m (m (m (approx_selMT (hx 0) _) (approx_selMT (hx 1) _)) (approx_selMT (hx 2) _))
    (approx_selMT (hx 3) _)) (approx_selMT (hx 4) _)) (approx_selMT (hx 5) _)) (approx_selMT (hx 6) _)

end M

end FurioLombardo.Discharge.SelmerSpan
