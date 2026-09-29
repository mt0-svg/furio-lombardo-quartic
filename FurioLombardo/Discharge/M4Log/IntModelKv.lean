import Mathlib
import FurioLombardo.Discharge.M4Log.Model
import FurioLombardo.Discharge.M4Log.Defs

/-!
# The integral models of the base setups, and `AdmM0`

For the base setup `baseKv k` of R7 (`f = f_k`, `V0 = b_k β`, `c0 = R2`, `w0 = X² + (R1/R2) X + R0/R2`)
and `p = π^a` with `a = 2` (`k = 0`), `a = 0` (`k = 1`), the hypotheses of `IntModel` are six norm
facts (code/local-group/integral_model_hypotheses.gp):

* H1: `β1 p, β2 p², β3 p³` are integral;
* H2, H3: `R0 p⁴ / (4 f0)`, `R1 p⁵ / (4 f0)` are integral and `R2 p⁶ / (4 f0)` is a unit.

With `g_j = 4 · coeff_j f`, `g_0 = 2^ε u` (`ε = 2, 0`: `u` a unit) and `z = p u⁻¹`, the six quantities
are `N_i(g) z^(i+1) / 2^(J_i)` for integer polynomials `N_i` (`Qm_eq`, a field identity). The residue
of `N_i(g) z^(i+1)` modulo `2^26` is computed on residue triples (`PE.evT`, reduced after every
operation, sound by `PE.approx_ev`) from the residues of `g_j` modulo `2^28` (`tG28`, one kernel check
`tG28_ok` of the `σ`-images of the zk coordinates); it is divisible by `2^(J_i)`, and the quotient of
the last one is invertible modulo `2` (`cert_ok`, one kernel check). Then `intModel k` and
`admM0 k : AdmM0 k` (`adm_of_intModel`, `M0 k = 4 a`).
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.Discharge.R7.ConcreteKv
open FurioLombardo.Discharge.M4Cert hiding fK
open FurioLombardo.Discharge.M3a (coeff_pQ)
open FurioLombardo.Discharge.M3a.Bruin (fRev approx_sub two_ne_zero_Kv pvT evZ_pvT DvdT divT
  approx_div)
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.G2Formal.Taylor FurioLombardo.Vendor.Toolbox.UnitBall
open FurioLombardo.Discharge.M4Log.Model

namespace FurioLombardo.Discharge.M4Log.IntModelKv

set_option autoImplicit false

/-! ## Integer polynomial expressions and their residues -/

/-- Integer polynomial expressions in the variables `g j` and `z`. -/
inductive PE where
  | g (j : ℕ)
  | z
  | c (m : ℤ)
  | add (a b : PE)
  | sub (a b : PE)
  | mul (a b : PE)

namespace PE

instance : Add PE := ⟨add⟩
instance : Sub PE := ⟨sub⟩
instance : Mul PE := ⟨mul⟩

/-- The power `a ^ n`. -/
def pow (a : PE) : ℕ → PE
  | 0 => c 1
  | n + 1 => pow a n * a

instance : HPow PE ℕ PE := ⟨pow⟩

/-- The value in a commutative ring. -/
def ev {R : Type*} [CommRing R] (G : ℕ → R) (Z : R) : PE → R
  | g j => G j
  | z => Z
  | c m => (m : R)
  | add a b => ev G Z a + ev G Z b
  | sub a b => ev G Z a - ev G Z b
  | mul a b => ev G Z a * ev G Z b

/-- The residue triple, reduced modulo `2^n` after every operation. -/
def evT (G : ℕ → T3) (Z : T3) (n : ℕ) : PE → T3
  | g j => G j
  | z => Z
  | c m => modT (m, 0, 0) n
  | add a b => modT (evT G Z n a + evT G Z n b) n
  | sub a b => modT (evT G Z n a - evT G Z n b) n
  | mul a b => modT (mulZ (evT G Z n a) (evT G Z n b)) n

section Ev

variable {R : Type*} [CommRing R] (G : ℕ → R) (Z : R)

@[simp] theorem ev_g (j : ℕ) : ev G Z (g j) = G j := rfl
@[simp] theorem ev_z : ev G Z z = Z := rfl
@[simp] theorem ev_c (m : ℤ) : ev G Z (c m) = (m : R) := rfl
@[simp] theorem ev_add (a b : PE) : ev G Z (a + b) = ev G Z a + ev G Z b := rfl
@[simp] theorem ev_sub (a b : PE) : ev G Z (a - b) = ev G Z a - ev G Z b := rfl
@[simp] theorem ev_mul (a b : PE) : ev G Z (a * b) = ev G Z a * ev G Z b := rfl

@[simp] theorem ev_pow (a : PE) : ∀ n : ℕ, ev G Z (a ^ n) = ev G Z a ^ n
  | 0 => by
    show ev G Z (c 1) = _
    simp
  | n + 1 => by
    show ev G Z (pow a n * a) = _
    rw [ev_mul, pow_succ]
    exact congrArg (· * ev G Z a) (ev_pow a n)

end Ev

/-- **Soundness of the residues.** -/
theorem approx_ev {G : ℕ → Kv} {GT : ℕ → T3} {Z : Kv} {ZT : T3} {n : ℕ}
    (hG : ∀ j, Approx (G j) (GT j) n) (hZ : Approx Z ZT n) :
    ∀ e : PE, Approx (ev G Z e) (evT GT ZT n e) n
  | g j => hG j
  | z => hZ
  | c m => (approx_int m n).reduce
  | add a b => ((approx_ev hG hZ a).add (approx_ev hG hZ b)).reduce
  | sub a b => (approx_sub (approx_ev hG hZ a) (approx_ev hG hZ b)).reduce
  | mul a b => ((approx_ev hG hZ a).mul (approx_ev hG hZ b)).reduce

end PE

open PE

/-! ## The six quantities as quotients of integer polynomials -/

/-- `4 g0 g2 - g1²` (the numerator of `β2`). -/
def nb2 : PE := c 4 * g 0 * g 2 - g 1 ^ 2

/-- `8 g0² g3 - 4 g0 g1 g2 + g1³` (the numerator of `β3`). -/
def nb3 : PE := c 8 * g 0 ^ 2 * g 3 - c 4 * g 0 * g 1 * g 2 + g 1 ^ 3

/-- The numerators `N_i`. -/
def Nm (i : Fin 6) : PE :=
  match (i : ℕ) with
  | 0 => g 1
  | 1 => nb2
  | 2 => nb3
  | 3 => c 64 * g 0 ^ 3 * g 4 - c 16 * g 0 ^ 2 * g 2 ^ 2 - c 32 * g 0 ^ 2 * g 1 * g 3 +
      c 24 * g 0 * g 1 ^ 2 * g 2 - c 5 * g 1 ^ 4
  | 4 => c 64 * g 0 ^ 4 * g 5 - nb2 * nb3
  | _ => c 256 * g 0 ^ 5 * g 6 - nb3 ^ 2

/-- `N_i z^(i+1)`. -/
def Xm (i : Fin 6) : PE := Nm i * z ^ ((i : ℕ) + 1)

/-- `log₂` of the constant denominators `2, 8, 16, 256, 256, 1024`. -/
def cl (i : Fin 6) : ℕ :=
  match (i : ℕ) with
  | 0 => 1
  | 1 => 3
  | 2 => 4
  | 3 => 8
  | 4 => 8
  | _ => 10

/-- The six quantities of H1 to H3 for `f` and the scale `p`. -/
noncomputable def Qm {K : Type*} [Field K] (f : K[X]) (p : K) (i : Fin 6) : K :=
  match (i : ℕ) with
  | 0 => tb1 f * p
  | 1 => tb2 f * p ^ 2
  | 2 => tb3 f * p ^ 3
  | 3 => tR0 f * p ^ 4 / (4 * f.coeff 0)
  | 4 => tR1 f * p ^ 5 / (4 * f.coeff 0)
  | _ => tR2 f * p ^ 6 / (4 * f.coeff 0)

/-- **The field identity**: with `4 f0 = e u`, `Q_i = N_i(4 f) (p / u)^(i+1) / (2^(cl i) e^(i+1))`. -/
theorem Qm_eq {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (f : K[X]) (p e u : K) (he : e ≠ 0)
    (hu : u ≠ 0) (h0 : 4 * f.coeff 0 = e * u) (i : Fin 6) :
    Qm f p i = (Xm i).ev (fun j => 4 * f.coeff j) (p / u) / (2 ^ cl i * e ^ ((i : ℕ) + 1)) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hf0 : f.coeff 0 = e * u / 4 := by
    rw [eq_div_iff h4, mul_comm, h0]
  obtain ⟨_ | _ | _ | _ | _ | _ | i, hi⟩ := i
  all_goals
    try (exfalso; omega)
  all_goals
    simp only [Qm, Xm, Nm, nb2, nb3, cl, tb1, tb2, tb3, tR0, tR1, tR2, ev_mul, ev_sub, ev_add,
      ev_pow, ev_g, ev_c, ev_z, Int.cast_ofNat, Nat.reduceAdd, div_pow]
    rw [hf0]
    field_simp
    try ring

/-! ## Residues of the coefficients modulo `2^28` -/

/-- The residues modulo `2^28` of `σ (zkE (rl k i))`, `i = 0, ..., 6`
(code/local-group/integral_model_residues.lean). -/
def tG28L : Fin 2 → List T3
  | 0 => [(198438884, 51226760, 71190788), (111730656, 92828160, 233961776),
      (39066064, 40279904, 121901376), (53663840, 238639456, 227835680),
      (185584756, 91188712, 82300828), (157860492, 36037532, 183325320),
      (42893427, 7998676, 150958866)]
  | 1 => [(267379804, 250315440, 107285848), (163927072, 210969824, 115336304),
      (14361904, 6797536, 101298288), (253538016, 243799648, 205561600),
      (76322060, 208555328, 68123248), (181091356, 23772964, 45754268),
      (233271777, 206664132, 179865115)]

/-- The residue triple of `4 · coeff_i F_k` modulo `2^28` (zero for `i ≥ 7`). -/
def tG28 (k : Fin 2) (i : ℕ) : T3 := (tG28L k).getD i (0, 0, 0)

/-- Kernel check: the residues modulo `2^28`. -/
theorem tG28_ok : ∀ k : Fin 2, ∀ i : Fin 7, modT (zres (rl k i)) 28 = tG28 k i := by
  decide +kernel

theorem approx_G28 (k : Fin 2) (i : ℕ) :
    Approx (4 * ((fRev k).map σ).coeff i) (tG28 k i) 28 := by
  by_cases hi : i < 7
  · rw [four_mul_coeff_FK k hi]
    have h := (approx_σ_zkE _ ((tGL_ok k ⟨i, hi⟩).1) (le_refl 28)).reduce
    rwa [tG28_ok k ⟨i, hi⟩] at h
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_FK]; omega), mul_zero]
    have : tG28 k i = 0 := by
      have hl : (tG28L k).length = 7 := by fin_cases k <;> rfl
      unfold tG28
      rw [List.getD_eq_default _ _ (by omega)]
      rfl
    rw [this]
    exact approx_zero 28

/-- The residue triple of `g_j = 4 · coeff_j f_k` modulo `2^28`. -/
def gT28 (k : Fin 2) (j : ℕ) : T3 :=
  ∑ n ∈ Finset.range 7, mulZ ((((n + j).choose j * (k : ℕ) ^ n : ℕ) : ℤ), 0, 0) (tG28 k (n + j))

theorem approx_g28 (k : Fin 2) (j : ℕ) : Approx (4 * (fK k).coeff j) (gT28 k j) 28 := by
  rw [R7.ConcreteKv.fK, coeff_comp_X_add_C _ _ (by rw [natDegree_FK]; omega), Finset.mul_sum]
  refine approx_sum_range _ _ 7 fun n _ => ?_
  have e : 4 * (((n + j).choose j : Kv) * ((fRev k).map σ).coeff (n + j) * aK k ^ n) =
      (((((n + j).choose j * (k : ℕ) ^ n : ℕ) : ℤ)) : Kv) *
        (4 * ((fRev k).map σ).coeff (n + j)) := by
    rw [aK]; push_cast; ring
  rw [e]
  exact (approx_int _ 28).mul (approx_G28 k (n + j))

/-! ## The certificate -/

/-- The scale exponent `a` (`p = π^a`). -/
def aa : Fin 2 → ℕ := ![2, 0]

/-- `g_0 = 2^ε u` with `u` a unit. -/
def eps : Fin 2 → ℕ := ![2, 0]

/-- An inverse modulo `2^n` of a unit triple, by eight Newton steps from `1`. -/
def invT (x : T3) (n : ℕ) : T3 :=
  Nat.iterate (fun y => modT (mulZ y ((2, 0, 0) - mulZ x y)) n) 8 (1, 0, 0)

/-- The residue of `u = g_0 / 2^ε`. -/
def uT (k : Fin 2) : T3 := divT (gT28 k 0) (2 ^ eps k)

/-- The residue of `u⁻¹`. -/
def wT (k : Fin 2) : T3 := invT (modT (uT k) 26) 26

/-- The residue of `z = π^a u⁻¹`. -/
def zT (k : Fin 2) : T3 := modT (mulZ (pvT (aa k)) (wT k)) 26

/-- The residue of `N_i(g) z^(i+1)` modulo `2^26`. -/
def XT (k : Fin 2) (i : Fin 6) : T3 := (Xm i).evT (fun j => modT (gT28 k j) 26) (zT k) 26

/-- The exponent `J_i = cl i + ε (i + 1)` of the denominator. -/
def JJ (k : Fin 2) (i : Fin 6) : ℕ := cl i + eps k * ((i : ℕ) + 1)

/-- The residue of `Q_i` modulo `2^(26 - J_i)`. -/
def QT (k : Fin 2) (i : Fin 6) : T3 := divT (XT k i) (2 ^ JJ k i)

/-- The residue of `Q_5⁻¹`. -/
def QiT (k : Fin 2) : T3 := invT (QT k 5) (26 - JJ k 5)

/-- **Kernel check** of the integral models: `2^ε ∣ g_0`, the inverse of `u`, the divisibility of
`N_i(g) z^(i+1)` by `2^(J_i)`, and the inverse of the last quotient. -/
theorem cert_ok : ∀ k : Fin 2,
    DvdT (gT28 k 0) (2 ^ eps k) ∧ modT (mulZ (uT k) (wT k)) 26 = modT (1, 0, 0) 26 ∧
    (∀ i : Fin 6, JJ k i + 1 ≤ 26 ∧ DvdT (XT k i) (2 ^ JJ k i)) ∧
    modT (mulZ (QT k 5) (QiT k)) (26 - JJ k 5) = modT (1, 0, 0) (26 - JJ k 5) := by
  decide +kernel

/-! ## The six norm facts -/

/-- `u = g_0 / 2^ε`. -/
noncomputable def uK (k : Fin 2) : Kv := 4 * (fK k).coeff 0 / 2 ^ eps k

theorem eps_le (k : Fin 2) : eps k ≤ 2 := by fin_cases k <;> decide

theorem approx_uK (k : Fin 2) : Approx (uK k) (uT k) 26 := by
  refine approx_div ((approx_g28 k 0).mono ?_) (cert_ok k).1
  have := eps_le k
  omega

theorem uK_inv (k : Fin 2) : uK k ≠ 0 ∧ Approx (uK k)⁻¹ (wT k) 26 :=
  approx_inv (by norm_num) (approx_uK k) (cert_ok k).2.1

theorem approx_zK (k : Fin 2) : Approx (pv ^ aa k / uK k) (zT k) 26 := by
  have hp : Approx (pv ^ aa k) (pvT (aa k)) 26 := by
    have h := approx_evZ (pvT (aa k)) 26
    rwa [evZ_pvT] at h
  rw [div_eq_mul_inv]
  exact (hp.mul (uK_inv k).2).reduce

theorem four_mul_coeff_zero (k : Fin 2) : 4 * (fK k).coeff 0 = 2 ^ eps k * uK k := by
  have h : (2 : Kv) ^ eps k ≠ 0 := pow_ne_zero _ two_ne_zero_Kv
  rw [uK]; field_simp

theorem approx_Qm (k : Fin 2) (i : Fin 6) :
    Approx (Qm (fK k) (pv ^ aa k) i) (QT k i) (26 - JJ k i) := by
  have h2e : (2 : Kv) ^ eps k ≠ 0 := pow_ne_zero _ two_ne_zero_Kv
  rw [Qm_eq two_ne_zero_Kv (fK k) (pv ^ aa k) (2 ^ eps k) (uK k) h2e (uK_inv k).1
    (four_mul_coeff_zero k) i]
  have hJ : (2 : Kv) ^ cl i * ((2 : Kv) ^ eps k) ^ ((i : ℕ) + 1) = 2 ^ JJ k i := by
    rw [← pow_mul, ← pow_add]; rfl
  rw [hJ]
  obtain ⟨hle, hd⟩ := (cert_ok k).2.2.1 i
  refine approx_div ?_ hd
  rw [show 26 - JJ k i + JJ k i = 26 by omega]
  exact PE.approx_ev (fun j => ((approx_g28 k j).mono (by norm_num)).reduce) (approx_zK k) (Xm i)

theorem norm_Qm_le (k : Fin 2) (i : Fin 6) : ‖Qm (fK k) (pv ^ aa k) i‖ ≤ 1 :=
  (approx_Qm k i).norm_le_one

theorem norm_Qm_inv_le (k : Fin 2) : ‖(Qm (fK k) (pv ^ aa k) 5)⁻¹‖ ≤ 1 := by
  have h1 : 1 ≤ 26 - JJ k 5 := by
    have := ((cert_ok k).2.2.1 5).1
    omega
  exact (approx_inv h1 (approx_Qm k 5) (cert_ok k).2.2.2).2.norm_le_one

/-! ## The integral models -/

section Qm

variable {K : Type*} [Field K] (f : K[X]) (p : K)

@[simp] theorem Qm_0 : Qm f p 0 = tb1 f * p := rfl
@[simp] theorem Qm_1 : Qm f p 1 = tb2 f * p ^ 2 := rfl
@[simp] theorem Qm_2 : Qm f p 2 = tb3 f * p ^ 3 := rfl
@[simp] theorem Qm_3 : Qm f p 3 = tR0 f * p ^ 4 / (4 * f.coeff 0) := rfl
@[simp] theorem Qm_4 : Qm f p 4 = tR1 f * p ^ 5 / (4 * f.coeff 0) := rfl
@[simp] theorem Qm_5 : Qm f p 5 = tR2 f * p ^ 6 / (4 * f.coeff 0) := rfl

end Qm

theorem tβ_coeff (f : Kv[X]) (n : ℕ) : (tβ f).coeff n =
    if n = 0 then 1 else if n = 1 then tb1 f else if n = 2 then tb2 f else if n = 3 then tb3 f
      else 0 := by
  rcases n with _ | _ | _ | _ | n <;> simp [tβ, coeff_X, coeff_X_pow, coeff_one]

theorem w0K_coeff (k : Fin 2) (n : ℕ) : (w0K k).coeff n =
    if n = 0 then tR0 (fK k) / tR2 (fK k) else if n = 1 then tR1 (fK k) / tR2 (fK k)
      else if n = 2 then 1 else 0 := by
  rcases n with _ | _ | _ | n <;> simp [w0K, coeff_X, coeff_X_pow]

/-- H1: the coefficients of `Ṽ0 = β(p X)`. -/
theorem norm_Vt_coeff (k : Fin 2) : ∀ n : ℕ, ‖(tβ (fK k)).coeff n * (pv ^ aa k) ^ n‖ ≤ 1
  | 0 => by simp [tβ_coeff]
  | 1 => by simpa [tβ_coeff] using norm_Qm_le k 0
  | 2 => by simpa [tβ_coeff] using norm_Qm_le k 1
  | 3 => by simpa [tβ_coeff] using norm_Qm_le k 2
  | n + 4 => by simp [tβ_coeff]

/-- The quotient `q = (R2 p⁴ / (4 b²)) w0(p X)` of the integral model. -/
noncomputable def qOf {K : Type*} [Field K] (w0 : K[X]) (b R2 p : K) : K[X] :=
  C (R2 * p ^ 4 / (4 * b ^ 2)) * w0.comp (C p * X)

theorem qOf_coeff {K : Type*} [Field K] (w0 : K[X]) (b R2 p : K) (n : ℕ) :
    (qOf w0 b R2 p).coeff n = R2 * p ^ 4 / (4 * b ^ 2) * (w0.coeff n * p ^ n) := by
  rw [qOf, coeff_C_mul, comp_C_mul_X_coeff]

/-- H2: the coefficients of `q`. -/
theorem norm_q_coeff (k : Fin 2) (n : ℕ) :
    ‖(qOf (w0K k) (bK k) (tR2 (fK k)) (pv ^ aa k)).coeff n‖ ≤ 1 := by
  have hR2 := tR2_fK_ne k
  rw [qOf_coeff, bK_sq, w0K_coeff]
  rcases n with _ | _ | _ | n
  · convert norm_Qm_le k 3 using 2
    rw [Qm_3, ite_eq_left rfl, pow_zero, mul_one]
    field_simp
  · convert norm_Qm_le k 4 using 2
    rw [Qm_4, ite_eq_right (by omega), ite_eq_left rfl]
    field_simp
    try ring
  · convert norm_Qm_le k 5 using 2
    rw [Qm_5, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, one_mul]
    field_simp
    try ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    simp

/-- The equation `f̃ - Ṽ0² = 4 X⁴ q` from `f - V0² = R2 X⁴ w0`, over any field. -/
theorem hfq_gen {K : Type*} [Field K] (f β w0 : K[X]) (b R2 p : K) (hb : b ≠ 0) (h4 : (4 : K) ≠ 0)
    (h : f - (C b * β) ^ 2 = C R2 * (X ^ 4 * w0)) :
    C (b ^ 2)⁻¹ * f.comp (C p * X) - (C b⁻¹ * (C b * β).comp (C p * X)) ^ 2 =
      4 * X ^ 4 * qOf w0 b R2 p := by
  have h' := congrArg (fun P : K[X] => P.comp (C p * X)) h
  simp only [sub_comp, pow_comp, mul_comp, C_comp, X_comp] at h'
  rw [mul_comp, C_comp, qOf]
  have e1 : C (b ^ 2)⁻¹ * C b ^ 2 = (1 : K[X]) := by
    rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 hb), C_1]
  have e2 : C b⁻¹ ^ 2 * C b ^ 2 = (1 : K[X]) := by
    rw [← mul_pow, ← C_mul, inv_mul_cancel₀ hb, C_1, one_pow]
  have e3 : 4 * C (R2 * p ^ 4 / (4 * b ^ 2)) = C (b ^ 2)⁻¹ * C R2 * C p ^ 4 := by
    rw [← C_pow, ← C_mul, ← C_mul, show (4 : K[X]) = C 4 from (map_ofNat C 4).symm, ← C_mul]
    congr 1
    field_simp
  linear_combination C (b ^ 2)⁻¹ * h' + (β.comp (C p * X)) ^ 2 * e1 -
    (β.comp (C p * X)) ^ 2 * e2 - X ^ 4 * w0.comp (C p * X) * e3

theorem V0_baseKv (k : Fin 2) : (baseKv k).toSetup.V0 = C (bK k) * tβ (fK k) := rfl

/-- **The integral model of `baseKv k` at `p = π^a`.** -/
noncomputable def intModel (k : Fin 2) : IntModel (baseKv k).toSetup (aa k) where
  b := bK k
  hb := bK_ne k
  hV00 := by
    rw [V0_baseKv, coeff_C_mul, tβ_coeff_zero, mul_one]
  q := qOf (w0K k) (bK k) (tR2 (fK k)) (pv ^ aa k)
  hVt n := by
    refine (mem_unitBall_iff (K := Kv)).2 ?_
    rw [coeff_C_mul, comp_C_mul_X_coeff, V0_baseKv, coeff_C_mul, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ (bK_ne k), one_mul]
    exact norm_Vt_coeff k n
  hqO n := (mem_unitBall_iff (K := Kv)).2 (norm_q_coeff k n)
  hfq := hfq_gen (fK k) (tβ (fK k)) (w0K k) (bK k) (tR2 (fK k)) (pv ^ aa k) (bK_ne k)
    four_ne_zero_Kv (fK_sub_sq k)
  hc0 := by
    refine (mem_unitBall_iff (K := Kv)).2 ?_
    rw [bK_sq]
    exact norm_Qm_inv_le k

/-- **`M0 k` is admissible** for the chart of `baseKv k`. -/
theorem admM0 (k : Fin 2) : AdmM0 k := by
  have e : M0 k = 4 * aa k := by fin_cases k <;> rfl
  unfold AdmM0
  rw [e]
  exact adm_of_intModel (intModel k)

end FurioLombardo.Discharge.M4Log.IntModelKv
