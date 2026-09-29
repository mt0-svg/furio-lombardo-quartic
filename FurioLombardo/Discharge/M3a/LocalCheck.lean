import FurioLombardo.Discharge.M3a.LocalData
import FurioLombardo.Discharge.M3a.LocalQE
import FurioLombardo.Discharge.M3a.LocalRes
import FurioLombardo.Discharge.M3a.Concrete

/-!
# Kernel checks of WP5 (local facts (irr) and (nsq) at `v`)

Over K21, for the twists `k = 0, 1` (data in LocalData.lean, rational atoms `QE.atom l m = zkE l / m`):

* `h_eq_normForm`: `h k = A² - d B²` with `A = X² + a1 X + a0`, `B = b1 X + b0`;
* `D0_eq`, `D1_eq`, `ND_eq`: the coordinates of `D = (a1 + b1 ω)² - 4 (a0 + b0 ω)` and its norm
  `D0² - d D1²` are the atoms `zQ k 0`, `zQ k 1`, `zQ k 2`;
* `R0_eq`, `R1_eq`, `NR_eq`: the same for `ρ = rhoN d a0 a1 b0 b1 q0 q1` and the atoms `zQ k 3`,
  `zQ k 4`, `zQ k 5`;

each from one Kronecker test (`ck_ids`, `decide +kernel`). `ck_res` checks the residue certificates
at `v` (`ResOK`): the square root certificates of `N(D)` and `N(ρ)` with the tests of
`(z0 ± n) / 2`, the test that `σ(46² d)` is not a square, and `σ(184 b1) ≢ 0` modulo 8.
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M4Cert

/-! ## The atoms -/

/-- zk coordinates of `ma a0, ma a1, mb b0, mb b1` (`i = 0, 1, 2, 3`). -/
def abL (k i : ℕ) : List ℤ := (abData.getD k []).getD i []

/-- zk coordinates of `m D0, m D1, m N(D), m ρ0, m ρ1, m N(ρ)` (`i = 0, ..., 5`). -/
def zL (k i : ℕ) : List ℤ := (zData.getD k []).getD i []

/-- The denominators `m` of `zL`. -/
def zM (k i : ℕ) : ℕ := (zDen.getD k []).getD i 1

def a0Q (k : ℕ) : QE := .atom (abL k 0) (maDen.getD k 1)
def a1Q (k : ℕ) : QE := .atom (abL k 1) (maDen.getD k 1)
def b0Q (k : ℕ) : QE := .atom (abL k 2) (mbDen.getD k 1)
def b1Q (k : ℕ) : QE := .atom (abL k 3) (mbDen.getD k 1)
def dQ (k : ℕ) : QE := .atom (dnL k) (qDenN k * qDenN k)
def q0Q (k : ℕ) : QE := .atom ((qData.getD k []).getD 0 []) (qDenN k)
def q1Q (k : ℕ) : QE := .atom ((qData.getD k []).getD 1 []) (qDenN k)
def hQ (k j : ℕ) : QE := .atom ((hData.getD k []).getD j []) (hDenN k)
def zQ (k i : ℕ) : QE := .atom (zL k i) (zM k i)

def sqQ (e : QE) : QE := .mul e e

@[simp] theorem ev_sqQ (e : QE) : (sqQ e).ev = e.ev ^ 2 := by rw [sqQ, QE.ev_mul, sq]

/-- `rho0` as an expression. -/
def rho0E (d a0 a1 b0 b1 q0 q1 : QE) : QE :=
  .add (.add (.add (.add (.sub (.add (.sub (.sub (.mul q0 (sqQ a1)) (.mul q1 (.mul a0 a1)))
    (.mul q0 (.mul q1 a1))) (.mul d (.mul q0 (sqQ b1)))) (.mul d (.mul q1 (.mul b0 b1))))
    (sqQ a0)) (.mul (.sub (sqQ q1) (.mul (.int 2) q0)) a0)) (.mul d (sqQ b0))) (sqQ q0)

/-- `rho1` as an expression. -/
def rho1E (a0 a1 b0 b1 q0 q1 : QE) : QE :=
  .add (.add (.sub (.sub (.sub (.mul (.int 2) (.mul q0 (.mul a1 b1))) (.mul q1 (.mul a1 b0)))
    (.mul q1 (.mul a0 b1))) (.mul q0 (.mul q1 b1))) (.mul (.int 2) (.mul a0 b0)))
    (.mul (.sub (sqQ q1) (.mul (.int 2) q0)) b0)

theorem ev_rho0E (d a0 a1 b0 b1 q0 q1 : QE) :
    (rho0E d a0 a1 b0 b1 q0 q1).ev = rho0 d.ev a0.ev a1.ev b0.ev b1.ev q0.ev q1.ev := by
  simp only [rho0E, rho0, QE.ev_add, QE.ev_sub, QE.ev_mul, QE.ev_int, ev_sqQ, Int.cast_ofNat]
  ring

theorem ev_rho1E (d a0 a1 b0 b1 q0 q1 : QE) :
    (rho1E a0 a1 b0 b1 q0 q1).ev = rho1 d.ev a0.ev a1.ev b0.ev b1.ev q0.ev q1.ev := by
  simp only [rho1E, rho1, QE.ev_add, QE.ev_sub, QE.ev_mul, QE.ev_int, ev_sqQ, Int.cast_ofNat]
  ring

/-! ## The identities -/

def idH3 (k : ℕ) : QE := .sub (hQ k 3) (.mul (.int 2) (a1Q k))
def idH2 (k : ℕ) : QE :=
  .sub (hQ k 2) (.sub (.add (sqQ (a1Q k)) (.mul (.int 2) (a0Q k))) (.mul (dQ k) (sqQ (b1Q k))))
def idH1 (k : ℕ) : QE :=
  .sub (hQ k 1) (.sub (.mul (.int 2) (.mul (a0Q k) (a1Q k)))
    (.mul (.int 2) (.mul (dQ k) (.mul (b0Q k) (b1Q k)))))
def idH0 (k : ℕ) : QE := .sub (hQ k 0) (.sub (sqQ (a0Q k)) (.mul (dQ k) (sqQ (b0Q k))))
def idD0 (k : ℕ) : QE :=
  .sub (zQ k 0) (.sub (.add (sqQ (a1Q k)) (.mul (dQ k) (sqQ (b1Q k)))) (.mul (.int 4) (a0Q k)))
def idD1 (k : ℕ) : QE :=
  .sub (zQ k 1) (.sub (.mul (.int 2) (.mul (a1Q k) (b1Q k))) (.mul (.int 4) (b0Q k)))
def idND (k : ℕ) : QE := .sub (zQ k 2) (.sub (sqQ (zQ k 0)) (.mul (dQ k) (sqQ (zQ k 1))))
def idR0 (k : ℕ) : QE :=
  .sub (zQ k 3) (rho0E (dQ k) (a0Q k) (a1Q k) (b0Q k) (b1Q k) (q0Q k) (q1Q k))
def idR1 (k : ℕ) : QE := .sub (zQ k 4) (rho1E (a0Q k) (a1Q k) (b0Q k) (b1Q k) (q0Q k) (q1Q k))
def idNR (k : ℕ) : QE := .sub (zQ k 5) (.sub (sqQ (zQ k 3)) (.mul (dQ k) (sqQ (zQ k 4))))

/-- All the identities of twist `k`. -/
def idsL (k : ℕ) : List QE :=
  [idH3 k, idH2 k, idH1 k, idH0 k, idD0 k, idD1 k, idND k, idR0 k, idR1 k, idNR k]

/-- The Kronecker tests at `N = 2^1024` (kernel). -/
theorem ck_ids : ∀ k : Fin 2, (idsL k).all (QE.qcheck 1024) = true := by decide +kernel

theorem qcheck_of_mem {k : Fin 2} {e : QE} (he : e ∈ idsL k) : QE.qcheck 1024 e = true :=
  List.all_eq_true.mp (ck_ids k) e he

/-! ## The residue certificates -/

/-- A certificate from `certD` or `certR`: the triple `b` and `[M, r, P, ip, jp, im, jm]`. -/
def certOf (C : List T3 × List (List ℕ)) (k : ℕ) : T3 × List ℕ := (C.1.getD k (0, 0, 0), C.2.getD k [])

/-- The residues of `z0 = zkE l0 / m0` modulo `2^P` and of `N = zkE lN / mN` modulo `2^M`, and the
square root certificate `C` (`ZOK`). -/
def ZCheck (l0 : List ℤ) (m0 j0 o0 : ℕ) (oi0 : ℤ) (lN : List ℤ) (mN jN oN : ℕ) (oiN : ℤ)
    (C : T3 × List ℕ) : Prop :=
  SQok l0 m0 j0 o0 oi0 (C.2.getD 2 0) ∧ SQok lN mN jN oN oiN (C.2.getD 0 0) ∧
    ZOK (sQres l0 j0 oi0 (C.2.getD 2 0)) (sQres lN jN oiN (C.2.getD 0 0)) C.1 (C.2.getD 0 0)
      (C.2.getD 1 0) (C.2.getD 2 0) (C.2.getD 3 0) (C.2.getD 4 0) (C.2.getD 5 0) (C.2.getD 6 0)

instance (l0 : List ℤ) (m0 j0 o0 : ℕ) (oi0 : ℤ) (lN : List ℤ) (mN jN oN : ℕ) (oiN : ℤ)
    (C : T3 × List ℕ) : Decidable (ZCheck l0 m0 j0 o0 oi0 lN mN jN oN oiN C) := by
  unfold ZCheck; infer_instance

/-- `z0 + z1 ω` is not a square in `K_v(ω)` from a `ZCheck`. -/
theorem not_isSquare_of_ZCheck {l0 : List ℤ} {m0 j0 o0 : ℕ} {oi0 : ℤ} {lN : List ℤ} {mN jN oN : ℕ}
    {oiN : ℤ} {C : T3 × List ℕ} (h : ZCheck l0 m0 j0 o0 oi0 lN mN jN oN oiN C) {δ z1 : Kv}
    (hN : σ ((m0 : K21)⁻¹ * zkE l0) ^ 2 - δ * z1 ^ 2 = σ ((mN : K21)⁻¹ * zkE lN)) :
    ¬ IsSquare (⟨σ ((m0 : K21)⁻¹ * zkE l0), z1⟩ : QuadraticAlgebra Kv δ 0) := by
  obtain ⟨h0, hN', hZ⟩ := h
  exact not_isSquare_of_ZOK (approx_σ_atom h0) (hN ▸ approx_σ_atom hN') hZ

/-- The odd parts `529 = 23²`, `279841 = 23⁴` of the denominators `2116 = 4 · 529`,
`4477456 = 16 · 279841`, with their inverses modulo `2^28`. -/
def ResOK (k : ℕ) : Prop :=
  ZCheck (zL k 0) (zM k 0) 2 529 112144113 (zL k 2) (zM k 2) 2 529 112144113 (certOf certD k) ∧
  ZCheck (zL k 3) (zM k 3) 2 529 112144113 (zL k 5) (zM k 5) 4 279841 35225313 (certOf certR k) ∧
  zresOK (dnL k) ∧ (dTest.getD k []).getD 2 0 ≤ 28 ∧
  SqTest (zres (dnL k)) ((dTest.getD k []).getD 0 0) ((dTest.getD k []).getD 1 0) 0
    ((dTest.getD k []).getD 2 0) ∧
  zresOK (abL k 3) ∧ modT (zres (abL k 3)) 3 ≠ modT (0, 0, 0) 3

instance (k : ℕ) : Decidable (ResOK k) := by unfold ResOK; infer_instance

/-- The residue certificates (kernel). -/
theorem ck_res : ∀ k : Fin 2, ResOK k := by decide +kernel

end FurioLombardo.Discharge.M3a.Bruin
