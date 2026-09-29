import FurioLombardo.M1.ZK

/-!
# Kernel-checked identities between rational expressions in K21 (WP5 of the M3a discharge)

A `QE` is a ring expression whose atoms are `zkE l / m` (`l` a list of zk coordinates, `m : ℕ`)
and integers. `QE.num` and `QE.den` clear the denominators (`den` is the product of the atoms'
denominators, no gcd is taken): `ev e = den e⁻¹ · evK (num e)` as soon as `den e ≠ 0`
(`ev_eq_num`). `qcheck k e` is the Kronecker test `checkK k (num e)` of lane M1 together with
`den e ≠ 0`; it gives `ev e = 0` (`ev_eq_zero_of_qcheck`).
-/

namespace FurioLombardo.Discharge.M3a

open FurioLombardo.M1 FurioLombardo.M1.Kron

/-- Rational ring expressions over the zk atoms. -/
inductive QE : Type
  /-- `zkE l / m` -/
  | atom (l : List ℤ) (m : ℕ)
  /-- an integer -/
  | int (z : ℤ)
  | add (e f : QE)
  | sub (e f : QE)
  | mul (e f : QE)
  deriving Inhabited

namespace QE

/-- The value in K21. -/
noncomputable def ev : QE → K21
  | atom l m => (m : K21)⁻¹ * zkE l
  | int z => z
  | add e f => ev e + ev f
  | sub e f => ev e - ev f
  | mul e f => ev e * ev f

/-- The common denominator (product of the atoms' denominators). -/
def den : QE → ℕ
  | atom _ m => m
  | int _ => 1
  | add e f => den e * den f
  | sub e f => den e * den f
  | mul e f => den e * den f

/-- The numerator, a Kronecker expression. -/
def num : QE → KE
  | atom l _ => .lin l
  | int z => .int z
  | add e f => .add (.mul (.int (den f)) (num e)) (.mul (.int (den e)) (num f))
  | sub e f => .sub (.mul (.int (den f)) (num e)) (.mul (.int (den e)) (num f))
  | mul e f => .mul (num e) (num f)

@[simp] theorem ev_atom (l : List ℤ) (m : ℕ) : ev (atom l m) = (m : K21)⁻¹ * zkE l := rfl
@[simp] theorem ev_int (z : ℤ) : ev (int z) = z := rfl
@[simp] theorem ev_add (e f : QE) : ev (add e f) = ev e + ev f := rfl
@[simp] theorem ev_sub (e f : QE) : ev (sub e f) = ev e - ev f := rfl
@[simp] theorem ev_mul (e f : QE) : ev (mul e f) = ev e * ev f := rfl

/-- **Clearing denominators.** -/
theorem ev_eq_num : ∀ e : QE, den e ≠ 0 → ev e = ((den e : ℕ) : K21)⁻¹ * evK (num e)
  | atom l m, _ => rfl
  | int z, _ => by simp [den, num]
  | add e f, h => by
    have he : den e ≠ 0 := left_ne_zero_of_mul h
    have hf : den f ≠ 0 := right_ne_zero_of_mul h
    have he' : ((den e : ℕ) : K21) ≠ 0 := Nat.cast_ne_zero.mpr he
    have hf' : ((den f : ℕ) : K21) ≠ 0 := Nat.cast_ne_zero.mpr hf
    rw [ev_add, ev_eq_num e he, ev_eq_num f hf, den, num]
    simp only [evK_add, evK_mul, evK_int, Int.cast_natCast, Nat.cast_mul]
    field_simp
  | sub e f, h => by
    have he : den e ≠ 0 := left_ne_zero_of_mul h
    have hf : den f ≠ 0 := right_ne_zero_of_mul h
    have he' : ((den e : ℕ) : K21) ≠ 0 := Nat.cast_ne_zero.mpr he
    have hf' : ((den f : ℕ) : K21) ≠ 0 := Nat.cast_ne_zero.mpr hf
    rw [ev_sub, ev_eq_num e he, ev_eq_num f hf, den, num]
    simp only [evK_sub, evK_mul, evK_int, Int.cast_natCast, Nat.cast_mul]
    field_simp
  | mul e f, h => by
    have he : den e ≠ 0 := left_ne_zero_of_mul h
    have hf : den f ≠ 0 := right_ne_zero_of_mul h
    rw [ev_mul, ev_eq_num e he, ev_eq_num f hf, den, num]
    simp only [evK_mul, Nat.cast_mul, mul_inv]
    ring

/-- The kernel test of `ev e = 0` at `N = 2 ^ k`. -/
def qcheck (k : ℕ) (e : QE) : Bool := decide (den e ≠ 0) && checkK k (num e)

theorem ev_eq_zero_of_qcheck (k : ℕ) (e : QE) (h : qcheck k e = true) : ev e = 0 := by
  rw [qcheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [ev_eq_num e h.1, evK_eq_zero_of_check k _ h.2, mul_zero]

/-- **Identities in K21 between rational expressions, from the kernel.** -/
theorem ev_eq_of_qcheck (k : ℕ) (e f : QE) (h : qcheck k (.sub e f) = true) : ev e = ev f :=
  sub_eq_zero.mp (ev_eq_zero_of_qcheck k _ h)

end QE

end FurioLombardo.Discharge.M3a
