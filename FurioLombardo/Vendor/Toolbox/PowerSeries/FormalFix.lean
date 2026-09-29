import Mathlib

/-!
# Fixed points of order-contracting maps on vectors of multivariate power series

Let `R` be a commutative ring, `σ` a type of variables and `ι` an index type. A map
`T : (ι → MvPowerSeries σ R) → (ι → MvPowerSeries σ R)` is order-contracting on a set `S` of
vectors when two vectors of `S` that agree up to order `k` have images that agree up to order
`k + 1`. If `S` is cut out by a coefficientwise condition, contains `0` and is stable under `T`,
then `T` has a unique fixed point in `S`, the coefficientwise limit of the iterates `T^n 0`
(`FurioLombardo.Vendor.Toolbox.FormalFix.fix`, `fix_mem`, `T_fix`, `eq_fix`).

This is the formal (power series) Banach fixed point theorem used for the implicit functions of
item R7 (square roots modulo monic polynomials whose lower
coefficients have no constant term). Orders are `MvPowerSeries.order` (total degree).

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

namespace FurioLombardo.Vendor.Toolbox.FormalFix

open MvPowerSeries

variable {σ R ι : Type*} [CommRing R]

/-- A vector of power series lies in the coefficientwise set given by `P`. -/
def CoeffSet (P : (σ →₀ ℕ) → R → Prop) : Set (ι → MvPowerSeries σ R) :=
  {y | ∀ i d, P d (coeff d (y i))}

/-- `T` is order-contracting on `S`. -/
def Contracting (S : Set (ι → MvPowerSeries σ R))
    (T : (ι → MvPowerSeries σ R) → (ι → MvPowerSeries σ R)) : Prop :=
  ∀ y ∈ S, ∀ z ∈ S, ∀ k : ℕ, (∀ i, (k : ℕ∞) ≤ (y i - z i).order) →
    ∀ i, ((k + 1 : ℕ) : ℕ∞) ≤ (T y i - T z i).order

/-- The iterates `T^n 0`. -/
def iter (T : (ι → MvPowerSeries σ R) → (ι → MvPowerSeries σ R)) : ℕ → (ι → MvPowerSeries σ R)
  | 0 => 0
  | n + 1 => T (iter T n)

section

variable {S : Set (ι → MvPowerSeries σ R)} {T : (ι → MvPowerSeries σ R) → (ι → MvPowerSeries σ R)}

theorem iter_mem (h0 : (0 : ι → MvPowerSeries σ R) ∈ S) (hS : ∀ y ∈ S, T y ∈ S) :
    ∀ n, iter T n ∈ S
  | 0 => h0
  | n + 1 => hS _ (iter_mem h0 hS n)

theorem order_iter_succ_sub (h0 : (0 : ι → MvPowerSeries σ R) ∈ S) (hS : ∀ y ∈ S, T y ∈ S)
    (hT : Contracting S T) : ∀ (n : ℕ) (i : ι), ((n : ℕ) : ℕ∞) ≤ (iter T (n + 1) i - iter T n i).order
  | 0, i => by simp
  | n + 1, i => by
    have := hT _ (iter_mem h0 hS (n + 1)) _ (iter_mem h0 hS n) n
      (order_iter_succ_sub h0 hS hT n) i
    simpa [iter] using this

theorem order_iter_sub_iter (h0 : (0 : ι → MvPowerSeries σ R) ∈ S) (hS : ∀ y ∈ S, T y ∈ S)
    (hT : Contracting S T) (n : ℕ) : ∀ (l : ℕ) (i : ι), ((n : ℕ) : ℕ∞) ≤ (iter T (n + l) i - iter T n i).order
  | 0, i => by simp
  | l + 1, i => by
    have h1 := order_iter_succ_sub h0 hS hT (n + l) i
    have h2 := order_iter_sub_iter h0 hS hT n l i
    have hsplit : iter T (n + (l + 1)) i - iter T n i =
        (iter T (n + l + 1) i - iter T (n + l) i) + (iter T (n + l) i - iter T n i) := by
      rw [← add_assoc]; abel
    rw [hsplit]
    refine le_trans (le_min ?_ h2) (min_order_le_add)
    exact le_trans (by exact_mod_cast Nat.le_add_right n l : ((n : ℕ) : ℕ∞) ≤ ((n + l : ℕ) : ℕ∞)) h1

theorem coeff_iter_eq (h0 : (0 : ι → MvPowerSeries σ R) ∈ S) (hS : ∀ y ∈ S, T y ∈ S)
    (hT : Contracting S T) {m n : ℕ} (i : ι) {d : σ →₀ ℕ} (hm : d.degree < m) (hn : d.degree < n) :
    coeff d (iter T m i) = coeff d (iter T n i) := by
  rcases le_total m n with hmn | hmn
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h := order_iter_sub_iter h0 hS hT m l i
    have hc := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hm) h)
    rw [map_sub, sub_eq_zero] at hc
    exact hc.symm
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have h := order_iter_sub_iter h0 hS hT n l i
    have hc := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hn) h)
    rw [map_sub, sub_eq_zero] at hc
    exact hc

/-- The coefficientwise limit of the iterates: the coefficient of `d` is taken from
`T^(deg d + 1) 0`. -/
noncomputable def fix (T : (ι → MvPowerSeries σ R) → (ι → MvPowerSeries σ R)) :
    ι → MvPowerSeries σ R :=
  fun i => (fun d => coeff d (iter T (d.degree + 1) i) : MvPowerSeries σ R)

theorem coeff_fix (i : ι) (d : σ →₀ ℕ) :
    coeff d (fix T i) = coeff d (iter T (d.degree + 1) i) := by
  rw [coeff_apply]; rfl

theorem order_fix_sub_iter (h0 : (0 : ι → MvPowerSeries σ R) ∈ S) (hS : ∀ y ∈ S, T y ∈ S)
    (hT : Contracting S T) (n : ℕ) (i : ι) : (n : ℕ∞) ≤ (fix T i - iter T n i).order := by
  refine le_order fun d hd => ?_
  have hd' : d.degree < n := by exact_mod_cast hd
  rw [map_sub, coeff_fix, sub_eq_zero]
  exact coeff_iter_eq h0 hS hT i (Nat.lt_succ_self _) hd'

/-- The limit lies in a coefficientwise set containing all iterates. -/
theorem fix_mem_coeffSet {P : (σ →₀ ℕ) → R → Prop} (h0 : (0 : ι → MvPowerSeries σ R) ∈ CoeffSet P)
    (hS : ∀ y ∈ CoeffSet P, T y ∈ CoeffSet P) : fix T ∈ CoeffSet P := by
  intro i d
  rw [coeff_fix]
  exact iter_mem h0 hS _ i d

/-- The limit is a fixed point. -/
theorem T_fix {P : (σ →₀ ℕ) → R → Prop} (h0 : (0 : ι → MvPowerSeries σ R) ∈ CoeffSet P)
    (hS : ∀ y ∈ CoeffSet P, T y ∈ CoeffSet P) (hT : Contracting (CoeffSet P) T) : T (fix T) = fix T := by
  funext i
  have hmem := fix_mem_coeffSet h0 hS
  rw [← sub_eq_zero, ← order_eq_top_iff]
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  have h1 := hT _ hmem _ (iter_mem h0 hS n) n (fun j => order_fix_sub_iter h0 hS hT n j) i
  have h2 := order_fix_sub_iter h0 hS hT (n + 1) i
  have hsplit : T (fix T) i - fix T i =
      (T (fix T) i - T (iter T n) i) + -(fix T i - iter T (n + 1) i) := by
    simp only [iter]; abel
  rw [hsplit]
  have h2' : ((n + 1 : ℕ) : ℕ∞) ≤ (-(fix T i - iter T (n + 1) i)).order := by
    rw [order_neg]; exact h2
  exact le_trans (by exact_mod_cast Nat.le_succ n) (le_trans (le_min h1 h2') min_order_le_add)

/-- Uniqueness: a fixed point in `S` is the limit. -/
theorem eq_of_fixed (hT : Contracting S T) {y z : ι → MvPowerSeries σ R} (hy : y ∈ S) (hz : z ∈ S)
    (hTy : T y = y) (hTz : T z = z) : y = z := by
  have key : ∀ k : ℕ, ∀ i, (k : ℕ∞) ≤ (y i - z i).order := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      have := hT y hy z hz k ih i
      rwa [hTy, hTz] at this
  funext i
  rw [← sub_eq_zero, ← order_eq_top_iff]
  exact ENat.eq_top_iff_forall_ge.mpr fun n => key n i

theorem eq_fix {P : (σ →₀ ℕ) → R → Prop} (h0 : (0 : ι → MvPowerSeries σ R) ∈ CoeffSet P)
    (hS : ∀ y ∈ CoeffSet P, T y ∈ CoeffSet P) (hT : Contracting (CoeffSet P) T)
    {y : ι → MvPowerSeries σ R} (hy : y ∈ CoeffSet P) (hTy : T y = y) : y = fix T :=
  eq_of_fixed hT hy (fix_mem_coeffSet h0 hS) hTy (T_fix h0 hS hT)

end

end FurioLombardo.Vendor.Toolbox.FormalFix
