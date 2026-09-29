import Mathlib

/-!
# Coefficientwise limits of polynomials

For a normed field `K`, `PTendsto l p q` says that the polynomials `p n` tend to `q`
coefficientwise along the filter `l`. Limits are compatible with the ring operations
(`PTendsto.add`, `PTendsto.mul`, ...), with reflection, with evaluation, and with division by monic
polynomials of fixed degree (`PTendsto.modByMonic`, `PTendsto.divByMonic`); divisibility by monic
polynomials of fixed degree passes to the limit (`PTendsto.dvd`), and bounded sequences of bounded
degree have convergent subsequences when `K` is proper (`exists_subseq_ptendsto`).

Origin: written for this formalization (finite index of the chart ball of a genus 2 Jacobian over
a 2-adic field, `FurioLombardo.Discharge.R7.FinIdx`).
-/

open Polynomial Filter Topology

namespace FurioLombardo.Vendor.Toolbox.PolyLim

variable {K : Type*} [NormedField K] {ι : Type*} {l : Filter ι}

/-- Coefficientwise convergence of a family of polynomials along a filter. -/
def PTendsto (l : Filter ι) (p : ι → K[X]) (q : K[X]) : Prop :=
  ∀ i, Tendsto (fun n => (p n).coeff i) l (𝓝 (q.coeff i))

/-- The sum of the norms of the coefficients of degree `≤ N`. -/
noncomputable def psize (N : ℕ) (p : K[X]) : ℝ := ∑ i ∈ Finset.range (N + 1), ‖p.coeff i‖

/-- A constant family tends to its value. -/
theorem ptendsto_const (q : K[X]) : PTendsto l (fun _ => q) q := fun _ => tendsto_const_nhds

/-- Limits of sums. -/
theorem PTendsto.add {p q : ι → K[X]} {p0 q0 : K[X]} (hp : PTendsto l p p0)
    (hq : PTendsto l q q0) : PTendsto l (fun n => p n + q n) (p0 + q0) := by
  intro i
  simpa only [coeff_add] using (hp i).add (hq i)

/-- Limits of negatives. -/
theorem PTendsto.neg {p : ι → K[X]} {p0 : K[X]} (hp : PTendsto l p p0) :
    PTendsto l (fun n => -p n) (-p0) := by
  intro i
  simpa only [coeff_neg] using (hp i).neg

/-- Limits of differences. -/
theorem PTendsto.sub {p q : ι → K[X]} {p0 q0 : K[X]} (hp : PTendsto l p p0)
    (hq : PTendsto l q q0) : PTendsto l (fun n => p n - q n) (p0 - q0) := by
  intro i
  simpa only [coeff_sub] using (hp i).sub (hq i)

/-- Limits of products. -/
theorem PTendsto.mul {p q : ι → K[X]} {p0 q0 : K[X]} (hp : PTendsto l p p0)
    (hq : PTendsto l q q0) : PTendsto l (fun n => p n * q n) (p0 * q0) := by
  intro i
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun x _ => (hp x.1).mul (hq x.2)

/-- Limits of powers. -/
theorem PTendsto.pow {p : ι → K[X]} {p0 : K[X]} (hp : PTendsto l p p0) (m : ℕ) :
    PTendsto l (fun n => p n ^ m) (p0 ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using ptendsto_const (l := l) (1 : K[X])
  | succ m ih => simpa only [pow_succ] using ih.mul hp

/-- Constant polynomials `C (c n)` tend to `C c0` when `c n → c0`. -/
theorem ptendsto_C {c : ι → K} {c0 : K} (hc : Tendsto c l (𝓝 c0)) :
    PTendsto l (fun n => C (c n)) (C c0) := by
  intro i
  rcases i with _ | i
  · simpa only [coeff_C_zero] using hc
  · simpa only [coeff_C_succ] using tendsto_const_nhds

/-- Limits of products `C (c n) * p n`. -/
theorem PTendsto.C_mul {c : ι → K} {c0 : K} (hc : Tendsto c l (𝓝 c0)) {p : ι → K[X]}
    {p0 : K[X]} (hp : PTendsto l p p0) : PTendsto l (fun n => C (c n) * p n) (C c0 * p0) :=
  (ptendsto_C hc).mul hp

/-- Limits of reflections `reflect N (p n)`. -/
theorem PTendsto.reflect {p : ι → K[X]} {p0 : K[X]} (hp : PTendsto l p p0) (N : ℕ) :
    PTendsto l (fun n => Polynomial.reflect N (p n)) (Polynomial.reflect N p0) := by
  intro i
  simpa only [coeff_reflect] using hp (revAt N i)

/-- Composition with `a X` for converging scalars `a`. -/
theorem PTendsto.comp_C_mul_X {p : ι → K[X]} {p0 : K[X]} (hp : PTendsto l p p0) {a : ι → K}
    {a0 : K} (ha : Tendsto a l (𝓝 a0)) :
    PTendsto l (fun n => (p n).comp (C (a n) * X)) (p0.comp (C a0 * X)) := by
  intro i
  simpa only [comp_C_mul_X_coeff] using (hp i).mul (ha.pow i)

/-- Limits along a reindexing `φ` tending to `l`. -/
theorem PTendsto.comp_tendsto {κ : Type*} {l' : Filter κ} {φ : κ → ι} (hφ : Tendsto φ l' l)
    {p : ι → K[X]} {p0 : K[X]} (hp : PTendsto l p p0) : PTendsto l' (p ∘ φ) p0 :=
  fun i => (hp i).comp hφ

/-- A limit only depends on the family eventually. -/
theorem PTendsto.congr' {p q : ι → K[X]} {p0 : K[X]} (h : ∀ᶠ n in l, p n = q n)
    (hp : PTendsto l p p0) : PTendsto l q p0 := by
  intro i
  exact (hp i).congr' (h.mono fun n hn => by rw [hn])

/-- Uniqueness of the limit along a nontrivial filter. -/
theorem PTendsto.unique [l.NeBot] {p : ι → K[X]} {a b : K[X]} (ha : PTendsto l p a)
    (hb : PTendsto l p b) : a = b := by
  ext i
  exact tendsto_nhds_unique (ha i) (hb i)

/-- An eventual bound `natDegree ≤ N` passes to the limit. -/
theorem PTendsto.natDegree_le [l.NeBot] {p : ι → K[X]} {p0 : K[X]} {N : ℕ}
    (hp : PTendsto l p p0) (hd : ∀ᶠ n in l, (p n).natDegree ≤ N) : p0.natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  refine tendsto_nhds_unique (hp i) (tendsto_const_nhds.congr' ?_)
  exact hd.mono fun n hn => ((natDegree_le_iff_coeff_eq_zero.1 hn) i hi).symm

/-- An eventual bound `degree < N` passes to the limit. -/
theorem PTendsto.degree_lt [l.NeBot] {p : ι → K[X]} {p0 : K[X]} {N : ℕ}
    (hp : PTendsto l p p0) (hd : ∀ᶠ n in l, (p n).degree < N) : p0.degree < N := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  refine tendsto_nhds_unique (hp i) (tendsto_const_nhds.congr' ?_)
  exact hd.mono fun n hn => ((degree_lt_iff_coeff_zero _ _).1 hn i hi).symm

/-- Evaluation at a point commutes with limits of families of bounded degree. -/
theorem PTendsto.eval {p : ι → K[X]} {p0 : K[X]} {N : ℕ} (hp : PTendsto l p p0)
    (hd : ∀ᶠ n in l, (p n).natDegree ≤ N) (x : K) :
    Tendsto (fun n => (p n).eval x) l (𝓝 (p0.eval x)) := by
  set M := max N p0.natDegree + 1
  have hM : p0.natDegree < M := Nat.lt_succ_of_le (le_max_right _ _)
  rw [eval_eq_sum_range' hM]
  refine Tendsto.congr' (f₁ := fun n => ∑ i ∈ Finset.range M, (p n).coeff i * x ^ i) ?_ ?_
  · exact hd.mono fun n hn => (eval_eq_sum_range' (Nat.lt_succ_of_le (hn.trans
      (le_max_left _ _))) x).symm
  · exact tendsto_finsetSum _ fun i _ => (hp i).mul_const _

/-- The size `psize N` is continuous. -/
theorem PTendsto.psize {p : ι → K[X]} {p0 : K[X]} (hp : PTendsto l p p0) (N : ℕ) :
    Tendsto (fun n => psize N (p n)) l (𝓝 (psize N p0)) :=
  tendsto_finsetSum _ fun i _ => (hp i).norm

/-- Finite sums of converging families converge. -/
theorem PTendsto.sum {κ : Type*} (s : Finset κ) {p : κ → ι → K[X]} {p0 : κ → K[X]}
    (hp : ∀ k ∈ s, PTendsto l (p k) (p0 k)) :
    PTendsto l (fun n => ∑ k ∈ s, p k n) (∑ k ∈ s, p0 k) := by
  intro i
  simp only [finsetSum_coeff]
  exact tendsto_finsetSum _ fun k hk => hp k hk i

/-- Remainder and quotient of `p` by a monic `q` are linear in `p`. -/
theorem modByMonic_divByMonic_eq_sum {p q : K[X]} {M : ℕ} (hp : p.natDegree ≤ M) :
    p %ₘ q = ∑ i ∈ Finset.range (M + 1), C (p.coeff i) * (X ^ i %ₘ q) ∧
      p /ₘ q = ∑ i ∈ Finset.range (M + 1), C (p.coeff i) * (X ^ i /ₘ q) := by
  have hs := as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  constructor
  · have h := congrArg (modByMonicHom q) hs
    simp only [map_sum, ← smul_eq_C_mul, map_smul, modByMonicHom_apply] at h
    simpa only [smul_eq_C_mul] using h
  · have h := congrArg (divByMonicHom q) hs
    simp only [map_sum, ← smul_eq_C_mul, map_smul, divByMonicHom_apply] at h
    simpa only [smul_eq_C_mul] using h

/-- One step of the division of `X ^ (i + 1)` by a monic `q` of degree `e + 1`. -/
theorem X_pow_succ_mod_div {q : K[X]} {e : ℕ} (hq : q.Monic) (hqd : q.natDegree = e + 1)
    (i : ℕ) :
    X ^ (i + 1) /ₘ q = X * (X ^ i /ₘ q) + C ((X ^ i %ₘ q).coeff e) ∧
      X ^ (i + 1) %ₘ q = X * (X ^ i %ₘ q) - C ((X ^ i %ₘ q).coeff e) * q := by
  have hdq : q.degree = (e + 1 : ℕ) := by rw [degree_eq_natDegree hq.ne_zero, hqd]
  have hr : (X ^ i %ₘ q).degree < (e + 1 : ℕ) := hdq ▸ degree_modByMonic_lt _ hq
  set r := X ^ i %ₘ q with hr_def
  refine div_modByMonic_unique _ _ hq ⟨?_, ?_⟩
  · have h := modByMonic_add_div (X ^ i) q
    rw [← hr_def] at h
    calc X * r - C (r.coeff e) * q + q * (X * (X ^ i /ₘ q) + C (r.coeff e))
        = X * (r + q * (X ^ i /ₘ q)) := by ring
      _ = X ^ (i + 1) := by rw [h, pow_succ']
  · rw [hdq, degree_lt_iff_coeff_zero]
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [coeff_sub, coeff_C_mul, show e + 1 + k = (e + k) + 1 by omega, coeff_X_mul]
    rcases k with _ | k
    · have : q.coeff (e + 1) = 1 := by rw [← hqd]; exact hq.coeff_natDegree
      simp [this]
    · have h1 : r.coeff (e + (k + 1)) = 0 :=
        (degree_lt_iff_coeff_zero _ _).1 hr _ (by omega)
      have h2 : q.coeff (e + (k + 1) + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h1, h2]

/-- Continuity of `X ^ i /ₘ q` and `X ^ i %ₘ q` in a monic `q` of fixed degree `e + 1`. -/
theorem ptendsto_X_pow_mod_div {q : ι → K[X]} {q0 : K[X]} {e : ℕ} (hq : PTendsto l q q0)
    (hqm : ∀ᶠ n in l, (q n).Monic ∧ (q n).natDegree = e + 1) (hq0m : q0.Monic)
    (hq0d : q0.natDegree = e + 1) (i : ℕ) :
    PTendsto l (fun n => X ^ i /ₘ q n) (X ^ i /ₘ q0) ∧
      PTendsto l (fun n => X ^ i %ₘ q n) (X ^ i %ₘ q0) := by
  have hlt : ∀ {q : K[X]}, q.Monic → q.natDegree = e + 1 → (1 : K[X]).degree < q.degree := by
    intro q hm hd
    rw [degree_one, degree_eq_natDegree hm.ne_zero, hd]
    exact WithBot.coe_lt_coe.2 (Nat.succ_pos e)
  induction i with
  | zero =>
    simp only [pow_zero]
    rw [(divByMonic_eq_zero_iff hq0m).2 (hlt hq0m hq0d),
      (modByMonic_eq_self_iff hq0m).2 (hlt hq0m hq0d)]
    exact ⟨(ptendsto_const 0).congr' (hqm.mono fun n hn =>
        ((divByMonic_eq_zero_iff hn.1).2 (hlt hn.1 hn.2)).symm),
      (ptendsto_const 1).congr' (hqm.mono fun n hn =>
        ((modByMonic_eq_self_iff hn.1).2 (hlt hn.1 hn.2)).symm)⟩
  | succ i ih =>
    obtain ⟨hd, hm⟩ := ih
    have hc : Tendsto (fun n => (X ^ i %ₘ q n).coeff e) l (𝓝 ((X ^ i %ₘ q0).coeff e)) := hm e
    rw [(X_pow_succ_mod_div hq0m hq0d i).1, (X_pow_succ_mod_div hq0m hq0d i).2]
    exact ⟨(((ptendsto_const X).mul hd).add (ptendsto_C hc)).congr' (hqm.mono fun n hn =>
        ((X_pow_succ_mod_div hn.1 hn.2 i).1).symm),
      (((ptendsto_const X).mul hm).sub ((ptendsto_C hc).mul hq)).congr' (hqm.mono fun n hn =>
        ((X_pow_succ_mod_div hn.1 hn.2 i).2).symm)⟩

/-- Joint form of `PTendsto.modByMonic` and `PTendsto.divByMonic`. -/
theorem ptendsto_mod_div {p q : ι → K[X]} {p0 q0 : K[X]} {N d : ℕ}
    (hp : PTendsto l p p0) (hpd : ∀ᶠ n in l, (p n).natDegree ≤ N) (hq : PTendsto l q q0)
    (hqm : ∀ᶠ n in l, (q n).Monic ∧ (q n).natDegree = d) (hq0m : q0.Monic)
    (hq0d : q0.natDegree = d) :
    PTendsto l (fun n => p n %ₘ q n) (p0 %ₘ q0) ∧
      PTendsto l (fun n => p n /ₘ q n) (p0 /ₘ q0) := by
  rcases d with _ | e
  · have h1 : ∀ {q : K[X]}, q.Monic → q.natDegree = 0 → q = 1 := fun hm hd =>
      eq_one_of_monic_natDegree_zero hm hd
    rw [h1 hq0m hq0d, modByMonic_one, divByMonic_one]
    exact ⟨(ptendsto_const 0).congr' (hqm.mono fun n hn => by rw [h1 hn.1 hn.2, modByMonic_one]),
      hp.congr' (hqm.mono fun n hn => by rw [h1 hn.1 hn.2, divByMonic_one])⟩
  · set M := max N p0.natDegree
    have hM : p0.natDegree ≤ M := le_max_right _ _
    have hpM : ∀ᶠ n in l, (p n).natDegree ≤ M := hpd.mono fun n hn => hn.trans (le_max_left _ _)
    have hX := ptendsto_X_pow_mod_div hq hqm hq0m hq0d
    rw [(modByMonic_divByMonic_eq_sum hM).1, (modByMonic_divByMonic_eq_sum hM).2]
    exact ⟨(PTendsto.sum _ fun i _ => (ptendsto_C (hp i)).mul (hX i).2).congr' (hpM.mono
        fun n hn => ((modByMonic_divByMonic_eq_sum hn).1).symm),
      (PTendsto.sum _ fun i _ => (ptendsto_C (hp i)).mul (hX i).1).congr' (hpM.mono
        fun n hn => ((modByMonic_divByMonic_eq_sum hn).2).symm)⟩

/-- **Remainders by monic polynomials of fixed degree are continuous.** -/
theorem PTendsto.modByMonic {p q : ι → K[X]} {p0 q0 : K[X]} {N d : ℕ}
    (hp : PTendsto l p p0) (hpd : ∀ᶠ n in l, (p n).natDegree ≤ N) (hq : PTendsto l q q0)
    (hqm : ∀ᶠ n in l, (q n).Monic ∧ (q n).natDegree = d) (hq0m : q0.Monic)
    (hq0d : q0.natDegree = d) : PTendsto l (fun n => p n %ₘ q n) (p0 %ₘ q0) :=
  (ptendsto_mod_div hp hpd hq hqm hq0m hq0d).1

/-- **Quotients by monic polynomials of fixed degree are continuous.** -/
theorem PTendsto.divByMonic {p q : ι → K[X]} {p0 q0 : K[X]} {N d : ℕ}
    (hp : PTendsto l p p0) (hpd : ∀ᶠ n in l, (p n).natDegree ≤ N) (hq : PTendsto l q q0)
    (hqm : ∀ᶠ n in l, (q n).Monic ∧ (q n).natDegree = d) (hq0m : q0.Monic)
    (hq0d : q0.natDegree = d) : PTendsto l (fun n => p n /ₘ q n) (p0 /ₘ q0) :=
  (ptendsto_mod_div hp hpd hq hqm hq0m hq0d).2

/-- **Divisibility by monic polynomials of fixed degree passes to the limit.** -/
theorem PTendsto.dvd [l.NeBot] {p q : ι → K[X]} {p0 q0 : K[X]} {N d : ℕ}
    (hp : PTendsto l p p0) (hpd : ∀ᶠ n in l, (p n).natDegree ≤ N) (hq : PTendsto l q q0)
    (hqm : ∀ᶠ n in l, (q n).Monic ∧ (q n).natDegree = d) (hq0m : q0.Monic)
    (hq0d : q0.natDegree = d) (h : ∀ᶠ n in l, q n ∣ p n) : q0 ∣ p0 := by
  have h1 := hp.modByMonic hpd hq hqm hq0m hq0d
  have h2 : PTendsto l (fun n => p n %ₘ q n) 0 := (ptendsto_const 0).congr'
    ((h.and hqm).mono fun n hn => ((modByMonic_eq_zero_iff_dvd hn.2.1).2 hn.1).symm)
  exact (modByMonic_eq_zero_iff_dvd hq0m).1 (h1.unique h2)

/-- **Extraction**: a sequence of polynomials of degree `≤ N` with bounded `psize N` has a
coefficientwise convergent subsequence. -/
theorem exists_subseq_ptendsto [ProperSpace K] {p : ℕ → K[X]} {N : ℕ}
    (hd : ∀ n, (p n).natDegree ≤ N) {B : ℝ} (hB : ∀ n, psize N (p n) ≤ B) :
    ∃ q : K[X], q.natDegree ≤ N ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ PTendsto atTop (p ∘ φ) q := by
  set v : ℕ → Fin (N + 1) → K := fun n j => (p n).coeff j
  have hB0 : 0 ≤ B := (Finset.sum_nonneg fun i _ => norm_nonneg _).trans (hB 0)
  have hv : ∀ n, v n ∈ Metric.closedBall (0 : Fin (N + 1) → K) B := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hB0]
    intro j
    refine le_trans ?_ (hB n)
    exact Finset.single_le_sum (f := fun i => ‖(p n).coeff i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.2 j.isLt)
  obtain ⟨c, -, φ, hφ, hc⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hv
  refine ⟨∑ j : Fin (N + 1), C (c j) * X ^ (j : ℕ), ?_, φ, hφ, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 j.isLt)
  · intro i
    simp only [finsetSum_coeff, coeff_C_mul_X_pow]
    by_cases hi : i < N + 1
    · rw [Finset.sum_eq_single ⟨i, hi⟩ (fun j _ hj => ite_eq_right (fun h => hj (Fin.ext h.symm)))
        (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]
      exact (continuous_apply (⟨i, hi⟩ : Fin (N + 1))).continuousAt.tendsto.comp hc
    · have h0 : ∀ n, (p n).coeff i = 0 := fun n =>
        coeff_eq_zero_of_natDegree_lt ((hd n).trans_lt (by omega))
      simp only [Function.comp_apply, h0]
      rw [Finset.sum_eq_zero fun j _ => ite_eq_right (by have := j.isLt; omega)]
      exact tendsto_const_nhds

end FurioLombardo.Vendor.Toolbox.PolyLim
