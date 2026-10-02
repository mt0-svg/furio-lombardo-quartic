import FurioLombardo.M1.Sieve
import FurioLombardo.M1.Local2
import FurioLombardo.M1.Local3
import FurioLombardo.M1.Signature
import FurioLombardo.M1.Primitive
import FurioLombardo.M1.Hypotheses
import FurioLombardo.M1.DataKnown

/-!
# The Selmer set theorem over `K21`

**`selmerSet`**: assume `Cl(K21)[2] = 0` (`ClK21TwoTorsionTrivial`). For every rational point
`P = (x : y : z)` of `C`, the descent value `qSel x y z` (`Q1(P)`, or `Q3(P)` when `Q1(P) = 0`)
is nonzero and is `δ_k t²` for `k = 0` or `k = 1` and some `t ∈ K21`, with `δ_0 = d0`,
`δ_1 = d1` (DataBruin.lean). `selmerSet_class` states the same in `K21^× / K21^×2`.

The chain, for a primitive integer point `a` of `C` and `i = 0` or `2` with `Q_(i+1)(a) ≠ 0`
(`selmer_int`):

1. the class of `Q_(i+1)(a)` is in `K21(S, 2)` (`mem_selmer_of_qO`);
2. the eighteen generators `gU` are in `K21(S, 2)` (`gU_mem`) and independent modulo squares
   (`gProd_eq_sq`); with `rank ≤ 11` (`rank_le`), `#S ≤ 6` (`S_ncard`) and `Cl(K21)[2] = 0`,
   `Q_(i+1)(a) gProd e` is a square for some `e` (`exists_isSquare_mul_prod`);
3. so `SqCond a e` (`sqCond_of`), and `e` is one of the eight survivors of the good prime sieve
   (`sieve_good`); `ℤ/27` kills four of them (`kill3`), the prime `lc` above 2 two more
   (`kill2`); the two left are `survE 4`, `survE 6`;
4. `δ_0 gProd (survE 4) = t_0²` and `δ_1 gProd (survE 6) = t_1²` (kernel checks `ck_known0`,
   `ck_known1`), so `Q_(i+1)(a) = δ_k (s / t_k)²`.

A rational point is `l a` with `a` primitive (`exists_primitive`), and `Q_(i+1)(l a) = l² Q_(i+1)(a)`.
-/

namespace FurioLombardo.M1

open NumberField Kron

/-! ## The two classes -/

/-- zk coordinates of `δ_k`. -/
def dKL (k : ℕ) : List ℤ := [d0L, d1L].getD k []
/-- zk coordinates of `t_k`. -/
def tKL (k : ℕ) : List ℤ := [t0L, t1L].getD k []
/-- zk coordinates of `δ_k⁻¹`. -/
def diKL (k : ℕ) : List ℤ := [d0iL, d1iL].getD k []
/-- The survivor of class `k`. -/
def survOf (k : ℕ) : ℕ := [4, 6].getD k 0

/-- The twists `δ_0 = d0`, `δ_1 = d1`. -/
noncomputable def δK (k : Fin 2) : K21 := zkE (dKL k)

/-- `δ_k gProd (survE (survOf k))`. -/
def knownL (k : ℕ) : KE := .mul (.lin (dKL k)) (gProdKE (survE (survOf k)))
/-- `t_k²`. -/
def knownR (k : ℕ) : KE := .mul (.lin (tKL k)) (.lin (tKL k))

theorem ck_known0 : checkK 512 (.sub (knownL 0) (knownR 0)) = true := by decide +kernel
theorem ck_known1 : checkK 832 (.sub (knownL 1) (knownR 1)) = true := by decide +kernel
theorem ck_inv0 : checkK 192 (.sub (.mul (.lin (dKL 0)) (.lin (diKL 0))) (.int 1)) = true := by
  decide +kernel
theorem ck_inv1 : checkK 192 (.sub (.mul (.lin (dKL 1)) (.lin (diKL 1))) (.int 1)) = true := by
  decide +kernel

theorem known_eq (k : Fin 2) :
    δK k * ((gProd (survE (survOf k)) : 𝓞 K21) : K21) = zkE (tKL k) ^ 2 := by
  have hc : checkK (if (k : ℕ) = 0 then 512 else 832) (.sub (knownL k) (knownR k)) = true := by
    fin_cases k
    exacts [ck_known0, ck_known1]
  have h := evK_eq_of_check _ _ _ hc
  simp only [knownL, knownR, evK_mul, evK_lin, evK_gProdKE] at h
  rw [δK, h, sq]

theorem δK_ne_zero (k : Fin 2) : δK k ≠ 0 := by
  have hc : checkK 192 (.sub (.mul (.lin (dKL k)) (.lin (diKL k))) (.int 1)) = true := by
    fin_cases k
    exacts [ck_inv0, ck_inv1]
  have h := evK_eq_of_check _ _ _ hc
  simp only [evK_mul, evK_lin, evK_int, Int.cast_one] at h
  intro h0
  rw [δK] at h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem gProd_ne_zero (e : Fin 18 → Bool) : ((gProd e : 𝓞 K21) : K21) ≠ 0 := by
  rw [Ne, RingOfIntegers.coe_eq_zero_iff, gProd, subprod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  split
  · exact gO_ne_zero i i.isLt
  · exact one_ne_zero

/-- From `q gProd (survE (survOf k)) = s²` to `q = δ_k t²`. -/
theorem eq_δK_mul_sq (k : Fin 2) (q s : K21)
    (hs : q * ((gProd (survE (survOf k)) : 𝓞 K21) : K21) = s ^ 2) :
    ∃ t : K21, q = δK k * t ^ 2 := by
  have hk := known_eq k
  have hG := gProd_ne_zero (survE (survOf k))
  have hδ := δK_ne_zero k
  have ht : zkE (tKL k) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hk
    exact mul_ne_zero hδ hG hk
  refine ⟨s / zkE (tKL k), ?_⟩
  rw [div_pow, ← hk]
  field_simp
  linear_combination hs

/-! ## Integer points -/

theorem coe_gProd (e : Fin 18 → Bool) :
    subprod (fun i => ((gU i : K21ˣ) : K21)) e = ((gProd e : 𝓞 K21) : K21) := by
  have h := subprod_map (algebraMap (𝓞 K21) K21).toMonoidHom (fun i : Fin 18 => gO i) e
  exact h.symm

/-- The generators are independent modulo squares of `K21`. -/
theorem gU_indep (e : Fin 18 → Bool) (h : IsSquare (subprod (fun i => ((gU i : K21ˣ) : K21)) e)) :
    ∀ i, e i = false := by
  obtain ⟨r, hr⟩ := h
  rw [coe_gProd] at hr
  obtain ⟨s, hs⟩ := exists_sq_of_sq (x := gProd e) (t := r) (by rw [sq, ← hr])
  exact gProd_eq_sq e s hs

/-- **The Selmer set at a primitive integer point.** Theorem 2.7 of the paper. -/
theorem selmer_int (hCl : ClK21TwoTorsionTrivial) (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (i : Fin 3) (hi : i = 0 ∨ i = 2)
    (hne : qO i a ≠ 0) : ∃ k : Fin 2, ∃ t : K21, ((qO i a : 𝓞 K21) : K21) = δK k * t ^ 2 := by
  have hK : ((qO i a : 𝓞 K21) : K21) ≠ 0 := by
    rw [Ne, RingOfIntegers.coe_eq_zero_iff]; exact hne
  have hu := mem_selmer_of_qO a r hr hF i hi (Units.mk0 _ hK) rfl
  have hm : Units.rank K21 + S.ncard + 1 ≤ 18 := by
    have := rank_le; have := S_ncard; omega
  obtain ⟨e, s, hs⟩ := exists_isSquare_mul_prod S S_finite hCl hm gU gU_mem gU_indep _ hu
  rw [coe_gProd, Units.val_mk0] at hs
  obtain ⟨s', hs'⟩ := exists_sq_of_sq (x := qO i a * gProd e) (t := s)
    (by rw [map_mul, sq, ← hs])
  have hsq := sqCond_of a hF e i hi hne s' hs'
  have hK' : ((qO i a : 𝓞 K21) : K21) * ((gProd e : 𝓞 K21) : K21) = ((s' : 𝓞 K21) : K21) ^ 2 := by
    rw [← map_mul, hs', map_pow]
  obtain ⟨k, hk, rfl⟩ := sieve_good a r hr hF e hsq
  interval_cases k
  · exact (kill3 a r hr hF 0 (by norm_num) hsq).elim
  · exact (kill3 a r hr hF 1 (by norm_num) hsq).elim
  · exact (kill3 a r hr hF 2 (by norm_num) hsq).elim
  · exact (kill3 a r hr hF 3 (by norm_num) hsq).elim
  · exact ⟨0, eq_δK_mul_sq 0 _ _ hK'⟩
  · exact (kill2 a r hr hF 5 (Or.inl rfl) hsq).elim
  · exact ⟨1, eq_δK_mul_sq 1 _ _ hK'⟩
  · exact (kill2 a r hr hF 7 (Or.inr rfl) hsq).elim

/-! ## Rational points -/

/-- The value of `Q_(i+1)` at a point of `K21³`. -/
noncomputable def qK (i : Fin 3) (P : Fin 3 → K21) : K21 := Vendor.NetOfConics.qev (fun m => (qC i m : K21)) P

/-- The rational triple `(x, y, z)` in `K21³`. -/
noncomputable def ptK (x y z : ℚ) : Fin 3 → K21 :=
  ![algebraMap ℚ K21 x, algebraMap ℚ K21 y, algebraMap ℚ K21 z]

open Classical in
/-- **The descent value** of `(x : y : z)`: `Q1(P)`, or `Q3(P)` when `Q1(P) = 0`. -/
noncomputable def qSel (x y z : ℚ) : K21 :=
  if qK 0 (ptK x y z) = 0 then qK 2 (ptK x y z) else qK 0 (ptK x y z)

theorem qK_smul (i : Fin 3) (l : K21) (P : Fin 3 → K21) : qK i (l • P) = l ^ 2 * qK i P := by
  simp only [qK, Vendor.NetOfConics.qev, Pi.smul_apply, smul_eq_mul]
  ring

theorem qK_intCast (i : Fin 3) (a : Fin 3 → ℤ) :
    qK i (fun j => ((a j : ℤ) : K21)) = ((qO i a : 𝓞 K21) : K21) := by
  rw [qO, coe_qev, qK]
  simp only [map_intCast]

/-- A rational point of `C` as `l a` with `a` a primitive integer point of `C`. -/
theorem exists_int_point (x y z : ℚ) (hne : (x, y, z) ≠ (0, 0, 0))
    (hF : FurioLombardo.F x y z = 0) :
    ∃ (a r : Fin 3 → ℤ) (l : ℚ), l ≠ 0 ∧ ∑ j, r j * a j = 1 ∧
      FurioLombardo.F (a 0) (a 1) (a 2) = 0 ∧
      ptK x y z = (algebraMap ℚ K21 l) • fun j => ((a j : ℤ) : K21) := by
  obtain ⟨a, b, c, l, hl, rfl, rfl, rfl, r, s, t, hr⟩ := exists_primitive x y z hne
  refine ⟨![a, b, c], ![r, s, t], l, hl, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact hr
  · have h4 : FurioLombardo.F (l * a) (l * b) (l * c) = l ^ 4 * FurioLombardo.F (a : ℚ) b c := by
      simp only [FurioLombardo.F]; ring
    rw [h4, F_intCast] at hF
    have h0 : ((FurioLombardo.F a b c : ℤ) : ℚ) = 0 :=
      (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 4 hl)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact_mod_cast h0
  · funext j
    fin_cases j <;> simp [ptK, map_mul, map_intCast]

/-- **The Selmer set theorem over `K21`** (lane M1): assuming `Cl(K21)[2] = 0`, for every
rational point `(x : y : z)` of `C`, the descent value `qSel x y z` is nonzero and equals
`δ_k t²` for `k = 0` or `k = 1` and some `t ∈ K21`. Remark 2.8 of the paper. -/
theorem selmerSet (hCl : ClK21TwoTorsionTrivial) (x y z : ℚ) (hne : (x, y, z) ≠ (0, 0, 0))
    (hF : FurioLombardo.F x y z = 0) :
    qSel x y z ≠ 0 ∧ ∃ k : Fin 2, ∃ t : K21, qSel x y z = δK k * t ^ 2 := by
  obtain ⟨a, r, l, hl, hr, hFa, hP⟩ := exists_int_point x y z hne hF
  have hl' : algebraMap ℚ K21 l ≠ 0 := (map_ne_zero _).mpr hl
  have hq : ∀ i, qK i (ptK x y z) = algebraMap ℚ K21 l ^ 2 * ((qO i a : 𝓞 K21) : K21) := by
    intro i; rw [hP, qK_smul, qK_intCast]
  have key : ∀ i : Fin 3, (i = 0 ∨ i = 2) → qO i a ≠ 0 →
      qK i (ptK x y z) ≠ 0 ∧ ∃ k : Fin 2, ∃ t : K21, qK i (ptK x y z) = δK k * t ^ 2 := by
    intro i hi hne'
    obtain ⟨k, t, ht⟩ := selmer_int hCl a r hr hFa i hi hne'
    refine ⟨?_, k, algebraMap ℚ K21 l * t, ?_⟩
    · rw [hq]
      refine mul_ne_zero (pow_ne_zero 2 hl') ?_
      rw [Ne, RingOfIntegers.coe_eq_zero_iff]; exact hne'
    · rw [hq, ht]; ring
  have hq0 : qK 0 (ptK x y z) = 0 ↔ qO 0 a = 0 := by
    rw [hq, mul_eq_zero, or_iff_right (pow_ne_zero 2 hl'), RingOfIntegers.coe_eq_zero_iff]
  unfold qSel
  split_ifs with h0
  · have h0' := hq0.mp h0
    obtain ⟨i, hi, hne'⟩ := exists_qO_ne_zero a r hr hFa
    rcases hi with rfl | rfl
    · exact absurd h0' hne'
    · exact key 2 (Or.inr rfl) hne'
  · exact key 0 (Or.inl rfl) fun h => h0 (hq0.mpr h)

/-- The twists as units. -/
noncomputable def δU (k : Fin 2) : K21ˣ := Units.mk0 (δK k) (δK_ne_zero k)

/-- **The Selmer set theorem, in `K21^× / K21^×2`**: the class of the descent value of a
rational point of `C` is the class of `δ_0` or of `δ_1`. -/
theorem selmerSet_class (hCl : ClK21TwoTorsionTrivial) (x y z : ℚ) (hne : (x, y, z) ≠ (0, 0, 0))
    (hF : FurioLombardo.F x y z = 0) :
    ∃ h0 : qSel x y z ≠ 0, ∃ k : Fin 2,
      (QuotientGroup.mk (Units.mk0 (qSel x y z) h0) : SqClass K21) = QuotientGroup.mk (δU k) := by
  obtain ⟨h0, k, t, ht⟩ := selmerSet hCl x y z hne hF
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero] at ht
    exact h0 ht
  refine ⟨h0, k, ((sqClass_mk_eq_mk_iff (δU k) _).mpr ⟨Units.mk0 t ht0, ?_⟩).symm⟩
  simp [δU, ht]

end FurioLombardo.M1
