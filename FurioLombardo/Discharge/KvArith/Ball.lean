import Mathlib
import FurioLombardo.Discharge.M4Cert.Resid
import FurioLombardo.Discharge.M4Cert.Hensel
import FurioLombardo.Discharge.KvArith.Comp.Ball

/-!
# Ball arithmetic on `K_v`: meaning and soundness (lane lean-kv-arith, D1)

The ball `b = ⟨c, e, r, v⟩` of `Comp/Ball.lean` contains `x ∈ K_v` when `‖2^e x - evN c‖ ≤ ‖pv‖^r`
(`Ball.Mem`, which also asks `‖evN c‖ ≤ ‖pv‖^v`), with `evN c = c₀ + c₁ pv + c₂ pv²`: the radius is
`π`-adic and the scale lets centres have negative valuation. Every reduction modulo `m = 2^P` moves a
centre by an element of `2^P O_v = pv^(3P) O_v` (`approxP_mulN` and the others). The rules:

* `Ball.add`, `Ball.sub`: radius `min(r_a, r_b)` after aligning the scales (`Ball.up`);
* `Ball.mulRaw`: `2^(e_a+e_b) x y - c_a c_b = (2^e_a x - c_a) 2^e_b y + c_a (2^e_b y - c_b)`, radius
  `min(r_a + min(v_b, r_b), v_a + r_b)`; `Ball.norm` divides the centre by a power of 2;
* `Ball.inv`: the candidate of `invCand` (unverified) is checked by the residual `c_a c - 2^(e + e')`; the
  exact valuation of the centre (`vN`, exact below `3P`: `norm_evN_eq`) is below the radius, which
  certifies `x ≠ 0` and `‖2^e x‖ = ‖pv‖^(vN c)`;
* `Ball.sqrt`: Hensel's lemma for `Y² = w` near a given root candidate (`exists_sq_eq_of_near`), with
  uniqueness of the root in the output ball (`Ball.sqrt_unique`).
* `Ball.incl`: inclusion of balls, for certificates that store a coarser ball than the computed one
  (`Ball.mem_of_incl`).
-/

namespace FurioLombardo.Discharge.KvArith

open FurioLombardo.Discharge.M4Cert

/-- The element `a₀ + a₁ pv + a₂ pv²` of a natural triple. -/
noncomputable def evN (a : N3) : Kv := (a.1 : Kv) + (a.2.1 : Kv) * pv + (a.2.2 : Kv) * pv ^ 2

/-- `x ≡ evN c` modulo `pv ^ r`. -/
def ApproxP (x : Kv) (c : N3) (r : ℕ) : Prop := ‖x - evN c‖ ≤ ‖pv‖ ^ r

theorem E0N_eq : (E0N : ℤ) = e0 := by
  simp [E0N, e0]

theorem E1N_eq : (E1N : ℤ) = e1 := by
  simp [E1N, e1]

theorem E2N_eq : (E2N : ℤ) = e2 := by
  simp [E2N, e2]

/-- Validity of a context: `m = 2^P` and `neᵢ ≡ -eᵢ (mod m)`. -/
def Ctx.Ok (k : Ctx) : Prop :=
  k.m = 2 ^ k.P ∧ (k.m : ℤ) ∣ k.ne0 + e0 ∧ (k.m : ℤ) ∣ k.ne1 + e1 ∧ (k.m : ℤ) ∣ k.ne2 + e2

theorem dvd_ofP_ne (P E : ℕ) : ((2 ^ P : ℕ) : ℤ) ∣ ((2 ^ P - E % 2 ^ P : ℕ) : ℤ) + (E : ℤ) := by
  have hlt : E % 2 ^ P < 2 ^ P := Nat.mod_lt _ (by positivity)
  rw [Nat.cast_sub hlt.le, Int.natCast_mod]
  rw [Int.emod_def]
  exact ⟨1 + (E : ℤ) / ((2 ^ P : ℕ) : ℤ), by ring⟩

theorem Ctx.ofP_ok (P : ℕ) : (Ctx.ofP P).Ok := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [← E0N_eq]; exact dvd_ofP_ne P E0N
  · rw [← E1N_eq]; exact dvd_ofP_ne P E1N
  · rw [← E2N_eq]; exact dvd_ofP_ne P E2N

section TripleLemmas

variable {k : Ctx}

theorem evN_eq_evZ (a : N3) : evN a = evZ (t3OfN a) := by
  simp [evN, evZ, t3OfN]

theorem norm_pv_pow_three_mul (P : ℕ) : ‖pv‖ ^ (3 * P) = (2⁻¹ : ℝ) ^ P := by
  rw [pow_mul, norm_pv_pow_three]

theorem Ctx.Ok.m_pos (hk : k.Ok) : 0 < k.m := by
  rw [hk.1]; positivity

theorem Ctx.Ok.ne0 (hk : k.Ok) : ((k.ne0 : ℕ) : ZMod k.m) = -((e0 : ℤ) : ZMod k.m) := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hk.2.1
  push_cast at h
  linear_combination h

theorem Ctx.Ok.ne1 (hk : k.Ok) : ((k.ne1 : ℕ) : ZMod k.m) = -((e1 : ℤ) : ZMod k.m) := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hk.2.2.1
  push_cast at h
  linear_combination h

theorem Ctx.Ok.ne2 (hk : k.Ok) : ((k.ne2 : ℕ) : ZMod k.m) = -((e2 : ℤ) : ZMod k.m) := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hk.2.2.2
  push_cast at h
  linear_combination h

/-- Integer triples congruent modulo `m = 2^P` to a natural triple are within `pv^(3P)`. -/
theorem approxP_evZ (hk : k.Ok) (a : T3) (c : N3)
    (h1 : ((a.1 : ℤ) : ZMod k.m) = ((c.1 : ℕ) : ZMod k.m))
    (h2 : ((a.2.1 : ℤ) : ZMod k.m) = ((c.2.1 : ℕ) : ZMod k.m))
    (h3 : ((a.2.2 : ℤ) : ZMod k.m) = ((c.2.2 : ℕ) : ZMod k.m)) : ApproxP (evZ a) c (3 * k.P) := by
  unfold ApproxP
  rw [evN_eq_evZ, ← evZ_sub, norm_pv_pow_three_mul]
  apply norm_evZ_le_of_dvd
  have hm : (2 : ℤ) ^ k.P = ((k.m : ℕ) : ℤ) := by rw [hk.1]; push_cast; rfl
  rw [hm]
  refine ⟨?_, ?_, ?_⟩ <;> rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] <;>
    simp [t3OfN, h1, h2, h3]

theorem norm_evN_le_one (a : N3) : ‖evN a‖ ≤ 1 := by
  rw [evN_eq_evZ]; exact norm_evZ_le_one _

theorem approxP_redN (hk : k.Ok) (a : N3) : ApproxP (evN a) (redN k a) (3 * k.P) := by
  rw [evN_eq_evZ]
  refine approxP_evZ hk _ _ ?_ ?_ ?_ <;> simp [t3OfN, redN]

theorem approxP_addN (hk : k.Ok) (a b : N3) : ApproxP (evN a + evN b) (addN k a b) (3 * k.P) := by
  rw [evN_eq_evZ, evN_eq_evZ, ← evZ_add]
  refine approxP_evZ hk _ _ ?_ ?_ ?_ <;> simp [t3OfN, addN]

theorem evZ_neg' (a : T3) : evZ (-a) = -evZ a := by
  obtain ⟨a0, a1, a2⟩ := a
  simp only [evZ, Prod.neg_mk]; push_cast; ring

theorem approxP_negN (hk : k.Ok) (a : N3) : ApproxP (-evN a) (negN k a) (3 * k.P) := by
  rw [evN_eq_evZ, ← evZ_neg']
  have hm := hk.m_pos
  refine approxP_evZ hk _ _ ?_ ?_ ?_ <;>
    simp [t3OfN, negN, Nat.cast_sub (Nat.mod_lt _ hm).le]

theorem approxP_subN (hk : k.Ok) (a b : N3) : ApproxP (evN a - evN b) (subN k a b) (3 * k.P) := by
  rw [evN_eq_evZ, evN_eq_evZ, ← evZ_sub]
  have hm := hk.m_pos
  refine approxP_evZ hk _ _ ?_ ?_ ?_ <;>
    simp [t3OfN, subN, Nat.cast_sub (Nat.mod_lt _ hm).le, sub_eq_add_neg]

theorem approxP_smulN (hk : k.Ok) (s : ℕ) (a : N3) :
    ApproxP ((s : Kv) * evN a) (smulN k s a) (3 * k.P) := by
  have he : (s : Kv) * evN a = evZ ((s : ℤ) * (a.1 : ℤ), (s : ℤ) * (a.2.1 : ℤ), (s : ℤ) * (a.2.2 : ℤ)) := by
    simp only [evN, evZ]; push_cast; ring
  rw [he]
  refine approxP_evZ hk _ _ ?_ ?_ ?_ <;> simp [smulN]

theorem approxP_mulN (hk : k.Ok) (a b : N3) : ApproxP (evN a * evN b) (mulN k a b) (3 * k.P) := by
  rw [evN_eq_evZ, evN_eq_evZ, ← evZ_mul]
  have h0 := hk.ne0
  have h1 := hk.ne1
  have h2 := hk.ne2
  refine approxP_evZ hk _ _ ?_ ?_ ?_ <;>
    simp only [mulZ, mulN, t3OfN, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Int.cast_sub,
      Int.cast_add, Int.cast_mul, Int.cast_natCast, h0, h1, h2] <;> ring

theorem two_pow_v2_dvd (hk : k.Ok) (n : ℕ) : 2 ^ v2 k n ∣ n := by
  have hg : Nat.gcd n k.m ∣ 2 ^ k.P := hk.1 ▸ Nat.gcd_dvd_right n k.m
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg
  have : v2 k n = j := by unfold v2; rw [hj, Nat.log2_two_pow]
  rw [this, ← hj]
  exact Nat.gcd_dvd_left n k.m

theorem norm_pv_le_one' : ‖pv‖ ≤ 1 := norm_pv_lt_one.le

theorem pv_pow_le_pv_pow {i j : ℕ} (h : i ≤ j) : ‖pv‖ ^ j ≤ ‖pv‖ ^ i :=
  pow_le_pow_of_le_one (norm_nonneg _) norm_pv_le_one' h

theorem pv_pow_lt_pv_pow {i j : ℕ} (h : i < j) : ‖pv‖ ^ j < ‖pv‖ ^ i :=
  pow_lt_pow_right_of_lt_one₀ norm_pv_pos norm_pv_lt_one h

theorem norm_natCast_Kv_le_one (n : ℕ) : ‖(n : Kv)‖ ≤ 1 := by
  have := norm_intCast_le_one (n : ℤ)
  rwa [Int.cast_natCast] at this

theorem norm_two_pow_Kv (j : ℕ) : ‖(2 : Kv) ^ j‖ = ‖pv‖ ^ (3 * j) := by
  rw [norm_pow, norm_two_Kv, norm_pv_pow_three_mul]

theorem norm_natCast_odd (q : ℕ) (hq : ¬ 2 ∣ q) : ‖(q : Kv)‖ = 1 := by
  have h1 : ‖(q : ℚ_[2])‖ = 1 := by
    refine le_antisymm (IsUltrametricDist.norm_natCast_le_one ℚ_[2] q) (not_lt.mp fun h => hq ?_)
    exact Padic.norm_natCast_lt_one_iff.mp h
  rw [← map_natCast (algebraMap ℚ_[2] Kv), M4Cert.norm_algebraMap, h1]

theorem norm_natCast_le_v2 (hk : k.Ok) (n : ℕ) : ‖(n : Kv)‖ ≤ ‖pv‖ ^ (3 * v2 k n) := by
  obtain ⟨q, hq⟩ := two_pow_v2_dvd hk n
  rw [show (n : Kv) = ((2 ^ v2 k n * q : ℕ) : Kv) by rw [← hq], Nat.cast_mul, norm_mul, Nat.cast_pow,
    Nat.cast_ofNat, norm_two_pow_Kv]
  calc ‖pv‖ ^ (3 * v2 k n) * ‖(q : Kv)‖ ≤ ‖pv‖ ^ (3 * v2 k n) * 1 :=
        mul_le_mul_of_nonneg_left (norm_natCast_Kv_le_one q) (by positivity)
    _ = _ := mul_one _

theorem v2_le (hk : k.Ok) (n : ℕ) : v2 k n ≤ k.P := by
  have hg : Nat.gcd n k.m ∣ 2 ^ k.P := hk.1 ▸ Nat.gcd_dvd_right n k.m
  obtain ⟨j, hjP, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg
  have : v2 k n = j := by unfold v2; rw [hj, Nat.log2_two_pow]
  omega

theorem norm_natCast_eq_v2 (hk : k.Ok) {n : ℕ} (h : v2 k n < k.P) :
    ‖(n : Kv)‖ = ‖pv‖ ^ (3 * v2 k n) := by
  have hg : Nat.gcd n k.m ∣ 2 ^ k.P := hk.1 ▸ Nat.gcd_dvd_right n k.m
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg
  have hv : v2 k n = j := by unfold v2; rw [hj, Nat.log2_two_pow]
  obtain ⟨q, hq⟩ := two_pow_v2_dvd hk n
  have hodd : ¬ 2 ∣ q := by
    rintro ⟨r, rfl⟩
    have h1 : 2 ^ (j + 1) ∣ n := ⟨r, by rw [hq, hv]; ring⟩
    have h2 : 2 ^ (j + 1) ∣ k.m := hk.1 ▸ Nat.pow_dvd_pow 2 (by omega)
    have h3 := Nat.dvd_gcd h1 h2
    rw [hj] at h3
    have := Nat.le_of_dvd (by positivity) h3
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self j)
    omega
  rw [show (n : Kv) = ((2 ^ v2 k n * q : ℕ) : Kv) by rw [← hq], Nat.cast_mul, norm_mul, Nat.cast_pow,
    Nat.cast_ofNat, norm_two_pow_Kv, norm_natCast_odd q hodd, mul_one]

theorem norm_evN_le (hk : k.Ok) (a : N3) : ‖evN a‖ ≤ ‖pv‖ ^ vN k a := by
  have t1 : ‖(a.1 : Kv)‖ ≤ ‖pv‖ ^ vN k a :=
    (norm_natCast_le_v2 hk _).trans (pv_pow_le_pv_pow (by unfold vN; omega))
  have t2 : ‖(a.2.1 : Kv) * pv‖ ≤ ‖pv‖ ^ vN k a := by
    rw [norm_mul]
    calc ‖(a.2.1 : Kv)‖ * ‖pv‖ ≤ ‖pv‖ ^ (3 * v2 k a.2.1) * ‖pv‖ :=
          mul_le_mul_of_nonneg_right (norm_natCast_le_v2 hk _) (norm_nonneg _)
      _ = ‖pv‖ ^ (3 * v2 k a.2.1 + 1) := (pow_succ _ _).symm
      _ ≤ _ := pv_pow_le_pv_pow (by unfold vN; omega)
  have t3 : ‖(a.2.2 : Kv) * pv ^ 2‖ ≤ ‖pv‖ ^ vN k a := by
    rw [norm_mul, norm_pow]
    calc ‖(a.2.2 : Kv)‖ * ‖pv‖ ^ 2 ≤ ‖pv‖ ^ (3 * v2 k a.2.2) * ‖pv‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_natCast_le_v2 hk _) (by positivity)
      _ = ‖pv‖ ^ (3 * v2 k a.2.2 + 2) := (pow_add _ _ _).symm
      _ ≤ _ := pv_pow_le_pv_pow (by unfold vN; omega)
  unfold evN
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ t3)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le t1 t2)

theorem norm_add_eq_left_of_lt {x y : Kv} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

theorem norm_evN_eq (hk : k.Ok) {a : N3} (h : vN k a < 3 * k.P) : ‖evN a‖ = ‖pv‖ ^ vN k a := by
  set A := 3 * v2 k a.1
  set B := 3 * v2 k a.2.1 + 1
  set C := 3 * v2 k a.2.2 + 2
  have hvN : vN k a = min A (min B C) := rfl
  have n1 : ‖(a.1 : Kv)‖ ≤ ‖pv‖ ^ A := norm_natCast_le_v2 hk _
  have n2 : ‖(a.2.1 : Kv) * pv‖ ≤ ‖pv‖ ^ B := by
    rw [norm_mul, pow_succ]
    exact mul_le_mul_of_nonneg_right (norm_natCast_le_v2 hk _) (norm_nonneg _)
  have n3 : ‖(a.2.2 : Kv) * pv ^ 2‖ ≤ ‖pv‖ ^ C := by
    rw [norm_mul, norm_pow, pow_add]
    exact mul_le_mul_of_nonneg_right (norm_natCast_le_v2 hk _) (by positivity)
  have two : ∀ {x y : Kv} {i j u : ℕ}, ‖x‖ ≤ ‖pv‖ ^ i → ‖y‖ ≤ ‖pv‖ ^ j → u < i → u < j →
      ‖x + y‖ < ‖pv‖ ^ u := fun hx hy hi hj =>
    lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (hx.trans_lt (pv_pow_lt_pv_pow hi)) (hy.trans_lt (pv_pow_lt_pv_pow hj)))
  unfold evN
  rcases Nat.lt_or_ge A (min B C) with hA | hA
  · -- the first term dominates
    have hu : vN k a = A := by omega
    have e1 : ‖(a.1 : Kv)‖ = ‖pv‖ ^ A := norm_natCast_eq_v2 hk (by omega)
    rw [add_assoc, norm_add_eq_left_of_lt, e1, hu]
    rw [e1]; exact two n2 n3 (by omega) (by omega)
  · rcases Nat.lt_or_ge B C with hB | hB
    · have hu : vN k a = B := by omega
      have e2 : ‖(a.2.1 : Kv) * pv‖ = ‖pv‖ ^ B := by
        rw [norm_mul, norm_natCast_eq_v2 hk (by omega), ← pow_succ]
      rw [show (a.1 : Kv) + (a.2.1 : Kv) * pv + (a.2.2 : Kv) * pv ^ 2 =
          (a.2.1 : Kv) * pv + ((a.1 : Kv) + (a.2.2 : Kv) * pv ^ 2) by ring,
        norm_add_eq_left_of_lt, e2, hu]
      rw [e2]; exact two n1 n3 (by omega) (by omega)
    · have hu : vN k a = C := by omega
      have e3 : ‖(a.2.2 : Kv) * pv ^ 2‖ = ‖pv‖ ^ C := by
        rw [norm_mul, norm_natCast_eq_v2 hk (by omega), norm_pow, ← pow_add]
      rw [show (a.1 : Kv) + (a.2.1 : Kv) * pv + (a.2.2 : Kv) * pv ^ 2 =
          (a.2.2 : Kv) * pv ^ 2 + ((a.1 : Kv) + (a.2.1 : Kv) * pv) by ring,
        norm_add_eq_left_of_lt, e3, hu]
      rw [e3]; exact two n1 n2 (by omega) (by omega)

end TripleLemmas

/-- `x` lies in the ball: `‖2^e x - evN c‖ ≤ ‖pv‖^r`, and the centre bound holds. -/
def Ball.Mem (b : Ball) (x : Kv) : Prop :=
  ApproxP (2 ^ b.e * x) b.c b.r ∧ ‖evN b.c‖ ≤ ‖pv‖ ^ b.v

/-- The centre of a ball as an element of `K_v`. -/
noncomputable def Ball.ctr (b : Ball) : Kv := evN b.c / 2 ^ b.e

section Sound

variable {k : Ctx}

/-- Ultrametric chaining of two bounds. -/
theorem norm_sub_le_pv {x y z : Kv} {i j l : ℕ} (h1 : ‖x - y‖ ≤ ‖pv‖ ^ i)
    (h2 : ‖y - z‖ ≤ ‖pv‖ ^ j) (hi : l ≤ i) (hj : l ≤ j) : ‖x - z‖ ≤ ‖pv‖ ^ l := by
  rw [show x - z = (x - y) + (y - z) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (h1.trans (pv_pow_le_pv_pow hi)) (h2.trans (pv_pow_le_pv_pow hj)))

theorem norm_le_pv_of_sub {x y : Kv} {i j l : ℕ} (h1 : ‖x - y‖ ≤ ‖pv‖ ^ i) (h2 : ‖y‖ ≤ ‖pv‖ ^ j)
    (hi : l ≤ i) (hj : l ≤ j) : ‖x‖ ≤ ‖pv‖ ^ l := by
  have := norm_sub_le_pv (z := 0) h1 (by simpa using h2) hi hj
  simpa using this

/-- `‖x - y‖ ≤ max ‖x‖ ‖y‖` in an ultrametric normed group. -/
theorem norm_sub_le_max_u {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] (x y : E) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  calc ‖x - y‖ = ‖x + -y‖ := by rw [sub_eq_add_neg]
    _ ≤ max ‖x‖ ‖-y‖ := IsUltrametricDist.norm_add_le_max _ _
    _ = max ‖x‖ ‖y‖ := by rw [norm_neg]

theorem two_ne_zero_Kv : (2 : Kv) ≠ 0 := by
  intro h; have := norm_two_Kv; rw [h, norm_zero] at this; norm_num at this

theorem two_pow_ne_zero_Kv (j : ℕ) : (2 : Kv) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero_Kv

/-- The residual of a product against a triple modulo `m`: `‖a b - z‖ ≤ ‖pv‖^min(vN d, 3P)` for
`d = mulN a b - t` and `z ≡ evN t`. -/
theorem norm_mul_sub_le (hk : k.Ok) (a b t : N3) {z : Kv} (hz : ApproxP z t (3 * k.P)) :
    ‖evN a * evN b - z‖ ≤ ‖pv‖ ^ min (vN k (subN k (mulN k a b) t)) (3 * k.P) := by
  have hm := approxP_mulN hk a b
  have hd := approxP_subN hk (mulN k a b) t
  have hv := norm_evN_le hk (subN k (mulN k a b) t)
  simp only [ApproxP] at hm hd hz
  rw [show evN a * evN b - z = ((evN a * evN b - evN (mulN k a b)) +
      ((evN (mulN k a b) - evN t) - evN (subN k (mulN k a b) t))) +
      (evN (subN k (mulN k a b) t) - (z - evN t)) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
    ((norm_sub_le_max_u _ _).trans (max_le ?_ ?_)))
  · exact hm.trans (pv_pow_le_pv_pow (min_le_right _ _))
  · exact hd.trans (pv_pow_le_pv_pow (min_le_right _ _))
  · exact hv.trans (pv_pow_le_pv_pow (min_le_left _ _))
  · exact hz.trans (pv_pow_le_pv_pow (min_le_right _ _))

theorem Ball.mem_ofN (hk : k.Ok) (c : N3) : (Ball.ofN k c).Mem (evN c) := by
  refine ⟨?_, norm_evN_le hk _⟩
  simp only [Ball.ofN, pow_zero, one_mul]
  exact approxP_redN hk c

theorem Ball.mem_ofInt (hk : k.Ok) (z : ℤ) : (Ball.ofInt k z).Mem (z : Kv) := by
  refine ⟨?_, norm_evN_le hk _⟩
  simp only [Ball.ofInt, pow_zero, one_mul]
  have hm : (k.m : ℤ) ≠ 0 := by exact_mod_cast hk.m_pos.ne'
  have he : (z : Kv) = evZ (z, 0, 0) := by simp [evZ]
  rw [he]
  refine approxP_evZ hk _ _ ?_ (by simp) (by simp)
  simp only
  rw [show (((z % (k.m : ℤ)).toNat : ℕ) : ZMod k.m) = (((z % (k.m : ℤ)).toNat : ℤ) : ZMod k.m) by
    push_cast; rfl, Int.toNat_of_nonneg (Int.emod_nonneg z hm), ZMod.intCast_mod]

theorem Ball.mem_exactN (hk : k.Ok) (b : Ball) : (b.exactN k).Mem b.ctr := by
  refine ⟨?_, norm_evN_le hk _⟩
  simp only [ApproxP, Ball.exactN, Ball.ctr]
  rw [mul_div_cancel₀ _ (two_pow_ne_zero_Kv _), sub_self, norm_zero]
  positivity

theorem Ball.up_e (j : ℕ) (b : Ball) : (b.up k j).e = b.e + j := by
  unfold Ball.up; split_ifs with h <;> simp [h]

theorem Ball.mem_up (hk : k.Ok) (j : ℕ) {b : Ball} {x : Kv} (h : b.Mem x) : (b.up k j).Mem x := by
  unfold Ball.up
  split_ifs with hj
  · exact h
  have hs := approxP_smulN hk (2 ^ j) b.c
  push_cast at hs
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [ApproxP] at h1 hs ⊢
    have e1 : ‖(2 : Kv) ^ (b.e + j) * x - (2 : Kv) ^ j * evN b.c‖ ≤ ‖pv‖ ^ (b.r + 3 * j) := by
      rw [show (2 : Kv) ^ (b.e + j) * x - (2 : Kv) ^ j * evN b.c =
        (2 : Kv) ^ j * ((2 : Kv) ^ b.e * x - evN b.c) by ring, norm_mul, norm_two_pow_Kv, pow_add,
        mul_comm (‖pv‖ ^ b.r)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    exact norm_sub_le_pv e1 hs (by omega) (by omega)
  · dsimp only
    have e2 : ‖(2 : Kv) ^ j * evN b.c‖ ≤ ‖pv‖ ^ (b.v + 3 * j) := by
      rw [norm_mul, norm_two_pow_Kv, pow_add, mul_comm (‖pv‖ ^ b.v)]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    exact norm_le_pv_of_sub (by rw [norm_sub_rev]; exact hs) e2 (by omega) (by omega)

/-- The common scale of the two aligned balls of `Ball.add`, `Ball.sub`. -/
theorem Ball.up_e_align (a b : Ball) :
    (a.up k (b.e - a.e)).e = (b.up k (a.e - b.e)).e := by
  rw [Ball.up_e, Ball.up_e]; omega

/-- `Ball.add` on two balls of the same scale. -/
theorem Ball.mem_add_core (hk : k.Ok) {a b : Ball} {x y : Kv} (hx : a.Mem x) (hy : b.Mem y)
    (he : a.e = b.e) :
    (⟨addN k a.c b.c, a.e, min (min a.r b.r) (3 * k.P), min (min a.v b.v) (3 * k.P)⟩ : Ball).Mem
      (x + y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hs := approxP_addN hk a.c b.c
  simp only [ApproxP] at hx1 hy1 hs
  rw [← he] at hy1
  refine ⟨?_, ?_⟩
  · simp only [ApproxP]
    have e1 : ‖(2 : Kv) ^ a.e * (x + y) - (evN a.c + evN b.c)‖ ≤ ‖pv‖ ^ min a.r b.r := by
      rw [show (2 : Kv) ^ a.e * (x + y) - (evN a.c + evN b.c) =
        ((2 : Kv) ^ a.e * x - evN a.c) + ((2 : Kv) ^ a.e * y - evN b.c) by ring]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        (hx1.trans (pv_pow_le_pv_pow (min_le_left _ _)))
        (hy1.trans (pv_pow_le_pv_pow (min_le_right _ _))))
    exact norm_sub_le_pv e1 hs (min_le_left _ _) (min_le_right _ _)
  · have e2 : ‖evN a.c + evN b.c‖ ≤ ‖pv‖ ^ min a.v b.v :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        (hx2.trans (pv_pow_le_pv_pow (min_le_left _ _)))
        (hy2.trans (pv_pow_le_pv_pow (min_le_right _ _))))
    exact norm_le_pv_of_sub (by rw [norm_sub_rev]; exact hs) e2 (min_le_right _ _)
      (min_le_left _ _)

theorem Ball.mem_add (hk : k.Ok) {a b : Ball} {x y : Kv} (hx : a.Mem x) (hy : b.Mem y) :
    (a.add k b).Mem (x + y) :=
  Ball.mem_add_core hk (Ball.mem_up hk (b.e - a.e) hx) (Ball.mem_up hk (a.e - b.e) hy)
    (Ball.up_e_align a b)

/-- `Ball.sub` on two balls of the same scale. -/
theorem Ball.mem_sub_core (hk : k.Ok) {a b : Ball} {x y : Kv} (hx : a.Mem x) (hy : b.Mem y)
    (he : a.e = b.e) :
    (⟨subN k a.c b.c, a.e, min (min a.r b.r) (3 * k.P), vN k (subN k a.c b.c)⟩ : Ball).Mem
      (x - y) := by
  have hx1 := hx.1
  have hy1 := hy.1
  have hs := approxP_subN hk a.c b.c
  simp only [ApproxP] at hx1 hy1 hs
  rw [← he] at hy1
  refine ⟨?_, norm_evN_le hk _⟩
  simp only [ApproxP]
  have e1 : ‖(2 : Kv) ^ a.e * (x - y) - (evN a.c - evN b.c)‖ ≤ ‖pv‖ ^ min a.r b.r := by
    rw [show (2 : Kv) ^ a.e * (x - y) - (evN a.c - evN b.c) =
      ((2 : Kv) ^ a.e * x - evN a.c) + -((2 : Kv) ^ a.e * y - evN b.c) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (hx1.trans (pv_pow_le_pv_pow (min_le_left _ _))) ?_)
    rw [norm_neg]; exact hy1.trans (pv_pow_le_pv_pow (min_le_right _ _))
  exact norm_sub_le_pv e1 hs (min_le_left _ _) (min_le_right _ _)

theorem Ball.mem_sub (hk : k.Ok) {a b : Ball} {x y : Kv} (hx : a.Mem x) (hy : b.Mem y) :
    (a.sub k b).Mem (x - y) :=
  Ball.mem_sub_core hk (Ball.mem_up hk (b.e - a.e) hx) (Ball.mem_up hk (a.e - b.e) hy)
    (Ball.up_e_align a b)

theorem Ball.mem_fresh (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) : (b.fresh k).Mem x :=
  ⟨hx.1, norm_evN_le hk _⟩

theorem Ball.mem_neg (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) : (b.neg k).Mem (-x) := by
  obtain ⟨h1, h2⟩ := hx
  have hs := approxP_negN hk b.c
  simp only [ApproxP] at h1 hs
  refine ⟨?_, ?_⟩
  · simp only [Ball.neg, ApproxP]
    have e1 : ‖(2 : Kv) ^ b.e * -x - -evN b.c‖ ≤ ‖pv‖ ^ b.r := by
      rw [show (2 : Kv) ^ b.e * -x - -evN b.c = -((2 : Kv) ^ b.e * x - evN b.c) by ring, norm_neg]
      exact h1
    exact norm_sub_le_pv e1 hs (by omega) (by omega)
  · simp only [Ball.neg]
    exact norm_le_pv_of_sub (by rw [norm_sub_rev]; exact hs) (by rw [norm_neg]; exact h2) (by omega) (by omega)

/-- A norm bound for the elements of a ball. -/
theorem Ball.norm_le_of_mem {b : Ball} {x : Kv} (hx : b.Mem x) :
    ‖(2 : Kv) ^ b.e * x‖ ≤ ‖pv‖ ^ min b.v b.r :=
  norm_le_pv_of_sub hx.1 hx.2 (min_le_right _ _) (min_le_left _ _)

/-- A norm bound for the elements of a ball of scale 0 whose centre bound and radius are at least `n`. -/
theorem Ball.norm_le_of_mem' {b : Ball} {x : Kv} (hx : b.Mem x) (he : b.e = 0) {n : ℕ}
    (hv : n ≤ b.v) (hr : n ≤ b.r) : ‖x‖ ≤ ‖pv‖ ^ n := by
  have := Ball.norm_le_of_mem hx
  rw [he, pow_zero, one_mul] at this
  exact this.trans (pv_pow_le_pv_pow (le_min hv hr))

/-- The same bound with the recomputed valuation `vN` of the centre in place of the stored bound `v`. -/
theorem Ball.norm_le_of_mem_vN (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) (he : b.e = 0) {n : ℕ}
    (hv : n ≤ vN k b.c) (hr : n ≤ b.r) : ‖x‖ ≤ ‖pv‖ ^ n := by
  have h1 := hx.1
  simp only [ApproxP, he, pow_zero, one_mul] at h1
  exact norm_le_pv_of_sub h1 (norm_evN_le hk _) hr hv

theorem Ball.mem_mulRaw (hk : k.Ok) {a b : Ball} {x y : Kv} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mulRaw k b).Mem (x * y) := by
  have ny := Ball.norm_le_of_mem hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hs := approxP_mulN hk a.c b.c
  simp only [ApproxP] at hx1 hy1 hs
  refine ⟨?_, ?_⟩
  · simp only [Ball.mulRaw, ApproxP]
    have e1 : ‖(2 : Kv) ^ (a.e + b.e) * (x * y) - evN a.c * evN b.c‖ ≤
        ‖pv‖ ^ min (a.r + min b.v b.r) (a.v + b.r) := by
      rw [show (2 : Kv) ^ (a.e + b.e) * (x * y) - evN a.c * evN b.c =
        ((2 : Kv) ^ a.e * x - evN a.c) * ((2 : Kv) ^ b.e * y) +
          evN a.c * ((2 : Kv) ^ b.e * y - evN b.c) by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        calc ‖(2 : Kv) ^ a.e * x - evN a.c‖ * ‖(2 : Kv) ^ b.e * y‖ ≤
              ‖pv‖ ^ a.r * ‖pv‖ ^ min b.v b.r := mul_le_mul hx1 ny (norm_nonneg _) (by positivity)
          _ = ‖pv‖ ^ (a.r + min b.v b.r) := (pow_add _ _ _).symm
          _ ≤ _ := pv_pow_le_pv_pow (min_le_left _ _)
      · rw [norm_mul]
        calc ‖evN a.c‖ * ‖(2 : Kv) ^ b.e * y - evN b.c‖ ≤ ‖pv‖ ^ a.v * ‖pv‖ ^ b.r :=
              mul_le_mul hx2 hy1 (norm_nonneg _) (by positivity)
          _ = ‖pv‖ ^ (a.v + b.r) := (pow_add _ _ _).symm
          _ ≤ _ := pv_pow_le_pv_pow (min_le_right _ _)
    exact norm_sub_le_pv e1 hs (by omega) (by omega)
  · simp only [Ball.mulRaw]
    have e2 : ‖evN a.c * evN b.c‖ ≤ ‖pv‖ ^ (a.v + b.v) := by
      rw [norm_mul, pow_add]; exact mul_le_mul hx2 hy2 (norm_nonneg _) (by positivity)
    exact norm_le_pv_of_sub (by rw [norm_sub_rev]; exact hs) e2 (by omega) (by omega)

theorem Ball.mem_norm (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) : (b.norm k).Mem x := by
  dsimp only [Ball.norm]
  split_ifs with he hj
  · exact hx
  · exact hx
  set j := min b.e (min (b.r / 3) (min (v2 k b.c.1) (min (v2 k b.c.2.1) (v2 k b.c.2.2))))
  have hj1 : 2 ^ j ∣ b.c.1 := (Nat.pow_dvd_pow 2 (by omega)).trans (two_pow_v2_dvd hk _)
  have hj2 : 2 ^ j ∣ b.c.2.1 := (Nat.pow_dvd_pow 2 (by omega)).trans (two_pow_v2_dvd hk _)
  have hj3 : 2 ^ j ∣ b.c.2.2 := (Nat.pow_dvd_pow 2 (by omega)).trans (two_pow_v2_dvd hk _)
  have hev : evN b.c = (2 : Kv) ^ j * evN (b.c.1 / 2 ^ j, b.c.2.1 / 2 ^ j, b.c.2.2 / 2 ^ j) := by
    have e1 : (b.c.1 : Kv) = 2 ^ j * ((b.c.1 / 2 ^ j : ℕ) : Kv) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hj1]
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have e2 : (b.c.2.1 : Kv) = 2 ^ j * ((b.c.2.1 / 2 ^ j : ℕ) : Kv) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hj2]
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have e3 : (b.c.2.2 : Kv) = 2 ^ j * ((b.c.2.2 / 2 ^ j : ℕ) : Kv) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hj3]
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [evN]
    rw [e1, e2, e3]
    ring
  obtain ⟨h1, h2⟩ := hx
  simp only [ApproxP] at h1
  have hpj : 0 < ‖pv‖ ^ (3 * j) := pow_pos norm_pv_pos _
  refine ⟨?_, ?_⟩
  · simp only [ApproxP]
    have heq : (2 : Kv) ^ b.e * x - evN b.c =
        (2 : Kv) ^ j * ((2 : Kv) ^ (b.e - j) * x -
          evN (b.c.1 / 2 ^ j, b.c.2.1 / 2 ^ j, b.c.2.2 / 2 ^ j)) := by
      rw [hev, mul_sub, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [heq, norm_mul, norm_two_pow_Kv] at h1
    rw [show b.r = 3 * j + (b.r - 3 * j) by omega, pow_add] at h1
    exact le_of_mul_le_mul_left h1 hpj
  · rcases Nat.lt_or_ge b.v (3 * j) with hv | hv
    · rw [show b.v - 3 * j = 0 by omega, pow_zero]; exact norm_evN_le_one _
    · rw [hev, norm_mul, norm_two_pow_Kv, show b.v = 3 * j + (b.v - 3 * j) by omega, pow_add] at h2
      exact le_of_mul_le_mul_left h2 hpj

theorem Ball.mem_mul (hk : k.Ok) {a b : Ball} {x y : Kv} (hx : a.Mem x) (hy : b.Mem y) :
    (a.mul k b).Mem (x * y) :=
  Ball.mem_norm hk (Ball.mem_mulRaw hk hx hy)

/-- The norm of an element of a ball whose centre is certified nonzero. -/
theorem Ball.norm_eq_of_nz (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) (h : b.nz k = true) :
    ‖(2 : Kv) ^ b.e * x‖ = ‖pv‖ ^ vN k b.c := by
  simp only [Ball.nz, Bool.and_eq_true, decide_eq_true_eq] at h
  have hc := norm_evN_eq hk h.2
  have h1 := hx.1
  simp only [ApproxP] at h1
  rw [show (2 : Kv) ^ b.e * x = evN b.c + ((2 : Kv) ^ b.e * x - evN b.c) by ring,
    norm_add_eq_left_of_lt, hc]
  rw [hc]; exact h1.trans_lt (pv_pow_lt_pv_pow h.1)

theorem Ball.ne_zero_of_nz (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) (h : b.nz k = true) :
    x ≠ 0 := by
  intro h0
  have := Ball.norm_eq_of_nz hk hx h
  rw [h0, mul_zero, norm_zero] at this
  exact (pow_pos norm_pv_pos _).ne' this.symm

/-- The core of `Ball.mem_inv`, for any candidate `c0` and scale `e'`. -/
theorem Ball.mem_inv_core (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) (hnz : b.nz k = true)
    (c0 : N3) (e' r' : ℕ)
    (hr' : r' = min (min (vN k (subN k (mulN k b.c c0) ((2 ^ (b.e + e')) % k.m, 0, 0))) (3 * k.P))
      (vN k c0 + b.r)) (hu : vN k b.c ≤ r') :
    (⟨c0, e', r' - vN k b.c, vN k c0⟩ : Ball).Mem x⁻¹ := by
  have hx0 := Ball.ne_zero_of_nz hk hx hnz
  have hX := Ball.norm_eq_of_nz hk hx hnz
  refine ⟨?_, norm_evN_le hk _⟩
  simp only [ApproxP]
  have h1 := hx.1
  simp only [ApproxP] at h1
  have ht : ApproxP ((2 : Kv) ^ (b.e + e')) ((2 ^ (b.e + e')) % k.m, 0, 0) (3 * k.P) := by
    have := approxP_redN hk ((2 ^ (b.e + e') : ℕ), 0, 0)
    simpa [redN, evN] using this
  have hA := norm_mul_sub_le hk b.c c0 _ ht
  have hc0 := norm_evN_le hk c0
  set X := (2 : Kv) ^ b.e * x with hXdef
  have hX0 : X ≠ 0 := mul_ne_zero (two_pow_ne_zero_Kv _) hx0
  have key : ‖(2 : Kv) ^ (b.e + e') - X * evN c0‖ ≤ ‖pv‖ ^ r' := by
    rw [show (2 : Kv) ^ (b.e + e') - X * evN c0 =
      -(evN b.c * evN c0 - (2 : Kv) ^ (b.e + e')) + (evN b.c - X) * evN c0 by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_neg]; exact hA.trans (pv_pow_le_pv_pow (by omega))
    · rw [norm_mul, norm_sub_rev]
      calc ‖X - evN b.c‖ * ‖evN c0‖ ≤ ‖pv‖ ^ b.r * ‖pv‖ ^ vN k c0 :=
            mul_le_mul h1 hc0 (norm_nonneg _) (by positivity)
        _ = ‖pv‖ ^ (vN k c0 + b.r) := by rw [← pow_add, add_comm]
        _ ≤ _ := pv_pow_le_pv_pow (by omega)
  have heq : (2 : Kv) ^ e' * x⁻¹ - evN c0 = ((2 : Kv) ^ (b.e + e') - X * evN c0) / X := by
    rw [eq_div_iff hX0, hXdef, pow_add]
    field_simp
  rw [heq, norm_div, hX, div_le_iff₀ (pow_pos norm_pv_pos _), ← pow_add, Nat.sub_add_cancel hu]
  exact key

/-- **Soundness of the inverse.** -/
theorem Ball.mem_inv (hk : k.Ok) {b b' : Ball} {x : Kv} (hx : b.Mem x) (h : b.inv k = some b') :
    x ≠ 0 ∧ b'.Mem x⁻¹ := by
  simp only [Ball.inv] at h
  split_ifs at h with hu <;> try simp only [reduceCtorEq] at h
  all_goals
    have hnz : b.nz k = true := by simp [Ball.nz, hu.1, hu.2]
    refine ⟨Ball.ne_zero_of_nz hk hx hnz, ?_⟩
    cases h
    exact Ball.mem_inv_core hk hx hnz _ _ _ rfl (by assumption)

/-- **Hensel's lemma for square roots** in a complete ultrametric field. -/
theorem exists_sq_eq_of_near {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {w s : K} (hs : ‖s‖ ≤ 1) (h : ‖s ^ 2 - w‖ < ‖2 * s‖ ^ 2) :
    ∃ y : K, y ^ 2 = w ∧ ‖y - s‖ ≤ ‖s ^ 2 - w‖ / ‖2 * s‖ := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h2s : ‖2 * s‖ ≤ 1 := by
    rw [norm_mul]; exact (mul_le_mul h2 hs (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hw : ‖w‖ ≤ 1 := by
    have hsw : ‖s ^ 2 - w‖ ≤ 1 := h.le.trans (pow_le_one₀ (norm_nonneg _) h2s)
    rw [show w = s ^ 2 - (s ^ 2 - w) by ring]
    refine (norm_sub_le_max_u _ _).trans (max_le ?_ hsw)
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hs
  set f : Polynomial K := Polynomial.X ^ 2 - Polynomial.C w
  have hf : ∀ i, ‖f.coeff i‖ ≤ 1 := by
    intro i
    simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs with h1 h2 <;> first | (exfalso; omega) | simp [hw]
  have hfe : f.eval s = s ^ 2 - w := by simp [f]
  have hde : f.derivative.eval s = 2 * s := by simp [f]; norm_num
  obtain ⟨z, hz, hle⟩ := hensel_of_norm_lt f hf s hs (by rw [hfe, hde]; exact h)
  refine ⟨z, ?_, by rwa [hfe, hde] at hle⟩
  have : f.eval z = z ^ 2 - w := by simp [f]
  rw [this] at hz; linear_combination hz

/-- The core of `Ball.exists_mem_sqrt`. -/
theorem Ball.exists_mem_sqrt_core (hk : k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) (s' : N3)
    (es j q : ℕ) (hj : b.e + j = 2 * es)
    (hq : q = min (min (vN k (subN k (mulN k s' s') (smulN k (2 ^ j) b.c))) (3 * k.P))
      (3 * j + b.r))
    (hvs : vN k s' < 3 * k.P) (h6 : 2 * vN k s' + 6 < q) :
    ∃ y : Kv, y ^ 2 = x ∧ (⟨s', es, q - 3 - vN k s', vN k s'⟩ : Ball).Mem y := by
  set vs := vN k s'
  have hs := approxP_smulN hk (2 ^ j) b.c
  push_cast at hs
  have hA := norm_mul_sub_le hk s' s' _ hs
  have h1 := hx.1
  simp only [ApproxP] at h1
  set W := (2 : Kv) ^ (2 * es) * x
  set S := evN s'
  have hS : ‖S‖ = ‖pv‖ ^ vs := norm_evN_eq hk hvs
  have hW : ‖S ^ 2 - W‖ ≤ ‖pv‖ ^ q := by
    rw [show S ^ 2 - W = (S * S - (2 : Kv) ^ j * evN b.c) +
      -((2 : Kv) ^ j * ((2 : Kv) ^ b.e * x - evN b.c)) by
      simp only [W]; rw [← hj, pow_add]; ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact hA.trans (pv_pow_le_pv_pow (by omega))
    · rw [norm_neg, norm_mul, norm_two_pow_Kv]
      calc ‖pv‖ ^ (3 * j) * ‖(2 : Kv) ^ b.e * x - evN b.c‖ ≤ ‖pv‖ ^ (3 * j) * ‖pv‖ ^ b.r :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖pv‖ ^ (3 * j + b.r) := (pow_add _ _ _).symm
        _ ≤ _ := pv_pow_le_pv_pow (by omega)
  have h2S : ‖2 * S‖ = ‖pv‖ ^ (3 + vs) := by
    rw [norm_mul, hS, norm_two_Kv, pow_add, ← norm_pv_pow_three]
  have hlt : ‖S ^ 2 - W‖ < ‖2 * S‖ ^ 2 := by
    rw [h2S, ← pow_mul]
    exact hW.trans_lt (pv_pow_lt_pv_pow (by omega))
  obtain ⟨Y, hY, hYS⟩ := exists_sq_eq_of_near (norm_evN_le_one s') hlt
  refine ⟨Y / 2 ^ es, ?_, ?_, norm_evN_le hk _⟩
  · rw [div_pow, hY, ← pow_mul, mul_comm es 2]
    exact mul_div_cancel_left₀ _ (two_pow_ne_zero_Kv _)
  · simp only [ApproxP]
    rw [mul_div_cancel₀ _ (two_pow_ne_zero_Kv _)]
    refine hYS.trans ?_
    rw [h2S, div_le_iff₀ (pow_pos norm_pv_pos _), ← pow_add]
    exact hW.trans (pv_pow_le_pv_pow (by omega))

/-- **Soundness of the square root**: a root exists in the output ball. -/
theorem Ball.exists_mem_sqrt (hk : k.Ok) {b b' : Ball} {x : Kv} {s : N3} {es : ℕ} (hx : b.Mem x)
    (h : b.sqrt k s es = some b') : ∃ y : Kv, y ^ 2 = x ∧ b'.Mem y := by
  simp only [Ball.sqrt] at h
  split_ifs at h with hj hc <;> try simp only [reduceCtorEq] at h
  cases h
  exact Ball.exists_mem_sqrt_core hk hx _ _ _ _ (by omega) rfl hc.1 hc.2

/-- The core of `Ball.sqrt_unique`. -/
theorem Ball.sqrt_unique_core (hk : k.Ok) (s' : N3) (es q : ℕ) (hvs : vN k s' < 3 * k.P)
    (h6 : 2 * vN k s' + 6 < q) {y y' : Kv} (hy : (⟨s', es, q - 3 - vN k s', vN k s'⟩ : Ball).Mem y)
    (hy' : (⟨s', es, q - 3 - vN k s', vN k s'⟩ : Ball).Mem y') (h2 : y ^ 2 = y' ^ 2) : y = y' := by
  have hyy : (y - y') * (y + y') = 0 := by linear_combination h2
  rcases mul_eq_zero.mp hyy with h0 | h0
  · exact sub_eq_zero.mp h0
  exfalso
  have hy1 := hy.1
  have hy1' := hy'.1
  simp only [ApproxP] at hy1 hy1'
  have hS : ‖evN s'‖ = ‖pv‖ ^ vN k s' := norm_evN_eq hk hvs
  have e1 : (2 : Kv) * evN s' = -((2 : Kv) ^ es * y - evN s') - ((2 : Kv) ^ es * y' - evN s') := by
    rw [show y' = -y by linear_combination h0]; ring
  have hb : ‖(2 : Kv) * evN s'‖ ≤ ‖pv‖ ^ (q - 3 - vN k s') := by
    rw [e1]
    refine (norm_sub_le_max_u _ _).trans (max_le ?_ hy1')
    rw [norm_neg]; exact hy1
  rw [norm_mul, hS, norm_two_Kv, ← norm_pv_pow_three, ← pow_add] at hb
  exact absurd hb (not_le.mpr (pv_pow_lt_pv_pow (by omega)))

/-- The root in the output ball of `Ball.sqrt` is unique. -/
theorem Ball.sqrt_unique (hk : k.Ok) {b b' : Ball} {s : N3} {es : ℕ}
    (h : b.sqrt k s es = some b') {y y' : Kv} (hy : b'.Mem y) (hy' : b'.Mem y') (h2 : y ^ 2 = y' ^ 2) :
    y = y' := by
  simp only [Ball.sqrt] at h
  split_ifs at h with hj hc <;> try simp only [reduceCtorEq] at h
  cases h
  exact Ball.sqrt_unique_core hk _ _ _ hc.1 hc.2 hy hy' h2

/-- **Inclusion**: a certificate ball containing the computed one. -/
theorem Ball.mem_of_incl (hk : k.Ok) {b b' : Ball} {x : Kv} (hx : b.Mem x) (h : b.incl k b' = true) :
    b'.Mem x := by
  simp only [Ball.incl, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨he, hr⟩, hd⟩, hv⟩ := h
  obtain ⟨ha1, -⟩ := Ball.mem_up hk (b'.e - b.e) hx
  have hae := Ball.up_e (k := k) (b'.e - b.e) b
  set a := b.up k (b'.e - b.e)
  rw [hae, Nat.add_sub_cancel' he] at ha1
  simp only [ApproxP] at ha1
  have hs := approxP_subN hk a.c b'.c
  simp only [ApproxP] at hs
  have hvd := norm_evN_le hk (subN k a.c b'.c)
  have hab : ‖evN a.c - evN b'.c‖ ≤ ‖pv‖ ^ b'.r := by
    rw [show evN a.c - evN b'.c = (evN a.c - evN b'.c - evN (subN k a.c b'.c)) +
      evN (subN k a.c b'.c) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (hs.trans (pv_pow_le_pv_pow (by omega)))
      (hvd.trans (pv_pow_le_pv_pow (by omega))))
  exact ⟨norm_sub_le_pv ha1 hab hr le_rfl,
    (norm_evN_le hk _).trans (pv_pow_le_pv_pow hv)⟩

/-! ## Bridges to `M4Cert.Approx` -/

theorem Ball.mem_ofApprox (hk : k.Ok) {x : Kv} {t : T3} {n : ℕ} (h : Approx x t n) :
    (Ball.ofApprox k t n).Mem x := by
  refine ⟨?_, norm_evN_le hk _⟩
  simp only [Ball.ofApprox, pow_zero, one_mul, ApproxP]
  have hm : (k.m : ℤ) ≠ 0 := by exact_mod_cast hk.m_pos.ne'
  have hc : ∀ z : ℤ, (((z % (k.m : ℤ)).toNat : ℕ) : ZMod k.m) = ((z : ℤ) : ZMod k.m) := by
    intro z
    rw [show (((z % (k.m : ℤ)).toNat : ℕ) : ZMod k.m) = (((z % (k.m : ℤ)).toNat : ℤ) : ZMod k.m) by
      push_cast; rfl, Int.toNat_of_nonneg (Int.emod_nonneg z hm), ZMod.intCast_mod]
  have ht := approxP_evZ hk t (natOfT3 k t) (hc _).symm (hc _).symm (hc _).symm
  simp only [ApproxP] at ht
  unfold Approx at h
  rw [← norm_pv_pow_three_mul] at h
  exact norm_sub_le_pv h ht (min_le_left _ _) (min_le_right _ _)

/-- A ball of scale 0 and radius at least `3q` gives the residue modulo `2^q`. -/
theorem Ball.approx_of_mem {b : Ball} {x : Kv} (hx : b.Mem x) (he : b.e = 0) {q : ℕ}
    (hq : 3 * q ≤ b.r) : Approx x (t3OfN b.c) q := by
  have h1 := hx.1
  simp only [ApproxP, he, pow_zero, one_mul] at h1
  unfold Approx
  rw [← evN_eq_evZ, ← norm_pv_pow_three_mul]
  exact h1.trans (pv_pow_le_pv_pow hq)

end Sound

end FurioLombardo.Discharge.KvArith
