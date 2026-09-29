import FurioLombardo.M1.SqCond
import FurioLombardo.M1.Valuation
import FurioLombardo.M1.Data2

/-!
# The local step at the prime `lc` above 2: the survivors 5 and 7 are killed

`π = lc = gO 14` has norm `±2`, so it is a prime element; `2 = π ^ 6 U` with
`U = eO 0 · gO 12 ^ 3 · gO 13 ^ 12` prime to `π` (`gO 12 = 1 + π T12`, `gO 13 = 1 + π T13`, kernel
identities), and `8 = π ^ 18 U ^ 3`.

A primitive integer point `a` is `λ P + 8 b` with `λ` odd and `P` a point of one of the charts
`(x, y, 1)`, `(1, y, 2 z)`, `(2 x, 1, 2 z)` modulo 8 (`lc_chart`), and `F(P) ≡ 0 (mod 8)`
(`lc_F8`). Every such `P` (32 of them, kernel check `ck_lcChart`) carries, for `k = 5` and `k = 7`,
a leaf certificate for one conic `Q_i` (`i ∈ {0, 2}`, data Data2.lean, kernel check `ck_lcLeaves`)
with `w0 = Q_i(P) G'`, `G = gProd (survE k) = G' + 8 H`:
* odd leaf: `w0 = π ^ v (1 + π T)` with `v` odd, `v < 18`;
* defect leaf: `w0 = π ^ (2 j) ((1 + π S) ^ 2 + π ^ d (1 + π Z))` with `d` odd, `d < 12`,
  `2 j + d < 18`.
Then `Q_i(a) G = λ² w0 + 8 R` is not a square (`leaf_odd`, `leaf_dfc`), against `SqCond`.
When `Q_i(a) = 0` the same argument applies to `0 = 0²`.
-/

namespace FurioLombardo.M1

open NumberField Kron Vendor.NetOfConics

/-! ## Valuation lemmas at a prime element `π` with `2 = π ^ 6 U` -/

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] {π U : R}

omit [IsDomain R] in
theorem lc_not_dvd (hπ : Prime π) {Y : R} (T : R) (h : Y = 1 + π * T) : ¬ π ∣ Y := by
  intro hd
  apply hπ.not_isUnit
  have h1 : π ∣ 1 := by
    have := dvd_sub hd (dvd_mul_right π T)
    rwa [h, add_sub_cancel_right] at this
  exact isUnit_of_dvd_one h1

theorem odd_sq_eq (lam : ℤ) (hlam : Odd lam) : ∃ c : ℤ, lam ^ 2 = 1 + 8 * c := by
  obtain ⟨m, rfl⟩ := hlam
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self m
  exact ⟨t, by linear_combination 4 * ht⟩

omit [IsDomain R] in
theorem odd_sq_cast (lam : ℤ) (c : ℤ) (hc : lam ^ 2 = 1 + 8 * c) :
    (lam : R) ^ 2 = 1 + 8 * (c : R) := by
  have := congrArg (Int.cast : ℤ → R) hc
  push_cast at this
  exact this

theorem sq_extract (hπ : Prime π) : ∀ (j : ℕ) (X s : R), π ^ (2 * j) * X = s ^ 2 →
    ∃ t : R, t ^ 2 = X
  | 0, X, s, h => ⟨s, by simpa using h.symm⟩
  | j + 1, X, s, h => by
    have hd : π ∣ s ^ 2 := ⟨π ^ (2 * j + 1) * X, by rw [← h]; ring⟩
    obtain ⟨s1, rfl⟩ := hπ.dvd_of_dvd_pow hd
    refine sq_extract hπ j X s1 ?_
    have h' : π ^ 2 * (π ^ (2 * j) * X) = π ^ 2 * s1 ^ 2 := by
      calc π ^ 2 * (π ^ (2 * j) * X) = π ^ (2 * (j + 1)) * X := by ring
        _ = (π * s1) ^ 2 := h
        _ = π ^ 2 * s1 ^ 2 := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) h'

omit [IsDomain R] in
theorem eight_eq (h2 : (2 : R) = π ^ 6 * U) : (8 : R) = π ^ 18 * U ^ 3 := by
  rw [show (8 : R) = 2 ^ 3 by norm_num, h2]; ring

/-- **Odd leaf**: `λ² π ^ v (1 + π T) + 8 R` is not a square for `v` odd, `v < 18`. -/
theorem leaf_odd (hπ : Prime π) (h2 : (2 : R) = π ^ 6 * U) (lam : ℤ) (hlam : Odd lam)
    (w0 R' T s : R) (v : ℕ) (hv : Odd v) (hv18 : v < 18) (hw : w0 = π ^ v * (1 + π * T))
    (hX : (lam : R) ^ 2 * w0 + 8 * R' = s ^ 2) : False := by
  obtain ⟨c, hc⟩ := odd_sq_eq lam hlam
  have hc' := odd_sq_cast (R := R) lam c hc
  obtain ⟨n, hn⟩ : ∃ n, n = 17 - v := ⟨_, rfl⟩
  have e18 : π ^ 18 = π ^ v * π * π ^ n := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (lam : R) ^ 2 * (1 + π * T) + π * π ^ n * U ^ 3 * R' := ⟨_, rfl⟩
  have hs : π ^ v * Y = s ^ 2 := by rw [← hX, hw, eight_eq h2, e18, hY]; ring
  have hY1 : Y = 1 + π * (T + π ^ 17 * U ^ 3 * c * (1 + π * T) + π ^ n * U ^ 3 * R') := by
    rw [hY, hc', eight_eq h2]; ring
  have hev := even_of_prime_pow_mul_eq_sq hπ v Y s (lc_not_dvd hπ _ hY1) hs
  exact (Nat.not_even_iff_odd.mpr hv) hev

/-- **Defect leaf**: `λ² π ^ (2 j) ((1 + π S)² + π ^ d (1 + π Z)) + 8 R` is not a square for
`d` odd, `d < 12`, `2 j + d < 18`. -/
theorem leaf_dfc (hπ : Prime π) (h2 : (2 : R) = π ^ 6 * U) (hU : ¬ π ∣ U) (lam : ℤ)
    (hlam : Odd lam) (w0 R' S Z s : R) (j d : ℕ) (hd : Odd d) (hd12 : d < 12)
    (hjd : 2 * j + d < 18) (hw : w0 = π ^ (2 * j) * ((1 + π * S) ^ 2 + π ^ d * (1 + π * Z)))
    (hX : (lam : R) ^ 2 * w0 + 8 * R' = s ^ 2) : False := by
  obtain ⟨c, hc⟩ := odd_sq_eq lam hlam
  have hc' := odd_sq_cast (R := R) lam c hc
  obtain ⟨m, hm⟩ := hlam
  have hm' : (lam : R) = 1 + 2 * (m : R) := by rw [hm]; push_cast; ring
  obtain ⟨n, hn⟩ : ∃ n, n = 17 - 2 * j - d := ⟨_, rfl⟩
  have e18 : π ^ 18 = π ^ (2 * j) * π ^ d * π * π ^ n := by
    rw [← pow_add, ← pow_succ, ← pow_add]; congr 1; omega
  obtain ⟨X', hX'⟩ : ∃ X', X' = (lam : R) ^ 2 * ((1 + π * S) ^ 2 + π ^ d * (1 + π * Z)) +
      π ^ d * π * π ^ n * U ^ 3 * R' := ⟨_, rfl⟩
  have hs : π ^ (2 * j) * X' = s ^ 2 := by rw [← hX, hw, eight_eq h2, e18, hX']; ring
  obtain ⟨t, ht⟩ := sq_extract hπ j X' s hs
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (lam : R) * (1 + π * S) := ⟨_, rfl⟩
  obtain ⟨Z', hZ'⟩ : ∃ Z', Z' = (lam : R) ^ 2 * (1 + π * Z) + π * π ^ n * U ^ 3 * R' := ⟨_, rfl⟩
  have hprod : (t - s0) * (t + s0) = π ^ d * Z' := by
    have e : (t - s0) * (t + s0) = t ^ 2 - s0 ^ 2 := by ring
    rw [e, ht, hX', hs0, hZ']; ring
  have hs0' : ¬ π ∣ s0 := lc_not_dvd hπ (S + π ^ 5 * U * m * (1 + π * S)) (by
    rw [hs0, hm', h2]; ring)
  have hZ'' : ¬ π ∣ Z' :=
    lc_not_dvd hπ (Z + π ^ 17 * U ^ 3 * c * (1 + π * Z) + π ^ n * U ^ 3 * R') (by
      rw [hZ', hc', eight_eq h2]; ring)
  exact no_sq_of_defect hπ 6 U h2 hU s0 t Z' hs0' hZ'' d hd (by omega) hprod

end Generic

/-! ## The prime `π = gO 14` -/

theorem lc_prime : Prime (gO 14) := by
  have hn : Ideal.absNorm (Ideal.span {gO 14}) = 2 := by rw [absNorm_span_gO, natAbs_nZ_lc]
  have hP : (Ideal.span {gO 14}).IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by rw [hn]; exact Nat.prime_two)
  exact (Ideal.span_singleton_prime (gO_ne_zero 14 (by norm_num))).mp hP

/-- `U` with `2 = π ^ 6 U`. -/
noncomputable def lcU : 𝓞 K21 := eO 0 * gO 12 ^ 3 * gO 13 ^ 12

theorem two_eq_lc : (2 : 𝓞 K21) = gO 14 ^ 6 * lcU := by rw [two_eq, lcU]; ring

/-- `π = lc` as an expression. -/
def lcπE : KE := gE 14

/-- `1 + π T`. -/
def onePE (T : List ℤ) : KE := .add (.int 1) (.mul lcπE (.lin T))

@[simp] theorem evK_lcπE : evK lcπE = ((gO 14 : 𝓞 K21) : K21) := rfl

theorem evK_onePE (T : List ℤ) :
    evK (onePE T) = 1 + ((gO 14 : 𝓞 K21) : K21) * ((zkO T : 𝓞 K21) : K21) := by
  simp [onePE]

theorem ck_lcT12 : checkK (lcKG.getD 2 0) (.sub (gE 12) (onePE lcT12)) = true := by decide +kernel
theorem ck_lcT13 : checkK (lcKG.getD 3 0) (.sub (gE 13) (onePE lcT13)) = true := by decide +kernel

theorem eq_onePE (i : ℕ) (T : List ℤ) (kk : ℕ) (h : checkK kk (.sub (gE i) (onePE T)) = true) :
    gO i = 1 + gO 14 * zkO T := by
  apply RingOfIntegers.coe_injective
  have h1 := evK_eq_of_check _ _ _ h
  rw [evK_onePE, evK_gE] at h1
  simp only [map_add, map_one, map_mul]
  exact h1

theorem lc_not_dvd_U : ¬ gO 14 ∣ lcU := by
  have hπ := lc_prime
  intro h
  rw [lcU] at h
  rcases hπ.dvd_or_dvd h with h | h
  · rcases hπ.dvd_or_dvd h with h | h
    · exact hπ.not_isUnit
        (isUnit_of_dvd_unit h (IsUnit.of_mul_eq_one _ (eO_mul_eIO 0 (by norm_num))))
    · exact lc_not_dvd hπ _ (eq_onePE 12 lcT12 _ ck_lcT12) (hπ.dvd_of_dvd_pow h)
  · exact lc_not_dvd hπ _ (eq_onePE 13 lcT13 _ ck_lcT13) (hπ.dvd_of_dvd_pow h)

/-! ## `G = gProd (survE k) = G' + 8 H` -/

/-- The product of the generators selected by `e`, as an expression. -/
def gProdKE (e : Fin 18 → Bool) : KE :=
  KE.prod ((List.finRange 18).map fun i => if e i then gE i else .int 1)

theorem evK_gProdKE (e : Fin 18 → Bool) : evK (gProdKE e) = ((gProd e : 𝓞 K21) : K21) := by
  simp only [gProdKE, evK_prod, List.map_map, gProd, subprod, Fin.prod_univ_def]
  change _ = algebraMap (𝓞 K21) K21 _
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left (fun i _ => ?_)
  by_cases h : e i <;> simp [h]

/-- `gProd (survE k) - (G' + 8 H)`. -/
def lcGE (k : ℕ) (Gp H : List ℤ) : KE :=
  .sub (gProdKE (survE k)) (.add (.lin Gp) (.mul (.int 8) (.lin H)))

theorem ck_lcG5 : checkK (lcKG.getD 0 0) (lcGE 5 lcGp5 lcH5) = true := by decide +kernel
theorem ck_lcG7 : checkK (lcKG.getD 1 0) (lcGE 7 lcGp7 lcH7) = true := by decide +kernel

theorem gProd_eq_of_check (k kk : ℕ) (Gp H : List ℤ) (h : checkK kk (lcGE k Gp H) = true) :
    gProd (survE k) = zkO Gp + 8 * zkO H := by
  apply RingOfIntegers.coe_injective
  have h1 := evK_eq_of_check _ _ _ h
  rw [evK_gProdKE] at h1
  simp only [evK_add, evK_mul, evK_lin, evK_int] at h1
  simp only [map_add, map_mul, map_ofNat, coe_zkO]
  rw [show (algebraMap (𝓞 K21) K21) (gProd (survE k)) = ((gProd (survE k) : 𝓞 K21) : K21) from rfl,
    h1]
  push_cast
  ring

/-! ## The conics at a point `P` -/

/-- `Q_(i+1)(P)` for an integer point `P`. -/
noncomputable def qPO (i : Fin 3) (P : List ℤ) : 𝓞 K21 :=
  qev (qC i) (fun j => ((P.getD j 0 : ℤ) : 𝓞 K21))

/-- The value of `Q_(i+1)` at the integer point `P` as an expression. -/
def qPE (i : ℕ) (P : List ℤ) : KE :=
  .add (.add (.add (.add (.add (.mul (.lin (qcA i 0)) (.int (P.getD 0 0 * P.getD 0 0)))
    (.mul (.lin (qcA i 1)) (.int (P.getD 0 0 * P.getD 1 0))))
    (.mul (.lin (qcA i 2)) (.int (P.getD 0 0 * P.getD 2 0))))
    (.mul (.lin (qcA i 3)) (.int (P.getD 1 0 * P.getD 1 0))))
    (.mul (.lin (qcA i 4)) (.int (P.getD 1 0 * P.getD 2 0))))
    (.mul (.lin (qcA i 5)) (.int (P.getD 2 0 * P.getD 2 0)))

theorem evK_qPE (i : ℕ) (hi : i < 3) (P : List ℤ) :
    evK (qPE i P) = ((qPO ⟨i, hi⟩ P : 𝓞 K21) : K21) := by
  simp only [qPE, qPO, qev, qC, evK_add, evK_mul, evK_lin, evK_int, map_add, map_mul, map_pow,
    map_intCast, coe_zkO]
  push_cast
  have h3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have h4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, h3, h4, h5]
  ring

theorem qev_affine {R : Type*} [CommRing R] (c : Fin 6 → R) (l : R) (P B : Fin 3 → R) :
    ∃ R1, qev c (fun j => l * P j + 8 * B j) = l ^ 2 * qev c P + 8 * R1 :=
  ⟨l * (c 0 * (2 * P 0 * B 0) + c 1 * (P 0 * B 1 + P 1 * B 0) + c 2 * (P 0 * B 2 + P 2 * B 0) +
      c 3 * (2 * P 1 * B 1) + c 4 * (P 1 * B 2 + P 2 * B 1) + c 5 * (2 * P 2 * B 2)) + 8 * qev c B,
    by simp only [qev]; ring⟩

theorem qO_eq (i : Fin 3) (a : Fin 3 → ℤ) (lam : ℤ) (P : List ℤ) (b : Fin 3 → ℤ)
    (hab : ∀ j : Fin 3, a j = lam * P.getD j 0 + 8 * b j) :
    ∃ R1, qO i a = (lam : 𝓞 K21) ^ 2 * qPO i P + 8 * R1 := by
  have e : (fun j : Fin 3 => ((a j : ℤ) : 𝓞 K21)) =
      fun j : Fin 3 => (lam : 𝓞 K21) * ((P.getD j 0 : ℤ) : 𝓞 K21) + 8 * ((b j : ℤ) : 𝓞 K21) := by
    funext j; rw [hab j]; push_cast; ring
  unfold qO qPO
  rw [e]
  exact qev_affine _ _ _ _

/-! ## Leaves -/

/-- The conic index of a leaf. -/
def LcCert.i : LcCert → ℕ
  | .odd i _ _ _ => i
  | .dfc i _ _ _ _ _ => i

/-- The Kronecker precision of a leaf. -/
def LcCert.kk : LcCert → ℕ
  | .odd _ _ kk _ => kk
  | .dfc _ _ _ kk _ _ => kk

/-- The right hand side of the leaf identity. -/
def LcCert.rhs : LcCert → KE
  | .odd _ v _ T => .mul (lcπE.pow v) (onePE T)
  | .dfc _ j d _ S Z =>
    .mul (lcπE.pow (2 * j)) (.add ((onePE S).pow 2) (.mul (lcπE.pow d) (onePE Z)))

/-- The numerical side conditions of a leaf. -/
def LcCert.cond : LcCert → Bool
  | .odd i v _ _ => (i == 0 || i == 2) && v % 2 == 1 && decide (v < 18)
  | .dfc i j d _ _ _ =>
    (i == 0 || i == 2) && d % 2 == 1 && decide (d < 12) && decide (2 * j + d < 18)

/-- The identity of a leaf: `Q_i(P) G' - rhs`. -/
def LcCert.idE (c : LcCert) (Gp P : List ℤ) : KE := .sub (.mul (qPE c.i P) (.lin Gp)) c.rhs

/-- The check of a leaf. -/
def lcOK (Gp P : List ℤ) (c : LcCert) : Bool := c.cond && checkK c.kk (c.idE Gp P)

/-- **A checked leaf**: for one conic `i ∈ {0, 2}`, `λ² Q_i(P) G' + 8 R` is never a square. -/
theorem lcOK_sound (Gp P : List ℤ) (c : LcCert) (h : lcOK Gp P c = true) :
    ∃ i : Fin 3, (i = 0 ∨ i = 2) ∧ ∀ lam : ℤ, Odd lam → ∀ R' s : 𝓞 K21,
      (lam : 𝓞 K21) ^ 2 * (qPO i P * zkO Gp) + 8 * R' = s ^ 2 → False := by
  simp only [lcOK, Bool.and_eq_true] at h
  obtain ⟨hc, hk⟩ := h
  have hid := evK_eq_of_check _ _ _ hk
  cases c with
  | odd i v kk T =>
    simp only [LcCert.cond, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hc
    obtain ⟨⟨hi, hv⟩, hv18⟩ := hc
    have hi3 : i < 3 := by omega
    refine ⟨⟨i, hi3⟩, ?_, ?_⟩
    · rcases hi with rfl | rfl
      · left; rfl
      · right; rfl
    · intro lam hlam R' s hX
      have hw : qPO ⟨i, hi3⟩ P * zkO Gp = gO 14 ^ v * (1 + gO 14 * zkO T) := by
        apply RingOfIntegers.coe_injective
        simp only [LcCert.i, LcCert.rhs, evK_mul, evK_pow, evK_lin, evK_qPE i hi3,
          evK_onePE, evK_lcπE] at hid
        simp only [map_mul, map_pow, map_add, map_one, coe_zkO]
        exact hid
      exact leaf_odd lc_prime two_eq_lc lam hlam _ R' _ s v (Nat.odd_iff.mpr hv) hv18 hw hX
  | dfc i j d kk S Z =>
    simp only [LcCert.cond, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hi, hd⟩, hd12⟩, hjd⟩ := hc
    have hi3 : i < 3 := by omega
    refine ⟨⟨i, hi3⟩, ?_, ?_⟩
    · rcases hi with rfl | rfl
      · left; rfl
      · right; rfl
    · intro lam hlam R' s hX
      have hw : qPO ⟨i, hi3⟩ P * zkO Gp = gO 14 ^ (2 * j) *
          ((1 + gO 14 * zkO S) ^ 2 + gO 14 ^ d * (1 + gO 14 * zkO Z)) := by
        apply RingOfIntegers.coe_injective
        simp only [LcCert.i, LcCert.rhs, evK_mul, evK_add, evK_pow, evK_lin, evK_qPE i hi3,
          evK_onePE, evK_lcπE] at hid
        simp only [map_mul, map_pow, map_add, map_one, coe_zkO]
        exact hid
      exact leaf_dfc lc_prime two_eq_lc lc_not_dvd_U lam hlam _ R' _ _ s j d
        (Nat.odd_iff.mpr hd) hd12 hjd hw hX

theorem ck_lcLeaves :
    lcLeaves.all (fun l => lcOK lcGp5 l.1 l.2.1 && lcOK lcGp7 l.1 l.2.2) = true := by
  decide +kernel

/-! ## Charts modulo 8 -/

/-- `0, ..., 7`. -/
def lcR8 : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7]

/-- `0, 2, 4, 6`. -/
def lcR4 : List ℤ := [0, 2, 4, 6]

/-- The normalized points modulo 8: `(x, y, 1)`, `(1, y, 2 z)`, `(2 x, 1, 2 z)`. -/
def lcChart : List (List ℤ) :=
  (lcR8.flatMap fun x => lcR8.map fun y => [x, y, 1]) ++
  (lcR8.flatMap fun y => lcR4.map fun z => [1, y, z]) ++
  (lcR4.flatMap fun x => lcR4.map fun z => [x, 1, z])

/-- `F` at an integer point given as a list. -/
def lcF (P : List ℤ) : ℤ := FurioLombardo.F (P.getD 0 0) (P.getD 1 0) (P.getD 2 0)

theorem ck_lcChart :
    lcChart.all (fun P => lcF P % 8 != 0 || (lcLeaves.map Prod.fst).contains P) = true := by
  decide +kernel

theorem mem_lcR8 (x : ℤ) (h0 : 0 ≤ x) (h8 : x < 8) : x ∈ lcR8 := by
  simp only [lcR8, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem mem_lcR4 (x : ℤ) (h0 : 0 ≤ x) (h8 : x < 8) (h2 : x % 2 = 0) : x ∈ lcR4 := by
  simp only [lcR4, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem emod8_bounds (p : ℤ) : 0 ≤ p % 8 ∧ p % 8 < 8 :=
  ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

theorem emod8_even (u l : ℤ) (hu : Even u) : (u * l) % 8 % 2 = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have : (w + w) * l = 2 * (w * l) := by ring
  rw [this]
  omega

/-- `u = λ ((u λ) mod 8) + 8 b` with an explicit integer `b`, for odd `λ`. -/
theorem split8 (lam : ℤ) (hlam : Odd lam) :
    ∃ c : ℤ, ∀ u : ℤ, u = lam * ((u * lam) % 8) + 8 * (lam * ((u * lam) / 8) - u * c) := by
  obtain ⟨c, hc⟩ := odd_sq_eq lam hlam
  refine ⟨c, fun u => ?_⟩
  have := Int.emod_add_mul_ediv (u * lam) 8
  linear_combination (-lam) * this - u * hc

/-- **Charts**: a primitive integer triple is `λ P + 8 b` with `λ` odd and `P` in the chart list. -/
theorem lc_chart (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1) :
    ∃ (lam : ℤ) (P : List ℤ) (b : Fin 3 → ℤ), Odd lam ∧ P ∈ lcChart ∧
      ∀ j : Fin 3, a j = lam * P.getD j 0 + 8 * b j := by
  have hsum : r 0 * a 0 + r 1 * a 1 + r 2 * a 2 = 1 := by simpa [Fin.sum_univ_three] using hr
  by_cases h2 : Odd (a 2)
  · obtain ⟨c, hc⟩ := split8 (a 2) h2
    refine ⟨a 2, [(a 0 * a 2) % 8, (a 1 * a 2) % 8, 1],
      ![a 2 * ((a 0 * a 2) / 8) - a 0 * c, a 2 * ((a 1 * a 2) / 8) - a 1 * c, 0], h2, ?_, ?_⟩
    · simp only [lcChart, List.mem_append, List.mem_flatMap, List.mem_map]
      refine Or.inl (Or.inl ⟨_, mem_lcR8 _ (emod8_bounds _).1 (emod8_bounds _).2, _,
        mem_lcR8 _ (emod8_bounds _).1 (emod8_bounds _).2, rfl⟩)
    · intro j
      fin_cases j
      · exact hc (a 0)
      · exact hc (a 1)
      · simp
  have h2e : Even (a 2) := Int.not_odd_iff_even.mp h2
  by_cases h0 : Odd (a 0)
  · obtain ⟨c, hc⟩ := split8 (a 0) h0
    refine ⟨a 0, [1, (a 1 * a 0) % 8, (a 2 * a 0) % 8],
      ![0, a 0 * ((a 1 * a 0) / 8) - a 1 * c, a 0 * ((a 2 * a 0) / 8) - a 2 * c], h0, ?_, ?_⟩
    · simp only [lcChart, List.mem_append, List.mem_flatMap, List.mem_map]
      refine Or.inl (Or.inr ⟨_, mem_lcR8 _ (emod8_bounds _).1 (emod8_bounds _).2, _,
        mem_lcR4 _ (emod8_bounds _).1 (emod8_bounds _).2 (emod8_even _ _ h2e), rfl⟩)
    · intro j
      fin_cases j
      · simp
      · exact hc (a 1)
      · exact hc (a 2)
  have h0e : Even (a 0) := Int.not_odd_iff_even.mp h0
  have h1 : Odd (a 1) := by
    by_contra h1
    have h1e : Even (a 1) := Int.not_odd_iff_even.mp h1
    have : Even (1 : ℤ) :=
      hsum ▸ ((h0e.mul_left (r 0)).add (h1e.mul_left (r 1))).add (h2e.mul_left (r 2))
    exact Int.not_even_one this
  obtain ⟨c, hc⟩ := split8 (a 1) h1
  refine ⟨a 1, [(a 0 * a 1) % 8, 1, (a 2 * a 1) % 8],
    ![a 1 * ((a 0 * a 1) / 8) - a 0 * c, 0, a 1 * ((a 2 * a 1) / 8) - a 2 * c], h1, ?_, ?_⟩
  · simp only [lcChart, List.mem_append, List.mem_flatMap, List.mem_map]
    refine Or.inr ⟨_, mem_lcR4 _ (emod8_bounds _).1 (emod8_bounds _).2 (emod8_even _ _ h0e), _,
      mem_lcR4 _ (emod8_bounds _).1 (emod8_bounds _).2 (emod8_even _ _ h2e), rfl⟩
  · intro j
    fin_cases j
    · exact hc (a 0)
    · simp
    · exact hc (a 2)

/-- `F(P) ≡ 0 (mod 8)` when `a = λ P + 8 b` is on `C` with `λ` odd. -/
theorem lc_F8 (a : Fin 3 → ℤ) (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (lam : ℤ)
    (hlam : Odd lam) (P : List ℤ) (b : Fin 3 → ℤ)
    (hab : ∀ j : Fin 3, a j = lam * P.getD j 0 + 8 * b j) :
    lcF P % 8 = 0 := by
  obtain ⟨c, hc⟩ := odd_sq_eq lam hlam
  have h80 : (8 : ZMod 8) = 0 := rfl
  have e : ∀ j : Fin 3, ((a j : ℤ) : ZMod 8) = (lam : ZMod 8) * ((P.getD j 0 : ℤ) : ZMod 8) := by
    intro j; rw [hab j]; push_cast; rw [h80]; ring
  have hF8 : FurioLombardo.F ((a 0 : ℤ) : ZMod 8) (a 1 : ZMod 8) (a 2 : ZMod 8) = 0 := by
    rw [F_intCast, hF, Int.cast_zero]
  rw [e 0, e 1, e 2] at hF8
  have hl : (lam : ZMod 8) ^ 2 = 1 := by rw [odd_sq_cast lam c hc, h80]; ring
  have hsm : ∀ l x y z : ZMod 8, FurioLombardo.F (l * x) (l * y) (l * z) =
      l ^ 4 * FurioLombardo.F x y z := by
    intro l x y z; simp only [FurioLombardo.F]; ring
  rw [hsm, show (lam : ZMod 8) ^ 4 = ((lam : ZMod 8) ^ 2) ^ 2 by ring, hl, one_pow, one_mul,
    F_intCast] at hF8
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hF8)

/-! ## The kill -/

/-- **The local step at `lc`**: at a primitive integer point of `C`, the classes `survE 5` and
`survE 7` fail the square condition. -/
theorem kill2 (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (k : ℕ) (hk : k = 5 ∨ k = 7)
    (hsq : SqCond a (survE k)) : False := by
  obtain ⟨lam, P, b, hlam, hP, hab⟩ := lc_chart a r hr
  have hF8 := lc_F8 a hF lam hlam P b hab
  have hmem : P ∈ lcLeaves.map Prod.fst := by
    have := List.all_eq_true.mp ck_lcChart P hP
    simpa [hF8] using this
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
  have hok := List.all_eq_true.mp ck_lcLeaves l hl
  simp only [Bool.and_eq_true] at hok
  obtain ⟨Gp, H, c, hG, hc⟩ : ∃ Gp H c, gProd (survE k) = zkO Gp + 8 * zkO H ∧
      lcOK Gp l.1 c = true := by
    rcases hk with rfl | rfl
    · exact ⟨lcGp5, lcH5, l.2.1, gProd_eq_of_check 5 _ _ _ ck_lcG5, hok.1⟩
    · exact ⟨lcGp7, lcH7, l.2.2, gProd_eq_of_check 7 _ _ _ ck_lcG7, hok.2⟩
  obtain ⟨i, hi, hno⟩ := lcOK_sound Gp l.1 c hc
  obtain ⟨R1, hR1⟩ := qO_eq i a lam l.1 b hab
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 K21, qO i a * gProd (survE k) = s ^ 2 := by
    by_cases h0 : qO i a = 0
    · exact ⟨0, by rw [h0]; ring⟩
    · exact hsq i hi h0
  apply hno lam hlam ((lam : 𝓞 K21) ^ 2 * qPO i l.1 * zkO H + R1 * zkO Gp + 8 * R1 * zkO H) s
  rw [← hs, hR1, hG]
  ring

end FurioLombardo.M1
