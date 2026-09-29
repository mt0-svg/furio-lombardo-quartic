import Mathlib
import FurioLombardo.Discharge.M4Cert.Resid
import FurioLombardo.M3a.Sections
import FurioLombardo.M4.Defs

/-!
# The discs of `C(ℚ_2)`, the twist predicate, and the box checker

* `discPt d X Y`: the point of the disc `d ∈ {1, ..., 5}` of `C(ℚ_2)` with parameters `X, Y`
  (code/earlier-computations/discs_q2.gp,
  `DISCS = [[1,0,0,1,2], [1,1,0,1,2], [1,1,1,1,2], [2,0,0,1,2], [2,1,0,1,2]]`): charts `z = 1` with
  `(x, y) = (a0 + 2X, b0 + 2Y)` for `d = 1, 2, 3` and `y = 1` with `(x, z) = (a0 + 2X, 2Y)` for
  `d = 4, 5`. The parameter of lane M4 is `X`.
* `Twist M1 M2 M3 δ d X`: some point `discPt d X Y` (`Y ∈ ℤ_[2]`) lies on `C` and lifts to
  `D_δ(K_v)`, the points of M3a's `DPoint` for the quadrics `M_i` and the twist `δ` mapped by `σ`,
  up to a nonzero factor. This is the predicate `Twist` of lane M4's `HExcl` and `HDisc`.
* `QFormData M c`: the matrix `M` over K21 has the quadratic form whose coefficient of `x_i x_j`
  (`i ≤ j`) is `zkE (c i j)` (diagonal entries, and sums `M i j + M j i` off the diagonal), so the
  statements below hold for the symmetric and for the upper triangular matrices of a form.
* `boxOK`: the Boolean exclusion check of a box, and `no_point_of_boxOK` its soundness.
-/

namespace FurioLombardo.Discharge.M4Cert

open FurioLombardo.M1 Matrix

/-! ## ℤ_[2] inside K_v -/

/-- `ℤ_[2] → K_v`. -/
noncomputable def toKv : ℤ_[2] →+* Kv := (algebraMap ℚ_[2] Kv).comp PadicInt.Coe.ringHom

theorem norm_toKv_le_one (z : ℤ_[2]) : ‖toKv z‖ ≤ 1 := by
  show ‖algebraMap ℚ_[2] Kv (z : ℚ_[2])‖ ≤ 1
  rw [norm_algebraMap]
  exact PadicInt.norm_le_one z

theorem approx_toKv {z : ℤ_[2]} {k : ℤ} {n : ℕ} (h : (2 : ℤ_[2]) ^ n ∣ z - k) :
    Approx (toKv z) (k, 0, 0) n := by
  obtain ⟨w, hw⟩ := h
  unfold Approx
  rw [evZ_const, show (k : Kv) = toKv (k : ℤ_[2]) by simp, ← map_sub, hw, map_mul, map_pow,
    map_ofNat, norm_mul, norm_pow, norm_two_Kv]
  calc (2⁻¹ : ℝ) ^ n * ‖toKv w‖ ≤ (2⁻¹ : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (norm_toKv_le_one w) (by positivity)
    _ = _ := mul_one _

theorem two_pow_dvd_intCast_iff (k : ℤ) (n : ℕ) : (2 : ℤ_[2]) ^ n ∣ (k : ℤ_[2]) ↔ (2 : ℤ) ^ n ∣ k := by
  rw [← intCast_mem_span_two_pow, Ideal.mem_span_singleton, Nat.cast_ofNat]

/-! ## The discs -/

/-- The point of parameters `(X, Y)` of the disc `d` of `C(ℚ_2)`. -/
def discPt {R : Type*} [CommRing R] (d : ℕ) (X Y : R) : Fin 3 → R :=
  if d = 1 then ![2 * X, 2 * Y, 1]
  else if d = 2 then ![1 + 2 * X, 2 * Y, 1]
  else if d = 3 then ![1 + 2 * X, 1 + 2 * Y, 1]
  else if d = 4 then ![2 * X, 1, 2 * Y]
  else if d = 5 then ![1 + 2 * X, 1, 2 * Y]
  else ![0, 0, 0]

theorem map_discPt {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (X Y : R)
    (i : Fin 3) : φ (discPt d X Y i) = discPt d (φ X) (φ Y) i := by
  unfold discPt
  split_ifs <;> fin_cases i <;> simp <;> exact congrArg (· * _) (map_ofNat φ 2)

theorem discPt_sub_dvd {X Y X' Y' : ℤ_[2]} {m : ℕ} (hX : (2 : ℤ_[2]) ^ m ∣ X - X')
    (hY : (2 : ℤ_[2]) ^ m ∣ Y - Y') (d : ℕ) (i : Fin 3) :
    (2 : ℤ_[2]) ^ (m + 1) ∣ discPt d X Y i - discPt d X' Y' i := by
  have h2X : (2 : ℤ_[2]) ^ (m + 1) ∣ 2 * X - 2 * X' := by
    rw [← mul_sub, pow_succ, mul_comm]; exact mul_dvd_mul_left 2 hX
  have h2Y : (2 : ℤ_[2]) ^ (m + 1) ∣ 2 * Y - 2 * Y' := by
    rw [← mul_sub, pow_succ, mul_comm]; exact mul_dvd_mul_left 2 hY
  have h1X : (2 : ℤ_[2]) ^ (m + 1) ∣ (1 + 2 * X) - (1 + 2 * X') := by
    rw [add_sub_add_left_eq_sub]; exact h2X
  have h1Y : (2 : ℤ_[2]) ^ (m + 1) ∣ (1 + 2 * Y) - (1 + 2 * Y') := by
    rw [add_sub_add_left_eq_sub]; exact h2Y
  have h0 : (2 : ℤ_[2]) ^ (m + 1) ∣ (1 : ℤ_[2]) - 1 := by rw [sub_self]; exact dvd_zero _
  have h00 : (2 : ℤ_[2]) ^ (m + 1) ∣ (0 : ℤ_[2]) - 0 := by rw [sub_self]; exact dvd_zero _
  unfold discPt
  split_ifs <;> fin_cases i <;> assumption

/-! ## The curve modulo powers of 2 -/

theorem map_F {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x y z : R) :
    φ (FurioLombardo.F x y z) = FurioLombardo.F (φ x) (φ y) (φ z) := by
  simp only [FurioLombardo.F, map_add, map_sub, map_mul, map_pow]
  rw [map_ofNat φ 2, map_ofNat φ 3, map_ofNat φ 4, map_ofNat φ 5, map_ofNat φ 6]

theorem F_dvd_of_congr {p : Fin 3 → ℤ_[2]} {q : Fin 3 → ℤ} {n : ℕ}
    (hpq : ∀ i, (2 : ℤ_[2]) ^ n ∣ p i - q i) (hF : FurioLombardo.F (p 0) (p 1) (p 2) = 0) :
    (2 : ℤ) ^ n ∣ FurioLombardo.F (q 0) (q 1) (q 2) := by
  set I : Ideal ℤ_[2] := Ideal.span {(2 : ℤ_[2]) ^ n}
  have hmk : ∀ i, Ideal.Quotient.mk I (p i) = Ideal.Quotient.mk I ((q i : ℤ) : ℤ_[2]) := fun i =>
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hpq i))
  have hc : ((FurioLombardo.F (q 0) (q 1) (q 2) : ℤ) : ℤ_[2]) =
      FurioLombardo.F ((q 0 : ℤ) : ℤ_[2]) ((q 1 : ℤ) : ℤ_[2]) ((q 2 : ℤ) : ℤ_[2]) := by
    simpa using map_F (Int.castRingHom ℤ_[2]) (q 0) (q 1) (q 2)
  have h0 : Ideal.Quotient.mk I ((FurioLombardo.F (q 0) (q 1) (q 2) : ℤ) : ℤ_[2]) = 0 := by
    rw [hc, map_F, ← hmk 0, ← hmk 1, ← hmk 2, ← map_F, hF, map_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  exact (two_pow_dvd_intCast_iff _ n).1 h0

/-! ## Quadratic forms -/

/-- `M` has the quadratic form with coefficients `zkE (c i j)` on `x_i x_j`, `i ≤ j`. -/
def QFormData (M : Matrix (Fin 3) (Fin 3) K21) (c : Fin 3 → Fin 3 → List ℤ) : Prop :=
  (∀ i, M i i = zkE (c i i)) ∧ ∀ i j : Fin 3, i < j → M i j + M j i = zkE (c i j)

/-- The value of the quadratic form with coefficients `Q i j` (`i ≤ j`) at `P`. -/
noncomputable def qvalK (Q : Fin 3 → Fin 3 → Kv) (P : Fin 3 → Kv) : Kv :=
  Q 0 0 * (P 0 * P 0) + Q 0 1 * (P 0 * P 1) + Q 0 2 * (P 0 * P 2) + Q 1 1 * (P 1 * P 1) +
    Q 1 2 * (P 1 * P 2) + Q 2 2 * (P 2 * P 2)

/-- The same on integer triples (exact, no reduction). -/
def qresT (QR : Fin 3 → Fin 3 → T3) (p : Fin 3 → ℤ) : T3 :=
  mulZ (QR 0 0) (p 0 * p 0, 0, 0) + mulZ (QR 0 1) (p 0 * p 1, 0, 0) +
    mulZ (QR 0 2) (p 0 * p 2, 0, 0) + mulZ (QR 1 1) (p 1 * p 1, 0, 0) +
    mulZ (QR 1 2) (p 1 * p 2, 0, 0) + mulZ (QR 2 2) (p 2 * p 2, 0, 0)

theorem quad_eq {M : Matrix (Fin 3) (Fin 3) K21} {c : Fin 3 → Fin 3 → List ℤ}
    (hM : QFormData M c) (p : Fin 3 → Kv) :
    p ⬝ᵥ ((M.map σ) *ᵥ p) = qvalK (fun i j => σ (zkE (c i j))) p := by
  obtain ⟨hd, ho⟩ := hM
  have h01 := congrArg σ (ho 0 1 (by decide))
  have h02 := congrArg σ (ho 0 2 (by decide))
  have h12 := congrArg σ (ho 1 2 (by decide))
  rw [map_add] at h01 h02 h12
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.map_apply, qvalK]
  rw [← hd 0, ← hd 1, ← hd 2]
  linear_combination (p 0 * p 1) * h01 + (p 0 * p 2) * h02 + (p 1 * p 2) * h12

theorem mulZ_const (a b : ℤ) : mulZ (a, 0, 0) (b, 0, 0) = (a * b, 0, 0) := by
  simp [mulZ]

theorem approx_qval {Q : Fin 3 → Fin 3 → Kv} {QR : Fin 3 → Fin 3 → T3} {P : Fin 3 → Kv}
    {p : Fin 3 → ℤ} {n : ℕ} (hQ : ∀ i j, i ≤ j → Approx (Q i j) (QR i j) n)
    (hP : ∀ i, Approx (P i) (p i, 0, 0) n) : Approx (qvalK Q P) (qresT QR p) n := by
  have hpp : ∀ i j, Approx (P i * P j) (p i * p j, 0, 0) n := fun i j => by
    rw [← mulZ_const]; exact (hP i).mul (hP j)
  unfold qvalK qresT
  exact (((((hQ 0 0 (by decide)).mul (hpp 0 0)).add ((hQ 0 1 (by decide)).mul (hpp 0 1))).add
    ((hQ 0 2 (by decide)).mul (hpp 0 2))).add ((hQ 1 1 (by decide)).mul (hpp 1 1))).add
    ((hQ 1 2 (by decide)).mul (hpp 1 2)) |>.add ((hQ 2 2 (by decide)).mul (hpp 2 2))

/-- **Core of the exclusion.** If the residue of `Q(P) δ⁻¹` modulo `2^n` is not a square, no nonzero
multiple of `P` satisfies `Q(p) = δ r²` in `K_v`. -/
theorem no_point_core {M : Matrix (Fin 3) (Fin 3) K21} {c : Fin 3 → Fin 3 → List ℤ}
    (hM : QFormData M c) {δ : K21} {QR : Fin 3 → Fin 3 → T3} {dr di : T3} {n : ℕ}
    {L : List T3} (hn : 1 ≤ n) (hQR : ∀ i j, i ≤ j → Approx (σ (zkE (c i j))) (QR i j) n)
    (hδ : Approx (σ δ) dr n) (hdi : modT (mulZ dr di) n = modT (1, 0, 0) n) (hL : SqClosed L n)
    {P : Fin 3 → Kv} {pr : Fin 3 → ℤ} (hP : ∀ i, Approx (P i) (pr i, 0, 0) n)
    (hres : modT (mulZ (qresT QR pr) di) n ∉ L) (t r : Kv) (ht : t ≠ 0) :
    (t • P) ⬝ᵥ ((M.map σ) *ᵥ (t • P)) ≠ σ δ * r ^ 2 := by
  intro h
  rw [quad_eq hM] at h
  obtain ⟨hδ0, hinv⟩ := approx_inv hn hδ hdi
  have hq : qvalK (fun i j => σ (zkE (c i j))) (t • P) =
      t ^ 2 * qvalK (fun i j => σ (zkE (c i j))) P := by
    simp only [qvalK, Pi.smul_apply, smul_eq_mul]; ring
  rw [hq] at h
  have hw : Approx (qvalK (fun i j => σ (zkE (c i j))) P * (σ δ)⁻¹) (mulZ (qresT QR pr) di) n :=
    (approx_qval hQR hP).mul hinv
  refine not_sq_of_approx hL hres hw (r / t) ?_
  field_simp
  linear_combination h

/-! ## The box checker -/

/-- The exclusion check of the box `X ≡ c mod 2^s` of the disc `d` at level `m`: for every residue
pair `(Xr, Yr)` modulo `2^m` in the box with `F(discPt d Xr Yr) ≡ 0 mod 2^(m+1)`, the residue of
`Q(discPt d Xr Yr) δ⁻¹` modulo `2^(m+1)` is not in `L`. -/
def boxOK (QR : Fin 3 → Fin 3 → T3) (di : T3) (L : List T3) (m d c s : ℕ) : Bool :=
  decide (s ≤ m) && (List.range (2 ^ m)).all fun Xr => (List.range (2 ^ m)).all fun Yr =>
    decide (Xr % 2 ^ s ≠ c % 2 ^ s) ||
      decide (FurioLombardo.F (discPt d (Xr : ℤ) (Yr : ℤ) 0) (discPt d (Xr : ℤ) (Yr : ℤ) 1)
        (discPt d (Xr : ℤ) (Yr : ℤ) 2) % 2 ^ (m + 1) ≠ 0) ||
      !(L.contains (modT (mulZ (qresT QR (discPt d (Xr : ℤ) (Yr : ℤ))) di) (m + 1)))

theorem boxOK_spec {QR : Fin 3 → Fin 3 → T3} {di : T3} {L : List T3} {m d c s : ℕ}
    (hb : boxOK QR di L m d c s = true) : s ≤ m ∧ ∀ Xr : ℕ, Xr < 2 ^ m → ∀ Yr : ℕ, Yr < 2 ^ m →
      Xr % 2 ^ s = c % 2 ^ s →
      FurioLombardo.F (discPt d (Xr : ℤ) (Yr : ℤ) 0) (discPt d (Xr : ℤ) (Yr : ℤ) 1)
        (discPt d (Xr : ℤ) (Yr : ℤ) 2) % 2 ^ (m + 1) = 0 →
      modT (mulZ (qresT QR (discPt d (Xr : ℤ) (Yr : ℤ))) di) (m + 1) ∉ L := by
  unfold boxOK at hb
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hb
  refine ⟨hb.1, fun Xr hX Yr hY hc hF hmem => ?_⟩
  have h := List.all_eq_true.1 (hb.2 Xr (List.mem_range.2 hX)) Yr (List.mem_range.2 hY)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact h hc
  · exact h hF
  · have hc' : L.contains (modT (mulZ (qresT QR (discPt d (Xr : ℤ) (Yr : ℤ))) di) (m + 1)) = true := by
      simpa using hmem
    rw [hc'] at h
    exact absurd h (by decide)

/-! ## The twist predicate and the soundness of the box checker -/

/-- The point of parameter `X` of the disc `d` of `C(ℚ_2)` lifts to `D_δ(K_v)`: for some `Y`,
`discPt d X Y` lies on `C` and a nonzero multiple of it is the point below a `K_v`-point of `D_δ`
(M3a's `DPoint` for the matrices and the twist mapped by `σ`). -/
def Twist (M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21) (δ : K21) (d : ℕ) (X : ℤ_[2]) : Prop :=
  ∃ Y : ℤ_[2], FurioLombardo.F (discPt d X Y 0) (discPt d X Y 1) (discPt d X Y 2) = 0 ∧
    ∃ D : FurioLombardo.M3a.DPoint Kv (M1.map σ) (M2.map σ) (M3.map σ) (σ δ), ∃ t : Kv, t ≠ 0 ∧
      D.p = t • fun i => toKv (discPt d X Y i)

/-- **Soundness of `boxOK`.** -/
theorem no_point_of_boxOK {M : Matrix (Fin 3) (Fin 3) K21} {c : Fin 3 → Fin 3 → List ℤ}
    (hM : QFormData M c) {δ : K21} {QR : Fin 3 → Fin 3 → T3} {dr di : T3} {L : List T3} {m : ℕ}
    (hQR : ∀ i j, i ≤ j → Approx (σ (zkE (c i j))) (QR i j) (m + 1))
    (hδ : Approx (σ δ) dr (m + 1)) (hdi : modT (mulZ dr di) (m + 1) = modT (1, 0, 0) (m + 1))
    (hL : SqClosed L (m + 1)) {d c0 s : ℕ} (hb : boxOK QR di L m d c0 s = true)
    {X : ℤ_[2]} (hX : FurioLombardo.M4.InBox X c0 s) (Y : ℤ_[2])
    (hF : FurioLombardo.F (discPt d X Y 0) (discPt d X Y 1) (discPt d X Y 2) = 0)
    (t r : Kv) (ht : t ≠ 0) :
    (t • fun i => toKv (discPt d X Y i)) ⬝ᵥ
      ((M.map σ) *ᵥ (t • fun i => toKv (discPt d X Y i))) ≠ σ δ * r ^ 2 := by
  obtain ⟨hsm, hbox⟩ := boxOK_spec hb
  have hXr : (2 : ℤ_[2]) ^ m ∣ X - ((X.appr m : ℕ) : ℤ_[2]) := by
    have := PadicInt.appr_spec m X
    rwa [Ideal.mem_span_singleton, Nat.cast_ofNat] at this
  have hYr : (2 : ℤ_[2]) ^ m ∣ Y - ((Y.appr m : ℕ) : ℤ_[2]) := by
    have := PadicInt.appr_spec m Y
    rwa [Ideal.mem_span_singleton, Nat.cast_ofNat] at this
  set Xr := X.appr m with hXrdef
  set Yr := Y.appr m with hYrdef
  have hcast : ∀ i, ((discPt d (Xr : ℤ) (Yr : ℤ) i : ℤ) : ℤ_[2]) =
      discPt d ((Xr : ℕ) : ℤ_[2]) ((Yr : ℕ) : ℤ_[2]) i := fun i => by
    have := map_discPt (Int.castRingHom ℤ_[2]) d (Xr : ℤ) (Yr : ℤ) i
    simpa using this
  have hpr : ∀ i, (2 : ℤ_[2]) ^ (m + 1) ∣ discPt d X Y i - ((discPt d (Xr : ℤ) (Yr : ℤ) i : ℤ) : ℤ_[2]) :=
    fun i => by rw [hcast i]; exact discPt_sub_dvd hXr hYr d i
  have hbx : Xr % 2 ^ s = c0 % 2 ^ s := by
    obtain ⟨y, hy⟩ := hX
    obtain ⟨w, hw⟩ := hXr
    have hd : (2 : ℤ_[2]) ^ s ∣ (((Xr : ℤ) - (c0 : ℤ) : ℤ) : ℤ_[2]) := by
      have e : (((Xr : ℤ) - (c0 : ℤ) : ℤ) : ℤ_[2]) = 2 ^ s * (y - 2 ^ (m - s) * w) := by
        have hx' : ((Xr : ℕ) : ℤ_[2]) = X - 2 ^ m * w := by rw [← hw]; ring
        push_cast
        rw [hx', hy, mul_sub, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hsm]
        ring
      rw [e]; exact dvd_mul_right _ _
    have h' := (two_pow_dvd_intCast_iff _ s).1 hd
    have h'' : (Xr : ℤ) % 2 ^ s = (c0 : ℤ) % 2 ^ s := (Int.modEq_iff_dvd.mpr h').symm
    exact_mod_cast h''
  have hFr := Int.emod_eq_zero_of_dvd (F_dvd_of_congr hpr hF)
  have hres := hbox Xr (PadicInt.appr_lt X m) Yr (PadicInt.appr_lt Y m) hbx hFr
  exact no_point_core hM (by omega) hQR hδ hdi hL (fun i => approx_toKv (hpr i)) hres t r ht

end FurioLombardo.Discharge.M4Cert
