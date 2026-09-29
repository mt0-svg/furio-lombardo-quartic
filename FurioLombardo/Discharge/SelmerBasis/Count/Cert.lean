import FurioLombardo.Discharge.SelmerBasis.AdicPlace
import FurioLombardo.M1.ZKInt

/-!
# Count lane: square and non-square certificates at `primeOf α`

At a place `primeOf α` of a number field (`α` generating a prime, AdicPlace.lean), with `b = 1` in the
certificates of the local layer:

* `cert_isSquare`: `y - t² = α^n a`, `t² = α^m a'` (`a'` a unit modulo `α`), `2e + m < n`, where
  `‖2‖ = ‖α‖^e`: `y` is a square (`sq_cert_adic`, `isSquare_of_norm_div_sq_sub_one_lt`); `cert_ne_zero`;
* `cert_not_isSquare_odd`: `y = α^n a`, `a` a unit, `n` odd;
* `cert_not_isSquare_depth`: `y - t² = α^n a`, `t² = α^m a'` with `a`, `a'` units, `n - m` odd,
  `m < n < m + 2e` (`sb_not_isSquare_of_norm_sub_one`);

and their versions on lane M1's Kronecker tests at `primeOf (eltO al)` (`ck_isSquare`, `ck_sq_ne_zero`,
`ck_not_isSquare_odd`, `ck_not_isSquare_depth`), where `y = evK Y` and the lists are zk coordinates.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped FurioLombardo.Discharge.SelmerBasis.Adic

namespace FurioLombardo.Discharge.SelmerBasis.Count

variable {K : Type*} [Field K] [NumberField K] {α : 𝓞 K}
  {hP : (Ideal.span {α} : Ideal (𝓞 K)).IsPrime} {hα : α ≠ 0}


/-- **Square from a certificate** at `primeOf α`: `y - t² = α^n a`, `t² = α^m a'` with `a'` a unit
modulo `α` and `2e + m < n`, where `‖2‖ = ‖α‖^e`. -/
theorem cert_isSquare {e : ℕ}
    (h2 : ‖(2 : (primeOf α hP hα).adicCompletion K)‖ =
      ‖((α : K) : (primeOf α hP hα).adicCompletion K)‖ ^ e)
    {y t : K} {n m : ℕ} {a a' ai ca : 𝓞 K} (hy : y - t ^ 2 = (α : K) ^ n * (a : K))
    (hs : t ^ 2 = (α : K) ^ m * (a' : K)) (ha' : a' * ai = 1 + α * ca) (hnm : 2 * e + m < n) :
    IsSquare (y : (primeOf α hP hα).adicCompletion K) := by
  have hb : (1 : 𝓞 K) * 1 = 1 + α * 0 := by ring
  have hlt := sq_cert_adic (hP := hP) (hα := hα) (y := y) (s := t ^ 2) (n := n) (m := m) (a := a)
    (a' := a') h2 hb (by push_cast; rw [mul_one, zpow_natCast]; exact hy) ha' hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hs) (by omega)
  have ht0 : t ≠ 0 := by
    rintro rfl
    have ha0 := primeOf_val_ne_zero hP hα ha'
    have hα0 : (α : K) ≠ 0 := by exact_mod_cast hα
    rw [zero_pow two_ne_zero] at hs
    exact mul_ne_zero (pow_ne_zero m hα0) ha0 hs.symm
  have ht : (t : (primeOf α hP hα).adicCompletion K) ≠ 0 :=
    (map_ne_zero (adicCoe (primeOf α hP hα))).mpr ht0
  have hcoe : ((t ^ 2 : K) : (primeOf α hP hα).adicCompletion K) = (t : _) ^ 2 :=
    map_pow (adicCoe (primeOf α hP hα)) t 2
  rw [hcoe] at hlt
  exact isSquare_of_norm_div_sq_sub_one_lt primeOf_normUnif two_ne_zero ht hlt

/-- The element `y` of a square certificate is nonzero: `‖t²‖ = ‖α‖^m` and `‖y - t²‖ ≤ ‖α‖^n`, `m < n`. -/
theorem cert_ne_zero (hP : (Ideal.span {α} : Ideal (𝓞 K)).IsPrime) (hα : α ≠ 0) {y t : K} {n m : ℕ} {a a' ai ca : 𝓞 K} (hy : y - t ^ 2 = (α : K) ^ n * (a : K))
    (hs : t ^ 2 = (α : K) ^ m * (a' : K)) (ha' : a' * ai = 1 + α * ca) (hmn : m < n) : y ≠ 0 := by
  rintro rfl
  set w := primeOf α hP hα
  have hb : (1 : 𝓞 K) * 1 = 1 + α * 0 := by ring
  have hu : NormUnif ((α : K) : w.adicCompletion K) := primeOf_normUnif
  have hr0 : 0 < ‖((α : K) : w.adicCompletion K)‖ := norm_pos_iff.mpr hu.ne_zero
  have h1 := primeOf_norm_le (hP := hP) (hα := hα) (x := 0 - t ^ 2) (n := (n : ℤ)) (a := a) hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hy)
  have h3 := primeOf_norm (hP := hP) (hα := hα) (x := t ^ 2) (n := (m : ℤ)) ha' hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hs)
  rw [zero_sub] at h1
  have hneg : ((-t ^ 2 : K) : w.adicCompletion K) = -((t ^ 2 : K) : w.adicCompletion K) :=
    map_neg (adicCoe w) _
  rw [hneg, norm_neg] at h1
  have hlt := zpow_lt_zpow_right_of_lt_one₀ hr0 hu.norm_lt_one (show (m : ℤ) < n by exact_mod_cast hmn)
  have := h1.trans_lt hlt
  rw [← h3] at this
  exact lt_irrefl _ this

/-- **Non-square from an odd valuation** at `primeOf α`: `y = α^n a`, `a` a unit modulo `α`,
`n` odd. -/
theorem cert_not_isSquare_odd {y : K} {n : ℕ} {a ai ca : 𝓞 K} (hy : y = (α : K) ^ n * (a : K))
    (ha : a * ai = 1 + α * ca) (hn : Odd n) :
    ¬ IsSquare (y : (primeOf α hP hα).adicCompletion K) := by
  have hb : (1 : 𝓞 K) * 1 = 1 + α * 0 := by ring
  have hu : NormUnif ((α : K) : (primeOf α hP hα).adicCompletion K) := primeOf_normUnif
  have h := primeOf_norm (hP := hP) (hα := hα) (x := y) (n := (n : ℤ)) ha hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hy)
  exact sb_not_isSquare_of_norm_odd hu.ne_zero hu.norm_lt_one hu.disc h (by exact_mod_cast hn)

/-- **Non-square from an odd depth** at `primeOf α`: `y - t² = α^n a`, `t² = α^m a'` with `a`, `a'`
units modulo `α`, `n - m` odd and `m < n < m + 2e`, where `‖2‖ = ‖α‖^e`. -/
theorem cert_not_isSquare_depth {e : ℕ}
    (h2 : ‖(2 : (primeOf α hP hα).adicCompletion K)‖ =
      ‖((α : K) : (primeOf α hP hα).adicCompletion K)‖ ^ e)
    {y t : K} {n m : ℕ} {a ai ca a' ai' ca' : 𝓞 K} (hy : y - t ^ 2 = (α : K) ^ n * (a : K))
    (ha : a * ai = 1 + α * ca) (hs : t ^ 2 = (α : K) ^ m * (a' : K))
    (ha' : a' * ai' = 1 + α * ca') (hodd : Odd (n - m)) (hmn : m < n) (hlt : n < m + 2 * e) :
    ¬ IsSquare (y : (primeOf α hP hα).adicCompletion K) := by
  set w := primeOf α hP hα
  have hb : (1 : 𝓞 K) * 1 = 1 + α * 0 := by ring
  have hu : NormUnif ((α : K) : w.adicCompletion K) := primeOf_normUnif
  set r := ‖((α : K) : w.adicCompletion K)‖
  have hr0 : 0 < r := norm_pos_iff.mpr hu.ne_zero
  have h1 := primeOf_norm (hP := hP) (hα := hα) (x := y - t ^ 2) (n := (n : ℤ)) ha hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hy)
  have h3 := primeOf_norm (hP := hP) (hα := hα) (x := t ^ 2) (n := (m : ℤ)) ha' hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hs)
  have hcoe1 : ((y - t ^ 2 : K) : w.adicCompletion K) = (y : w.adicCompletion K) - (t : _) ^ 2 := by
    rw [adic_coe_sub]; congr 1; exact map_pow (adicCoe w) t 2
  have hcoe3 : ((t ^ 2 : K) : w.adicCompletion K) = (t : w.adicCompletion K) ^ 2 :=
    map_pow (adicCoe w) t 2
  rw [hcoe1] at h1
  rw [hcoe3] at h3
  have hs0 : (t : w.adicCompletion K) ^ 2 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h3; exact (zpow_pos hr0 _).ne' h3.symm
  have hz : ‖(y : w.adicCompletion K) / (t : _) ^ 2 - 1‖ = r ^ (n - m) := by
    rw [div_sub_one hs0, norm_div, h1, h3, ← zpow_natCast, Nat.cast_sub hmn.le,
      zpow_sub₀ hr0.ne']
  have hns := sb_not_isSquare_of_norm_sub_one hu.ne_zero hu.norm_lt_one hu.disc h2 hodd
    (by omega) hz
  rintro ⟨z, hz'⟩
  apply hns
  refine ⟨z / (t : w.adicCompletion K), ?_⟩
  rw [hz']
  field_simp [pow_ne_zero_iff two_ne_zero |>.mp hs0]

/-! ## Square classes up to a nonzero square factor -/

theorem isSquare_of_sq_mul {F : Type*} [Field F] {y z u : F} (hu : u ≠ 0) (h : u ^ 2 * y = z)
    (hz : IsSquare z) : IsSquare y := by
  obtain ⟨r, hr⟩ := hz
  refine ⟨r / u, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hu hu)]
  linear_combination h + hr

theorem not_isSquare_of_sq_mul {F : Type*} [Field F] {y z u : F} (h : u ^ 2 * y = z)
    (hz : ¬ IsSquare z) : ¬ IsSquare y := by
  rintro ⟨r, hr⟩
  exact hz ⟨u * r, by rw [← h, hr]; ring⟩

/-! ## Certificates on lane M1's Kronecker expressions at `primeOf (eltO al)` -/

section Kron

open FurioLombardo.M1 FurioLombardo.M1.Kron

variable {al : List ℤ} {hP' : (Ideal.span {eltO al} : Ideal (𝓞 K21)).IsPrime} {hα' : eltO al ≠ 0}

theorem ck_unit {aL aiL caL : List ℤ} {N : ℕ}
    (h : checkK N (.sub (.mul (.lin aL) (.lin aiL)) (.add (.int 1) (.mul (.lin al) (.lin caL)))) =
      true) : zkO aL * zkO aiL = 1 + eltO al * zkO caL := by
  have e := evK_eq_of_check _ _ _ h
  simp only [evK_mul, evK_lin, evK_add, evK_int, Int.cast_one] at e
  have h3 : ((zkO aL : 𝓞 K21) : K21) * ((zkO aiL : 𝓞 K21) : K21) =
      1 + ((eltO al : 𝓞 K21) : K21) * ((zkO caL : 𝓞 K21) : K21) := by
    rw [coe_zkO, coe_zkO, coe_zkO, coe_elt, e]
  apply RingOfIntegers.ext
  exact_mod_cast h3

theorem ck_eq_pow {Y : KE} {aL : List ℤ} {n N : ℕ}
    (h : checkK N (.sub Y (.mul ((KE.lin al).pow n) (.lin aL))) = true) :
    evK Y = (((eltO al : 𝓞 K21) : K21)) ^ n * ((zkO aL : 𝓞 K21) : K21) := by
  have e := evK_eq_of_check _ _ _ h
  rw [evK_mul, evK_pow, evK_lin, evK_lin] at e
  rw [e, coe_elt, coe_zkO]

/-- Square at `primeOf (eltO al)` from three Kronecker tests. -/
theorem ck_isSquare {e : ℕ}
    (h2 : ‖(2 : (primeOf (eltO al) hP' hα').adicCompletion K21)‖ =
      ‖(((eltO al : 𝓞 K21) : K21) : (primeOf (eltO al) hP' hα').adicCompletion K21)‖ ^ e)
    (Y : KE) (tL aL a'L aiL caL : List ℤ) (n m : ℕ) {N1 N2 N3 : ℕ}
    (c1 : checkK N1 (.sub (.sub Y (.mul (.lin tL) (.lin tL))) (.mul ((KE.lin al).pow n) (.lin aL))) =
      true)
    (c2 : checkK N2 (.sub (.mul (.lin tL) (.lin tL)) (.mul ((KE.lin al).pow m) (.lin a'L))) = true)
    (c3 : checkK N3 (.sub (.mul (.lin a'L) (.lin aiL)) (.add (.int 1) (.mul (.lin al) (.lin caL)))) =
      true)
    (hnm : 2 * e + m < n) :
    IsSquare ((evK Y : K21) : (primeOf (eltO al) hP' hα').adicCompletion K21) := by
  have e1 := ck_eq_pow c1
  have e2 := ck_eq_pow c2
  simp only [evK_sub, evK_mul, evK_lin] at e1 e2
  have hy : evK Y - zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ n * ((zkO aL : 𝓞 K21) : K21) := by
    rw [sq, e1]
  have hs : zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ m * ((zkO a'L : 𝓞 K21) : K21) := by
    rw [sq, e2]
  exact cert_isSquare h2 hy hs (ck_unit c3) hnm

/-- The element of a square certificate is nonzero (two of the Kronecker tests of `ck_isSquare`). -/
theorem ck_sq_ne_zero (hP : (Ideal.span {eltO al} : Ideal (𝓞 K21)).IsPrime) (hα : eltO al ≠ 0)
    (Y : KE) (tL aL a'L aiL caL : List ℤ) (n m : ℕ) {N1 N2 N3 : ℕ}
    (c1 : checkK N1 (.sub (.sub Y (.mul (.lin tL) (.lin tL))) (.mul ((KE.lin al).pow n) (.lin aL))) =
      true)
    (c2 : checkK N2 (.sub (.mul (.lin tL) (.lin tL)) (.mul ((KE.lin al).pow m) (.lin a'L))) = true)
    (c3 : checkK N3 (.sub (.mul (.lin a'L) (.lin aiL)) (.add (.int 1) (.mul (.lin al) (.lin caL)))) =
      true)
    (hmn : m < n) : evK Y ≠ 0 := by
  have e1 := ck_eq_pow c1
  have e2 := ck_eq_pow c2
  simp only [evK_sub, evK_mul, evK_lin] at e1 e2
  have hy : evK Y - zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ n * ((zkO aL : 𝓞 K21) : K21) := by
    rw [sq, e1]
  have hs : zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ m * ((zkO a'L : 𝓞 K21) : K21) := by
    rw [sq, e2]
  exact cert_ne_zero hP hα hy hs (ck_unit c3) hmn

/-- Non-square at `primeOf (eltO al)` from an odd valuation (two Kronecker tests). -/
theorem ck_not_isSquare_odd (Y : KE) (aL aiL caL : List ℤ) (n : ℕ) {N1 N2 : ℕ}
    (c1 : checkK N1 (.sub Y (.mul ((KE.lin al).pow n) (.lin aL))) = true)
    (c2 : checkK N2 (.sub (.mul (.lin aL) (.lin aiL)) (.add (.int 1) (.mul (.lin al) (.lin caL)))) =
      true)
    (hn : Odd n) :
    ¬ IsSquare ((evK Y : K21) : (primeOf (eltO al) hP' hα').adicCompletion K21) :=
  cert_not_isSquare_odd (ck_eq_pow c1) (ck_unit c2) hn

/-- Non-square at `primeOf (eltO al)` from an odd depth (four Kronecker tests). -/
theorem ck_not_isSquare_depth {e : ℕ}
    (h2 : ‖(2 : (primeOf (eltO al) hP' hα').adicCompletion K21)‖ =
      ‖(((eltO al : 𝓞 K21) : K21) : (primeOf (eltO al) hP' hα').adicCompletion K21)‖ ^ e)
    (Y : KE) (tL aL aiL caL a'L ai'L ca'L : List ℤ) (n m : ℕ) {N1 N2 N3 N4 : ℕ}
    (c1 : checkK N1 (.sub (.sub Y (.mul (.lin tL) (.lin tL))) (.mul ((KE.lin al).pow n) (.lin aL))) =
      true)
    (c2 : checkK N2 (.sub (.mul (.lin aL) (.lin aiL)) (.add (.int 1) (.mul (.lin al) (.lin caL)))) =
      true)
    (c3 : checkK N3 (.sub (.mul (.lin tL) (.lin tL)) (.mul ((KE.lin al).pow m) (.lin a'L))) = true)
    (c4 : checkK N4 (.sub (.mul (.lin a'L) (.lin ai'L)) (.add (.int 1) (.mul (.lin al) (.lin ca'L)))) =
      true)
    (hodd : Odd (n - m)) (hmn : m < n) (hlt : n < m + 2 * e) :
    ¬ IsSquare ((evK Y : K21) : (primeOf (eltO al) hP' hα').adicCompletion K21) := by
  have e1 := ck_eq_pow c1
  have e3 := ck_eq_pow c3
  simp only [evK_sub, evK_mul, evK_lin] at e1 e3
  have hy : evK Y - zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ n * ((zkO aL : 𝓞 K21) : K21) := by
    rw [sq, e1]
  have hs : zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ m * ((zkO a'L : 𝓞 K21) : K21) := by
    rw [sq, e3]
  exact cert_not_isSquare_depth h2 hy (ck_unit c2) hs (ck_unit c4) hodd hmn hlt

end Kron

end FurioLombardo.Discharge.SelmerBasis.Count
