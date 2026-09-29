import FurioLombardo.Discharge.SelmerBasis.Bridge
import FurioLombardo.M2.Special
import FurioLombardo.M1.ZKInt
import FurioLombardo.Vendor.Toolbox.Padic.UnitBall

/-!
# The places w2, w3 and the place above 7 as height one primes, and norms of global elements

* `primeOf α`: the height one prime `(α)` of a number field, for `α` generating a prime ideal;
  `primeOf_val_self`: `v(α) = exp (-1)`; `primeOf_val_unit`: an element invertible modulo `α`
  has valuation `1`; `primeOf_norm`: the norm in the completion of `x` with `x b = α ^ n a`,
  `a`, `b` invertible modulo `α`, is `‖α‖ ^ n` (the certificate format of the per place data:
  products of `a`, `b` with inverses modulo `α` are checked by lane M2's `mulCheck`).
* `span_al_isPrime`: lane M2's generators `al1`, `al2`, `al3` (norm 2) and `al7` (norm 7³) generate
  prime ideals (the arguments of M2's `special_two`, `special_seven`, restated with the generator
  named); `w2`, `w3`, `w7` are the corresponding height one primes of `𝓞 K21`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField IsDedekindDomain Ideal

section Generic

variable {K : Type*} [Field K] [NumberField K]

/-- The height one prime `(α)`. -/
noncomputable def primeOf (α : 𝓞 K) (hP : (span {α} : Ideal (𝓞 K)).IsPrime) (hα : α ≠ 0) :
    HeightOneSpectrum (𝓞 K) where
  asIdeal := span {α}
  isPrime := hP
  ne_bot := by rwa [ne_eq, span_singleton_eq_bot]

variable {α : 𝓞 K} {hP : (span {α} : Ideal (𝓞 K)).IsPrime} {hα : α ≠ 0}

theorem primeOf_val_self : (primeOf α hP hα).valuation K (α : K) = WithZero.exp (-1) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton (primeOf α hP hα) hα rfl]

theorem primeOf_val_unit {a b c : 𝓞 K} (h : a * b = 1 + α * c) :
    (primeOf α hP hα).valuation K (a : K) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro ha
  apply hP.ne_top
  rw [eq_top_iff_one]
  have hm : a * b - α * c ∈ span {α} :=
    sub_mem (mul_mem_right _ _ ha) (mul_mem_right _ _ (mem_span_singleton_self α))
  rwa [h, add_sub_cancel_right] at hm

theorem primeOf_val_ne_zero (hP : (span {α} : Ideal (𝓞 K)).IsPrime) (hα : α ≠ 0) {a b c : 𝓞 K}
    (h : a * b = 1 + α * c) : (a : K) ≠ 0 := by
  intro h0
  have h1 := primeOf_val_unit (hP := hP) (hα := hα) h
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

/-- **Norms of global elements** from a valuation certificate `x b = α ^ n a`. -/
theorem primeOf_norm {x : K} {n : ℤ} {a b a' b' c c' : 𝓞 K}
    (ha : a * a' = 1 + α * c) (hb : b * b' = 1 + α * c')
    (hx : x * (b : K) = (α : K) ^ n * (a : K)) :
    ‖(x : (primeOf α hP hα).adicCompletion K)‖ =
      ‖((α : K) : (primeOf α hP hα).adicCompletion K)‖ ^ n := by
  refine adic_norm_coe (primeOf α hP hα) primeOf_val_self x n ?_
  have hva := primeOf_val_unit (hP := hP) (hα := hα) ha
  have hvb := primeOf_val_unit (hP := hP) (hα := hα) hb
  have h := congrArg ((primeOf α hP hα).valuation K) hx
  rw [map_mul, map_mul, hvb, hva, mul_one, mul_one, map_zpow₀, primeOf_val_self] at h
  rw [h, ← WithZero.exp_zsmul]
  congr 1
  simp

end Generic


section K21

open FurioLombardo.M2 FurioLombardo.M2.Special Polynomial

theorem absNorm_al2 : absNorm (span {elt al2} : Ideal (𝓞 FurioLombardo.M2.K21)) = 2 := by
  have hv := mulCheck_sound _ _ _ mul_v2; rw [elt_th] at hv
  have hvi := mulCheck_sound _ _ _ mul_v2i; rw [elt_one] at hvi
  have hb2 := mulCheck_sound _ _ _ mul_b2
  have hθ : θ = elt v2 * elt al2 ^ 2 := by rw [← hv, ← hb2]; ring
  have hn : absNorm (span {elt al2}) ^ 2 = 4 := by
    rw [← absNorm_pow, ← absNorm_θ, hθ, absNorm_mul, absNorm_of_mul_eq_one _ _ hvi, one_mul]
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) (by simpa using hn)

theorem absNorm_al1_al3 : absNorm (span {elt al1} : Ideal (𝓞 FurioLombardo.M2.K21)) = 2 ∧
    absNorm (span {elt al3} : Ideal (𝓞 FurioLombardo.M2.K21)) = 2 := by
  have hw := mulCheck_sound _ _ _ mul_w2; rw [elt_thm1] at hw
  have hwi := mulCheck_sound _ _ _ mul_w2i; rw [elt_one] at hwi
  have ha12 := mulCheck_sound _ _ _ mul_a12
  have ha14 := mulCheck_sound _ _ _ mul_a14
  have ha32 := mulCheck_sound _ _ _ mul_a32
  have ha33 := mulCheck_sound _ _ _ mul_a33
  have hm2 := mulCheck_sound _ _ _ mul_m2
  have hθ1 : θ - 1 = elt w2 * (elt al1 ^ 4 * elt al3 ^ 3) := by
    rw [← hw, ← hm2, ← ha14, ← ha33, ← ha12, ← ha32]; ring
  have hn : absNorm (span {elt al1}) ^ 4 * absNorm (span {elt al3}) ^ 3 = 128 := by
    have := absNorm_θ_sub_one
    rw [hθ1, absNorm_mul, absNorm_of_mul_eq_one _ _ hwi, one_mul, absNorm_mul, absNorm_pow,
      absNorm_pow] at this
    exact this
  set n1 := absNorm (span {elt al1})
  set n3 := absNorm (span {elt al3})
  have hn1 : n1 ≠ 0 := by rintro h0; rw [h0] at hn; simp at hn
  have hn3 : n3 ≠ 0 := by rintro h0; rw [h0] at hn; simp at hn
  have hb1 : n1 ≤ 3 := by
    by_contra hc; push_neg at hc
    have h4 : 4 ^ 4 ≤ n1 ^ 4 := Nat.pow_le_pow_left hc 4
    have h1 : 1 ≤ n3 ^ 3 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn3)
    nlinarith
  have hb3 : n3 ≤ 5 := by
    by_contra hc; push_neg at hc
    have h4 : 6 ^ 3 ≤ n3 ^ 3 := Nat.pow_le_pow_left hc 3
    have h1 : 1 ≤ n1 ^ 4 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn1)
    nlinarith
  interval_cases n1 <;> interval_cases n3 <;> simp_all

theorem isPrime_of_absNorm_two {K : Type*} [Field K] [NumberField K] {x : 𝓞 K} (h : absNorm (span {x}) = 2) :
    (span {x} : Ideal (𝓞 K)).IsPrime :=
  isPrime_of_irreducible_absNorm (by rw [h]; exact Nat.prime_two)

/-- `(al7)` is the prime above 7 (the argument of M2's `special_seven`, with the generator named). -/
theorem span_al7_eq (P : Ideal (𝓞 FurioLombardo.M2.K21))
    (hP : P ∈ primesOver (span {(7 : ℤ)}) (𝓞 FurioLombardo.M2.K21)) : span {elt al7} = P := by
  have hp7 : Nat.Prime 7 := by norm_num
  obtain ⟨_, h7P, hnormP⟩ := primesOver_facts hp7 hP
  have hPp : P.IsPrime := hP.1
  have h72 := mulCheck_sound _ _ _ mul_b72
  have h74 := mulCheck_sound _ _ _ mul_b74
  have h76 := mulCheck_sound _ _ _ mul_b76
  have h77 := mulCheck_sound _ _ _ mul_b77
  have he := mulCheck_sound _ _ _ mul_eps7; rw [elt_seven] at he
  have hei := mulCheck_sound _ _ _ mul_eps7i; rw [elt_one] at hei
  have h7 : (7 : 𝓞 FurioLombardo.M2.K21) = elt eps7 * elt al7 ^ 7 := by
    rw [← he, ← h77, ← h76, ← h74, ← h72]; ring
  have hα : elt al7 ∈ P := by
    have : elt eps7 * elt al7 ^ 7 ∈ P := by rw [← h7]; exact_mod_cast h7P
    exact hPp.mem_of_pow_mem 7 (mem_of_mul_mem_of_unit hei this)
  have hn : absNorm (span {elt al7}) ^ 7 = (7 ^ 3) ^ 7 := by
    rw [← absNorm_pow, show (7 ^ 3) ^ 7 = (7 : ℕ) ^ 21 by norm_num, ← absNorm_natCast 7]
    rw [show ((7 : ℕ) : 𝓞 FurioLombardo.M2.K21) = 7 by norm_num, h7, absNorm_mul,
      absNorm_of_mul_eq_one _ _ hei, one_mul]
  have hnα : absNorm (span {elt al7}) = 7 ^ 3 :=
    (Nat.pow_left_injective (by norm_num : 7 ≠ 0)) hn
  have hf : 3 ≤ P.inertiaDeg ℤ := by
    have hpos : 0 < P.inertiaDeg ℤ := by
      have : P.LiesOver (span {((7 : ℕ) : ℤ)}) := hP.2
      have : (span {((7 : ℕ) : ℤ)}).IsMaximal :=
        Int.ideal_span_isMaximal_of_prime 7
      exact inertiaDeg_pos ..
    by_contra hc; push_neg at hc
    have hroot := root_fLow θ evalZ_θ_fL
    rw [fLow_length] at hroot
    have hlt : 7 ^ P.inertiaDeg ℤ < 2 ^ 64 := by
      calc 7 ^ P.inertiaDeg ℤ ≤ 7 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 2 ^ 64 := by norm_num
    interval_cases h : P.inertiaDeg ℤ
    · obtain ⟨fac, hfac, _⟩ := residue_factor hp7 (by norm_num) hP (by rw [h]; norm_num) θ fLow
        fLow_length hroot [] (by simp) s71 (by rw [h]; exact fac7_1)
      simp at hfac
    · obtain ⟨fac, hfac, _⟩ := residue_factor hp7 (by norm_num) hP (by rw [h]; norm_num) θ fLow
        fLow_length hroot [] (by simp) s72 (by rw [h]; exact fac7_2)
      simp at hfac
  have hle : span {elt al7} ≤ P := (span_singleton_le_iff_mem _).mpr hα
  obtain ⟨J, hJ⟩ := (dvd_iff_le.mpr hle : P ∣ span {elt al7})
  have hnJ : absNorm P * absNorm J = 7 ^ 3 := by rw [← map_mul, ← hJ, hnα]
  have hP3 : 7 ^ 3 ≤ absNorm P := by
    rw [hnormP]; exact Nat.pow_le_pow_right (by norm_num) hf
  have hJ1 : absNorm J = 1 := by
    have hJ0 : absNorm J ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hnJ; norm_num at hnJ
    have : absNorm P * absNorm J ≥ 7 ^ 3 * absNorm J := Nat.mul_le_mul_right _ hP3
    have : absNorm J ≤ 1 := by nlinarith
    omega
  rw [absNorm_eq_one_iff] at hJ1
  rw [hJ1, mul_top] at hJ
  exact hJ

theorem span_al7_isPrime : (span {elt al7} : Ideal (𝓞 FurioLombardo.M2.K21)).IsPrime := by
  have : (span {(7 : ℤ)} : Ideal ℤ).IsPrime :=
    (Int.ideal_span_isMaximal_of_prime 7).isPrime
  obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 FurioLombardo.M2.K21) (span {(7 : ℤ)})
  rw [span_al7_eq P hP]
  exact hP.1

theorem absNorm_al7 : absNorm (span {elt al7} : Ideal (𝓞 FurioLombardo.M2.K21)) = 7 ^ 3 := by
  have he := mulCheck_sound _ _ _ mul_eps7; rw [elt_seven] at he
  have hei := mulCheck_sound _ _ _ mul_eps7i; rw [elt_one] at hei
  have h72 := mulCheck_sound _ _ _ mul_b72
  have h74 := mulCheck_sound _ _ _ mul_b74
  have h76 := mulCheck_sound _ _ _ mul_b76
  have h77 := mulCheck_sound _ _ _ mul_b77
  have h7 : (7 : 𝓞 FurioLombardo.M2.K21) = elt eps7 * elt al7 ^ 7 := by
    rw [← he, ← h77, ← h76, ← h74, ← h72]; ring
  have hn : absNorm (span {elt al7}) ^ 7 = (7 ^ 3) ^ 7 := by
    rw [← absNorm_pow, show (7 ^ 3) ^ 7 = (7 : ℕ) ^ 21 by norm_num, ← absNorm_natCast 7]
    rw [show ((7 : ℕ) : 𝓞 FurioLombardo.M2.K21) = 7 by norm_num, h7, absNorm_mul,
      absNorm_of_mul_eq_one _ _ hei, one_mul]
  exact (Nat.pow_left_injective (by norm_num : 7 ≠ 0)) hn

theorem elt_ne_zero_of_absNorm {K : Type*} [Field K] [NumberField K] {x : 𝓞 K} {n : ℕ} (h : absNorm (span {x}) = n)
    (hn : n ≠ 0) : x ≠ 0 := by
  rintro rfl
  rw [span_singleton_eq_bot.mpr rfl, absNorm_bot] at h
  exact hn h.symm

/-- Lane M2's `elt`, typed on M1's field (the same type, `M2.k21_eq`). -/
noncomputable def eltO (a : List ℤ) : 𝓞 FurioLombardo.M1.K21 := elt a

theorem absNorm_eltO_al2 : absNorm (span {eltO al2} : Ideal (𝓞 FurioLombardo.M1.K21)) = 2 :=
  absNorm_al2

theorem absNorm_eltO_al3 : absNorm (span {eltO al3} : Ideal (𝓞 FurioLombardo.M1.K21)) = 2 :=
  absNorm_al1_al3.2

theorem absNorm_eltO_al7 : absNorm (span {eltO al7} : Ideal (𝓞 FurioLombardo.M1.K21)) = 7 ^ 3 :=
  absNorm_al7

theorem span_eltO_al7_isPrime : (span {eltO al7} : Ideal (𝓞 FurioLombardo.M1.K21)).IsPrime :=
  span_al7_isPrime

/-- The place `w2` (`e = 12`), the prime `(al2)`. -/
noncomputable def w2 : HeightOneSpectrum (𝓞 FurioLombardo.M1.K21) :=
  primeOf (eltO al2) (isPrime_of_absNorm_two absNorm_eltO_al2)
    (elt_ne_zero_of_absNorm absNorm_eltO_al2 two_ne_zero)

/-- The place `w3` (`e = 6`), the prime `(al3)`. -/
noncomputable def w3 : HeightOneSpectrum (𝓞 FurioLombardo.M1.K21) :=
  primeOf (eltO al3) (isPrime_of_absNorm_two absNorm_eltO_al3)
    (elt_ne_zero_of_absNorm absNorm_eltO_al3 two_ne_zero)

/-- The place above 7, the prime `(al7)`. -/
noncomputable def w7 : HeightOneSpectrum (𝓞 FurioLombardo.M1.K21) :=
  primeOf (eltO al7) span_eltO_al7_isPrime (elt_ne_zero_of_absNorm absNorm_eltO_al7 (by norm_num))

theorem card_res_w2 : Nat.card (𝓞 FurioLombardo.M1.K21 ⧸ w2.asIdeal) = 2 := by
  rw [← absNorm_eltO_al2, absNorm_apply]
  rfl

theorem card_res_w3 : Nat.card (𝓞 FurioLombardo.M1.K21 ⧸ w3.asIdeal) = 2 := by
  rw [← absNorm_eltO_al3, absNorm_apply]
  rfl

theorem card_res_w7 : Nat.card (𝓞 FurioLombardo.M1.K21 ⧸ w7.asIdeal) = 7 ^ 3 := by
  rw [← absNorm_eltO_al7, absNorm_apply]
  rfl

end K21


/-! ## Norms at `primeOf α` from integrality certificates -/

section GenericNorm

variable {K : Type*} [Field K] [NumberField K]

/-- The coercion `K → K_v` as a ring hom. -/
noncomputable def adicCoe (v : HeightOneSpectrum (𝓞 K)) : K →+* v.adicCompletion K where
  toFun x := (x : v.adicCompletion K)
  map_one' := HeightOneSpectrum.adicCompletion.coe_one (K := K) (v := v)
  map_mul' x y := HeightOneSpectrum.adicCompletion.coe_mul (K := K) (v := v) x y
  map_zero' := HeightOneSpectrum.adicCompletion.coe_zero (K := K) (v := v)
  map_add' x y := HeightOneSpectrum.adicCompletion.coe_add (K := K) (v := v) x y

theorem adicCoe_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    adicCoe v x = (x : v.adicCompletion K) := rfl

theorem adic_coe_sub (v : HeightOneSpectrum (𝓞 K)) (x y : K) :
    ((x - y : K) : v.adicCompletion K) = (x : v.adicCompletion K) - y :=
  map_sub (adicCoe v) x y

theorem adic_coe_ofNat (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : K) : v.adicCompletion K) = OfNat.ofNat n :=
  map_ofNat (adicCoe v) n

variable {α : 𝓞 K} {hP : (span {α} : Ideal (𝓞 K)).IsPrime} {hα : α ≠ 0}

/-- **Upper bound from a certificate** `x b = α ^ n a` with `a` merely integral. -/
theorem primeOf_norm_le {x : K} {n : ℤ} {a b b' c' : 𝓞 K} (hb : b * b' = 1 + α * c')
    (hx : x * (b : K) = (α : K) ^ n * (a : K)) :
    ‖(x : (primeOf α hP hα).adicCompletion K)‖ ≤
      ‖((α : K) : (primeOf α hP hα).adicCompletion K)‖ ^ n := by
  have hvb := primeOf_val_unit (hP := hP) (hα := hα) hb
  have hva : (primeOf α hP hα).valuation K (a : K) ≤ 1 := HeightOneSpectrum.valuation_le_one _ a
  have h := congrArg ((primeOf α hP hα).valuation K) hx
  rw [map_mul, map_mul, hvb, mul_one, map_zpow₀, primeOf_val_self] at h
  have hle : (primeOf α hP hα).valuation K x ≤ WithZero.exp (-n) := by
    rw [h, ← WithZero.exp_zsmul]
    calc WithZero.exp (n • (-1 : ℤ)) * (primeOf α hP hα).valuation K (a : K)
        ≤ WithZero.exp (n • (-1 : ℤ)) * 1 := mul_le_mul_right hva _
      _ = WithZero.exp (-n) := by simp
  rcases hle.lt_or_eq with hlt | heq
  · exact (adic_norm_coe_lt (primeOf α hP hα) primeOf_val_self x n hlt).le
  · exact (adic_norm_coe (primeOf α hP hα) primeOf_val_self x n heq).le

theorem primeOf_normUnif : NormUnif ((α : K) : (primeOf α hP hα).adicCompletion K) :=
  adic_normUnif (primeOf α hP hα) primeOf_val_self

/-- **Square certificate at `primeOf α`**: `‖y / s - 1‖ < ‖4‖` from `(y - s) b = α ^ n a`,
`s b' = α ^ m a'` with `b`, `b'`, `a'` invertible modulo `α` and `2 e < n - m`, where
`‖2‖ = ‖α‖ ^ e`. With `s` a square, `isSquare_of_norm_div_sq_sub_one_lt` makes `y` a square. -/
theorem sq_cert_adic {y s : K} {n m : ℤ} {e : ℕ} {a b bi cb a' ai ca b' bi' cb' : 𝓞 K}
    (h2 : ‖(2 : (primeOf α hP hα).adicCompletion K)‖ =
      ‖((α : K) : (primeOf α hP hα).adicCompletion K)‖ ^ e)
    (hb : b * bi = 1 + α * cb) (hy : (y - s) * (b : K) = (α : K) ^ n * (a : K))
    (ha' : a' * ai = 1 + α * ca) (hb' : b' * bi' = 1 + α * cb')
    (hs : s * (b' : K) = (α : K) ^ m * (a' : K)) (hnm : 2 * (e : ℤ) < n - m) :
    ‖(y : (primeOf α hP hα).adicCompletion K) / (s : (primeOf α hP hα).adicCompletion K) - 1‖ <
      ‖(4 : (primeOf α hP hα).adicCompletion K)‖ := by
  set w := primeOf α hP hα
  have hu : NormUnif ((α : K) : w.adicCompletion K) := primeOf_normUnif
  set r := ‖((α : K) : w.adicCompletion K)‖
  have hr0 : 0 < r := norm_pos_iff.mpr hu.ne_zero
  have hr1 : r < 1 := hu.norm_lt_one
  have hys : ‖((y - s : K) : w.adicCompletion K)‖ ≤ r ^ n := primeOf_norm_le hb hy
  have hsn : ‖(s : w.adicCompletion K)‖ = r ^ m := primeOf_norm ha' hb' hs
  have hs0 : (s : w.adicCompletion K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hsn; exact (zpow_pos hr0 m).ne' hsn.symm
  have hcoe : ((y - s : K) : w.adicCompletion K) = (y : w.adicCompletion K) - s :=
    adic_coe_sub w y s
  have h4 : ‖(4 : w.adicCompletion K)‖ = r ^ (2 * (e : ℤ)) := by
    have h22 : (4 : w.adicCompletion K) = 2 ^ 2 := by norm_num
    rw [h22, norm_pow, h2, ← pow_mul, ← zpow_natCast]
    congr 1
    push_cast
    ring
  rw [div_sub_one hs0, norm_div, ← hcoe, hsn, h4, div_lt_iff₀ (zpow_pos hr0 m), ← zpow_add₀ hr0.ne']
  calc _ ≤ r ^ n := hys
    _ < r ^ (2 * (e : ℤ) + m) := zpow_lt_zpow_right_of_lt_one₀ hr0 hr1 (by omega)

end GenericNorm

/-! ## Uniformizers of the unit ball -/

section Unif

open FurioLombardo.Vendor.Toolbox.UnitBall

variable {F : Type*} [NontriviallyNormedField F]

/-- A norm uniformizer is a uniformizer of the unit ball. -/
theorem NormUnif.isUniformizer {π : F} (hπ : NormUnif π) : IsUniformizer π where
  norm_pos := norm_pos_iff.mpr hπ.ne_zero
  norm_lt_one := hπ.norm_lt_one
  norm_le_of_lt_one x hx := by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [norm_zero]; exact norm_nonneg _
    obtain ⟨n, hn⟩ := hπ.disc x hx0
    have h0 : 0 < ‖π‖ := norm_pos_iff.mpr hπ.ne_zero
    rw [hn] at hx ⊢
    have hn1 : 1 ≤ n := by
      by_contra h
      push_neg at h
      have : (1 : ℝ) ≤ ‖π‖ ^ n := one_le_zpow_of_nonpos₀ h0 hπ.norm_lt_one.le (by omega)
      linarith
    calc ‖π‖ ^ n ≤ ‖π‖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 hπ.norm_lt_one.le hn1
      _ = ‖π‖ := zpow_one _

/-- `p = π ^ e u` in the unit ball, `u` a unit, from `‖p‖ = ‖π‖ ^ e`. -/
theorem natCast_eq_pow_mul_unit [IsUltrametricDist F] {π : F} (hπ : IsUniformizer π) {p e : ℕ}
    (h : ‖(p : F)‖ = ‖π‖ ^ e) :
    ∃ u : unitBall F, IsUnit u ∧ (p : unitBall F) = hπ.toBall ^ e * u := by
  have hπe : π ^ e ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hnorm : ‖(p : F) / π ^ e‖ = 1 := by
    rw [norm_div, norm_pow, h, div_self (pow_ne_zero _ hπ.norm_pos.ne')]
  refine ⟨⟨(p : F) / π ^ e, hnorm.le⟩, isUnit_iff_norm_eq_one.mpr hnorm, ?_⟩
  apply Subtype.ext
  simp only [SubringClass.coe_natCast, SubmonoidClass.coe_pow, Subring.coe_mul,
    IsUniformizer.coe_toBall]
  field_simp

end Unif

/-! ## Instances on the completions of a number field (scoped) -/

namespace Adic

variable {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

noncomputable scoped instance instNontriviallyNormedField : NontriviallyNormedField (w.adicCompletion K) :=
  Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))

scoped instance instProperSpace : ProperSpace (w.adicCompletion K) := adic_properSpace w

scoped instance instCharZero : CharZero (w.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (w.adicCompletion K)).injective

end Adic

/-! ## Lane M2's integral basis is M1's (`elt_eq_zkO`), for the checker `checkK` -/

section Basis

theorem evalZ_eq_evalL {R : Type*} [CommRing R] (t : R) :
    ∀ l : List ℤ, M2.evalZ t l = M1.evalL t l
  | [] => rfl
  | a :: l => by rw [M2.evalZ_cons, evalZ_eq_evalL t l]; rfl

theorem addZ_eq_addL : ∀ l m : List ℤ, M2.addZ l m = M1.addL l m
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: m => by
    show (a + b) :: M2.addZ l m = (a + b) :: M1.addL l m
    rw [addZ_eq_addL l m]

theorem smulZ_eq_smulL (c : ℤ) : ∀ l : List ℤ, M2.smulZ c l = M1.smulL c l
  | [] => rfl
  | a :: l => by
    show c * a :: M2.smulZ c l = c * a :: M1.smulL c l
    rw [smulZ_eq_smulL c l]

theorem combo_eq_combo : ∀ (a : List ℤ) (Ws : List (List ℤ)), M2.combo a Ws = M1.Kron.combo a Ws
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | c :: a, W :: Ws => by
    show M2.addZ (M2.smulZ c W) (M2.combo a Ws) = M1.addL (M1.smulL c W) (M1.Kron.combo a Ws)
    rw [addZ_eq_addL, smulZ_eq_smulL, combo_eq_combo a Ws]

theorem WL_eq_zkNum : M2.WL = M1.zkNum := by decide +kernel

theorem eltK_eq_zkE (a : List ℤ) : (M2.eltK a : M1.K21) = M1.zkE a := by
  have hD : ((M2.DD : ℤ) : M1.K21) = ((M1.Dz : ℕ) : M1.K21) := by
    rw [show M2.DD = ((M1.Dz : ℕ) : ℤ) from rfl, Int.cast_natCast]
  show M2.evalZ (AdjoinRoot.root M1.fQ : M1.K21) (M2.combo a M2.WL) / ((M2.DD : ℤ) : M1.K21) =
    M1.dInv * M1.evalL M1.θ (M1.Kron.combo a M1.zkNum)
  rw [evalZ_eq_evalL, combo_eq_combo, WL_eq_zkNum, hD, div_eq_inv_mul]
  rfl

theorem elt_eq_zkO (a : List ℤ) : (eltO a : 𝓞 M1.K21) = M1.zkO a :=
  Subtype.ext (eltK_eq_zkE a)

theorem coe_elt (a : List ℤ) : ((eltO a : 𝓞 M1.K21) : M1.K21) = M1.zkE a := eltK_eq_zkE a

end Basis

/-! ## The places `w2`, `w3`, `w7`: uniformizers, `‖2‖`, `‖7‖`, residue fields -/

section Places

open FurioLombardo.M1.Kron (KE)
open scoped Adic

/-- `2 / al2 ^ 12` in PARI's integral basis (code/selmer-local-conditions/valuation_certs_w12_w6.out). -/
def w2aL : List ℤ := [-2789746660292993024135650510, -11468057532887506667414177082, -3139018006810396091980323019, 4487247904869661987644493460, -6671751312145592915509110132, 2820041571328957656809574652, 2099926622467857271501487639, 5086395101736747642098562224, -778268569875107041612608695, 2141652505747968564164248124, 7207339301725465499287134391, -1779922038909345797615241890, -3181393735463446986340578889, 1261639077741850435089472315, -991520394654865200280773366, 992594417499872282991729617, -4951213536084241515838107980, 2998593758576596963389254005, -972599132616319597728375186, 2636973226611381300213808565, -5139730037935155231692836446]

/-- `(w2aL - 1) / al2`. -/
def w2cL : List ℤ := [-1561413959746009391072938921351, 8957879841597760524203851616, 1525814910171904151474661815609, 1149173163231366376449135888262, 1125184631099111948433854113303, 401185777810777400717673699339, -260370293461597684968830797782, 699722614918691936296019379393, 122778292044951157692897265684, 303189254826295847386782958464, 150315236402636107182909209768, 430298707330448781831321948589, -324836915454693126560832899062, 144803123405917974308839565716, 353785075489985614768197442936, 1998058723692532220114901590932, 491785238805220086684470641445, -42364860139248164693282070459, 981624394812622077754170310180, 534169737401303434054412261864, 1722131151214173682504862118240]

/-- `2 / al3 ^ 6`. -/
def w3aL : List ℤ := [-150, 201, 193, 174, -52, -309, 355, -79, 120, 435, -95, 180, 294, -100, 18, 233, 170, -12, 18, 92, -163]

/-- `(w3aL - 1) / al3`. -/
def w3cL : List ℤ := [241, -785, -712, -473, 133, 1137, -918, 351, -428, -1501, 501, -614, -980, 410, -203, -578, -442, 49, -104, -351, 484]

theorem ck_w2a : M1.checkK 2048 (.sub (.mul ((KE.lin M2.Special.al2).pow 12) (.lin w2aL)) (.int 2)) =
    true := by decide +kernel

theorem ck_w2c : M1.checkK 2048
    (.sub (.lin w2aL) (.add (.int 1) (.mul (.lin M2.Special.al2) (.lin w2cL)))) = true := by
  decide +kernel

theorem ck_w3a : M1.checkK 2048 (.sub (.mul ((KE.lin M2.Special.al3).pow 6) (.lin w3aL)) (.int 2)) =
    true := by decide +kernel

theorem ck_w3c : M1.checkK 2048
    (.sub (.lin w3aL) (.add (.int 1) (.mul (.lin M2.Special.al3) (.lin w3cL)))) = true := by
  decide +kernel

/-- `‖2‖` at `primeOf (al)` from `al ^ e a = 2`, `a = 1 + al c`. -/
theorem norm_two_of_ck {al aL cL : List ℤ} {e : ℕ} {hP} {hα}
    (h1 : M1.checkK 2048 (.sub (.mul ((KE.lin al).pow e) (.lin aL)) (.int 2)) = true)
    (h2 : M1.checkK 2048 (.sub (.lin aL) (.add (.int 1) (.mul (.lin al) (.lin cL)))) = true) :
    ‖(2 : (primeOf (eltO al) hP hα).adicCompletion M1.K21)‖ =
      ‖(((eltO al : 𝓞 M1.K21) : M1.K21) : (primeOf (eltO al) hP hα).adicCompletion M1.K21)‖ ^ e := by
  have e1 := M1.evK_eq_of_check _ _ _ h1
  have e2 := M1.evK_eq_of_check _ _ _ h2
  simp only [M1.evK_mul, M1.evK_pow, M1.evK_lin, M1.evK_int, M1.evK_add] at e1 e2
  have ha : M1.zkO aL * 1 = 1 + eltO al * M1.zkO cL := by
    have h3 : ((M1.zkO aL : 𝓞 M1.K21) : M1.K21) =
        1 + ((eltO al : 𝓞 M1.K21) : M1.K21) * ((M1.zkO cL : 𝓞 M1.K21) : M1.K21) := by
      rw [M1.coe_zkO, M1.coe_zkO, coe_elt, e2]; push_cast; ring
    rw [mul_one]
    exact RingOfIntegers.ext h3
  have hb : (1 : 𝓞 M1.K21) * 1 = 1 + eltO al * 0 := by ring
  have hx : (2 : M1.K21) * ((1 : 𝓞 M1.K21) : M1.K21) =
      ((eltO al : 𝓞 M1.K21) : M1.K21) ^ (e : ℤ) * ((M1.zkO aL : 𝓞 M1.K21) : M1.K21) := by
    rw [zpow_natCast, coe_elt, M1.coe_zkO, e1]; push_cast; ring
  have h := primeOf_norm (hP := hP) (hα := hα) ha hb hx
  rw [zpow_natCast] at h
  rw [← h]
  congr 1
  exact (adic_coe_ofNat _ 2).symm

/-- The uniformizer of `w2`, `al2`. -/
theorem normUnif_w2 :
    NormUnif (((eltO M2.Special.al2 : 𝓞 M1.K21) : M1.K21) : w2.adicCompletion M1.K21) :=
  primeOf_normUnif

theorem normUnif_w3 :
    NormUnif (((eltO M2.Special.al3 : 𝓞 M1.K21) : M1.K21) : w3.adicCompletion M1.K21) :=
  primeOf_normUnif

theorem normUnif_w7 :
    NormUnif (((eltO M2.Special.al7 : 𝓞 M1.K21) : M1.K21) : w7.adicCompletion M1.K21) :=
  primeOf_normUnif

theorem isUniformizer_w2 : FurioLombardo.Vendor.Toolbox.UnitBall.IsUniformizer
    (((eltO M2.Special.al2 : 𝓞 M1.K21) : M1.K21) : w2.adicCompletion M1.K21) :=
  normUnif_w2.isUniformizer

theorem isUniformizer_w3 : FurioLombardo.Vendor.Toolbox.UnitBall.IsUniformizer
    (((eltO M2.Special.al3 : 𝓞 M1.K21) : M1.K21) : w3.adicCompletion M1.K21) :=
  normUnif_w3.isUniformizer

theorem isUniformizer_w7 : FurioLombardo.Vendor.Toolbox.UnitBall.IsUniformizer
    (((eltO M2.Special.al7 : 𝓞 M1.K21) : M1.K21) : w7.adicCompletion M1.K21) :=
  normUnif_w7.isUniformizer

/-- `e(w2 / 2) = 12`. -/
theorem norm_two_w2 : ‖(2 : w2.adicCompletion M1.K21)‖ =
    ‖(((eltO M2.Special.al2 : 𝓞 M1.K21) : M1.K21) : w2.adicCompletion M1.K21)‖ ^ 12 :=
  norm_two_of_ck ck_w2a ck_w2c

/-- `e(w3 / 2) = 6`. -/
theorem norm_two_w3 : ‖(2 : w3.adicCompletion M1.K21)‖ =
    ‖(((eltO M2.Special.al3 : 𝓞 M1.K21) : M1.K21) : w3.adicCompletion M1.K21)‖ ^ 6 :=
  norm_two_of_ck ck_w3a ck_w3c

/-- `e(w7 / 7) = 7`, from lane M2's `7 = eps7 al7 ^ 7` with `eps7` a unit. -/
theorem norm_seven_w7 : ‖(7 : w7.adicCompletion M1.K21)‖ =
    ‖(((eltO M2.Special.al7 : 𝓞 M1.K21) : M1.K21) : w7.adicCompletion M1.K21)‖ ^ 7 := by
  have he := M2.mulCheck_sound _ _ _ M2.Special.mul_eps7; rw [M2.elt_seven] at he
  have hei := M2.mulCheck_sound _ _ _ M2.Special.mul_eps7i; rw [M2.elt_one] at hei
  have h72 := M2.mulCheck_sound _ _ _ M2.Special.mul_b72
  have h74 := M2.mulCheck_sound _ _ _ M2.Special.mul_b74
  have h76 := M2.mulCheck_sound _ _ _ M2.Special.mul_b76
  have h77 := M2.mulCheck_sound _ _ _ M2.Special.mul_b77
  have h7 : (7 : 𝓞 M1.K21) = eltO M2.Special.eps7 * eltO M2.Special.al7 ^ 7 := by
    have h : (7 : 𝓞 M2.K21) = M2.elt M2.Special.eps7 * M2.elt M2.Special.al7 ^ 7 := by
      rw [← he, ← h77, ← h76, ← h74, ← h72]; ring
    exact h
  have ha : eltO M2.Special.eps7 * eltO M2.Special.eps7i = 1 + eltO M2.Special.al7 * 0 := by
    rw [mul_zero, add_zero]; exact hei
  have hb : (1 : 𝓞 M1.K21) * 1 = 1 + eltO M2.Special.al7 * 0 := by ring
  have hx : (7 : M1.K21) * ((1 : 𝓞 M1.K21) : M1.K21) =
      ((eltO M2.Special.al7 : 𝓞 M1.K21) : M1.K21) ^ ((7 : ℕ) : ℤ) *
        ((eltO M2.Special.eps7 : 𝓞 M1.K21) : M1.K21) := by
    have h := congrArg (algebraMap (𝓞 M1.K21) M1.K21) h7
    rw [map_ofNat, map_mul, map_pow] at h
    rw [zpow_natCast, RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
      RingOfIntegers.coe_eq_algebraMap, map_one, mul_one, h]
    ring
  have h := primeOf_norm (hP := span_eltO_al7_isPrime)
    (hα := elt_ne_zero_of_absNorm absNorm_eltO_al7 (by norm_num)) ha hb hx
  rw [zpow_natCast] at h
  have h' : ‖((7 : M1.K21) : w7.adicCompletion M1.K21)‖ =
      ‖(((eltO M2.Special.al7 : 𝓞 M1.K21) : M1.K21) : w7.adicCompletion M1.K21)‖ ^ 7 := h
  rw [← h', adic_coe_ofNat]

/-- The residue field of `w2` is `𝔽₂`. -/
theorem res_w2 : ∀ y : w2.adicCompletion M1.K21, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1 :=
  res_F2 (w2.adicCompletionIntegers M1.K21) (adic_mem_integers_iff w2)
    ((adic_residue_card w2).trans card_res_w2)

/-- The residue field of `w3` is `𝔽₂`. -/
theorem res_w3 : ∀ y : w3.adicCompletion M1.K21, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1 :=
  res_F2 (w3.adicCompletionIntegers M1.K21) (adic_mem_integers_iff w3)
    ((adic_residue_card w3).trans card_res_w3)

/-- `2 = al2 ^ 12 u` in the unit ball of `K_w2`, `u` a unit. -/
theorem two_eq_pow_mul_unit_w2 : ∃ u : FurioLombardo.Vendor.Toolbox.UnitBall.unitBall (w2.adicCompletion M1.K21),
    IsUnit u ∧ ((2 : ℕ) : FurioLombardo.Vendor.Toolbox.UnitBall.unitBall (w2.adicCompletion M1.K21)) =
      isUniformizer_w2.toBall ^ 12 * u :=
  natCast_eq_pow_mul_unit isUniformizer_w2 (by rw [Nat.cast_ofNat]; exact norm_two_w2)

theorem two_eq_pow_mul_unit_w3 : ∃ u : FurioLombardo.Vendor.Toolbox.UnitBall.unitBall (w3.adicCompletion M1.K21),
    IsUnit u ∧ ((2 : ℕ) : FurioLombardo.Vendor.Toolbox.UnitBall.unitBall (w3.adicCompletion M1.K21)) =
      isUniformizer_w3.toBall ^ 6 * u :=
  natCast_eq_pow_mul_unit isUniformizer_w3 (by rw [Nat.cast_ofNat]; exact norm_two_w3)

theorem seven_eq_pow_mul_unit_w7 : ∃ u : FurioLombardo.Vendor.Toolbox.UnitBall.unitBall (w7.adicCompletion M1.K21),
    IsUnit u ∧ ((7 : ℕ) : FurioLombardo.Vendor.Toolbox.UnitBall.unitBall (w7.adicCompletion M1.K21)) =
      isUniformizer_w7.toBall ^ 7 * u :=
  natCast_eq_pow_mul_unit isUniformizer_w7 (by rw [Nat.cast_ofNat]; exact norm_seven_w7)

end Places

end FurioLombardo.Discharge.SelmerBasis
