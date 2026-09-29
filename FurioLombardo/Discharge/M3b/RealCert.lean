import FurioLombardo.M1.ListPoly

/-!
# Sign certificates for integer polynomials on real intervals (Möbius transform positivity)

A polynomial is an integer coefficient list `l` (constant term first, as in `FurioLombardo.M1.evalL`).
For coefficient lists `u, v` the transform `mobL u v l = Σ_k l_k u^k v^(L-1-k)` (`L` the length of `l`)
satisfies `v(y) · mobL u v l (y) = v(y)^L · l(u(y) / v(y))` (`evalL_mobL`). So if every coefficient of
`s · mobL u v l` is `≥ 0` and one is `> 0` (`signCert s u v l`, a Bool the kernel decides), then
`s · l(u(y)/v(y)) > 0` for every `y > 0` with `v(y) > 0`. The substitutions used:
* interval `(A/D, B/D)`: `u = A + B y`, `v = D + D y` (`signCert_Ioo`);
* rays `(C/D, ∞)` and `(-∞, C/D)`: `u = C ± D y`, `v = D` (`signCert_Ioi`, `signCert_Iio`);
* point `A/D`: `u = A`, `v = D` (`signCert_pt`).

`derivL` is the derivative of a list; a sign certificate of `derivL l` on an interval makes
`x ↦ l(x)` injective on the closed interval (`injOn_of_signCert`). `rootCover` checks that the real
line is covered by rays and pieces where `l` has a sign, except for a list of pieces `mono`: every
real root of `l` then lies in the interior of one of them (`rootCover_sound`). `bracketL` gives a
root by the intermediate value theorem (`exists_root_of_bracketL`).
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1

/-! ## The transform -/

/-- `v ^ n` as a coefficient list. -/
def powL (v : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => mulL v (powL v n)

/-- `mobL u v l = Σ_k l_k u^k v^(L-1-k)`, `L = l.length`. -/
def mobL (u v : List ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: l => addL (smulL a (powL v l.length)) (mulL u (mobL u v l))

/-- Every coefficient is `≥ 0`. -/
def nonnegL : List ℤ → Bool
  | [] => true
  | a :: l => decide (0 ≤ a) && nonnegL l

/-- Some coefficient is `> 0`. -/
def someposL : List ℤ → Bool
  | [] => false
  | a :: l => decide (0 < a) || someposL l

/-- Every coefficient is `≥ 0` and one is `> 0`. -/
def posCoeffL (q : List ℤ) : Bool := nonnegL q && someposL q

/-- The sign certificate: `s · mobL u v l` has coefficients `≥ 0`, not all zero. -/
def signCert (s : ℤ) (u v l : List ℤ) : Bool := posCoeffL (smulL s (mobL u v l))

theorem evalL_powL {R : Type*} [CommRing R] (y : R) (v : List ℤ) :
    ∀ n : ℕ, evalL y (powL v n) = evalL y v ^ n
  | 0 => by simp [powL]
  | n + 1 => by rw [powL, evalL_mulL, evalL_powL y v n, pow_succ, mul_comm]

theorem evalL_mobL {F : Type*} [Field F] (y : F) (u v : List ℤ) (hv : evalL y v ≠ 0) :
    ∀ l : List ℤ, evalL y v * evalL y (mobL u v l) =
      evalL y v ^ l.length * evalL (evalL y u / evalL y v) l
  | [] => by simp [mobL]
  | a :: l => by
    have ih := evalL_mobL y u v hv l
    simp only [mobL, evalL_addL, evalL_smulL, evalL_mulL, evalL_powL, evalL_cons,
      List.length_cons]
    set V := evalL y v
    set U := evalL y u
    calc V * (a * V ^ l.length + U * evalL y (mobL u v l))
        = a * V ^ (l.length + 1) + U * (V * evalL y (mobL u v l)) := by ring
      _ = a * V ^ (l.length + 1) + U * (V ^ l.length * evalL (U / V) l) := by rw [ih]
      _ = V ^ (l.length + 1) * (a + U / V * evalL (U / V) l) := by
        field_simp
        ring

/-! ## Positivity of a list with nonnegative coefficients -/

theorem evalL_nonneg_of_nonnegL {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {y : F} (hy : 0 ≤ y) : ∀ l : List ℤ, nonnegL l = true → 0 ≤ evalL y l
  | [], _ => by simp
  | a :: l, h => by
    simp only [nonnegL, Bool.and_eq_true, decide_eq_true_eq] at h
    have := evalL_nonneg_of_nonnegL hy l h.2
    simp only [evalL_cons]
    have ha : (0 : F) ≤ a := by exact_mod_cast h.1
    positivity

theorem evalL_pos_of_posCoeffL {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {y : F} (hy : 0 < y) : ∀ l : List ℤ, nonnegL l = true → someposL l = true → 0 < evalL y l
  | [], _, h => by simp [someposL] at h
  | a :: l, h, h' => by
    simp only [nonnegL, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [someposL, Bool.or_eq_true, decide_eq_true_eq] at h'
    simp only [evalL_cons]
    have h0 := evalL_nonneg_of_nonnegL hy.le l h.2
    rcases h' with ha | hl
    · have ha' : (0 : F) < a := by exact_mod_cast ha
      have : 0 ≤ y * evalL y l := mul_nonneg hy.le h0
      linarith
    · have ha' : (0 : F) ≤ a := by exact_mod_cast h.1
      have : 0 < y * evalL y l := mul_pos hy (evalL_pos_of_posCoeffL hy l h.2 hl)
      linarith

/-- **Soundness of a sign certificate.** -/
theorem signCert_spec {s : ℤ} {u v l : List ℤ} (h : signCert s u v l = true) {y : ℝ} (hy : 0 < y)
    (hv : 0 < evalL y v) : 0 < (s : ℝ) * evalL (evalL y u / evalL y v) l := by
  unfold signCert posCoeffL at h
  rw [Bool.and_eq_true] at h
  have h1 := evalL_pos_of_posCoeffL hy _ h.1 h.2
  rw [evalL_smulL] at h1
  have h2 := evalL_mobL y u v hv.ne' l
  have h3 : 0 < evalL y v * ((s : ℝ) * evalL y (mobL u v l)) := mul_pos hv h1
  have h4 : evalL y v * ((s : ℝ) * evalL y (mobL u v l)) =
      evalL y v ^ l.length * ((s : ℝ) * evalL (evalL y u / evalL y v) l) := by
    linear_combination (s : ℝ) * h2
  rw [h4] at h3
  exact pos_of_mul_pos_right h3 (pow_pos hv _).le

/-- Sign on the open interval `(A/D, B/D)`. -/
theorem signCert_Ioo {s A B : ℤ} {D : ℕ} {l : List ℤ} (hD : 0 < D)
    (h : signCert s [A, B] [(D : ℤ), (D : ℤ)] l = true) {x : ℝ} (h1 : (A : ℝ) / D < x)
    (h2 : x < (B : ℝ) / D) : 0 < (s : ℝ) * evalL x l := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hA : (A : ℝ) < D * x := by rwa [div_lt_iff₀ hD', mul_comm] at h1
  have hB : D * x < (B : ℝ) := by rwa [lt_div_iff₀ hD', mul_comm] at h2
  set y : ℝ := (D * x - A) / (B - D * x) with hy
  have hy0 : 0 < y := div_pos (by linarith) (by linarith)
  have hv : 0 < evalL y [(D : ℤ), (D : ℤ)] := by
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast]
    positivity
  have := signCert_spec h hy0 hv
  have hx : evalL y [A, B] / evalL y [(D : ℤ), (D : ℤ)] = x := by
    rw [div_eq_iff hv.ne']
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast]
    have hne : (B : ℝ) - D * x ≠ 0 := by linarith
    rw [hy]
    field_simp
    ring
  rwa [hx] at this

/-- Sign on the ray `(C/D, ∞)`. -/
theorem signCert_Ioi {s C : ℤ} {D : ℕ} {l : List ℤ} (hD : 0 < D)
    (h : signCert s [C, (D : ℤ)] [(D : ℤ)] l = true) {x : ℝ} (h1 : (C : ℝ) / D < x) :
    0 < (s : ℝ) * evalL x l := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hy0 : 0 < x - C / D := by linarith
  have hv : 0 < evalL (x - C / D) [(D : ℤ)] := by
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast]
    exact hD'
  have := signCert_spec h hy0 hv
  have hx : evalL (x - C / D) [C, (D : ℤ)] / evalL (x - C / D) [(D : ℤ)] = x := by
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast]
    field_simp
    ring
  rwa [hx] at this

/-- Sign on the ray `(-∞, C/D)`. -/
theorem signCert_Iio {s C : ℤ} {D : ℕ} {l : List ℤ} (hD : 0 < D)
    (h : signCert s [C, -(D : ℤ)] [(D : ℤ)] l = true) {x : ℝ} (h1 : x < (C : ℝ) / D) :
    0 < (s : ℝ) * evalL x l := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hy0 : 0 < C / D - x := by linarith
  have hv : 0 < evalL (C / D - x) [(D : ℤ)] := by
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast]
    exact hD'
  have := signCert_spec h hy0 hv
  have hx : evalL (C / D - x) [C, -(D : ℤ)] / evalL (C / D - x) [(D : ℤ)] = x := by
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast, Int.cast_neg]
    field_simp
    ring
  rwa [hx] at this

/-- Sign at the point `A/D`. -/
theorem signCert_pt {s A : ℤ} {D : ℕ} {l : List ℤ} (hD : 0 < D)
    (h : signCert s [A] [(D : ℤ)] l = true) : 0 < (s : ℝ) * evalL ((A : ℝ) / D) l := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hv : 0 < evalL (1 : ℝ) [(D : ℤ)] := by
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast]
    exact hD'
  have := signCert_spec h one_pos hv
  have hx : evalL (1 : ℝ) [A] / evalL (1 : ℝ) [(D : ℤ)] = (A : ℝ) / D := by
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_natCast]
  rwa [hx] at this

theorem ne_zero_of_pos_mul {s : ℤ} {z : ℝ} (h : 0 < (s : ℝ) * z) : z ≠ 0 := by
  rintro rfl; simp at h

/-! ## Derivative, continuity, monotone pieces -/

/-- The derivative of a coefficient list (same length, trailing zero). -/
def derivL : List ℤ → List ℤ
  | [] => []
  | _ :: l => addL l (0 :: derivL l)

theorem hasDerivAt_evalL (x : ℝ) :
    ∀ l : List ℤ, HasDerivAt (fun t : ℝ => evalL t l) (evalL x (derivL l)) x
  | [] => by simpa [derivL] using hasDerivAt_const x (0 : ℝ)
  | a :: l => by
    have ih := hasDerivAt_evalL x l
    have h := ((hasDerivAt_id x).mul ih).const_add (a : ℝ)
    have e : 1 * evalL x l + id x * evalL x (derivL l) = evalL x (derivL (a :: l)) := by
      simp [derivL, evalL_addL]
    rw [← e]
    exact h

theorem continuous_evalL (l : List ℤ) : Continuous (fun t : ℝ => evalL t l) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_evalL x l).continuousAt

/-- A sign certificate of the derivative on `(A/D, B/D)` makes `l` injective on `[A/D, B/D]`. -/
theorem injOn_of_signCert {s A B : ℤ} {D : ℕ} {l : List ℤ} (hD : 0 < D)
    (h : signCert s [A, B] [(D : ℤ), (D : ℤ)] (derivL l) = true) :
    Set.InjOn (fun t : ℝ => evalL t l) (Set.Icc ((A : ℝ) / D) ((B : ℝ) / D)) := by
  have hmono : StrictMonoOn (fun t : ℝ => (s : ℝ) * evalL t l)
      (Set.Icc ((A : ℝ) / D) ((B : ℝ) / D)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuous_const.mul (continuous_evalL l)).continuousOn) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [((hasDerivAt_evalL x l).const_mul (s : ℝ)).deriv]
    exact signCert_Ioo hD h hx.1 hx.2
  intro x hx x' hx' hxx
  exact hmono.injOn hx hx' (by simp only at hxx ⊢; rw [hxx])

/-! ## Covering the real roots -/

/-- `l(A/D) ≠ 0`. -/
def ptOK (D : ℕ) (l : List ℤ) (A : ℤ) : Bool :=
  signCert 1 [A] [(D : ℤ)] l || signCert (-1) [A] [(D : ℤ)] l

/-- `(A/D, B/D)` is one of the excluded pieces, or `l` has a sign on it. -/
def pieceOK (D : ℕ) (l : List ℤ) (mono : List (ℤ × ℤ)) (A B : ℤ) : Bool :=
  mono.any (fun p => p.1 == A && p.2 == B) || signCert 1 [A, B] [(D : ℤ), (D : ℤ)] l ||
    signCert (-1) [A, B] [(D : ℤ), (D : ℤ)] l

/-- The last element of `a :: bs`. -/
def lastL : ℤ → List ℤ → ℤ
  | a, [] => a
  | _, b :: bs => lastL b bs

/-- The chain of breakpoints `a < b₁ < ... < bₘ` (over `D`): `l` does not vanish at the breakpoints,
and every piece is excluded or carries a sign certificate of `l`. -/
def chainOK (D : ℕ) (l : List ℤ) (mono : List (ℤ × ℤ)) : ℤ → List ℤ → Bool
  | a, [] => ptOK D l a
  | a, b :: bs => ptOK D l a && decide (a < b) && pieceOK D l mono a b && chainOK D l mono b bs

/-- The full cover: the ray left of the first breakpoint, the chain, the ray right of the last. -/
def rootCover (D : ℕ) (l : List ℤ) (mono : List (ℤ × ℤ)) (a : ℤ) (bs : List ℤ) : Bool :=
  (signCert 1 [a, -(D : ℤ)] [(D : ℤ)] l || signCert (-1) [a, -(D : ℤ)] [(D : ℤ)] l) &&
    chainOK D l mono a bs &&
    (signCert 1 [lastL a bs, (D : ℤ)] [(D : ℤ)] l || signCert (-1) [lastL a bs, (D : ℤ)] [(D : ℤ)] l)

theorem ptOK_ne_zero {D : ℕ} {l : List ℤ} {A : ℤ} (hD : 0 < D) (h : ptOK D l A = true) :
    evalL ((A : ℝ) / D) l ≠ 0 := by
  unfold ptOK at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact ne_zero_of_pos_mul (signCert_pt hD h)
  · exact ne_zero_of_pos_mul (signCert_pt hD h)

theorem chainOK_sound {D : ℕ} {l : List ℤ} {mono : List (ℤ × ℤ)} (hD : 0 < D) :
    ∀ (bs : List ℤ) (a : ℤ), chainOK D l mono a bs = true → ∀ x : ℝ, (a : ℝ) / D ≤ x →
      x ≤ (lastL a bs : ℝ) / D → evalL x l = 0 →
        ∃ p ∈ mono, (p.1 : ℝ) / D < x ∧ x < (p.2 : ℝ) / D
  | [], a, h, x, h1, h2, hx => by
    simp only [lastL] at h2
    have : x = a / D := le_antisymm h2 h1
    subst this
    exact absurd hx (ptOK_ne_zero hD h)
  | b :: bs, a, h, x, h1, h2, hx => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hpt, hab⟩, hpc⟩, hch⟩ := h
    rcases h1.lt_or_eq with h1 | h1
    · rcases lt_or_ge x ((b : ℝ) / D) with h3 | h3
      · unfold pieceOK at hpc
        simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hpc
        rcases hpc with (⟨p, hp, hp1, hp2⟩ | hs) | hs
        · exact ⟨p, hp, by rw [hp1]; exact h1, by rw [hp2]; exact h3⟩
        · exact absurd hx (ne_zero_of_pos_mul (signCert_Ioo hD hs h1 h3))
        · exact absurd hx (ne_zero_of_pos_mul (signCert_Ioo hD hs h1 h3))
      · exact chainOK_sound hD bs b hch x h3 (by simpa only [lastL] using h2) hx
    · subst h1
      exact absurd hx (ptOK_ne_zero hD hpt)

/-- **Every real root of `l` lies inside one of the excluded pieces.** -/
theorem rootCover_sound {D : ℕ} {l : List ℤ} {mono : List (ℤ × ℤ)} {a : ℤ} {bs : List ℤ}
    (hD : 0 < D) (h : rootCover D l mono a bs = true) {x : ℝ} (hx : evalL x l = 0) :
    ∃ p ∈ mono, (p.1 : ℝ) / D < x ∧ x < (p.2 : ℝ) / D := by
  unfold rootCover at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hL, hc⟩, hR⟩ := h
  rcases lt_or_ge x ((a : ℝ) / D) with h1 | h1
  · rcases hL with hL | hL
    · exact absurd hx (ne_zero_of_pos_mul (signCert_Iio hD hL h1))
    · exact absurd hx (ne_zero_of_pos_mul (signCert_Iio hD hL h1))
  rcases le_or_gt x ((lastL a bs : ℝ) / D) with h2 | h2
  · exact chainOK_sound hD bs a hc x h1 h2 hx
  · rcases hR with hR | hR
    · exact absurd hx (ne_zero_of_pos_mul (signCert_Ioi hD hR h2))
    · exact absurd hx (ne_zero_of_pos_mul (signCert_Ioi hD hR h2))

/-! ## Existence of a root -/

/-- `A < B` and `l` has opposite signs at `A/D` and `B/D`. -/
def bracketL (D : ℕ) (l : List ℤ) (A B : ℤ) : Bool :=
  decide (A < B) && ((signCert (-1) [A] [(D : ℤ)] l && signCert 1 [B] [(D : ℤ)] l) ||
    (signCert 1 [A] [(D : ℤ)] l && signCert (-1) [B] [(D : ℤ)] l))

theorem exists_root_of_bracketL {D : ℕ} {l : List ℤ} {A B : ℤ} (hD : 0 < D)
    (h : bracketL D l A B = true) :
    ∃ r : ℝ, (A : ℝ) / D < r ∧ r < (B : ℝ) / D ∧ evalL r l = 0 := by
  unfold bracketL at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hAB, h⟩ := h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hle : (A : ℝ) / D ≤ (B : ℝ) / D :=
    div_le_div_of_nonneg_right (by exact_mod_cast hAB.le) hD'.le
  have hc := (continuous_evalL l).continuousOn (s := Set.Icc ((A : ℝ) / D) ((B : ℝ) / D))
  rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · have hA' := signCert_pt hD hA
    have hB' := signCert_pt hD hB
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_pos] at hA' hB'
    obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ := intermediate_value_Ioo hle hc ⟨hA', hB'⟩
    exact ⟨r, hr1, hr2, hr⟩
  · have hA' := signCert_pt hD hA
    have hB' := signCert_pt hD hB
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_pos] at hA' hB'
    obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ := intermediate_value_Ioo' hle hc ⟨hB', hA'⟩
    exact ⟨r, hr1, hr2, hr⟩

end FurioLombardo.Discharge.M3b
