import Mathlib
import FurioLombardo.Discharge.M3a.TwoTorsionClass
import FurioLombardo.Discharge.M3a.LocalFacts
import FurioLombardo.Discharge.SelmerBasis.Count.Poly

/-!
# Count lane: the 2-torsion of `A(K)` from the monic quadratic divisors of `f`

* `exists_tors_finset`: a finset of `A(K) = Jac f` containing `A(K)[2]` with at most `1 + #D` elements, for
  any finset `D` containing the monic quadratic divisors of `f` (M3a's `jac_sq_eq_one`: a point of order
  dividing `2` is `1` or the class of `⟨u, Y⟩` for such a `u`);
* on the reversed Prym sextics `fRev k = c q (A² - d B²)` over a field `kv` with `σ : K21 →+* kv`:
  `fRev_map_eq` (the normal form after `σ`), `noRoot_fRev` (no root when `σ(d)` is not a square),
  `irrFactor_fRev` (a monic irreducible quadratic factor when `σ(ndK)` is not a square,
  `ndK = D0² - d D1²`, M3a's `ND`), and the resulting bounds `#A(kv)[2] ≤ 4` (`tors_noRoot`) and `≤ 8`
  (`tors_irrFactor`).
-/

set_option autoImplicit false

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M3a (jac_sq_eq_one)
open FurioLombardo.Discharge.M3a.Bruin (fRev q h c d a0 a1 b0 b1 zQ fRev_eq_mul q_explicit
  h_eq_normForm ND_eq D0_eq D1_eq)

namespace FurioLombardo.Discharge.SelmerBasis.Count

section Tors

variable {K : Type*} [Field K]

/-- **`A(K)[2]` from the monic quadratic divisors.** If `D` contains every monic quadratic divisor
of `f`, some finset with at most `#D + 1` points contains every `c` with `c² = 1`. -/
theorem exists_tors_finset (f : K[X]) [GoodSextic f] (D : Finset K[X])
    (hD : ∀ u : K[X], u.Monic → u.natDegree = 2 → u ∣ f → u ∈ D) :
    ∃ tT : Finset (Jac f), tT.card ≤ D.card + 1 ∧ ∀ c : Jac f, c ^ 2 = 1 → c ∈ tT := by
  classical
  let g : K[X] → Jac f := fun u =>
    if hex : ∃ c : Jac f, ∃ hu : u.Monic, (c : Pic f) = ClassGroup.mk0 (mumford0 f hu.ne_zero 0)
    then hex.choose else 1
  refine ⟨insert 1 (D.image g), ?_, ?_⟩
  · calc (insert 1 (D.image g)).card ≤ (D.image g).card + 1 := Finset.card_insert_le _ _
      _ ≤ D.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
  · intro c hc
    rcases jac_sq_eq_one f hc with h1 | ⟨u, hu, hud, huf, hcu⟩
    · rw [h1]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      refine Finset.mem_image.mpr ⟨u, hD u hu hud huf, ?_⟩
      have hex : ∃ c : Jac f, ∃ hu : u.Monic, (c : Pic f) = ClassGroup.mk0 (mumford0 f hu.ne_zero 0) :=
        ⟨c, hu, hcu⟩
      obtain ⟨hu', h'⟩ := hex.choose_spec
      simp only [g, hex, ↓reduceDIte]
      exact Subtype.ext (h'.trans hcu.symm)

end Tors

section FRev

variable {kv : Type*} [Field kv] (σ : K21 →+* kv) (k : Fin 2)

/-- `fRev k` after `σ`, in the normal form `c q (A² - d B²)` with `d = disc q`. -/
theorem fRev_map_eq : (fRev k).map σ =
    C (σ (c k)) * (X ^ 2 + C (σ ((q k).coeff 1)) * X + C (σ ((q k).coeff 0))) *
      ((X ^ 2 + C (σ (a1 k)) * X + C (σ (a0 k))) ^ 2 -
        C (σ ((q k).coeff 1) ^ 2 - 4 * σ ((q k).coeff 0)) *
          (C (σ (b1 k)) * X + C (σ (b0 k))) ^ 2) := by
  have hq := q_explicit k
  have hh := h_eq_normForm k
  rw [fRev_eq_mul]
  conv_lhs => rw [hq, hh]
  simp only [FurioLombardo.Discharge.M3a.normForm, d, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_ofNat, map_C, map_X, map_sub, map_mul,
    map_pow, map_ofNat]

theorem sigma_d : σ (d k) = σ ((q k).coeff 1) ^ 2 - 4 * σ ((q k).coeff 0) := by
  simp only [d, map_sub, map_mul, map_pow, map_ofNat]

/-- No root of `fRev k` over `kv` when `σ(d k)` is not a square. -/
theorem noRoot_fRev [GoodSextic ((fRev k).map σ)] (hd : ¬ IsSquare (σ (d k))) (x : kv) :
    ((fRev k).map σ).eval x ≠ 0 :=
  cnt_noRoot_normForm (GoodSextic.two_ne_zero (f := (fRev k).map σ)) _ _ _ _ _ _ _ _
    (fRev_map_eq σ k) GoodSextic.squarefree (by rwa [sigma_d] at hd) x

/-- M3a's `ND = D0² - d D1²`, with `D0 = a1² + d b1² - 4 a0`, `D1 = 2 a1 b1 - 4 b0`: the norm of the
discriminant of `X² + (a1 + ω b1) X + (a0 + ω b0)`, `ω² = d`. -/
noncomputable def ndK (k : Fin 2) : K21 :=
  (a1 k ^ 2 + d k * b1 k ^ 2 - 4 * a0 k) ^ 2 - d k * (2 * a1 k * b1 k - 4 * b0 k) ^ 2

theorem ndK_eq (k : Fin 2) : ndK k = (zQ k 2).ev := by
  rw [ND_eq, D0_eq, D1_eq]; rfl

/-- A monic irreducible quadratic factor of `fRev k` over `kv` when `σ(ndK k)` is not a square. -/
theorem irrFactor_fRev [GoodSextic ((fRev k).map σ)] (hND : ¬ IsSquare (σ (ndK k))) :
    ∃ g : kv[X], g.Monic ∧ g.natDegree = 2 ∧ Irreducible g ∧ g ∣ (fRev k).map σ := by
  refine cnt_irrFactor_of_ND (GoodSextic.two_ne_zero (f := (fRev k).map σ)) _ _ _ _ _ _ _ _
    (fRev_map_eq σ k) ?_
  simpa only [ndK, d, map_sub, map_mul, map_pow, map_add, map_ofNat] using hND

/-- `#A(kv)[2] ≤ 4` when `σ(d k)` is not a square. -/
theorem tors_noRoot [GoodSextic ((fRev k).map σ)] (hd : ¬ IsSquare (σ (d k))) :
    ∃ tT : Finset (Jac ((fRev k).map σ)), tT.card ≤ 2 ^ 2 ∧
      ∀ c : Jac ((fRev k).map σ), c ^ 2 = 1 → c ∈ tT := by
  have h6 := GoodSextic.natDegree_eq (f := (fRev k).map σ)
  obtain ⟨D, hDc, hD⟩ := cnt_quadDiv_noRoot _ (GoodSextic.squarefree.ne_zero) h6.le
    (noRoot_fRev σ k hd)
  obtain ⟨tT, htc, ht⟩ := exists_tors_finset _ D hD
  exact ⟨tT, by omega, ht⟩

/-- `#A(kv)[2] ≤ 8` when `σ(ndK k)` is not a square. -/
theorem tors_irrFactor [GoodSextic ((fRev k).map σ)] (hND : ¬ IsSquare (σ (ndK k))) :
    ∃ tT : Finset (Jac ((fRev k).map σ)), tT.card ≤ 2 ^ 3 ∧
      ∀ c : Jac ((fRev k).map σ), c ^ 2 = 1 → c ∈ tT := by
  have h6 := GoodSextic.natDegree_eq (f := (fRev k).map σ)
  obtain ⟨g, hgm, hgd, hg, hgf⟩ := irrFactor_fRev σ k hND
  obtain ⟨D, hDc, hD⟩ := cnt_quadDiv_irrFactor _ g (GoodSextic.squarefree.ne_zero) h6 hg hgm hgd hgf
  obtain ⟨tT, htc, ht⟩ := exists_tors_finset _ D hD
  exact ⟨tT, by omega, ht⟩

end FRev

end FurioLombardo.Discharge.SelmerBasis.Count
