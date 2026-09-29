import FurioLombardo.M1.Norms
import FurioLombardo.M1.ResRing
import FurioLombardo.M1.DataAvoid

/-!
# The set S of six primes

`S = {v | 2 ∈ v ∨ 7 ∈ v ∨ pi3 ∈ v ∨ pi439 ∈ v}` and `S ⊆ {(la), (lb), (lc), (pi7), v3, v439}`, so
`S.ncard ≤ 6`.

* `(la), (lb), (lc)` are prime (absolute norm 2), `(pi7)` is prime (norm 343 and residue degree 3).
* Primes containing `pi3` (resp. `pi439`): a maximal ideal `Q ∋ p` gives a root of one factor of
  `f mod p` in `𝓞/Q` (`exists_factor`), and the quotient map factors through the residue ring of
  that factor (`mk_eq_liftRR_comp`, uniqueness of homomorphisms out of `𝓞 K21`). At every factor
  but one the image of the generator is invertible (kernel check `avOK`), so `Q` is the kernel of
  the residue map at the remaining degree one factor.
-/

namespace FurioLombardo.M1

open Polynomial NumberField Kron IsDedekindDomain

/-! ## Factorizations modulo `p` -/

/-- Coefficients of the monic `X ^ n + gl`. -/
def fullL (gl : List ℤ) : List ℤ := gl ++ [1]

theorem evalL_append {R : Type*} [CommRing R] (t : R) :
    ∀ l m : List ℤ, evalL t (l ++ m) = evalL t l + t ^ l.length * evalL t m
  | [], m => by simp
  | a :: l, m => by
    simp only [List.cons_append, evalL_cons, evalL_append t l m, List.length_cons, pow_succ]
    ring

theorem evalL_fullL {R : Type*} [CommRing R] (t : R) (gl : List ℤ) :
    evalL t (fullL gl) = t ^ gl.length + evalL t gl := by
  rw [fullL, evalL_append]; simp; ring

/-- Product of the monic factors. -/
def prodFull : List (List ℤ) → List ℤ
  | [] => [1]
  | gl :: l => mulL (fullL gl) (prodFull l)

theorem evalL_prodFull {R : Type*} [CommRing R] (t : R) :
    ∀ l : List (List ℤ), evalL t (prodFull l) = (l.map fun gl => evalL t (fullL gl)).prod
  | [] => by simp [prodFull]
  | gl :: l => by rw [prodFull, evalL_mulL, evalL_prodFull t l]; simp

/-- In a field of characteristic `p` where `t` is a root of `f`, `t` is a root of one factor. -/
theorem exists_factor {F : Type*} [CommRing F] [IsDomain F] (p : ℤ) (hp : (p : F) = 0)
    (φs : List (List ℤ))
    (hprod : eqM p fL (prodFull φs) = true) (t : F) (ht : evalL t fL = 0) :
    ∃ gl ∈ φs, t ^ gl.length + evalL t gl = 0 := by
  have h := evalL_eq_of_eqM p hp t _ _ hprod
  rw [ht, evalL_prodFull] at h
  obtain ⟨gl, hgl, hx0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h.symm)
  exact ⟨gl, hgl, by rw [← evalL_fullL]; exact hx0⟩

/-! ## Factoring the quotient map -/

section Quot

variable (Q : Ideal (𝓞 K21)) [hQ : Q.IsMaximal] (p : ℕ) [hp : Fact p.Prime]
  (hpQ : ((p : ℤ) : 𝓞 K21) ∈ Q)

/-- The residue field `𝓞/Q`. -/
abbrev QF := 𝓞 K21 ⧸ Q

include hpQ in
theorem QF_p_eq_zero : ((p : ℤ) : QF Q) = 0 := by
  rw [← map_intCast (Ideal.Quotient.mk Q)]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hpQ

include hpQ in
theorem QF_charP : CharP (QF Q) p := by
  rw [CharP.charP_iff_prime_eq_zero hp.out]
  exact_mod_cast QF_p_eq_zero Q p hpQ

/-- The image of `θ` in `𝓞/Q`. -/
noncomputable def θQ : QF Q := Ideal.Quotient.mk Q θO

theorem evalL_θQ_fL : evalL (θQ Q) fL = 0 := by
  rw [θQ, ← map_evalL]
  have : evalL θO fL = 0 := by rw [← aeval_ofListL, ofListL_fL]; exact aeval_θO_fZ
  rw [this, map_zero]

theorem aeval_θQ_fZ : @aeval ℤ (QF Q) _ _ (Ring.toIntAlgebra (QF Q)) (θQ Q) fZ = 0 := by
  rw [← ofListL_fL, aeval_ofListL]; exact evalL_θQ_fL Q

include hpQ in
theorem QF_uB (uB : ℤ) (huB : (uB * DB - 1) % p = 0) : (uB : QF Q) * (DB : QF Q) = 1 := by
  have h1 : (((uB * DB - 1) % p : ℤ) : QF Q) = 0 := by rw [huB]; simp
  rw [intCast_emod (p : ℤ) (QF_p_eq_zero Q p hpQ)] at h1
  push_cast at h1
  exact sub_eq_zero.mp h1

/-- The ring homomorphism `RR p gl → 𝓞/Q`, root to `θ mod Q`. -/
noncomputable def liftRR (gl : List ℤ) (ht : θQ Q ^ gl.length + evalL (θQ Q) gl = 0) :
    RR p gl →+* QF Q :=
  haveI := QF_charP Q p hpQ
  AdjoinRoot.lift (ZMod.castHom (dvd_refl p) (QF Q)) (θQ Q) (by
    have e : (ZMod.castHom (dvd_refl p) (QF Q)).comp (Int.castRingHom (ZMod p)) =
        Int.castRingHom (QF Q) := RingHom.ext_int _ _
    rw [phiP, eval₂_add, eval₂_X_pow, eval₂_map, e, evalL_ofListL]
    exact ht)

theorem liftRR_rr (gl : List ℤ) (ht : θQ Q ^ gl.length + evalL (θQ Q) gl = 0) :
    liftRR Q p hpQ gl ht (rr p gl) = θQ Q := AdjoinRoot.lift_root _

/-- The quotient map factors through the residue ring of the factor. -/
theorem mk_eq_liftRR_comp (gl : List ℤ) (hdiv : dividesF p gl = true) (uB : ℤ)
    (huB : (uB * DB - 1) % p = 0) (ht : θQ Q ^ gl.length + evalL (θQ Q) gl = 0) :
    Ideal.Quotient.mk Q = (liftRR Q p hpQ gl ht).comp (resRR p gl hdiv uB huB) := by
  have hu := QF_uB Q p hpQ uB huB
  exact (resHom_unique (θQ Q) (aeval_θQ_fZ Q) (uB : QF Q) hu (Ideal.Quotient.mk Q) rfl).trans
    (resHom_unique (θQ Q) (aeval_θQ_fZ Q) (uB : QF Q) hu
      ((liftRR Q p hpQ gl ht).comp (resRR p gl hdiv uB huB))
      (by rw [RingHom.comp_apply, resRR_θO, liftRR_rr])).symm

/-- The residue map at a degree one factor `X + c`, into `ZMod p`. -/
noncomputable def resZ (c : ℤ) (hdiv : dividesF p [c] = true) (uB : ℤ)
    (huB : (uB * DB - 1) % p = 0) : 𝓞 K21 →+* ZMod p :=
  resHom ((-c : ℤ) : ZMod p)
    (by
      rw [← ofListL_fL, aeval_ofListL]
      have hroot : ((-c : ℤ) : ZMod p) ^ [c].length + evalL ((-c : ℤ) : ZMod p) [c] = 0 := by
        simp
      rw [← evalL_redL _ [c] hroot]
      refine evalL_eq_zero_of_allDvdL (p : ℤ) (by simp) _ _ hdiv)
    (uB : ZMod p)
    (by
      have h1 : (((uB * DB - 1) % p : ℤ) : ZMod p) = 0 := by rw [huB]; simp
      rw [intCast_emod (p : ℤ) (by simp)] at h1
      push_cast at h1
      exact sub_eq_zero.mp h1)

include hpQ in
/-- At a degree one factor, `Q` is the kernel of the residue map. -/
theorem eq_ker_resZ (c : ℤ) (hdiv : dividesF p [c] = true) (uB : ℤ)
    (huB : (uB * DB - 1) % p = 0) (ht : θQ Q + (c : QF Q) = 0) :
    Q = RingHom.ker (resZ p c hdiv uB huB) := by
  have := QF_charP Q p hpQ
  let ι : ZMod p →+* QF Q := ZMod.castHom (dvd_refl p) (QF Q)
  have hu := QF_uB Q p hpQ uB huB
  have hcomp : Ideal.Quotient.mk Q = ι.comp (resZ p c hdiv uB huB) := by
    exact (resHom_unique (θQ Q) (aeval_θQ_fZ Q) (uB : QF Q) hu (Ideal.Quotient.mk Q) rfl).trans
      (resHom_unique (θQ Q) (aeval_θQ_fZ Q) (uB : QF Q) hu (ι.comp (resZ p c hdiv uB huB))
        (by
          rw [RingHom.comp_apply, resZ, resHom_θO, map_intCast]
          push_cast
          linear_combination -ht)).symm
  ext x
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, hcomp, RingHom.comp_apply]
  exact map_eq_zero_iff ι ι.injective

end Quot

/-! ## The residue image of `zkO a` as a list -/

/-- `ρ(zkO a)` in `RR p gl` as a list, for `uD * Dz ≡ 1 (mod p)`. -/
def resL (p : ℤ) (gl : List ℤ) (uD : ℤ) (a : List ℤ) : List ℤ :=
  modL p (smulL uD (redL gl (combo a zkNum)))

theorem evalL_resL (p : ℕ) [Fact p.Prime] (gl : List ℤ) (hdiv : dividesF p gl = true) (uB : ℤ)
    (huB : (uB * DB - 1) % p = 0) (uD : ℤ) (huD : (uD * Dz - 1) % p = 0) (a : List ℤ) :
    evalL (rr p gl) (resL p gl uD a) = resRR p gl hdiv uB huB (zkO a) := by
  have hpR := RR_p_eq_zero p gl
  have hu : (uD : RR p gl) * ((Dz : ℤ) : RR p gl) = 1 := by
    have h1 : (((uD * Dz - 1) % p : ℤ) : RR p gl) = 0 := by rw [huD]; simp
    rw [intCast_emod (p : ℤ) hpR] at h1
    push_cast at h1
    exact_mod_cast sub_eq_zero.mp h1
  rw [hom_zkO _ (uD : RR p gl) hu, resRR_θO, resL, evalL_modL (p : ℤ) hpR, evalL_smulL,
    evalL_redL _ gl (rr_root p gl)]

/-! ## Primes containing `pi3` and `pi439` -/

/-- The kernel check: every factor divides `f`, the product of the factors is `f`, the factor
`idx` is `X + c`, and the generator is invertible at every other factor. -/
def avOK (p : ℤ) (fac inv : List (List ℤ)) (idx : ℕ) (uD : ℤ) (a : List ℤ) : Bool :=
  eqM p fL (prodFull fac) &&
  (List.range fac.length).all fun i =>
    dividesF p (fac.getD i []) &&
    (if i = idx then (fac.getD i []).length == 1 else
      eqM p (mulM p (fac.getD i []) (resL p (fac.getD i []) uD a) (inv.getD i [])) [1])

theorem avOK3 : avOK 3 avFac3 avInv3 avIdx3 avUD3 (gensL.getD 16 []) = true := by decide +kernel

theorem avOK439 : avOK 439 avFac439 avInv439 avIdx439 avUD439 (gensL.getD 17 []) = true := by
  decide +kernel

theorem avUB3_ok : (avUB3 * DB - 1) % (3 : ℕ) = 0 := by decide +kernel
theorem avUB439_ok : (avUB439 * DB - 1) % (439 : ℕ) = 0 := by decide +kernel
theorem avUD3_ok : (avUD3 * Dz - 1) % (3 : ℕ) = 0 := by decide +kernel
theorem avUD439_ok : (avUD439 * Dz - 1) % (439 : ℕ) = 0 := by decide +kernel

/-- **Prime avoidance**: a maximal ideal containing the generator `zkO a` (which divides `p`) is
the kernel of the residue map at the factor `idx`. -/
theorem eq_ker_of_mem (p : ℕ) [Fact p.Prime] (fac inv : List (List ℤ)) (idx : ℕ) (uD uB : ℤ)
    (a : List ℤ) (hok : avOK p fac inv idx uD a = true) (huB : (uB * DB - 1) % p = 0)
    (huD : (uD * Dz - 1) % p = 0) (hidx : idx < fac.length)
    (Q : Ideal (𝓞 K21)) [Q.IsMaximal] (hpQ : ((p : ℤ) : 𝓞 K21) ∈ Q) (haQ : zkO a ∈ Q) :
    ∃ (c : ℤ) (hdiv : dividesF p [c] = true), fac.getD idx [] = [c] ∧
      Q = RingHom.ker (resZ p c hdiv uB huB) := by
  simp only [avOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hprod, hall⟩ := hok
  obtain ⟨gl, hgl, ht⟩ := exists_factor (p : ℤ) (QF_p_eq_zero Q p hpQ) fac hprod (θQ Q)
    (evalL_θQ_fL Q)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgl
  have hgi : fac.getD i [] = fac[i] := by simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨hdiv, hcase⟩ := hall i hi
  rw [hgi] at hdiv hcase
  by_cases hii : i = idx
  · subst hii
    simp only [↓reduceIte] at hcase
    have hlen : fac[i].length = 1 := by simpa using hcase
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
    rw [hc] at hdiv ht
    refine ⟨c, hdiv, by rw [hgi, hc], eq_ker_resZ Q p hpQ c hdiv uB huB ?_⟩
    simpa [add_comm] using ht
  · exfalso
    simp only [hii, ↓reduceIte] at hcase
    have hcomp := mk_eq_liftRR_comp Q p hpQ fac[i] hdiv uB huB ht
    have h1 := evalL_eq_of_eqM (p : ℤ) (RR_p_eq_zero p fac[i]) (rr p fac[i]) _ _ hcase
    rw [evalL_mulM (p : ℤ) (RR_p_eq_zero p fac[i]) fac[i] (rr p fac[i]) (rr_root p fac[i]),
      evalL_resL p fac[i] hdiv uB huB uD huD] at h1
    have h2 := congrArg (liftRR Q p hpQ fac[i] ht) h1
    rw [map_mul, ← RingHom.comp_apply, ← hcomp, Ideal.Quotient.eq_zero_iff_mem.mpr haQ,
      zero_mul] at h2
    simp at h2

/-! ## The primes above 2 and 7 -/

/-- A maximal ideal containing `g` with the same absolute norm as `(g)` is `(g)`. -/
theorem eq_span_of_absNorm_eq (Q : Ideal (𝓞 K21)) (g : 𝓞 K21) (hg : g ∈ Q)
    (h : Ideal.absNorm Q = Ideal.absNorm (Ideal.span {g}))
    (h0 : Ideal.absNorm (Ideal.span {g}) ≠ 0) : Q = Ideal.span {g} := by
  have hle : Ideal.span {g} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hg
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hn := congrArg Ideal.absNorm hJ
  rw [map_mul, ← h] at hn
  have hQ0 : Ideal.absNorm Q ≠ 0 := h ▸ h0
  have hJ1 : Ideal.absNorm J = 1 := by
    have : Ideal.absNorm Q * Ideal.absNorm J = Ideal.absNorm Q * 1 := by rw [← hn, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hQ0) this
  rw [Ideal.absNorm_eq_one_iff] at hJ1
  rw [hJ, hJ1, Ideal.mul_top]

theorem absNorm_span_gO (i : ℕ) : Ideal.absNorm (Ideal.span {gO i}) = (nZ (gO i)).natAbs :=
  Ideal.absNorm_span_singleton _

theorem unit_not_mem {Q : Ideal (𝓞 K21)} (hQ : Q ≠ ⊤) {x y : 𝓞 K21} (h : x * y = 1) : x ∉ Q := by
  intro hx
  exact hQ ((Ideal.eq_top_iff_one Q).mpr (h ▸ Q.mul_mem_right y hx))

/-- A maximal ideal containing `2` is one of `(la)`, `(lb)`, `(lc)`. -/
theorem eq_of_two_mem (Q : Ideal (𝓞 K21)) [hQ : Q.IsMaximal] (h2 : (2 : 𝓞 K21) ∈ Q) :
    Q = Ideal.span {gO 12} ∨ Q = Ideal.span {gO 13} ∨ Q = Ideal.span {gO 14} := by
  have hP : Q.IsPrime := hQ.isPrime
  have key : ∀ i, gO i ∈ Q → (nZ (gO i)).natAbs = 2 → Q = Ideal.span {gO i} := by
    intro i hi hn
    refine eq_span_of_absNorm_eq Q _ hi ?_ (by rw [absNorm_span_gO, hn]; norm_num)
    rw [absNorm_span_gO, hn]
    have hd : Ideal.absNorm Q ∣ 2 := hn ▸ absNorm_span_gO i ▸
      Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem Q).mpr hi)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd (Ideal.absNorm_eq_one_iff.mp h1) hQ.ne_top
    · exact h1
  rw [two_eq] at h2
  have he := unit_not_mem hQ.ne_top (eO_mul_eIO 0 (by norm_num))
  rcases hP.mem_or_mem h2 with h | h
  · rcases hP.mem_or_mem h with h | h
    · rcases hP.mem_or_mem h with h | h
      · exact absurd h he
      · exact Or.inl (key 12 (hP.mem_of_pow_mem 3 h) natAbs_nZ_la)
    · exact Or.inr (Or.inl (key 13 (hP.mem_of_pow_mem 12 h) natAbs_nZ_lb))
  · exact Or.inr (Or.inr (key 14 (hP.mem_of_pow_mem 6 h) natAbs_nZ_lc))

/-- In a finite field with 7 or 49 elements, `x ^ 49 = x`. -/
theorem pow_49_of_card (Q : Ideal (𝓞 K21)) [hQ : Q.IsMaximal]
    (hc : Ideal.absNorm Q = 7 ∨ Ideal.absNorm Q = 49) (x : 𝓞 K21 ⧸ Q) : x ^ 49 = x := by
  letI := Ideal.Quotient.field Q
  have hcard : Nat.card (𝓞 K21 ⧸ Q) = Ideal.absNorm Q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 K21 ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  letI := Fintype.ofFinite (𝓞 K21 ⧸ Q)
  have hq : ∀ y : 𝓞 K21 ⧸ Q, y ^ Nat.card (𝓞 K21 ⧸ Q) = y := by
    intro y
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card y
  rw [hcard] at hq
  rcases hc with h | h
  · rw [h] at hq
    rw [show 49 = 7 * 7 by norm_num, pow_mul, hq, hq]
  · rw [h] at hq; exact hq x

/-- A maximal ideal containing `7` is `(pi7)`: its norm divides `343`, and residue degree `1` or
`2` would give `θ ^ 49 = θ` modulo it, against `(θ ^ 49 - θ) u = 1 + 7 v`. -/
theorem eq_of_seven_mem (Q : Ideal (𝓞 K21)) [hQ : Q.IsMaximal] (h7 : (7 : 𝓞 K21) ∈ Q) :
    Q = Ideal.span {gO 15} := by
  have hP : Q.IsPrime := hQ.isPrime
  have hpi : gO 15 ∈ Q := by
    have h := h7
    rw [seven_eq] at h
    rcases hP.mem_or_mem h with h | h
    · exact absurd h (unit_not_mem hQ.ne_top (eO_mul_eIO 3 (by norm_num)))
    · exact hP.mem_of_pow_mem 7 h
  have hd : Ideal.absNorm Q ∣ 7 ^ 3 := by
    have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem Q).mpr hpi)
    rwa [absNorm_span_gO, natAbs_nZ_pi7] at this
  obtain ⟨m, hm, hQm⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hd
  have hn3 : Ideal.absNorm Q = 343 := by
    interval_cases m
    · exact absurd (Ideal.absNorm_eq_one_iff.mp (by simpa using hQm)) hQ.ne_top
    all_goals first
      | (norm_num at hQm; exact hQm)
      | exfalso
        have h49 := pow_49_of_card Q (by norm_num at hQm; omega) (Ideal.Quotient.mk Q θO)
        have hmem : θO ^ 49 - θO ∈ Q := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h49, sub_self]
        have h1 : (1 : 𝓞 K21) + 7 * zkO v7L ∈ Q := residue_seven ▸ Q.mul_mem_right _ hmem
        have h2 : (1 : 𝓞 K21) ∈ Q := by
          have := Q.sub_mem h1 (Q.mul_mem_right (zkO v7L) h7)
          simpa using this
        exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h2)
  exact eq_span_of_absNorm_eq Q _ hpi (by rw [hn3, absNorm_span_gO, natAbs_nZ_pi7])
    (by rw [absNorm_span_gO, natAbs_nZ_pi7]; norm_num)

/-! ## The primes containing `pi3` and `pi439` -/

instance fact_prime_439 : Fact (Nat.Prime 439) := ⟨by norm_num⟩

theorem hdiv3 : dividesF ((3 : ℕ) : ℤ) [1] = true := by decide +kernel
theorem hdiv439 : dividesF ((439 : ℕ) : ℤ) [314] = true := by decide +kernel

/-- The prime `(pi3)`: kernel of `𝓞 → F_3`, `θ ↦ -1`. -/
noncomputable def I3 : Ideal (𝓞 K21) := RingHom.ker (resZ 3 1 hdiv3 avUB3 avUB3_ok)

/-- The prime `(pi439)`: kernel of `𝓞 → F_439`, `θ ↦ -314`. -/
noncomputable def I439 : Ideal (𝓞 K21) := RingHom.ker (resZ 439 314 hdiv439 avUB439 avUB439_ok)

theorem three_eq : gO 16 * cO 4 = 3 := by
  have := gO_mul_cO 4 (by norm_num)
  simpa [primeIdx, primeOf] using this

theorem four39_eq : gO 17 * cO 5 = 439 := by
  have := gO_mul_cO 5 (by norm_num)
  simpa [primeIdx, primeOf] using this

theorem eq_I3 (Q : Ideal (𝓞 K21)) [Q.IsMaximal] (hg : gO 16 ∈ Q) : Q = I3 := by
  have h3 : (((3 : ℕ) : ℤ) : 𝓞 K21) ∈ Q := by
    have := Q.mul_mem_right (cO 4) hg
    rw [three_eq] at this
    exact_mod_cast this
  obtain ⟨c, hdiv, hc, hQ⟩ := eq_ker_of_mem 3 avFac3 avInv3 avIdx3 avUD3 avUB3 (gensL.getD 16 [])
    avOK3 avUB3_ok avUD3_ok (by decide) Q h3 hg
  have hc1 : avFac3.getD avIdx3 [] = [1] := by decide
  rw [hc1, List.cons.injEq] at hc
  obtain ⟨rfl, -⟩ := hc
  exact hQ

theorem eq_I439 (Q : Ideal (𝓞 K21)) [Q.IsMaximal] (hg : gO 17 ∈ Q) : Q = I439 := by
  have h3 : (((439 : ℕ) : ℤ) : 𝓞 K21) ∈ Q := by
    have := Q.mul_mem_right (cO 5) hg
    rw [four39_eq] at this
    exact_mod_cast this
  obtain ⟨c, hdiv, hc, hQ⟩ := eq_ker_of_mem 439 avFac439 avInv439 avIdx439 avUD439 avUB439
    (gensL.getD 17 []) avOK439 avUB439_ok avUD439_ok (by decide) Q h3 hg
  have hc1 : avFac439.getD avIdx439 [] = [314] := by decide
  rw [hc1, List.cons.injEq] at hc
  obtain ⟨rfl, -⟩ := hc
  exact hQ

/-! ## The set `S` -/

/-- The set of primes of the descent: those containing `2`, `7`, `pi3` or `pi439`. -/
def S : Set (HeightOneSpectrum (𝓞 K21)) :=
  {v | (2 : 𝓞 K21) ∈ v.asIdeal ∨ (7 : 𝓞 K21) ∈ v.asIdeal ∨ gO 16 ∈ v.asIdeal ∨
    gO 17 ∈ v.asIdeal}

/-- The six ideals. -/
noncomputable def sixIdeals : Set (Ideal (𝓞 K21)) :=
  {Ideal.span {gO 12}, Ideal.span {gO 13}, Ideal.span {gO 14}, Ideal.span {gO 15}, I3, I439}

theorem asIdeal_mem_sixIdeals (v : HeightOneSpectrum (𝓞 K21)) (hv : v ∈ S) :
    v.asIdeal ∈ sixIdeals := by
  rcases hv with h | h | h | h
  · rcases eq_of_two_mem v.asIdeal h with e | e | e <;> simp [sixIdeals, e]
  · simp [sixIdeals, eq_of_seven_mem v.asIdeal h]
  · simp [sixIdeals, eq_I3 v.asIdeal h]
  · simp [sixIdeals, eq_I439 v.asIdeal h]

theorem ncard_six {α : Type*} (a b c d e f : α) : ({a, b, c, d, e, f} : Set α).ncard ≤ 6 := by
  classical
  have : ({a, b, c, d, e, f} : Set α) = ↑({a, b, c, d, e, f} : Finset α) := by simp
  rw [this, Set.ncard_coe_finset]
  exact Finset.card_le_six

theorem sixIdeals_finite : sixIdeals.Finite := by
  simp only [sixIdeals]
  exact Set.toFinite _

theorem S_finite : S.Finite :=
  (sixIdeals_finite.preimage HeightOneSpectrum.asIdeal_injective.injOn).subset
    fun v hv => asIdeal_mem_sixIdeals v hv

theorem S_ncard : S.ncard ≤ 6 :=
  (Set.ncard_le_ncard_of_injOn HeightOneSpectrum.asIdeal asIdeal_mem_sixIdeals
    HeightOneSpectrum.asIdeal_injective.injOn sixIdeals_finite).trans (ncard_six _ _ _ _ _ _)

/-- Outside `S`, the eighteen generators are units. -/
theorem gO_not_mem (v : HeightOneSpectrum (𝓞 K21)) (hv : v ∉ S) (i : ℕ) (hi : i < 18) :
    gO i ∉ v.asIdeal := by
  simp only [S, Set.mem_ofPred_eq, not_or] at hv
  obtain ⟨h2, h7, h3, h439⟩ := hv
  have hdiv : ∀ j (hj : j < 6), gO (primeIdx.getD j 0) ∈ v.asIdeal →
      ((primeOf.getD j 0 : ℤ) : 𝓞 K21) ∈ v.asIdeal := fun j hj h =>
    gO_mul_cO j hj ▸ v.asIdeal.mul_mem_right _ h
  intro hg
  by_cases h12 : i < 12
  · exact unit_not_mem v.isMaximal.ne_top (gO_mul_gIO i h12) hg
  · interval_cases i
    · exact h2 (by simpa [primeIdx, primeOf] using hdiv 0 (by norm_num) hg)
    · exact h2 (by simpa [primeIdx, primeOf] using hdiv 1 (by norm_num) hg)
    · exact h2 (by simpa [primeIdx, primeOf] using hdiv 2 (by norm_num) hg)
    · exact h7 (by simpa [primeIdx, primeOf] using hdiv 3 (by norm_num) hg)
    · exact h3 hg
    · exact h439 hg

end FurioLombardo.M1
