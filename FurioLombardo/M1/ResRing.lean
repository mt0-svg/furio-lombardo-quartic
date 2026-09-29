import FurioLombardo.M1.Residue

/-!
# Residue rings `F_p[x]/(φ)` and computations in them

For a prime `p` and the lower coefficients `gl` of a monic integer polynomial
`φ = X ^ n + gl`, `RR p gl = AdjoinRoot (φ mod p)` with root `rr`. Elements are computed by the
kernel as integer lists (`modL`, `mulM`, `powF`): `evalL rr` turns each list operation into the
ring operation (`evalL_mulM`, `evalL_powF`), and `allDvdL p` checks equalities.

* `RR_pow_eq_self`: if `rr ^ (p ^ d) = rr` then `y ^ (p ^ d) = y` for every `y` (the iterated
  Frobenius is an algebra endomorphism fixing the root). No irreducibility of `φ` is used.
* `char_mul_eq`: in such a ring, if `w g = z ^ 2` and `w ^ ((q - 1) / 2)`, `g ^ ((q - 1) / 2)`
  are `±1`, their product is `1` (Euler's criterion, the direction used by the sieve).
* `resRR`: the residue homomorphism `𝓞 K21 → RR p gl` when `φ` divides `f` modulo `p` and `p`
  does not divide `DB`, and its values on `zkO a`.
-/

namespace FurioLombardo.M1

open Polynomial NumberField Kron

/-! ## List computations modulo `p` and a monic polynomial -/

/-- Reduce every coefficient modulo `p`. -/
def modL (p : ℤ) (l : List ℤ) : List ℤ := l.map (· % p)

/-- Product modulo `p` and `X ^ n + gl`. -/
def mulM (p : ℤ) (gl a b : List ℤ) : List ℤ := modL p (redL gl (mulL a b))

/-- Power by repeated squaring, with fuel (enough when `k < 2 ^ fuel`). -/
def powF (p : ℤ) (gl : List ℤ) : ℕ → List ℤ → ℕ → List ℤ
  | 0, _, _ => [1]
  | fuel + 1, a, k =>
    if k = 0 then [1] else
      let h := powF p gl fuel (mulM p gl a a) (k / 2)
      if k % 2 = 1 then mulM p gl a h else h

/-- `l ≡ m` modulo `p` coefficientwise. -/
def eqM (p : ℤ) (l m : List ℤ) : Bool := allDvdL p (subL l m)

section Generic

variable {R : Type*} [CommRing R] (p : ℤ) (hp : (p : R) = 0)

include hp in
theorem intCast_emod (a : ℤ) : ((a % p : ℤ) : R) = (a : R) := by
  rw [Int.emod_def]; push_cast; rw [hp]; ring

include hp in
theorem evalL_modL (t : R) : ∀ l : List ℤ, evalL t (modL p l) = evalL t l
  | [] => rfl
  | a :: l => by
    simp only [modL, List.map_cons, evalL_cons] at *
    rw [intCast_emod p hp a, ← evalL_modL t l]; rfl

include hp in
theorem evalL_eq_zero_of_allDvdL (t : R) : ∀ l : List ℤ, allDvdL p l = true → evalL t l = 0
  | [] => fun _ => rfl
  | a :: l => by
    intro h
    simp only [allDvdL, Bool.and_eq_true, beq_iff_eq] at h
    rw [evalL_cons, evalL_eq_zero_of_allDvdL t l h.2]
    have : (a : R) = ((a % p : ℤ) : R) := (intCast_emod p hp a).symm
    rw [this, h.1]; simp

include hp in
theorem evalL_eq_of_eqM (t : R) (l m : List ℤ) (h : eqM p l m = true) :
    evalL t l = evalL t m := by
  have := evalL_eq_zero_of_allDvdL p hp t _ h
  rw [evalL_subL, sub_eq_zero] at this
  exact this

variable (gl : List ℤ) (t : R) (ht : t ^ gl.length + evalL t gl = 0)

include hp ht in
theorem evalL_mulM (a b : List ℤ) : evalL t (mulM p gl a b) = evalL t a * evalL t b := by
  rw [mulM, evalL_modL p hp, evalL_redL t gl ht, evalL_mulL]

include hp ht in
theorem evalL_powF : ∀ (fuel : ℕ) (a : List ℤ) (k : ℕ), k < 2 ^ fuel →
    evalL t (powF p gl fuel a k) = evalL t a ^ k
  | 0, a, k, hk => by
    have : k = 0 := by simpa using hk
    subst this; simp [powF]
  | fuel + 1, a, k, hk => by
    unfold powF
    by_cases h0 : k = 0
    · subst h0; simp
    rw [if_neg h0]
    have hk2 : k / 2 < 2 ^ fuel := by
      rw [pow_succ] at hk; omega
    have ih := evalL_powF fuel (mulM p gl a a) (k / 2) hk2
    rw [evalL_mulM p hp gl t ht] at ih
    have hdiv := Nat.div_add_mod k 2
    split_ifs with h1
    · rw [evalL_mulM p hp gl t ht, ih, ← pow_two, ← pow_mul]
      conv_rhs => rw [← hdiv, h1]
      ring
    · have h1' : k % 2 = 0 := by omega
      rw [ih, ← pow_two, ← pow_mul]
      conv_rhs => rw [← hdiv, h1']
      ring

end Generic

/-! ## The rings `RR p gl` -/

section Rings

variable (p : ℕ) [hp : Fact p.Prime] (gl : List ℤ)

theorem degree_ofListL_lt (l : List ℤ) : (ofListL l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [KE.coeff_ofListL]
  exact KE.getD_eq_zero_of_length_le l m hm

/-- The monic polynomial `X ^ n + gl` modulo `p`. -/
noncomputable def phiP : (ZMod p)[X] :=
  X ^ gl.length + (ofListL gl).map (Int.castRingHom (ZMod p))

theorem phiP_monic : (phiP p gl).Monic := by
  refine monic_X_pow_add ?_
  exact (degree_map_le (p := ofListL gl) (f := Int.castRingHom (ZMod p))).trans_lt
    (degree_ofListL_lt gl)

theorem natDegree_phiP : (phiP p gl).natDegree = gl.length := by
  rw [phiP, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact (degree_map_le (p := ofListL gl) (f := Int.castRingHom (ZMod p))).trans_lt
    (degree_ofListL_lt gl)

/-- The residue ring `F_p[x]/(X ^ n + gl)`. -/
abbrev RR := AdjoinRoot (phiP p gl)

/-- The root of `X ^ n + gl` in `RR p gl`. -/
noncomputable def rr : RR p gl := AdjoinRoot.root _

theorem rr_root : rr p gl ^ gl.length + evalL (rr p gl) gl = 0 := by
  have h := AdjoinRoot.eval₂_root (phiP p gl)
  have e : ∀ q : (ZMod p)[X],
      (AdjoinRoot.of q).comp (Int.castRingHom (ZMod p)) = Int.castRingHom (AdjoinRoot q) :=
    fun q => RingHom.ext_int _ _
  rw [phiP, eval₂_add, eval₂_X_pow, eval₂_map, e, evalL_ofListL] at h
  exact h

theorem RR_p_eq_zero : ((p : ℤ) : RR p gl) = 0 := by
  rw [← map_intCast (algebraMap (ZMod p) (RR p gl)), Int.cast_natCast, ZMod.natCast_self,
    map_zero]

theorem RR_nontrivial (hgl : gl ≠ []) : Nontrivial (RR p gl) := by
  refine AdjoinRoot.nontrivial (R := ZMod p) (f := phiP p gl) ?_
  rw [degree_eq_natDegree (phiP_monic p gl).ne_zero, natDegree_phiP]
  simp [hgl]

/-- **Frobenius**: if `rr ^ (p ^ d) = rr` then every element is fixed by `y ↦ y ^ (p ^ d)`. -/
theorem RR_pow_eq_self (hgl : gl ≠ []) (d : ℕ) (h : rr p gl ^ (p ^ d) = rr p gl)
    (y : RR p gl) : y ^ (p ^ d) = y := by
  have := RR_nontrivial p gl hgl
  have : CharP (RR p gl) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (RR p gl)).injective p
  have : ExpChar (RR p gl) p := ExpChar.prime hp.out
  let φ : RR p gl →ₐ[ZMod p] RR p gl :=
    { iterateFrobenius (RR p gl) p d with
      commutes' := fun c => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, iterateFrobenius_def]
        rw [← map_pow, ZMod.pow_card_pow] }
  have hφ : φ = AlgHom.id (ZMod p) (RR p gl) := by
    apply AdjoinRoot.algHom_ext
    show (AdjoinRoot.root (phiP p gl)) ^ (p ^ d) = AdjoinRoot.root (phiP p gl)
    exact h
  have := congrArg (fun ψ : RR p gl →ₐ[ZMod p] RR p gl => ψ y) hφ
  simpa [φ, iterateFrobenius_def] using this

end Rings

/-! ## Euler's criterion, the direction used -/

theorem isUnit_of_pow_eq_sign {R : Type*} [CommRing R] (w : R) (k : ℕ) (hk : 0 < k) (s : R)
    (hs : s = 1 ∨ s = -1) (h : w ^ k = s) : IsUnit w := by
  have hs' : IsUnit s := by rcases hs with rfl | rfl <;> simp
  rw [← h] at hs'
  exact (isUnit_pow_iff hk.ne').mp hs'

/-- In a ring where `y ^ q = y` for all `y` (`q` odd), if `w g = z ^ 2` and
`w ^ ((q - 1) / 2) = sw`, `g ^ ((q - 1) / 2) = sg` with `sw, sg = ±1`, then `sw * sg = 1`. -/
theorem char_mul_eq {R : Type*} [CommRing R] (q : ℕ) (hq : ∀ y : R, y ^ q = y) (hq3 : 3 ≤ q)
    (hodd : q % 2 = 1) (w g z : R) (hz : w * g = z ^ 2) (sw sg : R) (hsw : sw = 1 ∨ sw = -1)
    (hsg : sg = 1 ∨ sg = -1) (hw : w ^ ((q - 1) / 2) = sw) (hg : g ^ ((q - 1) / 2) = sg) :
    sw * sg = 1 := by
  have hk : 0 < (q - 1) / 2 := by omega
  have hwu := isUnit_of_pow_eq_sign w _ hk sw hsw hw
  have hgu := isUnit_of_pow_eq_sign g _ hk sg hsg hg
  have hzu : IsUnit z := by
    have : IsUnit (z ^ 2) := hz ▸ hwu.mul hgu
    exact (isUnit_pow_iff two_ne_zero).mp this
  have hz1 : z ^ (q - 1) = 1 := by
    have h1 := hq z
    have : z ^ (q - 1) * z = 1 * z := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, h1]
    exact hzu.mul_right_cancel this
  calc sw * sg = (w * g) ^ ((q - 1) / 2) := by rw [mul_pow, hw, hg]
    _ = z ^ (q - 1) := by
      rw [hz, ← pow_mul]; congr 1; omega
    _ = 1 := hz1

/-! ## Residue homomorphisms into `RR p gl` -/

section Res

variable (p : ℕ) [Fact p.Prime] (gl : List ℤ)

/-- `f ≡ 0` modulo `p` and `X ^ n + gl`, i.e. the factor divides `f` modulo `p`. -/
def dividesF (p : ℤ) (gl : List ℤ) : Bool := allDvdL p (redL gl fL)

theorem evalL_rr_fL (h : dividesF p gl = true) : evalL (rr p gl) fL = 0 := by
  rw [← evalL_redL (rr p gl) gl (rr_root p gl)]
  exact evalL_eq_zero_of_allDvdL (p : ℤ) (RR_p_eq_zero p gl) _ _ h

/-- The residue homomorphism `𝓞 K21 → RR p gl` (`θ ↦ rr`), for `uB * DB ≡ 1 (mod p)`. -/
noncomputable def resRR (h : dividesF p gl = true) (uB : ℤ) (huB : (uB * DB - 1) % p = 0) :
    𝓞 K21 →+* RR p gl :=
  resHom (rr p gl) (by rw [← ofListL_fL, aeval_ofListL]; exact evalL_rr_fL p gl h) (uB : RR p gl) (by
    have h1 : (((uB * DB - 1) % p : ℤ) : RR p gl) = 0 := by rw [huB]; simp
    rw [intCast_emod (p : ℤ) (RR_p_eq_zero p gl)] at h1
    push_cast at h1
    exact sub_eq_zero.mp h1)

theorem resRR_θO (h : dividesF p gl = true) (uB : ℤ) (huB : (uB * DB - 1) % p = 0) :
    resRR p gl h uB huB θO = rr p gl := resHom_θO _ _ _ _

end Res

/-! ## Values on the lattice `zkO a` -/

theorem map_evalL {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : R) :
    ∀ l : List ℤ, φ (evalL t l) = evalL (φ t) l
  | [] => by simp
  | a :: l => by simp [map_evalL φ t l]

/-- `Dz · zkO a = (combo a zkNum)(θ)` in `𝓞 K21`. -/
theorem Dz_mul_zkO (a : List ℤ) :
    ((Dz : ℤ) : 𝓞 K21) * zkO a = evalL θO (combo a zkNum) := by
  apply RingOfIntegers.coe_injective
  rw [map_mul, map_intCast, map_evalL]
  show ((Dz : ℤ) : K21) * zkE a = evalL θ (combo a zkNum)
  simp only [zkE, evK, KE.ev]
  rw [← mul_assoc]
  have : ((Dz : ℤ) : K21) * dInv = 1 := by
    rw [mul_comm]; exact_mod_cast dInv_mul
  rw [this, one_mul]

/-- The value of a ring homomorphism on `zkO a`, from its value on `θ` and an inverse of `Dz`. -/
theorem hom_zkO {R : Type*} [CommRing R] (ψ : 𝓞 K21 →+* R) (uD : R)
    (huD : uD * ((Dz : ℤ) : R) = 1) (a : List ℤ) :
    ψ (zkO a) = uD * evalL (ψ θO) (combo a zkNum) := by
  have := congrArg ψ (Dz_mul_zkO a)
  rw [map_mul, map_intCast, map_evalL] at this
  rw [← this, ← mul_assoc, huD, one_mul]

end FurioLombardo.M1
