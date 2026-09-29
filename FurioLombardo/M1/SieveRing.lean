import FurioLombardo.M1.ResRing
import FurioLombardo.M1.Descent

/-!
# One ring of the sieve

A certificate for a ring `RR p gl = F_p[x]/(phi)` (`ringOK`): `phi` divides `f` modulo `p`, the
root is fixed by `y ↦ y ^ q` (`q = p ^ deg phi`), the residues of the eighteen generators and of the
coefficients of `Q1`, `Q3` are the given lists, and each generator has character `±1` (bit `b_i`).

`ring_parity`: if `w · G_e = s²` in `𝓞 K21` (`G_e` the product of the generators selected by `e`)
and `ρ(w) ^ ((q - 1) / 2) = (-1) ^ β`, then `β + Σ_i e_i b_i` is even.

`ring_point`: at a primitive integer point `a` congruent modulo `p` to `λ P` (`λ ≠ 0`), the character
of `ρ(Q_(i+1)(a))` is the one of the list value of `Q_(i+1)` at `P` (the factor `λ ^ 2` has trivial
character).
-/

namespace FurioLombardo.M1

open Polynomial NumberField Kron Vendor.NetOfConics

/-- The product of the generators selected by `e`. -/
noncomputable def gProd (e : Fin 18 → Bool) : 𝓞 K21 := subprod (fun i => gO i) e

/-- The sign `(-1) ^ b`. -/
def sgnR {R : Type*} [CommRing R] (b : Bool) : R := if b then -1 else 1

/-- The sign as a list. -/
def sgnL (b : Bool) : List ℤ := if b then [-1] else [1]

theorem evalL_sgnL {R : Type*} [CommRing R] (t : R) (b : Bool) : evalL t (sgnL b) = sgnR b := by
  cases b <;> simp [sgnL, sgnR]

theorem sgnR_eq_pow {R : Type*} [CommRing R] (b : Bool) : (sgnR b : R) = (-1) ^ b.toNat := by
  cases b <;> simp [sgnR]

/-- The value of a conic with list coefficients at an integer point, reduced modulo `p`. -/
def qevL (p : ℤ) (c : List (List ℤ)) (P : List ℤ) : List ℤ :=
  modL p (addL (smulL (P.getD 0 0 * P.getD 0 0) (c.getD 0 []))
    (addL (smulL (P.getD 0 0 * P.getD 1 0) (c.getD 1 []))
    (addL (smulL (P.getD 0 0 * P.getD 2 0) (c.getD 2 []))
    (addL (smulL (P.getD 1 0 * P.getD 1 0) (c.getD 3 []))
    (addL (smulL (P.getD 1 0 * P.getD 2 0) (c.getD 4 [])) (smulL (P.getD 2 0 * P.getD 2 0) (c.getD 5 [])))))))

theorem evalL_qevL {R : Type*} [CommRing R] (p : ℤ) (hp : (p : R) = 0) (t : R) (c : List (List ℤ))
    (P : List ℤ) :
    evalL t (qevL p c P) =
      qev (fun m : Fin 6 => evalL t (c.getD m [])) (fun j : Fin 3 => ((P.getD j 0 : ℤ) : R)) := by
  simp only [qevL, evalL_modL p hp, evalL_addL, evalL_smulL, qev]
  push_cast
  simp
  ring

theorem qev_smul {R : Type*} [CommRing R] (c : Fin 6 → R) (l : R) (P : Fin 3 → R) :
    qev c (fun j => l * P j) = l ^ 2 * qev c P := by
  simp only [qev]; ring

/-- `w = t y²` in the ring, with `t = n` if `β` and `t = 1` otherwise, and `y z = 1`. -/
def sqOK (p : ℕ) (gl n w : List ℤ) (β : Bool) (y z : List ℤ) : Bool :=
  eqM p (mulM p gl (if β then n else [1]) (mulM p gl y y)) w && eqM p (mulM p gl y z) [1]

/-- The certificate of one ring. -/
def ringOK (p : ℕ) (gl : List ℤ) (uB uD : ℤ) (gen : List (List ℤ)) (bits : List Bool)
    (qd : List (List (List ℤ))) (n : List ℤ) (gy gz : List (List ℤ)) : Bool :=
  !gl.isEmpty && dividesF p gl && ((uB * DB - 1) % (p : ℤ) == 0) &&
  ((uD * (Dz : ℤ) - 1) % (p : ℤ) == 0) && decide (p ^ gl.length < 2 ^ 40) && decide (5 ≤ p) &&
  (p % 2 == 1) && eqM p (powF p gl 40 [0, 1] (p ^ gl.length)) (redL gl [0, 1]) &&
  eqM p (powF p gl 40 n ((p ^ gl.length - 1) / 2)) [-1] &&
  (List.range 18).all (fun i => eqM p (resL p gl uD (gensL.getD i [])) (gen.getD i []) &&
    sqOK p gl n (gen.getD i []) (bits.getD i false) (gy.getD i []) (gz.getD i [])) &&
  ([0, 2] : List ℕ).all (fun i => (List.range 6).all fun m =>
    eqM p (resL p gl uD (qcA i m)) ((qd.getD i []).getD m []))

section Ring

variable {p : ℕ} [hp : Fact p.Prime] {gl : List ℤ} {uB uD : ℤ} {gen : List (List ℤ)}
  {bits : List Bool} {qd : List (List (List ℤ))} {n : List ℤ} {gy gz : List (List ℤ)}

structure RingFacts (p : ℕ) [Fact p.Prime] (gl : List ℤ) (uB uD : ℤ) (gen : List (List ℤ))
    (bits : List Bool) (qd : List (List (List ℤ))) (n : List ℤ) (gy gz : List (List ℤ)) : Prop where
  hgl : gl ≠ []
  hdiv : dividesF p gl = true
  huB : (uB * DB - 1) % (p : ℤ) = 0
  huD : (uD * (Dz : ℤ) - 1) % (p : ℤ) = 0
  hq40 : p ^ gl.length < 2 ^ 40
  hp5 : 5 ≤ p
  hodd : p % 2 = 1
  hfrob : eqM p (powF p gl 40 [0, 1] (p ^ gl.length)) (redL gl [0, 1]) = true
  hn : eqM p (powF p gl 40 n ((p ^ gl.length - 1) / 2)) [-1] = true
  hgen : ∀ i < 18, eqM p (resL p gl uD (gensL.getD i [])) (gen.getD i []) = true
  hgsq : ∀ i < 18,
    sqOK p gl n (gen.getD i []) (bits.getD i false) (gy.getD i []) (gz.getD i []) = true
  hq : ∀ i ∈ ([0, 2] : List ℕ), ∀ m < 6,
    eqM p (resL p gl uD (qcA i m)) ((qd.getD i []).getD m []) = true

theorem RingFacts.of_ok (h : ringOK p gl uB uD gen bits qd n gy gz = true) :
    RingFacts p gl uB uD gen bits qd n gy gz := by
  simp only [ringOK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h8n⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h8n, fun i hi => (h9 i hi).1, fun i hi => (h9 i hi).2,
    fun i hi m hm => h10 i hi m hm⟩

variable (F : RingFacts p gl uB uD gen bits qd n gy gz)
include F

/-- The residue map of the ring. -/
noncomputable def RingFacts.ρ : 𝓞 K21 →+* RR p gl := resRR p gl F.hdiv uB F.huB

theorem RingFacts.q_pos : 0 < p ^ gl.length := pow_pos hp.out.pos _

theorem RingFacts.pow_q (y : RR p gl) : y ^ (p ^ gl.length) = y := by
  apply RR_pow_eq_self p gl F.hgl
  have h := evalL_eq_of_eqM (p : ℤ) (RR_p_eq_zero p gl) (rr p gl) _ _ F.hfrob
  rw [evalL_powF (p : ℤ) (RR_p_eq_zero p gl) gl (rr p gl) (rr_root p gl) 40 _ _ F.hq40, evalL_redL _ gl (rr_root p gl)] at h
  simpa using h

theorem RingFacts.nontrivial : Nontrivial (RR p gl) := RR_nontrivial p gl F.hgl

theorem RingFacts.neg_one_ne_one : (-1 : RR p gl) ≠ 1 := by
  haveI := F.nontrivial
  intro h
  have h2 : ((2 : ZMod p) : ZMod p) = 0 := by
    have : algebraMap (ZMod p) (RR p gl) 2 = 0 := by
      rw [map_ofNat]
      linear_combination -h
    exact (map_eq_zero_iff _ (algebraMap (ZMod p) (RR p gl)).injective).mp this
  have : (p : ℕ) ∣ 2 := by
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    exact this
  have := Nat.le_of_dvd (by norm_num) this
  have := F.hp5
  omega

theorem RingFacts.ρ_eval (a : List ℤ) (l : List ℤ) (h : eqM p (resL p gl uD a) l = true) :
    F.ρ (zkO a) = evalL (rr p gl) l := by
  rw [RingFacts.ρ, ← evalL_resL p gl F.hdiv uB F.huB uD F.huD a]
  exact evalL_eq_of_eqM (p : ℤ) (RR_p_eq_zero p gl) (rr p gl) _ _ h

theorem RingFacts.pow_h_eq (l : List ℤ) (β : Bool)
    (h : eqM p (powF p gl 40 l ((p ^ gl.length - 1) / 2)) (sgnL β) = true) :
    evalL (rr p gl) l ^ ((p ^ gl.length - 1) / 2) = sgnR β := by
  have h1 := evalL_eq_of_eqM (p : ℤ) (RR_p_eq_zero p gl) (rr p gl) _ _ h
  rw [evalL_powF (p : ℤ) (RR_p_eq_zero p gl) gl (rr p gl) (rr_root p gl) 40 _ _
    (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_le_of_lt (Nat.sub_le _ _) F.hq40)),
    evalL_sgnL] at h1
  exact h1

/-- **Character from a square root certificate.** -/
theorem RingFacts.char_of_sq (w : List ℤ) (β : Bool) (y z : List ℤ)
    (h : sqOK p gl n w β y z = true) :
    evalL (rr p gl) w ^ ((p ^ gl.length - 1) / 2) = sgnR β := by
  simp only [sqOK, Bool.and_eq_true] at h
  have hpR := RR_p_eq_zero p gl
  have h1 := evalL_eq_of_eqM (p : ℤ) hpR (rr p gl) _ _ h.1
  have h2 := evalL_eq_of_eqM (p : ℤ) hpR (rr p gl) _ _ h.2
  rw [evalL_mulM (p : ℤ) hpR gl (rr p gl) (rr_root p gl),
    evalL_mulM (p : ℤ) hpR gl (rr p gl) (rr_root p gl)] at h1
  rw [evalL_mulM (p : ℤ) hpR gl (rr p gl) (rr_root p gl)] at h2
  set Y := evalL (rr p gl) y
  have h2' : Y * evalL (rr p gl) z = 1 := by simpa using h2
  have hu : IsUnit Y := IsUnit.of_mul_eq_one _ h2'
  have hY : Y ^ (p ^ gl.length - 1) = 1 := by
    have e1 : Y ^ (p ^ gl.length - 1) * Y = 1 * Y := by
      rw [<- pow_succ, Nat.sub_add_cancel F.q_pos, one_mul, F.pow_q Y]
    exact hu.mul_right_cancel e1
  have hodd : p ^ gl.length % 2 = 1 := by rw [Nat.pow_mod, F.hodd, one_pow]; rfl
  rw [<- h1, mul_pow, <- sq, <- pow_mul,
    show 2 * ((p ^ gl.length - 1) / 2) = p ^ gl.length - 1 by omega, hY, mul_one]
  cases β
  · simp [sgnR]
  · have := F.pow_h_eq n true F.hn
    simpa using this

theorem RingFacts.gen_pow (i : ℕ) (hi : i < 18) :
    F.ρ (gO i) ^ ((p ^ gl.length - 1) / 2) = sgnR (bits.getD i false) := by
  rw [show gO i = zkO (gensL.getD i []) from rfl, F.ρ_eval _ _ (F.hgen i hi)]
  exact F.char_of_sq _ _ _ _ (F.hgsq i hi)

theorem RingFacts.gProd_pow (e : Fin 18 → Bool) :
    F.ρ (gProd e) ^ ((p ^ gl.length - 1) / 2) =
      (-1) ^ (∑ i : Fin 18, if e i && bits.getD i false then 1 else 0) := by
  rw [gProd, subprod, map_prod, ← Finset.prod_pow, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases he : e i
  · simp
  · simp only [if_true, F.gen_pow i i.isLt, sgnR_eq_pow, Bool.true_and]
    cases bits.getD (↑i) false <;> simp

/-- **Parity at one ring**. -/
theorem RingFacts.parity (e : Fin 18 → Bool) (w s : 𝓞 K21) (hws : w * gProd e = s ^ 2)
    (β : Bool) (hβ : F.ρ w ^ ((p ^ gl.length - 1) / 2) = sgnR β) :
    Even (β.toNat + ∑ i : Fin 18, if e i && bits.getD i false then 1 else 0) := by
  have hq3 : 3 ≤ p ^ gl.length := by
    have := F.hp5
    calc 3 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ gl.length := Nat.pow_le_pow_right (by omega)
          (List.length_pos_iff_ne_nil.mpr F.hgl)
  have hodd : p ^ gl.length % 2 = 1 := by
    rw [Nat.pow_mod, F.hodd, one_pow]; rfl
  have h := char_mul_eq (p ^ gl.length) F.pow_q hq3 hodd (F.ρ w) (F.ρ (gProd e)) (F.ρ s)
    (by rw [← map_mul, hws, map_pow]) (sgnR β) _
    (by cases β <;> simp [sgnR]) (neg_one_pow_eq_or _ _) hβ (F.gProd_pow e)
  rw [sgnR_eq_pow, ← pow_add] at h
  exact (neg_one_pow_eq_one_iff_even F.neg_one_ne_one).mp h

theorem RingFacts.ne_zero_of_pow (w : 𝓞 K21) (β : Bool)
    (hβ : F.ρ w ^ ((p ^ gl.length - 1) / 2) = sgnR β) : w ≠ 0 := by
  haveI := F.nontrivial
  rintro rfl
  have hh : 0 < (p ^ gl.length - 1) / 2 := by
    have := F.hp5
    have : p ≤ p ^ gl.length := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ gl.length := Nat.pow_le_pow_right (by omega)
            (List.length_pos_iff_ne_nil.mpr F.hgl)
    omega
  rw [map_zero, zero_pow hh.ne'] at hβ
  cases β
  · exact zero_ne_one (α := RR p gl) (by simpa [sgnR] using hβ)
  · have : (1 : RR p gl) = 0 := by
      have h' : (0 : RR p gl) = -1 := by simpa [sgnR] using hβ
      linear_combination h'
    exact one_ne_zero this

/-- **Character at a point**: `a ≡ λ P (mod p)` with `λ ≠ 0`. -/
theorem RingFacts.point_pow (a : Fin 3 → ℤ) (P : List ℤ) (lam : ZMod p) (hlam : lam ≠ 0)
    (ha : ∀ j : Fin 3, ((a j : ℤ) : ZMod p) = lam * ((P.getD j 0 : ℤ) : ZMod p)) (i : Fin 3)
    (hi : (i : ℕ) ∈ ([0, 2] : List ℕ)) (β : Bool)
    (y z : List ℤ) (hc : sqOK p gl n (qevL p (qd.getD i []) P) β y z = true) :
    F.ρ (qO i a) ^ ((p ^ gl.length - 1) / 2) = sgnR β := by
  set Λ : RR p gl := algebraMap (ZMod p) (RR p gl) lam
  have hcoef : ∀ m : Fin 6, F.ρ (qC i m) = evalL (rr p gl) ((qd.getD i []).getD m []) :=
    fun m => F.ρ_eval _ _ (F.hq i hi m m.isLt)
  have hpt : ∀ j : Fin 3, F.ρ ((a j : ℤ) : 𝓞 K21) = Λ * ((P.getD j 0 : ℤ) : RR p gl) := by
    intro j
    rw [map_intCast]
    have e1 : ((a j : ℤ) : RR p gl) = algebraMap (ZMod p) (RR p gl) ((a j : ℤ) : ZMod p) := by
      rw [map_intCast]
    rw [e1, ha j, map_mul, map_intCast]
  have hval : F.ρ (qO i a) = Λ ^ 2 * evalL (rr p gl) (qevL p (qd.getD i []) P) := by
    rw [qO, map_qev, evalL_qevL (p : ℤ) (RR_p_eq_zero p gl)]
    simp only [hcoef, hpt]
    rw [qev_smul]
  have hΛ : Λ ^ (p ^ gl.length - 1) = 1 := by
    haveI := F.nontrivial
    have hu : IsUnit Λ := (IsUnit.mk0 lam hlam).map _
    have h1 := F.pow_q Λ
    have h2 : Λ ^ (p ^ gl.length - 1) * Λ = 1 * Λ := by
      rw [← pow_succ, Nat.sub_add_cancel F.q_pos, one_mul, h1]
    exact hu.mul_right_cancel h2
  have hodd : p ^ gl.length % 2 = 1 := by rw [Nat.pow_mod, F.hodd, one_pow]; rfl
  rw [hval, mul_pow, ← pow_mul, show 2 * ((p ^ gl.length - 1) / 2) = p ^ gl.length - 1 by omega,
    hΛ, one_mul]
  exact F.char_of_sq _ _ _ _ hc

end Ring

end FurioLombardo.M1
