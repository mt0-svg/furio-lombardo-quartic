import FurioLombardo.Discharge.SelmerBasis.SUnitOrder
import FurioLombardo.Discharge.M3a.PolyK

/-!
# Residue characters of `OL` and `ON` at degree one primes (piece (d))

A prime `p` (odd, prime to `DB` and `Dz`) with a root `t` of `f` modulo `p` gives lane M1's
residue map `ρK : 𝓞 K21 → ZMod p`, `θ ↦ t` (`resHom`). A square root `s` of `ρK ε` extends it to
`ρL : OL → ZMod p` (`ω ↦ s`), and a square root `t2` of `ρL EO` to `ρN : ON → ZMod p`
(`ω' ↦ t2`). Every hypothesis is a Boolean check on natural numbers (`goodK`, `goodL`, `goodN`)
for `decide +kernel`: residues are computed as `Dz⁻¹ Σ a_i z_i mod p` from the residues `z_i` of
the 21 numerators of the integral basis (`rzk`), powers with `Nat.pow` (GMP in the kernel).

`ρL`, `ρN` send squares of `L42`, `N84` lying in the order to squares (`isSquare_ρL`,
`isSquare_ρN`, through `D y ∈ order`, with `ρ D ≠ 0` checked). Rows of characters of a list of
generators are checked by `rowL`, `rowN`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.SU

open NumberField QuadraticAlgebra Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3b

/-! ### Arithmetic modulo `p` -/

/-- Primality by trial division. -/
def primeB (p : ℕ) : Bool := 2 ≤ p && (List.range p).all fun m => m < 2 || p % m != 0

theorem prime_of_primeB {p : ℕ} (h : primeB p = true) : p.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  refine Nat.prime_def_lt.mpr ⟨h.1, fun m hm hdvd => ?_⟩
  rcases h.2 m hm with h' | h'
  · interval_cases m
    · rw [zero_dvd_iff] at hdvd; omega
    · rfl
  · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h'

/-- An inverse of `n` modulo `p` (Fermat). -/
def invZ (p : ℕ) (n : ℤ) : ℕ := (n % (p : ℤ)).toNat ^ (p - 2) % p

/-- The residues of the numerators of the integral basis at `θ ↦ t`. -/
def zkRes (p t : ℕ) : List ℤ := zkNum.map fun W => evalL (t : ℤ) W % p

/-- The residue of `zkO a` at `(p, θ ↦ t)`, in `[0, p)`. -/
def rzk (p t : ℕ) (a : List ℤ) : ℕ := (((invZ p Dz : ℤ) * dot a (zkRes p t)) % (p : ℤ)).toNat

/-- `(p, t)` is a degree one prime of `K21` prime to `2 DB Dz`. -/
def goodK (p t : ℕ) : Bool :=
  primeB p && p != 2 && evalL (t : ℤ) fL % p == 0 && ((invZ p DB : ℤ) * DB) % p == 1 &&
    ((invZ p Dz : ℤ) * Dz) % p == 1

section Cast

variable {p : ℕ}

theorem intCast_eq_of_emod {a b : ℤ} (h : a % p = b % p) : (a : ZMod p) = b :=
  (ZMod.intCast_eq_intCast_iff' a b p).mpr h

theorem natCast_toNat_emod (hp : 0 < p) (n : ℤ) : (((n % p).toNat : ℕ) : ZMod p) = (n : ZMod p) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), ZMod.intCast_mod]

theorem dot_map_intCast {R : Type*} [CommRing R] :
    ∀ (a l : List ℤ), dot a (l.map (Int.cast : ℤ → R)) = ((dot a l : ℤ) : R)
  | c :: a, v :: l => by simp [dot, dot_map_intCast a l]
  | [], _ => by simp [dot]
  | _ :: _, [] => by simp [dot]

theorem natCast_ne_zero_of_mod {n : ℕ} (h : n % p ≠ 0) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun hd => h (Nat.mod_eq_zero_of_dvd hd)

theorem natCast_eq_of_mod {a b : ℕ} (h : a % p = b % p) : (a : ZMod p) = b := by
  rw [← ZMod.natCast_mod a, h, ZMod.natCast_mod]

end Cast

section K

variable {p t : ℕ} (h : goodK p t = true)
include h

theorem goodK_prime : p.Prime := by
  simp only [goodK, Bool.and_eq_true] at h; exact prime_of_primeB h.1.1.1.1

theorem goodK_ne_two : p ≠ 2 := by
  simp only [goodK, Bool.and_eq_true, bne_iff_ne] at h; exact h.1.1.1.2

theorem goodK_pos : 0 < p := (goodK_prime h).pos

theorem goodK_root : aeval (t : ZMod p) fZ = 0 := by
  apply aeval_fZ_of_evalL
  simp only [goodK, Bool.and_eq_true, beq_iff_eq] at h
  have e := map_evalL (Int.castRingHom (ZMod p)) (t : ℤ) fL
  simp only [eq_intCast, Int.cast_natCast] at e
  rw [← e, intCast_eq_of_emod (b := 0) (by rw [h.1.1.2]; simp), Int.cast_zero]

theorem goodK_DB : ((invZ p DB : ℕ) : ZMod p) * (DB : ZMod p) = 1 := by
  simp only [goodK, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : ((1 : ℤ) % p) = 1 := Int.emod_eq_of_lt (by norm_num) (by
    have := (prime_of_primeB h.1.1.1.1).two_le; omega)
  have := intCast_eq_of_emod (p := p) (a := (invZ p DB : ℤ) * DB) (b := 1) (by rw [h.1.2, h1])
  push_cast at this; exact this

theorem goodK_Dz : ((invZ p Dz : ℕ) : ZMod p) * (Dz : ZMod p) = 1 := by
  simp only [goodK, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : ((1 : ℤ) % p) = 1 := Int.emod_eq_of_lt (by norm_num) (by
    have := (prime_of_primeB h.1.1.1.1).two_le; omega)
  have := intCast_eq_of_emod (p := p) (a := (invZ p Dz : ℤ) * Dz) (b := 1) (by rw [h.2, h1])
  push_cast at this; exact this

end K

/-- The residue map `𝓞 K21 → ZMod p`, `θ ↦ t`. -/
noncomputable def ρK (p t : ℕ) (h : goodK p t = true) : 𝓞 K21 →+* ZMod p :=
  resHom (t : ZMod p) (goodK_root h) (invZ p DB : ZMod p) (goodK_DB h)

theorem ρK_zkO {p t : ℕ} (h : goodK p t = true) (a : List ℤ) :
    ρK p t h (zkO a) = (rzk p t a : ZMod p) := by
  rw [ρK, resHom_zkO _ _ _ _ (invZ p Dz : ZMod p) (goodK_Dz h) a, KE.evalL_combo, rzk,
    natCast_toNat_emod (goodK_pos h)]
  have e : zkNum.map (evalL (t : ZMod p)) = (zkRes p t).map (Int.cast : ℤ → ZMod p) := by
    rw [zkRes, List.map_map]
    refine List.map_congr_left fun W _ => ?_
    have e1 := map_evalL (Int.castRingHom (ZMod p)) (t : ℤ) W
    simp only [eq_intCast, Int.cast_natCast] at e1
    simp only [Function.comp_apply, ZMod.intCast_mod, e1]
  rw [e, dot_map_intCast]
  push_cast; rfl

/-! ### `ρL` -/

/-- `(p, t, s)`: a degree one prime of `K21` with `s² = ε`, `2 s² ≠ 0` modulo `p`. -/
def goodL (p t s : ℕ) : Bool :=
  goodK p t && (s * s) % p == rzk p t epsL % p && (2 * s * s) % p != 0

section L

variable {p t s : ℕ} (h : goodL p t s = true)
include h

theorem goodL_K : goodK p t = true := by
  simp only [goodL, Bool.and_eq_true] at h; exact h.1.1

theorem goodL_eps : ((s : ZMod p) * s) = ρK p t (goodL_K h) epsO := by
  have h' := h
  simp only [goodL, Bool.and_eq_true, beq_iff_eq] at h'
  rw [epsO, ρK_zkO, ← Nat.cast_mul]
  exact natCast_eq_of_mod h'.1.2

theorem goodL_two : ((2 * s * s : ℕ) : ZMod p) ≠ 0 := by
  simp only [goodL, Bool.and_eq_true, bne_iff_ne] at h; exact natCast_ne_zero_of_mod h.2

end L

/-- The residue map `OL → ZMod p`, `ω ↦ s`. -/
noncomputable def ρL (p t s : ℕ) (h : goodL p t s = true) : OL →+* ZMod p :=
  extendHom (ρK p t (goodL_K h)) (s : ZMod p) (goodL_eps h)

theorem ρL_mk {p t s : ℕ} (h : goodL p t s = true) (a0 a1 : List ℤ) :
    ρL p t s h ⟨zkO a0, zkO a1⟩ = ((rzk p t a0 + s * rzk p t a1 : ℕ) : ZMod p) := by
  rw [ρL, extendHom_apply]
  dsimp only
  rw [ρK_zkO, ρK_zkO]; push_cast; ring

theorem ρL_DL {p t s : ℕ} (h : goodL p t s = true) : ρL p t s h DL = ((2 * s * s : ℕ) : ZMod p) := by
  rw [ρL, DL, extendHom_algebraMap, map_mul, map_ofNat, ← goodL_eps h]; push_cast; ring

theorem isSquare_ρL {p t s : ℕ} (h : goodL p t s = true) (X : OL) (hX : IsSquare (ιL X)) :
    IsSquare (ρL p t s h X) := by
  have : Fact p.Prime := ⟨goodK_prime (goodL_K h)⟩
  have hD : ρL p t s h DL ≠ 0 := by rw [ρL_DL]; exact goodL_two h
  exact isSquare_of_isSquare_map ιL ιL_injective (ρL p t s h) DL hD hDy_L X hX

/-! ### `ρN` -/

/-- `(p, t, s, t2)`: `goodL` and `t2² = 2 ea + 2 eb s`, `2 s² t2² ≠ 0` modulo `p`. -/
def goodN (p t s t2 : ℕ) : Bool :=
  goodL p t s && (t2 * t2) % p == (2 * rzk p t eaL + s * (2 * rzk p t ebL)) % p &&
    (2 * s * s * (t2 * t2)) % p != 0

section N

variable {p t s t2 : ℕ} (h : goodN p t s t2 = true)
include h

theorem goodN_L : goodL p t s = true := by
  simp only [goodN, Bool.and_eq_true] at h; exact h.1.1

theorem goodN_EO : ((t2 : ZMod p) * t2) = ρL p t s (goodN_L h) EO := by
  have h' := h
  simp only [goodN, Bool.and_eq_true, beq_iff_eq] at h'
  rw [EO, ρL, extendHom_apply]
  dsimp only
  rw [map_mul, map_mul, map_ofNat, ρK_zkO, ρK_zkO, ← Nat.cast_mul]
  rw [natCast_eq_of_mod h'.1.2]; push_cast; ring

theorem goodN_ne : ((2 * s * s * (t2 * t2) : ℕ) : ZMod p) ≠ 0 := by
  simp only [goodN, Bool.and_eq_true, bne_iff_ne] at h; exact natCast_ne_zero_of_mod h.2

end N

/-- The residue map `ON → ZMod p`, `ω' ↦ t2`. -/
noncomputable def ρN (p t s t2 : ℕ) (h : goodN p t s t2 = true) : ON →+* ZMod p :=
  extendHom (ρL p t s (goodN_L h)) (t2 : ZMod p) (goodN_EO h)

theorem ρN_mk {p t s t2 : ℕ} (h : goodN p t s t2 = true) (a0 a1 a2 a3 : List ℤ) :
    ρN p t s t2 h ⟨⟨zkO a0, zkO a1⟩, ⟨zkO a2, zkO a3⟩⟩ =
      ((rzk p t a0 + s * rzk p t a1 + t2 * (rzk p t a2 + s * rzk p t a3) : ℕ) : ZMod p) := by
  rw [ρN, extendHom_apply]
  dsimp only
  rw [ρL_mk, ρL_mk]; push_cast; ring

theorem ρN_DN {p t s t2 : ℕ} (h : goodN p t s t2 = true) :
    ρN p t s t2 h DN = ((2 * s * s * (t2 * t2) : ℕ) : ZMod p) := by
  rw [ρN, DN, extendHom_algebraMap, map_mul, ρL_DL, ← goodN_EO h]; push_cast; ring

theorem isSquare_ρN {p t s t2 : ℕ} (h : goodN p t s t2 = true) (X : ON) (hX : IsSquare (ιN X)) :
    IsSquare (ρN p t s t2 h X) := by
  have : Fact p.Prime := ⟨goodK_prime (goodL_K (goodN_L h))⟩
  have hD : ρN p t s t2 h DN ≠ 0 := by rw [ρN_DN]; exact goodN_ne h
  exact isSquare_of_isSquare_map ιN ιN_injective (ρN p t s t2 h) DN hD hDy_N X hX

/-! ### Character values -/

/-- `v^((p-1)/2) mod p`. -/
def charB (p v : ℕ) : ℕ := v ^ ((p - 1) / 2) % p

/-- The value `-1` (bit set) or `1` (bit clear). -/
def bitOK (p c : ℕ) (b : Bool) : Bool := if b then c == p - 1 else c == 1

theorem pow_of_bitOK {p v : ℕ} (hp : 0 < p) {b : Bool} (h : bitOK p (charB p v) b = true) :
    (v : ZMod p) ^ ((p - 1) / 2) = if b then -1 else 1 := by
  rw [← Nat.cast_pow, ← ZMod.natCast_mod]
  cases b
  · simp only [bitOK, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, charB] at h ⊢
    rw [h, Nat.cast_one]
  · simp only [bitOK, ↓reduceIte, beq_iff_eq, charB] at h ⊢
    rw [h, Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem pow_mod_of_bitOK {p v : ℕ} (hp : 0 < p) {b : Bool} (h : bitOK p (charB p (v % p)) b = true) :
    (v : ZMod p) ^ ((p - 1) / 2) = if b then -1 else 1 := by
  rw [← ZMod.natCast_mod v p]; exact pow_of_bitOK hp h

/-- The character bits of `m` elements of `OL` given by zk lists, against the row `R`. -/
def rowL (p t s R m : ℕ) (gl : List (List (List ℤ))) : Bool :=
  (List.range m).all fun i =>
    bitOK p (charB p ((rzk p t ((gl.getD i []).getD 0 []) +
      s * rzk p t ((gl.getD i []).getD 1 [])) % p)) (R.testBit i)

/-- The element of `OL` with zk lists `l`. -/
noncomputable def mkOL (l : List (List ℤ)) : OL := ⟨zkO (l.getD 0 []), zkO (l.getD 1 [])⟩

theorem rowL_spec {p t s R m : ℕ} {gl : List (List (List ℤ))} (h : goodL p t s = true)
    (hr : rowL p t s R m gl = true) (i : Fin m) :
    ρL p t s h (mkOL (gl.getD i [])) ^ ((p - 1) / 2) = if R.testBit i then -1 else 1 := by
  simp only [rowL, List.all_eq_true, List.mem_range] at hr
  rw [mkOL, ρL_mk]
  exact pow_mod_of_bitOK (goodK_pos (goodL_K h)) (hr i i.isLt)

/-- The character bits of `m` elements of `ON` given by zk lists, against the row `R`. -/
def rowN (p t s t2 R m : ℕ) (gl : List (List (List ℤ))) : Bool :=
  (List.range m).all fun i =>
    bitOK p (charB p ((rzk p t ((gl.getD i []).getD 0 []) + s * rzk p t ((gl.getD i []).getD 1 []) +
      t2 * (rzk p t ((gl.getD i []).getD 2 []) + s * rzk p t ((gl.getD i []).getD 3 []))) % p))
      (R.testBit i)

/-- The element of `ON` with zk lists `l`. -/
noncomputable def mkON (l : List (List ℤ)) : ON :=
  ⟨⟨zkO (l.getD 0 []), zkO (l.getD 1 [])⟩, ⟨zkO (l.getD 2 []), zkO (l.getD 3 [])⟩⟩

theorem rowN_spec {p t s t2 R m : ℕ} {gl : List (List (List ℤ))} (h : goodN p t s t2 = true)
    (hr : rowN p t s t2 R m gl = true) (i : Fin m) :
    ρN p t s t2 h (mkON (gl.getD i [])) ^ ((p - 1) / 2) = if R.testBit i then -1 else 1 := by
  simp only [rowN, List.all_eq_true, List.mem_range] at hr
  rw [mkON, ρN_mk]
  exact pow_mod_of_bitOK (goodK_pos (goodL_K (goodN_L h))) (hr i i.isLt)

end FurioLombardo.Discharge.SelmerBasis.SU
