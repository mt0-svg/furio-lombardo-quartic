import FurioLombardo.M2.Spec

/-!
# Semantics of the packed checkers modulo `p` (lane M2)

A packed number `pack l` stores the coefficient list `l` in slots of `Bw = 2^128` bits. The
arithmetic of the kernel functions (`mulmod`, `redOnce`, `mulX`, `mkTable`, `powXT`, `prodP`) is
carry free under the bounds used (`p < 2^20`, at most 44 slots), so it is list arithmetic on the
slots, and in every commutative ring `F` with `p = 0` it computes products of polynomials modulo
the monic `X^d + gl` at a root `t`.

The proofs go through explicit coefficient lists: `addL`, `smulL`, `mulL` (natural numbers, no
reduction) satisfy `pack (mulL l m) = pack l * pack m` and `evalN t (mulL l m) = evalN t l *
evalN t m`, and the slot bounds make `%`, `/` by powers of `Bw` act as `take`, `drop`.
-/

namespace FurioLombardo.M2

/-- Horner evaluation of a natural coefficient list (constant term first). -/
def evalN {R : Type*} [CommRing R] (t : R) : List ℕ → R
  | [] => 0
  | a :: l => (a : R) + t * evalN t l

/-- The value at `t` of the polynomial whose coefficients are the first `n` slots of `N`. -/
def evP {R : Type*} [CommRing R] (t : R) : ℕ → ℕ → R
  | 0, _ => 0
  | n + 1, N => ((N % Bw : ℕ) : R) + t * evP t n (N / Bw)

/-- Coefficientwise sum (no reduction). -/
def addL : List ℕ → List ℕ → List ℕ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

/-- Scalar multiple (no reduction). -/
def smulL (c : ℕ) (l : List ℕ) : List ℕ := l.map (c * ·)

/-- Product (no reduction). -/
def mulL : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: l, m => addL (smulL a m) (0 :: mulL l m)

/-- The list form of `foldT`: `Σ_j h_j tl_j`. -/
def foldL : List (List ℕ) → List ℕ → List ℕ
  | [], _ => []
  | tl :: tls, h => addL (smulL (h.headD 0) tl) (foldL tls h.tail)

/-- A canonical list: at most `n` entries, each below `p`. -/
def CanonL (p n : ℕ) (l : List ℕ) : Prop := l.length ≤ n ∧ ∀ x ∈ l, x < p

section Basic

variable {R : Type*} [CommRing R]

@[simp] theorem evalN_nil (t : R) : evalN t [] = 0 := rfl

@[simp] theorem evalN_cons (t : R) (a : ℕ) (l : List ℕ) :
    evalN t (a :: l) = (a : R) + t * evalN t l := rfl

@[simp] theorem pack_nil : pack [] = 0 := rfl

@[simp] theorem pack_cons (a : ℕ) (l : List ℕ) : pack (a :: l) = a + Bw * pack l := rfl

theorem Bw_pos : 0 < Bw := by unfold Bw; positivity

theorem Bw_eq : Bw = 2 ^ 128 := rfl

theorem mod_Bw (a N : ℕ) (ha : a < Bw) : (a + Bw * N) % Bw = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem div_Bw (a N : ℕ) (ha : a < Bw) : (a + Bw * N) / Bw = N := by
  rw [Nat.add_mul_div_left _ _ Bw_pos, Nat.div_eq_of_lt ha, zero_add]

theorem evP_zero_right (t : R) : ∀ n : ℕ, evP t n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [evP, evP_zero_right t n]

theorem evP_pack (t : R) : ∀ (l : List ℕ) (n : ℕ), (∀ x ∈ l, x < Bw) → l.length ≤ n →
    evP t n (pack l) = evalN t l
  | [], n, _, _ => by simp [evP_zero_right]
  | a :: l, 0, _, hn => by simp at hn
  | a :: l, n + 1, hl, hn => by
    have ha : a < Bw := hl a (by simp)
    simp only [evP, pack_cons, mod_Bw a _ ha, div_Bw a _ ha, evalN_cons]
    rw [evP_pack t l n (fun x hx => hl x (by simp [hx])) (by simpa using hn)]

theorem pack_addL : ∀ l m : List ℕ, pack (addL l m) = pack l + pack m
  | [], m => by simp [addL]
  | a :: l, [] => by simp [addL]
  | a :: l, b :: m => by simp only [addL, pack_cons, pack_addL l m]; ring

theorem pack_smulL (c : ℕ) : ∀ l : List ℕ, pack (smulL c l) = c * pack l
  | [] => by simp [smulL]
  | a :: l => by
    have := pack_smulL c l
    simp only [smulL, List.map_cons, pack_cons] at this ⊢
    rw [this]; ring

theorem pack_mulL : ∀ l m : List ℕ, pack (mulL l m) = pack l * pack m
  | [], m => by simp [mulL]
  | a :: l, m => by simp only [mulL, pack_addL, pack_smulL, pack_cons, pack_mulL l m]; ring

theorem evalN_addL (t : R) : ∀ l m : List ℕ, evalN t (addL l m) = evalN t l + evalN t m
  | [], m => by simp [addL]
  | a :: l, [] => by simp [addL]
  | a :: l, b :: m => by simp only [addL, evalN_cons, evalN_addL t l m, Nat.cast_add]; ring

theorem evalN_smulL (t : R) (c : ℕ) : ∀ l : List ℕ, evalN t (smulL c l) = c * evalN t l
  | [] => by simp [smulL]
  | a :: l => by
    have := evalN_smulL t c l
    simp only [smulL, List.map_cons, evalN_cons, Nat.cast_mul] at this ⊢
    rw [this]; ring

theorem evalN_mulL (t : R) : ∀ l m : List ℕ, evalN t (mulL l m) = evalN t l * evalN t m
  | [], m => by simp [mulL]
  | a :: l, m => by
    simp only [mulL, evalN_addL, evalN_smulL, evalN_cons, evalN_mulL t l m, Nat.cast_zero]; ring

theorem length_addL : ∀ l m : List ℕ, (addL l m).length = max l.length m.length
  | [], m => by simp [addL]
  | a :: l, [] => by simp [addL]
  | a :: l, b :: m => by simp [addL, length_addL l m, Nat.succ_max_succ]

theorem length_smulL (c : ℕ) (l : List ℕ) : (smulL c l).length = l.length := by simp [smulL]

theorem length_mulL_add_one (m : List ℕ) (hm : m ≠ []) :
    ∀ l : List ℕ, (mulL l m).length + 1 ≤ l.length + m.length
  | [] => by simp [mulL]; exact List.length_pos_of_ne_nil hm
  | a :: l => by
    have ih := length_mulL_add_one m hm l
    simp only [mulL, length_addL, length_smulL, List.length_cons]
    omega

theorem length_mulL_nil_right : ∀ l : List ℕ, (mulL l []).length = l.length
  | [] => rfl
  | a :: l => by simp [mulL, addL, smulL, length_mulL_nil_right l]

theorem le_addL (A B : ℕ) : ∀ l m : List ℕ, (∀ x ∈ l, x ≤ A) → (∀ x ∈ m, x ≤ B) →
    ∀ x ∈ addL l m, x ≤ A + B
  | [], m, _, hm => fun x hx => (hm x hx).trans (Nat.le_add_left _ _)
  | a :: l, [], hl, _ => fun x hx => (hl x hx).trans (Nat.le_add_right _ _)
  | a :: l, b :: m, hl, hm => by
    intro x hx
    simp only [addL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.add_le_add (hl a (by simp)) (hm b (by simp))
    · exact le_addL A B l m (fun y hy => hl y (by simp [hy])) (fun y hy => hm y (by simp [hy])) x hx

theorem le_smulL (c A : ℕ) (l : List ℕ) (hl : ∀ x ∈ l, x ≤ A) : ∀ x ∈ smulL c l, x ≤ c * A := by
  intro x hx
  simp only [smulL, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Nat.mul_le_mul_left _ (hl y hy)

theorem le_mulL (A B : ℕ) : ∀ l m : List ℕ, (∀ x ∈ l, x ≤ A) → (∀ x ∈ m, x ≤ B) →
    ∀ x ∈ mulL l m, x ≤ l.length * A * B
  | [], _, _, _ => by simp [mulL]
  | a :: l, m, hl, hm => by
    intro x hx
    simp only [mulL] at hx
    have h1 : ∀ y ∈ smulL a m, y ≤ A * B := fun y hy =>
      (le_smulL a B m hm y hy).trans (Nat.mul_le_mul_right _ (hl a (by simp)))
    have h2 : ∀ y ∈ (0 : ℕ) :: mulL l m, y ≤ l.length * A * B := by
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.zero_le _
      · exact le_mulL A B l m (fun z hz => hl z (by simp [hz])) hm y hy
    have := le_addL _ _ _ _ h1 h2 x hx
    simp only [List.length_cons]
    nlinarith

theorem pack_mod_pow : ∀ (d : ℕ) (l : List ℕ), (∀ x ∈ l, x < Bw) →
    pack l % Bw ^ d = pack (l.take d)
  | 0, l, _ => by simp [Nat.mod_one]
  | d + 1, [], _ => by simp
  | d + 1, a :: l, hl => by
    have ha : a < Bw := hl a (by simp)
    rw [pow_succ', Nat.mod_mul, pack_cons, mod_Bw a _ ha, div_Bw a _ ha,
      pack_mod_pow d l (fun x hx => hl x (by simp [hx]))]
    simp

theorem pack_div_pow : ∀ (d : ℕ) (l : List ℕ), (∀ x ∈ l, x < Bw) →
    pack l / Bw ^ d = pack (l.drop d)
  | 0, l, _ => by simp
  | d + 1, [], _ => by simp
  | d + 1, a :: l, hl => by
    have ha : a < Bw := hl a (by simp)
    rw [pow_succ', ← Nat.div_div_eq_div_mul, pack_cons, div_Bw a _ ha,
      pack_div_pow d l (fun x hx => hl x (by simp [hx]))]
    simp

theorem evalN_take_drop (t : R) : ∀ (d : ℕ) (l : List ℕ),
    evalN t l = evalN t (l.take d) + t ^ d * evalN t (l.drop d)
  | 0, l => by simp
  | d + 1, [] => by simp
  | d + 1, a :: l => by
    simp only [List.take_succ_cons, List.drop_succ_cons, evalN_cons]
    rw [evalN_take_drop t d l]; ring

theorem evalN_map_mod {F : Type*} [CommRing F] (t : F) (p : ℕ) (hpF : (p : F) = 0) :
    ∀ l : List ℕ, evalN t (l.map (· % p)) = evalN t l
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, evalN_cons, evalN_map_mod t p hpF l]
    congr 1
    have : ((a % p : ℕ) : F) + p * ((a / p : ℕ) : F) = a := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [hpF, zero_mul, add_zero] at this
    exact this

theorem modSlots_zero (p : ℕ) : ∀ n : ℕ, modSlots p n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [modSlots, modSlots_zero p n]

theorem modSlots_pack (p : ℕ) : ∀ (n : ℕ) (l : List ℕ), (∀ x ∈ l, x < Bw) →
    modSlots p n (pack l) = pack ((l.take n).map (· % p))
  | 0, l, _ => rfl
  | n + 1, [], _ => by simp [modSlots_zero]
  | n + 1, a :: l, hl => by
    have ha : a < Bw := hl a (by simp)
    simp only [modSlots, pack_cons, mod_Bw a _ ha, div_Bw a _ ha, List.take_succ_cons,
      List.map_cons]
    rw [modSlots_pack p n l (fun x hx => hl x (by simp [hx]))]

theorem foldT_pack : ∀ (tls : List (List ℕ)) (h : List ℕ), (∀ x ∈ h, x < Bw) →
    foldT (tls.map pack) (pack h) = pack (foldL tls h)
  | [], _, _ => rfl
  | tl :: tls, [], _ => by
    have := foldT_pack tls [] (by simp)
    simp only [List.map_cons, foldT, pack_nil, Nat.zero_mod, Nat.zero_div, zero_mul, zero_add,
      foldL, List.headD_nil, List.tail_nil, pack_addL, pack_smulL] at this ⊢
    exact this
  | tl :: tls, a :: h, hh => by
    have ha : a < Bw := hh a (by simp)
    simp only [List.map_cons, foldT, pack_cons, mod_Bw a _ ha, div_Bw a _ ha, foldL,
      List.headD_cons, List.tail_cons, pack_addL, pack_smulL]
    rw [foldT_pack tls h (fun x hx => hh x (by simp [hx]))]

theorem evalN_foldL (t : R) : ∀ (tls : List (List ℕ)) (h : List ℕ) (d : ℕ),
    h.length ≤ tls.length → (∀ (j : ℕ) (hj : j < tls.length), evalN t tls[j] = t ^ (d + j)) →
    evalN t (foldL tls h) = t ^ d * evalN t h
  | [], h, d, hl, _ => by
    have : h = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this; simp [foldL]
  | tl :: tls, [], d, _, hv => by
    have := evalN_foldL t tls [] (d + 1) (by simp) (fun j hj => by
      have := hv (j + 1) (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
    simp only [foldL, List.headD_nil, List.tail_nil, evalN_addL, evalN_smulL, this]
    simp
  | tl :: tls, a :: h, d, hl, hv => by
    have ih := evalN_foldL t tls h (d + 1) (by simpa using hl) (fun j hj => by
      have := hv (j + 1) (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
    have h0 := hv 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at h0
    simp only [foldL, List.headD_cons, List.tail_cons, evalN_addL, evalN_smulL, ih, h0,
      evalN_cons, pow_succ]
    ring

theorem le_foldL (A B : ℕ) : ∀ (tls : List (List ℕ)) (h : List ℕ),
    (∀ tl ∈ tls, ∀ x ∈ tl, x ≤ A) → (∀ x ∈ h, x ≤ B) →
    ∀ x ∈ foldL tls h, x ≤ tls.length * (B * A)
  | [], _, _, _ => by simp [foldL]
  | tl :: tls, h, htl, hh => by
    intro x hx
    simp only [foldL] at hx
    have hb : h.headD 0 ≤ B := by
      cases h with
      | nil => simp
      | cons a h => exact hh a (by simp)
    have h1 : ∀ y ∈ smulL (h.headD 0) tl, y ≤ B * A := fun y hy =>
      (le_smulL _ A tl (htl tl (by simp)) y hy).trans (Nat.mul_le_mul_right _ hb)
    have h2 := le_foldL A B tls h.tail (fun t ht => htl t (by simp [ht]))
      (fun y hy => hh y (List.mem_of_mem_tail hy))
    have := le_addL _ _ _ _ h1 h2 x hx
    simp only [List.length_cons]
    nlinarith

theorem length_foldL (d : ℕ) : ∀ (tls : List (List ℕ)) (h : List ℕ),
    (∀ tl ∈ tls, tl.length ≤ d) → (foldL tls h).length ≤ d
  | [], _, _ => by simp [foldL]
  | tl :: tls, h, htl => by
    simp only [foldL, length_addL, length_smulL]
    exact max_le (htl tl (by simp)) (length_foldL d tls h.tail (fun t ht => htl t (by simp [ht])))

end Basic


section Rep

variable {F : Type*} [CommRing F]

/-- `N` packs a canonical list (at most `n` entries, each below `p`) whose value at `t` is `x`. -/
def IsRep (p n : ℕ) (t : F) (N : ℕ) (x : F) : Prop :=
  ∃ l : List ℕ, l.length ≤ n ∧ (∀ y ∈ l, y < p) ∧ pack l = N ∧ evalN t l = x

theorem IsRep.mono {p n m : ℕ} {t : F} {N : ℕ} {x : F} (h : IsRep p n t N x) (hnm : n ≤ m) :
    IsRep p m t N x := by
  obtain ⟨l, h1, h2, h3, h4⟩ := h
  exact ⟨l, h1.trans hnm, h2, h3, h4⟩

/-- Two representations of the same packed number have the same value. -/
theorem IsRep.unique {p n : ℕ} {t : F} {N : ℕ} {x y : F} (hp : p ≤ Bw) (hx : IsRep p n t N x)
    (hy : IsRep p n t N y) : x = y := by
  obtain ⟨l, h1, h2, rfl, rfl⟩ := hx
  obtain ⟨m, h1', h2', h3', rfl⟩ := hy
  rw [← evP_pack t l n (fun z hz => (h2 z hz).trans_le hp) h1,
    ← evP_pack t m n (fun z hz => (h2' z hz).trans_le hp) h1', h3']

theorem modSlots_rep (t : F) (p n m : ℕ) (hpF : (p : F) = 0) (hp : 0 < p) (h : List ℕ)
    (hh : ∀ y ∈ h, y < Bw) (hlen : h.length ≤ n) (hm : h.length ≤ m) :
    IsRep p m t (modSlots p n (pack h)) (evalN t h) := by
  refine ⟨h.map (· % p), by simpa using hm, ?_, ?_, evalN_map_mod t p hpF h⟩
  · intro y hy
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
    exact Nat.mod_lt _ hp
  · rw [modSlots_pack p n h hh, List.take_of_length_le hlen]

theorem one_rep (t : F) (p n : ℕ) (hp : 2 ≤ p) (hn : 1 ≤ n) : IsRep p n t 1 1 :=
  ⟨[1], by simpa using hn, by simp; omega, by simp, by simp⟩

theorem pack_eq_evalN_of_length_le_one (t : F) :
    ∀ l : List ℕ, l.length ≤ 1 → ((pack l : ℕ) : F) = evalN t l
  | [], _ => by simp
  | [a], _ => by simp
  | _ :: _ :: _, h => by simp at h

theorem mulmod_rep (t : F) (p d : ℕ) (hpF : (p : F) = 0) (hp0 : 0 < p) (hp : p < 2 ^ 20)
    (hd : d ≤ 22) (tls : List (List ℕ)) (htl : ∀ tl ∈ tls, tl.length ≤ d ∧ ∀ z ∈ tl, z < p)
    (htv : ∀ (j : ℕ) (hj : j < tls.length), evalN t tls[j] = t ^ (d + j))
    (hlen : d ≤ tls.length + 1) (htlen : tls.length ≤ 21)
    {N M : ℕ} {x y : F} (hN : IsRep p d t N x) (hM : IsRep p d t M y) :
    IsRep p d t (mulmod p d (tls.map pack) N M) (x * y) := by
  obtain ⟨l, hl1, hl2, rfl, rfl⟩ := hN
  obtain ⟨m, hm1, hm2, rfl, rfl⟩ := hM
  have hp' : p ≤ 2 ^ 20 := hp.le
  have hb : ∀ z ∈ mulL l m, z ≤ d * p * p := fun z hz =>
    (le_mulL p p l m (fun z hz => (hl2 z hz).le) (fun z hz => (hm2 z hz).le) z hz).trans
      (by gcongr)
  have hBw : d * p * p < Bw := by
    have : d * p * p ≤ 22 * 2 ^ 20 * 2 ^ 20 := by gcongr
    exact this.trans_lt (by norm_num [Bw])
  have hhB : ∀ z ∈ mulL l m, z < Bw := fun z hz => (hb z hz).trans_lt hBw
  have hdrop : (List.drop d (mulL l m)).length ≤ tls.length := by
    rw [List.length_drop]
    by_cases hm : m = []
    · subst hm; rw [length_mulL_nil_right]; omega
    · have := length_mulL_add_one m hm l; omega
  have hsum : ∀ z ∈ addL ((mulL l m).take d) (foldL tls ((mulL l m).drop d)),
      z ≤ d * p * p + tls.length * (d * p * p * p) := by
    refine le_addL _ _ _ _ (fun z hz => hb z (List.mem_of_mem_take hz)) ?_
    have := le_foldL p (d * p * p) tls ((mulL l m).drop d)
      (fun tl htl' z hz => ((htl tl htl').2 z hz).le) (fun z hz => hb z (List.mem_of_mem_drop hz))
    intro z hz
    exact (this z hz).trans (le_of_eq (by ring))
  have hsB : d * p * p + tls.length * (d * p * p * p) < Bw := by
    have : d * p * p + tls.length * (d * p * p * p) ≤
        22 * 2 ^ 20 * 2 ^ 20 + 21 * (22 * 2 ^ 20 * 2 ^ 20 * 2 ^ 20) := by gcongr
    exact this.trans_lt (by norm_num [Bw])
  have hlen' : (addL ((mulL l m).take d) (foldL tls ((mulL l m).drop d))).length ≤ d := by
    rw [length_addL]
    exact max_le (List.length_take_le _ _) (length_foldL d tls _ (fun tl h => (htl tl h).1))
  unfold mulmod
  rw [← pack_mulL, pack_mod_pow d _ hhB, pack_div_pow d _ hhB,
    foldT_pack tls _ (fun z hz => hhB z (List.mem_of_mem_drop hz)), ← pack_addL]
  have := modSlots_rep t p d d hpF hp0 _ (fun z hz => (hsum z hz).trans_lt hsB) hlen' hlen'
  rwa [evalN_addL, evalN_foldL t tls _ d hdrop htv, ← evalN_take_drop, evalN_mulL] at this

theorem redOnce_rep (t : F) (p d : ℕ) (hpF : (p : F) = 0) (hp0 : 0 < p) (hp : p < 2 ^ 20)
    {T0 : ℕ} (hT0 : IsRep p d t T0 (t ^ d)) {H : ℕ} {x : F} (hH : IsRep p (d + 1) t H x) :
    IsRep p d t (redOnce p d T0 H) x := by
  obtain ⟨h, hh1, hh2, rfl, rfl⟩ := hH
  obtain ⟨tl, ht1, ht2, rfl, htv⟩ := hT0
  have hp' : p ≤ 2 ^ 20 := hp.le
  have hhB : ∀ z ∈ h, z < Bw := fun z hz =>
    (hh2 z hz).trans (hp.trans_le (by norm_num [Bw]))
  have hd1 : (h.drop d).length ≤ 1 := by rw [List.length_drop]; omega
  have hc : pack (h.drop d) < p := by
    rcases hdr : h.drop d with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp; exact hp0
    · simpa using hh2 a (List.mem_of_mem_drop (hdr ▸ List.mem_singleton_self a))
    · rw [hdr] at hd1; simp at hd1
  have hsum : ∀ z ∈ addL (h.take d) (smulL (pack (h.drop d)) tl), z ≤ p + p * p :=
    le_addL _ _ _ _ (fun z hz => (hh2 z (List.mem_of_mem_take hz)).le)
      (fun z hz => (le_smulL _ p tl (fun w hw => (ht2 w hw).le) z hz).trans
        (Nat.mul_le_mul_right _ hc.le))
  have hsB : p + p * p < Bw := by
    have : p + p * p ≤ 2 ^ 20 + 2 ^ 20 * 2 ^ 20 := by gcongr
    exact this.trans_lt (by norm_num [Bw])
  have hlen' : (addL (h.take d) (smulL (pack (h.drop d)) tl)).length ≤ d := by
    rw [length_addL, length_smulL]; exact max_le (List.length_take_le _ _) ht1
  unfold redOnce
  rw [pack_mod_pow d _ hhB, pack_div_pow d _ hhB, ← pack_smulL, ← pack_addL]
  have := modSlots_rep t p d d hpF hp0 _ (fun z hz => (hsum z hz).trans_lt hsB) hlen' hlen'
  rw [evalN_addL, evalN_smulL, htv, pack_eq_evalN_of_length_le_one t _ hd1] at this
  convert this using 1
  rw [evalN_take_drop t d h]; ring

theorem mulX_rep (t : F) (p d : ℕ) (hpF : (p : F) = 0) (hp0 : 0 < p) (hp : p < 2 ^ 20)
    {T0 : ℕ} (hT0 : IsRep p d t T0 (t ^ d)) {N : ℕ} {x : F} (hN : IsRep p d t N x) :
    IsRep p d t (mulX p d T0 N) (t * x) := by
  obtain ⟨l, hl1, hl2, rfl, rfl⟩ := hN
  refine redOnce_rep t p d hpF hp0 hp hT0 ⟨0 :: l, by simpa using hl1, ?_, ?_, by simp⟩
  · intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hp0
    · exact hl2 z hz
  · simp [mul_comm]

theorem negLow_rep (t : F) (p : ℕ) (hpF : (p : F) = 0) (hp0 : 0 < p) (gl : List ℤ)
    (hg : t ^ gl.length + evalZ t gl = 0) : IsRep p gl.length t (negLow p gl) (t ^ gl.length) := by
  have hval : ∀ l : List ℤ,
      evalN t (l.map fun c => ((-c) % (p : ℤ)).toNat) = -evalZ t l := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons, evalN_cons, evalZ_cons, ih]
      have hnn : 0 ≤ (-c) % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp0.ne')
      have : (((-c) % (p : ℤ)).toNat : F) = -(c : F) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, Int.emod_def, Int.cast_sub, Int.cast_mul,
          Int.cast_natCast, hpF]
        simp
      rw [this]; ring
  refine ⟨gl.map fun c => ((-c) % (p : ℤ)).toNat, by simp, ?_, rfl, ?_⟩
  · intro y hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hy
    have hnn : 0 ≤ (-c) % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp0.ne')
    have hlt : (-c) % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp0)
    omega
  · rw [hval]; linear_combination (-1 : F) * hg

theorem mkTable_rep (t : F) (p d : ℕ) (hpF : (p : F) = 0) (hp0 : 0 < p) (hp : p < 2 ^ 20)
    {T0 : ℕ} (hT0 : IsRep p d t T0 (t ^ d)) :
    ∀ (n T : ℕ) (x : F), IsRep p d t T x → ∃ tls : List (List ℕ),
      mkTable p d T0 n T = tls.map pack ∧ tls.length = n ∧
      (∀ tl ∈ tls, tl.length ≤ d ∧ ∀ z ∈ tl, z < p) ∧
      ∀ (j : ℕ) (hj : j < tls.length), evalN t tls[j] = x * t ^ j
  | 0, _, _, _ => ⟨[], rfl, rfl, by simp, by simp⟩
  | n + 1, T, x, hT => by
    obtain ⟨tls, h1, h2, h3, h4⟩ :=
      mkTable_rep t p d hpF hp0 hp hT0 n _ _ (mulX_rep t p d hpF hp0 hp hT0 hT)
    obtain ⟨l, hl1, hl2, rfl, rfl⟩ := hT
    refine ⟨l :: tls, by simp [mkTable, h1], by simp [h2], ?_, ?_⟩
    · intro tl htl
      simp only [List.mem_cons] at htl
      rcases htl with rfl | htl
      · exact ⟨hl1, hl2⟩
      · exact h3 tl htl
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [h4 j (by simpa using hj)]; ring

/-- The exponent built by the bits `bs` (most significant first) on top of `k`. -/
def bitsVal (k : ℕ) (bs : List Bool) : ℕ := bs.foldl (fun a b => 2 * a + if b then 1 else 0) k

theorem bitsVal_bitsHigh : ∀ (fuel n : ℕ), n < 2 ^ fuel → bitsVal 0 (bitsHigh fuel n) = n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; rfl
  | fuel + 1, n, h => by
    unfold bitsHigh
    split_ifs with hn
    · subst hn; rfl
    · have ih := bitsVal_bitsHigh fuel (n / 2) (by rw [pow_succ] at h; omega)
      unfold bitsVal at ih ⊢
      rw [List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil]
      rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2] <;> omega

theorem powXT_rep (t : F) (p d : ℕ) (hpF : (p : F) = 0) (hp2 : 2 ≤ p) (hp : p < 2 ^ 20)
    (hd : d ≤ 22) (hd1 : 1 ≤ d) {T0 : ℕ} (hT0 : IsRep p d t T0 (t ^ d))
    (tls : List (List ℕ)) (htl : ∀ tl ∈ tls, tl.length ≤ d ∧ ∀ z ∈ tl, z < p)
    (htv : ∀ (j : ℕ) (hj : j < tls.length), evalN t tls[j] = t ^ (d + j))
    (hlen : d ≤ tls.length + 1) (htlen : tls.length ≤ 21) (e : ℕ) (he : e < 2 ^ 64) :
    IsRep p d t (powXT p d T0 (tls.map pack) e) (t ^ e) := by
  have hp0 : 0 < p := by omega
  have key : ∀ (bs : List Bool) (acc k : ℕ), IsRep p d t acc (t ^ k) →
      IsRep p d t (bs.foldl (fun acc b =>
        let s := mulmod p d (tls.map pack) acc acc
        if b then mulX p d T0 s else s) acc) (t ^ bitsVal k bs) := by
    intro bs
    induction bs with
    | nil => intro acc k h; exact h
    | cons b bs ih =>
      intro acc k h
      have hs := mulmod_rep t p d hpF hp0 hp hd tls htl htv hlen htlen h h
      rw [← pow_add] at hs
      simp only [List.foldl_cons, bitsVal] at ih ⊢
      apply ih
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        convert hs using 2; ring
      · simp only [↓reduceIte]
        convert mulX_rep t p d hpF hp0 hp hT0 hs using 2; ring
  have := key (bitsHigh 64 e) 1 0 (by simpa using one_rep t p d hp2 hd1)
  rwa [bitsVal_bitsHigh 64 e he] at this

theorem prodP_rep (t : F) (p n : ℕ) (hpF : (p : F) = 0) (hp2 : 2 ≤ p) (hp : p < 2 ^ 20)
    (hn : n ≤ 22) : ∀ Ls : List (List ℕ), (∀ L ∈ Ls, 1 ≤ L.length ∧ ∀ z ∈ L, z < p) →
      (Ls.map fun L => L.length - 1).sum + 1 ≤ n →
      IsRep p ((Ls.map fun L => L.length - 1).sum + 1) t (prodP p n (Ls.map pack))
        (Ls.map (evalN t)).prod
  | [], _, _ => by
    simp only [List.map_nil, prodP, List.sum_nil, zero_add, List.prod_nil]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact one_rep t p 1 hp2 le_rfl
  | L :: Ls, hL, hsum => by
    have hp0 : 0 < p := by omega
    have hL1 := hL L (by simp)
    simp only [List.map_cons, List.sum_cons] at hsum ⊢
    obtain ⟨l, hl1, hl2, hl3, hl4⟩ := prodP_rep t p n hpF hp2 hp hn Ls
      (fun L' h => hL L' (by simp [h])) (by omega)
    simp only [prodP, List.prod_cons]
    rw [← hl3, ← pack_mulL, ← hl4, ← evalN_mulL]
    have hLlen : L.length ≤ 22 := by omega
    have hb : ∀ z ∈ mulL L l, z ≤ L.length * p * p := le_mulL p p L l
      (fun z hz => (hL1.2 z hz).le) (fun z hz => (hl2 z hz).le)
    have hB : L.length * p * p < Bw := by
      have : L.length * p * p ≤ 22 * 2 ^ 20 * 2 ^ 20 := by have := hp.le; gcongr
      exact this.trans_lt (by norm_num [Bw])
    have hlenm : (mulL L l).length ≤ L.length - 1 + (List.map (fun L => L.length - 1) Ls).sum + 1 := by
      by_cases hl : l = []
      · subst hl; rw [length_mulL_nil_right]; omega
      · have := length_mulL_add_one l hl L; omega
    exact modSlots_rep t p n _ hpF hp0 _ (fun z hz => (hb z hz).trans_lt hB) (by omega) hlenm

end Rep

end FurioLombardo.M2
