import FurioLombardo.M2.Check
import FurioLombardo.M2.Poly

/-!
# Soundness of the factor certificates (lane M2)

`facCheckE p T0 Ts facs e s = true` (with `T0`, `Ts` built from the lower coefficients `gl` of a
monic `g` of degree 21) gives, in every commutative ring `F` with `p = 0` and every root `t` of
`g`, the identity `s(t) (t^(p^e) - t) = ∏_{deg L ∣ e} L(t)`. In a finite field with `p^e`
elements the left side vanishes, so some listed factor `L` with `deg L ∣ e` has `L(t) = 0`.
-/

namespace FurioLombardo.M2

open Polynomial

theorem facCheckE_sound {F : Type*} [CommRing F] (t : F) (p : ℕ) (hpF : (p : F) = 0)
    (hp2 : 2 ≤ p) (hp : p < 2 ^ 20) (gl : List ℤ) (hgl : gl.length = 21)
    (hg : t ^ 21 + evalZ t gl = 0) (facs : List Fac)
    (hfacs : ∀ fac ∈ facs, fac.L.length = fac.deg + 1 ∧ ∀ z ∈ fac.L, z < p)
    (e : ℕ) (he : p ^ e < 2 ^ 64) (s : List ℕ)
    (h : facCheckE p (negLow p gl) (mkTable p 21 (negLow p gl) 20 (negLow p gl)) facs e s = true) :
    evalN t s * (t ^ (p ^ e) - t) =
      ((facs.filter fun fac => e % fac.deg == 0).map fun fac => evalN t fac.L).prod := by
  have hp0 : 0 < p := by omega
  unfold facCheckE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hsum, hslen⟩, hslt⟩, heq⟩ := h
  have hT0 : IsRep p 21 t (negLow p gl) (t ^ 21) := by
    have := negLow_rep t p hpF hp0 gl (by rw [hgl]; exact hg)
    rwa [hgl] at this
  obtain ⟨tls, htab, htlen, htl, htv⟩ := mkTable_rep t p 21 hpF hp0 hp hT0 20 _ _ hT0
  have htv' : ∀ (j : ℕ) (hj : j < tls.length), evalN t tls[j] = t ^ (21 + j) := by
    intro j hj; rw [htv j hj, pow_add]
  rw [htab] at heq
  obtain ⟨l, hl1, hl2, hl3, hl4⟩ := powXT_rep t p 21 hpF hp2 hp (by norm_num) (by norm_num) hT0
    tls htl htv' (by omega) (by omega) (p ^ e) he
  have hadd : pack l + (p - 1) * Bw = pack (addL l [0, p - 1]) := by
    rw [pack_addL]; simp [pack]; ring
  have hX : IsRep p 21 t
      (modSlots p 21 (powXT p 21 (negLow p gl) (tls.map pack) (p ^ e) + (p - 1) * Bw))
      (t ^ (p ^ e) - t) := by
    rw [← hl3, hadd]
    have hb : ∀ z ∈ addL l [0, p - 1], z ≤ p + p :=
      le_addL _ _ _ _ (fun z hz => (hl2 z hz).le) (by intro z hz; simp at hz; omega)
    have hlen : (addL l [0, p - 1]).length ≤ 21 := by rw [length_addL]; simp; omega
    have := modSlots_rep t p 21 21 hpF hp0 _ (fun z hz => (hb z hz).trans_lt (by
      have : p + p ≤ 2 ^ 20 + 2 ^ 20 := by omega
      exact this.trans_lt (by norm_num [Bw]))) hlen hlen
    convert this using 1
    rw [evalN_addL, hl4]
    simp [Nat.cast_sub (by omega : 1 ≤ p), hpF]
    ring
  have hs : IsRep p 21 t (pack s) (evalN t s) := ⟨s, hslen, hslt, rfl, rfl⟩
  have hL := mulmod_rep t p 21 hpF hp0 hp (by norm_num) tls htl htv' (by omega) (by omega) hs hX
  have hsel : ∀ fac ∈ facs.filter (fun fac => e % fac.deg == 0),
      fac.L.length = fac.deg + 1 ∧ ∀ z ∈ fac.L, z < p :=
    fun fac hf => hfacs fac (List.mem_of_mem_filter hf)
  have hdeg : (((facs.filter fun fac => e % fac.deg == 0).map Fac.L).map fun L => L.length - 1) =
      (facs.filter fun fac => e % fac.deg == 0).map Fac.deg := by
    rw [List.map_map]; apply List.map_congr_left; intro fac hf; simp [(hsel fac hf).1]
  have hP := prodP_rep t p 22 hpF hp2 hp le_rfl ((facs.filter fun fac => e % fac.deg == 0).map Fac.L)
    (by
      intro L hL
      obtain ⟨fac, hf, rfl⟩ := List.mem_map.mp hL
      exact ⟨by rw [(hsel fac hf).1]; omega, (hsel fac hf).2⟩)
    (by rw [hdeg]; omega)
  have hR := redOnce_rep t p 21 hpF hp0 hp hT0 (hP.mono (by rw [hdeg]; omega))
  simp only [List.map_map] at hR
  have := IsRep.unique (by norm_num [Bw]; omega) hL (heq ▸ hR)
  rw [this]
  rfl

/-- In a finite field with `p ^ e` elements, a root `t` of `g` is a root of a listed factor of
degree dividing `e`. -/
theorem exists_factor_root {F : Type*} [Field F] [Fintype F] (t : F) (p : ℕ) (hpF : (p : F) = 0)
    (hp2 : 2 ≤ p) (hp : p < 2 ^ 20) (gl : List ℤ) (hgl : gl.length = 21)
    (hg : t ^ 21 + evalZ t gl = 0) (facs : List Fac)
    (hfacs : ∀ fac ∈ facs, fac.L.length = fac.deg + 1 ∧ ∀ z ∈ fac.L, z < p)
    (e : ℕ) (he : p ^ e < 2 ^ 64) (hcard : Fintype.card F = p ^ e) (s : List ℕ)
    (h : facCheckE p (negLow p gl) (mkTable p 21 (negLow p gl) 20 (negLow p gl)) facs e s = true) :
    ∃ fac ∈ facs, e % fac.deg = 0 ∧ evalN t fac.L = 0 := by
  have key := facCheckE_sound t p hpF hp2 hp gl hgl hg facs hfacs e he s h
  rw [← hcard, FiniteField.pow_card, sub_self, mul_zero] at key
  obtain ⟨x, hx, hx0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp key.symm)
  obtain ⟨hxf, hxe⟩ := List.mem_filter.mp hx
  exact ⟨x, hxf, by simpa using hxe, hx0⟩

end FurioLombardo.M2
