import FurioLombardo.M2.Factor
import FurioLombardo.M2.Norm

/-!
# Residue fields of 𝓞 K21 and factor certificates (lane M2)

For a prime `P` above `p`, `𝓞 K21 ⧸ P` is a field with `p ^ f(P)` elements. A factor certificate
for `e = f(P)` and a root `x` (in `𝓞 K21`) of a monic `g` of degree 21 gives a listed factor `L`
with `L(x) ∈ P` (`residue_factor`).
-/

namespace FurioLombardo.M2

open Polynomial NumberField Ideal

theorem primesOver_facts {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K21)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K21)) :
    P.IsMaximal ∧ (p : 𝓞 K21) ∈ P ∧ absNorm P = p ^ P.inertiaDeg ℤ := by
  have hPp : P.IsPrime := hP.1
  have : P.LiesOver (span {(p : ℤ)}) := hP.2
  have hne : P ≠ ⊥ := ne_bot_of_mem_primesOver (by simp [hp.ne_zero]) hP
  refine ⟨hPp.isMaximal hne, ?_, ?_⟩
  · have hover : span {(p : ℤ)} = P.under ℤ := (inferInstance : P.LiesOver _).over
    have : (p : ℤ) ∈ P.under ℤ := hover ▸ mem_span_singleton_self _
    rw [under_def, mem_comap] at this
    simpa using this
  · have := natAbs_pow_inertiaDeg (p : ℤ) P
    simpa using this.symm

theorem residue_factor {p : ℕ} (hp : p.Prime) (hp20 : p < 2 ^ 20) {P : Ideal (𝓞 K21)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K21)) (hpe : p ^ P.inertiaDeg ℤ < 2 ^ 64)
    (x : 𝓞 K21) (gl : List ℤ) (hgl : gl.length = 21) (hx : x ^ 21 + evalZ x gl = 0)
    (facs : List Fac) (hfacs : ∀ fac ∈ facs, fac.L.length = fac.deg + 1 ∧ ∀ z ∈ fac.L, z < p)
    (s : List ℕ)
    (h : facCheckE p (negLow p gl) (mkTable p 21 (negLow p gl) 20 (negLow p gl)) facs
      (P.inertiaDeg ℤ) s = true) :
    ∃ fac ∈ facs, P.inertiaDeg ℤ % fac.deg = 0 ∧
      evalZ x (fac.L.map fun z : ℕ => (z : ℤ)) ∈ P := by
  obtain ⟨hmax, hpP, hnorm⟩ := primesOver_facts hp hP
  let : Field (𝓞 K21 ⧸ P) := Ideal.Quotient.field P
  have hcardN : Nat.card (𝓞 K21 ⧸ P) = p ^ P.inertiaDeg ℤ := by
    rw [← hnorm, absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 K21 ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcardN]; exact pow_ne_zero _ hp.ne_zero)
  let : Fintype (𝓞 K21 ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K21 ⧸ P) = p ^ P.inertiaDeg ℤ := by
    rw [← Nat.card_eq_fintype_card, hcardN]
  have hpF : ((p : ℕ) : 𝓞 K21 ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P)]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hg : (Ideal.Quotient.mk P x) ^ 21 + evalZ (Ideal.Quotient.mk P x) gl = 0 := by
    rw [← evalZ_map, ← map_pow, ← map_add, hx, map_zero]
  obtain ⟨fac, hf, hfe, hfr⟩ := exists_factor_root (Ideal.Quotient.mk P x) p hpF hp.two_le hp20
    gl hgl hg facs hfacs _ hpe hcard s h
  refine ⟨fac, hf, hfe, ?_⟩
  rw [evalN_eq_evalZ, ← evalZ_map] at hfr
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfr

end FurioLombardo.M2
