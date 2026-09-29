import FurioLombardo.M2.Gen
import FurioLombardo.M2.Factor

/-!
# Soundness of the per-prime checker (lane M2)

`checkPrime p N = true` for a prime `p` makes every prime ideal `P` of `𝓞 K21` above `p` with
`p ^ f(P) ≤ Bnd` principal. Route: `p ∤ ResZ` gives `p ∤ exponent θ` (`not_dvd_exponent`), so
Mathlib's Dedekind-Kummer bijection attaches to `P` a monic irreducible factor `Q` of `fZ mod p`
of degree `f(P)` with `P = (p, Q(θ))`. The factor certificate for `e = f(P)`, read in the field
`(ZMod p)[X]/(Q)` of `p^e` elements, gives a listed factor `L` with `Q ∣ L`, hence `Q = L`, and the
generator certificate of `L` makes `P` principal.
-/

namespace FurioLombardo.M2

open Polynomial NumberField Ideal RingOfIntegers

theorem checkSS_get (p T0 : ℕ) (Ts : List ℕ) (facs : List Fac) :
    ∀ (ss : List (List ℕ)) (e0 : ℕ), checkSS p T0 Ts facs e0 ss = true →
      ∀ (i : ℕ) (hi : i < ss.length), facCheckE p T0 Ts facs (e0 + i) ss[i] = true
  | [], _, _, i, hi => absurd hi (by simp)
  | s :: ss, e0, h, i, hi => by
    simp only [checkSS, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := checkSS_get p T0 Ts facs ss (e0 + 1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem facOK_spec (p : ℕ) (fac : Fac) (h : facOK p fac = true) :
    1 ≤ fac.deg ∧ fac.L.length = fac.deg + 1 ∧ fac.L.getLast? = some 1 ∧ ∀ z ∈ fac.L, z < p := by
  unfold facOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A root in `(ZMod p)[X]/(Q)` of a listed factor `L` with `deg L ∣ deg Q` forces `L = Q`. -/
theorem eq_of_root (p : ℕ) [Fact p.Prime] (Q : (ZMod p)[X]) [hQi : Fact (Irreducible Q)]
    (hQm : Q.Monic) (fac : Fac) (hok : facOK p fac = true)
    (hdvd : Q.natDegree % fac.deg = 0)
    (hroot : evalN (AdjoinRoot.root Q) fac.L = 0) :
    toPoly (ZMod p) (fac.L.map fun x : ℕ => (x : ℤ)) = Q := by
  obtain ⟨hd1, hlen, hlast, _⟩ := facOK_spec p fac hok
  have hQ0 : Q ≠ 0 := hQm.ne_zero
  have hlast' : (fac.L.map fun x : ℕ => (x : ℤ)).getLast? = some 1 := by
    rw [List.getLast?_map, hlast]; rfl
  obtain ⟨hLm, hLd⟩ := monic_toPoly (R := ZMod p) _ hlast'
  rw [List.length_map, hlen, Nat.add_sub_cancel] at hLd
  have hmin : minpoly (ZMod p) (AdjoinRoot.root Q) = Q := by
    rw [AdjoinRoot.minpoly_root hQ0, hQm.leadingCoeff, inv_one, map_one, mul_one]
  have haev : aeval (AdjoinRoot.root Q) (toPoly (ZMod p) (fac.L.map fun x : ℕ => (x : ℤ))) = 0 := by
    rw [aeval_toPoly, ← evalN_eq_evalZ]; exact hroot
  have hQL : Q ∣ toPoly (ZMod p) (fac.L.map fun x : ℕ => (x : ℤ)) := hmin ▸ minpoly.dvd _ _ haev
  have hle := natDegree_le_of_dvd hQL hLm.ne_zero
  have hQpos : 0 < Q.natDegree := hQi.out.natDegree_pos
  have hdeg_le : fac.deg ≤ Q.natDegree := Nat.le_of_dvd hQpos (Nat.dvd_of_mod_eq_zero hdvd)
  exact eq_of_monic_of_dvd_of_natDegree_le hQm hLm hQL (by omega)

theorem card_adjoinRoot (p : ℕ) [Fact p.Prime] (Q : (ZMod p)[X]) [Fact (Irreducible Q)]
    (hQ0 : Q ≠ 0) [Fintype (AdjoinRoot Q)] : Fintype.card (AdjoinRoot Q) = p ^ Q.natDegree := by
  rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, (AdjoinRoot.powerBasis hQ0).finrank,
    AdjoinRoot.powerBasis_dim]

/-- Soundness of the per-prime checker. -/
theorem checkData_sound (p : ℕ) (hp : p.Prime) (d : PData) (h : checkData p d = true)
    (P : Ideal (𝓞 K21)) (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K21))
    (hPB : p ^ P.inertiaDeg ℤ ≤ Bnd) : Submodule.IsPrincipal P := by
  have : Fact p.Prime := ⟨hp⟩
  unfold checkData at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hRes, hp3⟩, hp17⟩, hE⟩, hfacs⟩, hss⟩, hgen⟩ := h
  have hRes' : ¬ (p : ℤ) ∣ ResZ := fun h => hRes (Int.emod_eq_zero_of_dvd h)
  have hexp := not_dvd_exponent p hRes'
  have hpDD : ¬ (p : ℤ) ∣ DD := fun h => hRes' (h.trans DD_dvd_ResZ')
  set eqv := primesOverSpanEquivMonicFactorsMod (K := K21) hexp with heqv
  set x := eqv ⟨P, hP⟩ with hx
  have hPx : ((eqv.symm x : primesOver (span {(p : ℤ)}) (𝓞 K21)) : Ideal (𝓞 K21)) = P := by
    rw [hx, Equiv.symm_apply_apply]
  have hdeg : P.inertiaDeg ℤ = x.1.natDegree := by
    rw [← hPx]; exact inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp x.2
  have hf0 : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hQmem := x.2
  simp only [Multiset.mem_toFinset] at hQmem
  classical
  obtain ⟨hQirr, hQm, hQdvd⟩ := (Polynomial.mem_normalizedFactors_iff hf0).mp hQmem
  set Q := x.1 with hQdef
  have : Fact (Irreducible Q) := ⟨hQirr⟩
  have hQ0 : Q ≠ 0 := hQm.ne_zero
  -- the residue degree and the index of the factor certificate
  set e := Q.natDegree with he
  have he1 : 1 ≤ e := hQirr.natDegree_pos
  have hpe : p ^ e ≤ Bnd := hdeg ▸ hPB
  have hlt : e < d.ss.length + 1 :=
    (Nat.pow_lt_pow_iff_right (by omega)).mp (lt_of_le_of_lt hpe hE)
  have hfc := checkSS_get p _ _ d.facs d.ss 1 hss (e - 1) (by omega)
  rw [show 1 + (e - 1) = e by omega] at hfc
  -- the finite field (ZMod p)[X]/(Q)
  have : Module.Finite (ZMod p) (AdjoinRoot Q) := (AdjoinRoot.powerBasis hQ0).finite
  have : Finite (AdjoinRoot Q) := Module.finite_of_finite (ZMod p)
  let : Fintype (AdjoinRoot Q) := Fintype.ofFinite _
  have hcard := card_adjoinRoot p Q hQ0
  have hpF : (p : AdjoinRoot Q) = 0 := by
    rw [← map_natCast (algebraMap (ZMod p) (AdjoinRoot Q)), ZMod.natCast_self, map_zero]
  have hfL : evalZ (AdjoinRoot.root Q) fL = 0 := by
    rw [← aeval_fZ_eq, ← aeval_map_algebraMap (ZMod p), algebraMap_int_eq, ← minpoly_θ]
    obtain ⟨g, hg⟩ := hQdvd
    rw [hg, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have hg := root_fLow _ hfL
  rw [fLow_length] at hg
  obtain ⟨fac, hfac, hfe, hfr⟩ := exists_factor_root (AdjoinRoot.root Q) p hpF (by omega)
    (by omega) fLow fLow_length hg d.facs
    (fun fac hf => ⟨(facOK_spec p fac (hfacs fac hf)).2.1, (facOK_spec p fac (hfacs fac hf)).2.2.2⟩)
    e (lt_of_le_of_lt hpe (by norm_num [Bnd])) hcard _ hfc
  have hLQ := eq_of_root p Q hQm fac (hfacs fac hfac) hfe hfr
  -- P = (p, L(θ))
  have hQ' : map (Int.castRingHom (ZMod p)) (toPoly ℤ (fac.L.map fun x : ℕ => (x : ℤ))) ∈
      monicFactorsMod θ p := by
    rw [map_toPoly, hLQ]; exact x.2
  have hPs : P = span {(p : 𝓞 K21), evalZ θ (fac.L.map fun x : ℕ => (x : ℤ))} := by
    rw [← aeval_toPoly (R := ℤ), ← primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hexp hQ',
      ← hPx]
    congr 2
    exact Subtype.ext (show Q = map (Int.castRingHom (ZMod p))
      (toPoly ℤ (fac.L.map fun x : ℕ => (x : ℤ))) by rw [map_toPoly, hLQ])
  have : P.IsPrime := hP.1
  have hPZ : ∀ n : ℤ, (n : 𝓞 K21) ∈ P → (p : ℤ) ∣ n := by
    intro n hn
    have hover : span {(p : ℤ)} = P.under ℤ := hP.2.over
    have : n ∈ P.under ℤ := by
      rw [under_def, mem_comap, algebraMap_int_eq, eq_intCast]; exact hn
    rw [← hover, mem_span_singleton] at this
    exact this
  exact genCheck_sound p hp (by omega) hpDD fac (hfacs fac hfac) (hgen fac hfac) P hPZ hPs

theorem checkPrime_sound (p N : ℕ) (hp : p.Prime) (h : checkPrime p N = true)
    (P : Ideal (𝓞 K21)) (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K21))
    (hPB : p ^ P.inertiaDeg ℤ ≤ Bnd) : Submodule.IsPrincipal P :=
  checkData_sound p hp _ h P hP hPB

end FurioLombardo.M2
