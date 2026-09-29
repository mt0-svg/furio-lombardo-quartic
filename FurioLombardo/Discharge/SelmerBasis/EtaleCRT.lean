import Mathlib

/-!
# `K[X]/(g)` as a product of two fields (for the relation at v)

For `g = p q` with `p`, `q` coprime, two ring maps `ev1 : K[X]/(g) → F1`, `ev2 : K[X]/(g) → F2`
whose kernels on `K[X]` are the multiples of `p` and of `q` give an injective map to `F1 × F2`
(`injective_prod_of_coprime`); with `dim F1 + dim F2 = deg g` it is bijective
(`bijective_of_injective_finrank`). The kernels come from irreducibility: a root `τ` of an
irreducible `p` has `p ∣ P` whenever `P(τ) = 0` (`dvd_of_aeval_eq_zero`).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial

theorem dvd_of_aeval_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L] {p : K[X]}
    (hp : Irreducible p) {τ : L} (hτ : aeval τ p = 0) {P : K[X]} (hP : aeval τ P = 0) : p ∣ P := by
  have hp_ne_zero : p ≠ 0 := hp.ne_zero
  have hτ_mem : τ ∈ p.rootSet L := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hp_ne_zero, hτ⟩
  have hτ_alg : IsAlgebraic K τ := isAlgebraic_of_mem_rootSet hτ_mem
  have hτ_int : IsIntegral K τ := hτ_alg.isIntegral
  have h_min_dvd_p : minpoly K τ ∣ p := minpoly.dvd K τ hτ
  have h_min_dvd_P : minpoly K τ ∣ P := minpoly.dvd K τ hP
  have h_min_irred : Irreducible (minpoly K τ) := minpoly.irreducible hτ_int
  have h_assoc : Associated (minpoly K τ) p :=
    h_min_irred.associated_of_dvd hp h_min_dvd_p
  exact (h_assoc.dvd_iff_dvd_left.mp h_min_dvd_P)

theorem injective_prod_of_coprime {K F1 F2 : Type*} [Field K] [CommRing F1] [CommRing F2]
    {p q : K[X]} (hpq : IsCoprime p q) (ev1 : AdjoinRoot (p * q) →+* F1)
    (ev2 : AdjoinRoot (p * q) →+* F2)
    (h1 : ∀ P : K[X], ev1 (AdjoinRoot.mk (p * q) P) = 0 → p ∣ P)
    (h2 : ∀ P : K[X], ev2 (AdjoinRoot.mk (p * q) P) = 0 → q ∣ P) :
    Function.Injective (RingHom.prod ev1 ev2) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro y hy
  have hy' : (RingHom.prod ev1 ev2) y = 0 := hy
  rw [RingHom.prod_apply] at hy'
  have hy1 : ev1 y = 0 := by
    have := congrArg Prod.fst hy'
    simpa using this
  have hy2 : ev2 y = 0 := by
    have := congrArg Prod.snd hy'
    simpa using this
  obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective y
  rw [← hP] at hy1 hy2
  have hp : p ∣ P := h1 P hy1
  have hq : q ∣ P := h2 P hy2
  have hpq_mul : p * q ∣ P := IsCoprime.mul_dvd hpq hp hq
  rw [← hP, AdjoinRoot.mk_eq_zero]
  exact hpq_mul

/-- An injective `K`-algebra map from `K[X]/(g)` to an algebra of dimension `deg g` is bijective. -/
theorem bijective_of_injective_finrank {K : Type*} [Field K] {g : K[X]} (hg : g ≠ 0)
    {A : Type*} [Ring A] [Algebra K A] [FiniteDimensional K A] (φ : AdjoinRoot g →ₐ[K] A)
    (hφ : Function.Injective φ) (hdim : Module.finrank K A = g.natDegree) :
    Function.Bijective φ := by
  let pb := AdjoinRoot.powerBasis hg
  haveI : FiniteDimensional K (AdjoinRoot g) := pb.finite
  have hfinrank : Module.finrank K (AdjoinRoot g) = g.natDegree := by
    rw [PowerBasis.finrank pb, AdjoinRoot.powerBasis_dim hg]
  have hfinrank_eq : Module.finrank K (AdjoinRoot g) = Module.finrank K A := by
    rw [hfinrank, hdim]
  have hsurj : Function.Surjective φ :=
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap) hfinrank_eq).mp hφ)
  exact ⟨hφ, hsurj⟩

end FurioLombardo.Discharge.SelmerBasis
