import FurioLombardo.M3b.SUnits
import FurioLombardo.M3b.Dyadic
import FurioLombardo.M3b.DyadicCert

/-!
# Lane M3b: the named inputs of route R on `K21 ⊂ L ⊂ N`, and the top theorem

Route R of (K1) uses `h(K21) = 1`, `Cl(L)[2] = 0` for `L = K21(√d)` (degree 42) and
`Cl(N)[2] = 0` for `N = L(√e)` (degree 84). Everything that is proved for all number fields is
proved (Chevalley's formula, the characters, the dyadic test, the S-unit transfer); what depends
on the concrete fields is a named Prop below, with the computation that supports it. For the
tower `K21 ⊂ L42 ⊂ N84` all of them are theorems: `FurioLombardo.Discharge.M3b.routeRClassInputs`
(Discharge/M3b/Main.lean) given `Cl(K21)[2] = 1`, which is `Discharge.SelmerBasis.clTwoTrivial_K21`
(from lane M2's `FurioLombardo.M2.Proved.isPrincipalIdealRing_M1K21`).

* `ClTwoTrivial K` for `K = K21`: lane M2 (`h(K21) = 1`).
* `RamBound K L 2`: the primes of `K21` ramified in `L` are the two primes above 2 with `e = 3`
  and `e = 6`, and `d` is positive at the three real places, so no real place ramifies
  (code/selmer-global-bound/chevalley_symbols_plan.gp, .out; code/earlier-computations/class_group_l42_two.gp).
* `DyadicReduction K L`: a valuation `v` of `K21` (the place above 2 with `e = 3`, `f = 1`), a
  ring homomorphism from its valuation ring onto `O_v/4 = (ℤ/4)[π]/(π³ + 2)`, `L = K21(δ)` with
  `δ² = d'` (`d' = d / PI^18`, a unit at `v`), and the images `U = 3 + 3π + 3π²` of the unit
  `u = zk[19] - 1` and `D = 1 + 2π²` of `d'` (code/selmer-global-bound/dyadic_nonnorm_cert.gp, .out). The finite
  check on `O_v/4` is kernel checked (`DyadicCert.cert`), so this Prop only records the reduction
  map computed by PARI (proved for `L42` as `Discharge.M3b.dyadic_L42`).
* `RamBound L N 4`: one prime of `L` above 7 and three real places of `L` ramify in `N`
  (code/earlier-computations/class_group_n84_two.gp, .out).
* `SignPattern L N 3`: at the real places 1, 2, 6 of `L` (ramified in `N`, above the real places
  2, 3, 1 of `K21`) the units `ε₂ ε₄`, `ε₄`, `ε₈` of `K21` (numbering of chevalley_symbols_plan.out; sign
  rows at the real places 1, 2, 3 of `K21`: `ε₂ ε₄` gives `[0,1,1] + [0,0,1] = [0,1,0]`, `ε₄` gives
  `[0,0,1]`, `ε₈` gives `[1,0,0]`) have the diagonal sign pattern.

`routeR_classGroups`: these give `Cl(L)[2] = 0` and `Cl(N)[2] = 0`. `routeR_sUnits`: then every
element of `L` or `N` with even valuation outside a set `S` of primes is an `S`-unit times a
square, the form in which (K1) uses the class groups. The dimension count `dim Sel² = 4` itself
(the local images and the linear algebra of code/earlier-computations/prym_two_descent.gp) is not part
of this lane: it is inside `FurioLombardo.M3a.SelmerInjective` of lane M3a (hypothesis `hsel` of
`FurioLombardo.M3a.hloc_of_xT`), which the concrete route derives from the Selmer bases
`Discharge.SelmerBasis.Assembly.selmerBasis_0`, `selmerBasis_1` (`selmer_and_indep`,
Discharge/M3a/ConcreteRoute.lean).
-/

namespace FurioLombardo.M3b

open NumberField IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

/-- The reduction data at the dyadic place of `K` with `e = 3` for `L = K(δ)`: a valuation `v`,
a ring homomorphism `ρ` from its valuation ring to `O_v/4 = (ℤ/4)[π]/(π³ + 2)`, `δ² = d` with
`v d ≤ 1`, `δ ∉ K`, and a unit `u` of `K` with `ρ u = 3 + 3π + 3π²`, `ρ d = 1 + 2π²`. -/
def DyadicReduction (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Prop :=
  ∃ (v : Valuation K (WithZero (Multiplicative ℤ))) (ρ : v.integer →+* DyadicCert.R) (δ : L)
    (d : v.integer) (u : (𝓞 K)ˣ) (u' : v.integer),
    δ ^ 2 = algebraMap K L d ∧ (∀ k : K, algebraMap K L k ≠ δ) ∧ (u' : K) = ((u : 𝓞 K) : K) ∧
      ρ u' = DyadicCert.elt DyadicCert.U ∧ ρ d = DyadicCert.elt DyadicCert.D

variable {K L N : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
  [NumberField N] [Algebra K L] [Algebra L N]

/-- The dyadic reduction data give a unit of `K` that is not a norm from `L`. -/
theorem nonNormUnit_of_dyadicReduction (h2 : Module.finrank K L = 2)
    (h : DyadicReduction K L) : NonNormUnit K L := by
  obtain ⟨v, ρ, δ, d, u, u', hδ, hδK, hu, hρu, hρd⟩ := h
  refine ⟨u, not_mem_normUnits_of_residue h2 v ρ d hδ hδK u u' hu ?_⟩
  rw [hρu, hρd]
  exact DyadicCert.cert

/-- The named inputs of route R on the tower `K ⊂ L ⊂ N`. -/
structure RouteRClassInputs (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field N] [NumberField N] [Algebra K L] [Algebra L N] : Prop where
  finrank_KL : Module.finrank K L = 2
  finrank_LN : Module.finrank L N = 2
  clK : ClTwoTrivial K
  ramL : RamBound K L 2
  dyadicL : DyadicReduction K L
  ramN : RamBound L N 4
  signsN : SignPattern L N 3

/-- **Top theorem of lane M3b**: `Cl(L)[2] = 0` and `Cl(N)[2] = 0`. -/
theorem routeR_classGroups (h : RouteRClassInputs K L N) : ClTwoTrivial L ∧ ClTwoTrivial N :=
  classGroups_twoTorsion_trivial h.finrank_KL h.finrank_LN h.clK h.ramL
    (nonNormUnit_of_dyadicReduction h.finrank_KL h.dyadicL) h.ramN h.signsN

/-- The form used by (K1): in `L` and in `N`, an element with even valuation outside `S` is an
`S`-unit times a square. -/
theorem routeR_sUnits (h : RouteRClassInputs K L N) :
    (∀ (S : Set (HeightOneSpectrum (𝓞 L))) (x : Lˣ),
      (∀ v ∉ S, Even (count L v (spanSingleton (𝓞 L)⁰ (x : L)))) →
      ∃ s y : Lˣ, x = s * y ^ 2 ∧ ∀ v ∉ S, count L v (spanSingleton (𝓞 L)⁰ (s : L)) = 0) ∧
    (∀ (S : Set (HeightOneSpectrum (𝓞 N))) (x : Nˣ),
      (∀ v ∉ S, Even (count N v (spanSingleton (𝓞 N)⁰ (x : N)))) →
      ∃ s y : Nˣ, x = s * y ^ 2 ∧ ∀ v ∉ S, count N v (spanSingleton (𝓞 N)⁰ (s : N)) = 0) :=
  ⟨fun S x hx => exists_sUnit_mul_sq (routeR_classGroups h).1 S x hx,
    fun S x hx => exists_sUnit_mul_sq (routeR_classGroups h).2 S x hx⟩

end FurioLombardo.M3b
