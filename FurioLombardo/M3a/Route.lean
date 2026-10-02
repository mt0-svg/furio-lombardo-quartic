import Mathlib
import FurioLombardo.M3a.Hypotheses

/-!
# The route of the proof on the concrete model (lane M3a)

The abstract chain (`Sections.lean`, `StollSat.lean`) instantiated with the ideal class model of
`A = Jac(F_δ)` over `k` and `k_v` (`A(k) = Jac f`, `A(k_v) = Jac (f.map σ)`, `ι = jacMap σ f`),
the `x - T` map `muJ` (`XminusT.lean`) and the 2-torsion point `T = [⟨q, Y⟩]` (`TwoTorsion.lean`).

* `hloc_jac`: the global part. From (K1) and (K2) (`XTKernel`, `SelmerInjective`) and the proved
  facts `muJ_sq` (the easy direction `μ_v(2A(k_v)) = 0`) and `muJ_jacMap` (naturality): a point
  of `A(k)` divisible by 2 in `A(k_v)` is divisible by 2 in `A(k)`.
* `hker_jac`: the local kernel. From (L1) and (L2): `ker λ ⊆ 2A(k_v) ∪ (T_v + 2A(k_v))`.
* `two_nsmul_Tpt`: `2T = 0`.
  These three are the global inputs `hloc`, `hker`, `hT2` of lane M4's local chain.
* `twistConclusion_of_inputs`, `twistConclusion_of_route`: the local argument for one twist.
* `onlyFourPoints_of_route`: the conclusion. The descent (`Descent`, lane M1) and the
  route for the twists `δ0` (known points `(0:0:1)`, `(2:0:1)`) and `δ1` (`(1:1:1)`, `(-1:0:1)`)
  give the frozen statement `FurioLombardo.OnlyFourPoints`.
-/

open Polynomial
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.M3a.Route

variable {k kv : Type*} [Field k] [Field kv]

/-- The global part: local divisibility by 2 implies global divisibility by 2, from (K1), (K2)
and the proved properties of the `x - T` map. Corollary 5.9 of the paper. -/
theorem hloc_jac (σ : k →+* kv) (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)]
    (hK1 : XTKernel f) (hK2 : SelmerInjective σ f) :
    ∀ Q : Additive (Jac f), (∃ b : Additive (Jac (f.map σ)), iotaA σ f Q = (2 : ℕ) • b) →
      ∃ Q' : Additive (Jac f), Q = (2 : ℕ) • Q' := by
  refine hloc_of_xT (HA := Additive (H f)) (HB := Additive (H (f.map σ)))
    (iotaA σ f) (muJ f).toAdditive (muJ (f.map σ)).toAdditive
    (Hmap σ f).toAdditive ?_ ?_ ?_ ?_
  · intro Q
    exact congrArg Additive.ofMul (muJ_jacMap σ f (Additive.toMul Q))
  · intro b
    exact congrArg Additive.ofMul (muJ_sq (f.map σ) (Additive.toMul b))
  · intro Q hQ
    obtain ⟨R, hR⟩ := hK1 (Additive.toMul Q) (congrArg Additive.toMul hQ)
    exact ⟨Additive.ofMul R, congrArg Additive.ofMul hR⟩
  · intro Q hQ
    exact congrArg Additive.ofMul (hK2 (Additive.toMul Q) (congrArg Additive.toMul hQ))

/-- The local kernel: from (L1) and (L2), a point of `A(k_v)` killed by the logarithm is in `2A(k_v)`
or in `T_v + 2A(k_v)`. -/
theorem hker_jac {V : Type*} [AddCommGroup V] (f : kv[X]) [GoodSextic f] (Tv : Jac f)
    (lam : Additive (Jac f) →+ V) (hL1 : LocalTwoTorsion f Tv) (hL2 : LogKernelTorsion f lam) :
    ∀ b : Additive (Jac f), lam b = 0 → ∃ c : Additive (Jac f),
      b = (2 : ℕ) • c ∨ b = Additive.ofMul Tv + (2 : ℕ) • c := by
  refine hker_of_torsion lam (Additive.ofMul Tv) ?_ hL2
  rintro b ⟨n, hn⟩
  rcases hL1 (Additive.toMul b) ⟨n, congrArg Additive.toMul hn⟩ with h | h
  · exact Or.inl (congrArg Additive.ofMul h)
  · exact Or.inr (congrArg Additive.ofMul h)

/-- `2T = 0` in `A(k)`, additively. -/
theorem two_nsmul_Tpt (f : k[X]) [GoodSextic f] {q : k[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2) : (2 : ℕ) • Additive.ofMul (Tpt f hq hqf hdeg) = 0 :=
  congrArg Additive.ofMul (Tpt_sq f hq hqf hdeg)

theorem two_smul_eq_zero_V (v : Fin 6 → ℤ_[2]) (hv : (2 : ℤ_[2]) • v = 0) : v = 0 := by
  funext i
  have h := congrFun hv i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

variable [Algebra ℚ k]

/-- The local argument for one twist, from its inputs. Theorem 8.1 of the paper. -/
theorem twistConclusion_of_inputs {σ : k →+* kv} {f : k[X]} [GoodSextic f] [GoodSextic (f.map σ)]
    {q : k[X]} {hq : q.Monic} {hqf : q ∣ f} {hdeg : q.natDegree = 2}
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k} {Pa Pb : ℚ × ℚ × ℚ}
    {φ : DPoint k M1 M2 M3 δ → Jac f} {xa xb : DPoint k M1 M2 M3 δ}
    {lam : Additive (Jac (f.map σ)) →+ (Fin 6 → ℤ_[2])} {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])}
    {W : Set (Fin 6 → ℤ_[2])} (h : Inputs σ f hq hqf hdeg M1 M2 M3 δ Pa Pb φ xa xb lam Λ S W) :
    TwistConclusion k M1 M2 M3 δ Pa Pb := by
  have key := twist_sat two_smul_eq_zero_V (iotaA σ f) lam Λ S W
    (Additive.ofMul (Tpt f hq hqf hdeg)) (fun d : Lift M1 M2 M3 δ => Additive.ofMul (φ d.1))
    (Additive.ofMul (φ xa)) (Additive.ofMul (φ xb)) (fun d => GoodLift Pa Pb d.1)
    h.logRange h.saturated h.mem_a h.mem_b (two_nsmul_Tpt f hq hqf hdeg)
    (hloc_jac σ f h.xtKernel h.selmerInjective)
    (hker_jac (f.map σ) _ lam h.localTwoTorsion h.logKernelTorsion) h.selmerW h.quarter
    h.coverIII h.knownZero
  intro d x y z hd
  exact key ⟨d, x, y, z, hd⟩ x y z hd

/-- The local argument for one twist. -/
theorem twistConclusion_of_route {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ : k}
    {Pa Pb : ℚ × ℚ × ℚ} (h : TwistRoute M1 M2 M3 δ Pa Pb) : TwistConclusion k M1 M2 M3 δ Pa Pb := by
  obtain ⟨kv, _, σ, f, _, _, q, hq, hqf, hdeg, φ, xa, xb, lam, Λ, S, W, hin⟩ := h
  exact twistConclusion_of_inputs hin

/-- The conclusion: the descent and the route for the two twists give
the frozen statement `FurioLombardo.OnlyFourPoints`. -/
theorem onlyFourPoints_of_route {M1 M2 M3 : Matrix (Fin 3) (Fin 3) k} {δ0 δ1 : k}
    (hdesc : Descent k M1 M2 M3 δ0 δ1) (h0 : TwistRoute M1 M2 M3 δ0 (0, 0, 1) (2, 0, 1))
    (h1 : TwistRoute M1 M2 M3 δ1 (1, 1, 1) (-1, 0, 1)) : FurioLombardo.OnlyFourPoints :=
  onlyFourPoints_of_twists hdesc (twistConclusion_of_route h0) (twistConclusion_of_route h1)

end FurioLombardo.M3a.Route
