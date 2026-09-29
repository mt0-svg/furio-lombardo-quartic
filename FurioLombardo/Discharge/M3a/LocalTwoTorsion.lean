import Mathlib
import FurioLombardo.M3a.Hypotheses
import FurioLombardo.Discharge.M3a.TwoTorsionClass

/-!
# (L1) `LocalTwoTorsion` from two local facts (discharge of M3a, WP1)

For a field `K` and `f : K[X]` with `GoodSextic f`, and a monic quadratic divisor `q` of `f` with
`T = [⟨q, Y⟩]` (M3a's `Tpt`):

* `sq_eq_one_of_unique`: if `q` is the only monic quadratic divisor of `f`, then `A(K)[2] = {1, T}`;
* `localTwoTorsion_of_unique`: if moreover `T` is not a square in `A(K)`, then every 2-power
  torsion point of `A(K)` is `1` or `T`, which is M3a's `LocalTwoTorsion f T`;
* `jacMap_Tpt`: the base change of `T` along `σ : k →+* k_v` is the point `T` of `f.map σ`;
* `localTwoTorsion_route`: the field `localTwoTorsion` of M3a's `Inputs` from the two local facts
  at `v` (uniqueness of the monic quadratic divisor of `f_v`, `T_v` not a square);
* `not_sq_of_muJ_ne_one`, `localTwoTorsion_route_of_mu`: `T_v` is not a square as soon as its
  `x - T` image `μ(T_v)` is nontrivial.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.M3a

variable {K : Type*} [Field K]

/-- If `q` is the only monic quadratic divisor of `f`, the 2-torsion of `A(K)` is `{1, T}`. -/
theorem sq_eq_one_of_unique (f : K[X]) [GoodSextic f] {q : K[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2)
    (huniq : ∀ u : K[X], u.Monic → u.natDegree = 2 → u ∣ f → u = q) {c : Jac f}
    (hc : c ^ 2 = 1) : c = 1 ∨ c = Tpt f hq hqf hdeg := by
  rcases jac_sq_eq_one f hc with h | ⟨u, hu, hudeg, huf, hcu⟩
  · exact Or.inl h
  right
  obtain rfl := huniq u hu hudeg huf
  apply Subtype.ext
  rw [hcu, coe_Tpt]

/-- (L1) over any field: if `q` is the only monic quadratic divisor of `f` and `T` is not a
square in `A(K)`, every 2-power torsion point of `A(K)` is `1` or `T`. -/
theorem localTwoTorsion_of_unique (f : K[X]) [GoodSextic f] {q : K[X]} (hq : q.Monic)
    (hqf : q ∣ f) (hdeg : q.natDegree = 2)
    (huniq : ∀ u : K[X], u.Monic → u.natDegree = 2 → u ∣ f → u = q)
    (hT : ∀ R : Jac f, R ^ 2 ≠ Tpt f hq hqf hdeg) :
    LocalTwoTorsion f (Tpt f hq hqf hdeg) := by
  have key : ∀ n : ℕ, ∀ b : Jac f, b ^ (2 ^ n) = 1 → b = 1 ∨ b = Tpt f hq hqf hdeg := by
    intro n
    induction n with
    | zero => intro b hb; left; simpa using hb
    | succ n ih =>
      intro b hb
      have hb' : (b ^ 2) ^ (2 ^ n) = 1 := by rw [← pow_mul, ← pow_succ']; exact hb
      rcases ih _ hb' with h1 | h1
      · exact sq_eq_one_of_unique f hq hqf hdeg huniq h1
      · exact absurd h1 (hT b)
  rintro b ⟨n, hn⟩
  exact key n b hn

/-- The base change of `T = [⟨q, Y⟩]` along `σ` is `T = [⟨q^σ, Y⟩]` for `f^σ`. -/
theorem jacMap_Tpt {k kv : Type*} [Field k] [Field kv] (σ : k →+* kv) (f : k[X]) [GoodSextic f]
    [GoodSextic (f.map σ)] {q : k[X]} (hq : q.Monic) (hqf : q ∣ f) (hdeg : q.natDegree = 2) :
    jacMap σ f (Tpt f hq hqf hdeg) =
      Tpt (f.map σ) (hq.map σ) (Polynomial.map_dvd σ hqf) (by rw [natDegree_map, hdeg]) := by
  apply Subtype.ext
  change picMap σ f (Tpt f hq hqf hdeg : Pic f) = _
  rw [coe_Tpt, coe_Tpt]
  apply picMap_mk0
  change mumford (f.map σ) (q.map σ) 0 = (mumford f q 0).map (baseChange σ f)
  rw [mumford, mumford, Ideal.map_span, Set.image_pair, baseChange_algebraMap, map_sub,
    baseChange_Yc, baseChange_algebraMap, Polynomial.map_zero]

/-- The field `localTwoTorsion` of M3a's `Inputs`, from two local facts at `v`: `q^σ` is the only
monic quadratic divisor of `f^σ`, and `T_v` is not a square in `A(k_v)`. -/
theorem localTwoTorsion_route {k kv : Type*} [Field k] [Field kv] (σ : k →+* kv) (f : k[X])
    [GoodSextic f] [GoodSextic (f.map σ)] {q : k[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2)
    (huniq : ∀ u : kv[X], u.Monic → u.natDegree = 2 → u ∣ f.map σ → u = q.map σ)
    (hT : ∀ R : Jac (f.map σ), R ^ 2 ≠ jacMap σ f (Tpt f hq hqf hdeg)) :
    LocalTwoTorsion (f.map σ) (jacMap σ f (Tpt f hq hqf hdeg)) := by
  rw [jacMap_Tpt] at hT ⊢
  exact localTwoTorsion_of_unique (f.map σ) _ _ _ huniq hT

/-- A point with nontrivial `x - T` image is not a square. -/
theorem not_sq_of_muJ_ne_one (f : K[X]) [GoodSextic f] {T : Jac f} (h : muJ f T ≠ 1)
    (R : Jac f) : R ^ 2 ≠ T := fun hR => h (hR ▸ muJ_sq f R)

/-- `localTwoTorsion_route` with the non-square condition replaced by `μ(T_v) ≠ 1`. -/
theorem localTwoTorsion_route_of_mu {k kv : Type*} [Field k] [Field kv] (σ : k →+* kv)
    (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)] {q : k[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2)
    (huniq : ∀ u : kv[X], u.Monic → u.natDegree = 2 → u ∣ f.map σ → u = q.map σ)
    (hmu : Hmap σ f (muJ f (Tpt f hq hqf hdeg)) ≠ 1) :
    LocalTwoTorsion (f.map σ) (jacMap σ f (Tpt f hq hqf hdeg)) :=
  localTwoTorsion_route σ f hq hqf hdeg huniq
    (not_sq_of_muJ_ne_one (f.map σ) (by rwa [muJ_jacMap]))

end FurioLombardo.Discharge.M3a
