import Mathlib
import FurioLombardo.Discharge.M4Box.Comp.AbelPrym
import FurioLombardo.Discharge.KvArith.Cantor
import FurioLombardo.Discharge.M3a.AbelPrymExists

/-!
# Soundness of the Abel-Prym program over a field (lane lean-m4box, D4)

`apPhi_spec`: over a field `L` with `2 ≠ 0`, for symmetric `M1, M2, M3`, `δ ≠ 0`,
`f = -δ det(M1 + 2t M2 + t² M3)` and a point `x` of `D_δ`, a successful run of `apPhi` on the exact
values (`fieldOps L`) gives a certificate `c : AbelPrym.Cert M1 M2 M3 δ f x` (lane M3a's
`Cert.ofEntry`) with `bruinU c.T = m.u` and `c.V = m.v`, so Bruin's class at `x` is the class of the
Mumford pair `m`.

The steps: `apPhi_field` reads the run (the three inverted quantities are nonzero and `m` is given by
the formulas); `kerVec_dot` (the cofactor vector is a kernel vector of the rows, a determinant with a
repeated row); `polarD_eq_dot` (the rows are `W ↦ polarD i P W` for symmetric forms); `quadD_eq`,
`nv_eq` and `hodge_eq` (the quantities of the program are those of the certificate); `gAg_eq`
(the entry `(l, 3)` of `G A G` is the cubic `e₀ + e₁ t + e₂ t² + e₃ t³`) and its division by `U`.
-/

open Polynomial Matrix
open FurioLombardo.Discharge.KvArith FurioLombardo.Discharge.M3a.AbelPrym FurioLombardo.M3a

namespace FurioLombardo.Discharge.M4Box

variable {L : Type*} [Field L]

/-! ## Inputs from a point -/

/-- The entries of a matrix, read as a symmetric one. -/
def Sym3.ofMatrix (M : Matrix (Fin 3) (Fin 3) L) : Sym3 L := ⟨M 0 0, M 0 1, M 0 2, M 1 1, M 1 2, M 2 2⟩

/-- The input of the program at a point of `D_δ`. -/
def APIn.ofPoint (M1 M2 M3 : Matrix (Fin 3) (Fin 3) L) (δ : L) (x : DPoint L M1 M2 M3 δ) : APIn L :=
  ⟨Sym3.ofMatrix M1, Sym3.ofMatrix M2, Sym3.ofMatrix M3, δ, x.p 0, x.p 1, x.p 2, x.r, x.s⟩

/-- A `Vec5` as a vector of the ambient space of `D_δ`. -/
def Vec5.toV5 (v : Vec5 L) : V5 L := (![v.c0, v.c1, v.c2], v.c3, v.c4)

/-- The dot product of two `Vec5`. -/
def Vec5.dot (v w : Vec5 L) : L := v.c0 * w.c0 + v.c1 * w.c1 + v.c2 * w.c2 + v.c3 * w.c3 + v.c4 * w.c4

/-- The index `l` of the minor as a row of `⋆A`. -/
def lFin : ℕ → Fin 4
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The index `jN` as a coordinate. -/
def jFin : ℕ → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-! ## The run over a field -/

theorem fieldOps_inv_of_ne {a : L} (ha : a ≠ 0) : (fieldOps L).inv a = some a⁻¹ := by
  unfold fieldOps
  simp [ha]

theorem fieldOps_inv_zero : (fieldOps L).inv 0 = none := by
  unfold fieldOps
  simp

/-- **The run over a field**: the inverted quantities are nonzero and the output is given by the
formulas. -/
theorem apPhi_field {prm : APPrm} {x : APIn L} {m : Mum L}
    (h : apPhi (fieldOps L) prm x = some m) :
    trip (apNv (fieldOps L) x) prm.jN ≠ 0 ∧
      (apA (fieldOps L) x (apT (fieldOps L) x prm.kd)).2.2 ≠ 0 ∧
      minor2 (fieldOps L) x.p0 x.p1 x.p2 (apT (fieldOps L) x prm.kd).c0
        (apT (fieldOps L) x prm.kd).c1 (apT (fieldOps L) x prm.kd).c2 prm.l ≠ 0 ∧
      let T := apT (fieldOps L) x prm.kd
      let a := apA (fieldOps L) x T
      let u1 := (a.2.1 + a.2.1) * a.2.2⁻¹
      let u0 := a.1 * a.2.2⁻¹
      let e := apE (fieldOps L) x T prm.l
      let ic := (minor2 (fieldOps L) x.p0 x.p1 x.p2 T.c0 T.c1 T.c2 prm.l)⁻¹
      m = ⟨u0, u1, (e.c0 - e.c2 * u0 + e.c3 * (u1 * u0)) * ic,
        (e.c1 - e.c2 * u1 + e.c3 * (u1 * u1 - u0)) * ic⟩ := by
  unfold apPhi at h
  by_cases h1 : trip (apNv (fieldOps L) x) prm.jN = 0
  · rw [h1, fieldOps_inv_zero] at h
    simp at h
  rw [fieldOps_inv_of_ne h1] at h
  by_cases h2 : (apA (fieldOps L) x (apT (fieldOps L) x prm.kd)).2.2 = 0
  · simp only [Option.bind_eq_bind, Option.bind_some] at h
    rw [h2, fieldOps_inv_zero] at h
    simp at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  rw [fieldOps_inv_of_ne h2] at h
  by_cases h3 : minor2 (fieldOps L) x.p0 x.p1 x.p2 (apT (fieldOps L) x prm.kd).c0
      (apT (fieldOps L) x prm.kd).c1 (apT (fieldOps L) x prm.kd).c2 prm.l = 0
  · simp only [Option.bind_some] at h
    rw [h3, fieldOps_inv_zero] at h
    simp at h
  simp only [Option.bind_some] at h
  rw [fieldOps_inv_of_ne h3] at h
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
  refine ⟨h1, h2, h3, ?_⟩
  rw [← h]
  rfl

/-! ## Exact identities -/

theorem fo_add (a b : L) : (fieldOps L).add a b = a + b := rfl
theorem fo_sub (a b : L) : (fieldOps L).sub a b = a - b := rfl
theorem fo_mul (a b : L) : (fieldOps L).mul a b = a * b := rfl
theorem fo_neg (a : L) : (fieldOps L).neg a = -a := rfl
theorem fo_zero : (fieldOps L).zero = 0 := by simp [Ops.zero, fieldOps]

/-- **The cofactor vector is a kernel vector of the three rows.** -/
theorem kerVec_dot (J0 J1 J2 : Vec5 L) (kd : ℕ) :
    J0.dot (kerVec (fieldOps L) J0 J1 J2 kd) = 0 ∧ J1.dot (kerVec (fieldOps L) J0 J1 J2 kd) = 0 ∧
      J2.dot (kerVec (fieldOps L) J0 J1 J2 kd) = 0 := by
  rcases kd with _ | _ | _ | _ | kd <;>
  simp only [kerVec, minor3, det3, Vec5.get, Vec5.dot, fo_add, fo_sub, fo_mul, fo_neg, fo_zero] <;>
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem sym_entries {M : Matrix (Fin 3) (Fin 3) L} (h : Mᵀ = M) :
    M 1 0 = M 0 1 ∧ M 2 0 = M 0 2 ∧ M 2 1 = M 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun (congrFun h 0) 1; rwa [transpose_apply] at this
  · have := congrFun (congrFun h 0) 2; rwa [transpose_apply] at this
  · have := congrFun (congrFun h 1) 2; rwa [transpose_apply] at this

variable {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

/-- The rows of the program are the tangent forms `W ↦ polarD i P W`. -/
theorem polarD_eq_dot (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (x : DPoint L M1 M2 M3 δ)
    (W : Vec5 L) :
    polarD ![M1, M2, M3] δ 0 (pt x) W.toV5 = (apJ0 (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x)).dot W ∧
      polarD ![M1, M2, M3] δ 1 (pt x) W.toV5 =
        (apJ1 (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x)).dot W ∧
      polarD ![M1, M2, M3] δ 2 (pt x) W.toV5 =
        (apJ2 (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x)).dot W := by
  obtain ⟨a10, a20, a21⟩ := sym_entries h1
  obtain ⟨b10, b20, b21⟩ := sym_entries h2
  obtain ⟨c10, c20, c21⟩ := sym_entries h3
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [polarD, pt, Vec5.toV5, apJ0, apJ1, apJ2, tanRow, Sym3.mulVec, Sym3.ofMatrix, APIn.ofPoint,
    Vec5.dot, dotProduct, mulVec, Fin.sum_univ_three, fo_add, fo_sub, fo_mul, fo_neg, fo_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    a10, a20, a21, b10, b20, b21, c10, c20, c21] <;> ring

/-- **The tangent vector**: `T` is tangent to `D_δ` at `x`. -/
theorem apT_tangent (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (x : DPoint L M1 M2 M3 δ)
    (kd : ℕ) (i : Fin 3) :
    polarD ![M1, M2, M3] δ i (pt x) (apT (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) kd).toV5 = 0 := by
  obtain ⟨e0, e1, e2⟩ := polarD_eq_dot h1 h2 h3 x (apT (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) kd)
  obtain ⟨k0, k1, k2⟩ := kerVec_dot (apJ0 (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x))
    (apJ1 (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x)) (apJ2 (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x)) kd
  fin_cases i
  · exact e0.trans k0
  · exact e1.trans k1
  · exact e2.trans k2

/-- The `a_i` of the program are `quadD i T`. -/
theorem quadD_eq (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (x : DPoint L M1 M2 M3 δ)
    (T : Vec5 L) :
    quadD ![M1, M2, M3] δ 0 T.toV5 = (apA (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) T).1 ∧
      quadD ![M1, M2, M3] δ 1 T.toV5 = (apA (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) T).2.1 ∧
      quadD ![M1, M2, M3] δ 2 T.toV5 = (apA (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) T).2.2 := by
  obtain ⟨a10, a20, a21⟩ := sym_entries h1
  obtain ⟨b10, b20, b21⟩ := sym_entries h2
  obtain ⟨c10, c20, c21⟩ := sym_entries h3
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [quadD, Vec5.toV5, apA, Sym3.quad, Sym3.mulVec, Sym3.ofMatrix, APIn.ofPoint,
    dotProduct, mulVec, Fin.sum_univ_three, fo_add, fo_sub, fo_mul, fo_neg,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    a10, a20, a21, b10, b20, b21, c10, c20, c21] <;> ring

/-- The rank vector of the program. -/
theorem nv_eq (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (x : DPoint L M1 M2 M3 δ) (j : ℕ) :
    (((pt x).2.2 ^ 2 • ![M1, M2, M3] 0 - (2 * (pt x).2.1 * (pt x).2.2) • ![M1, M2, M3] 1 +
      (pt x).2.1 ^ 2 • ![M1, M2, M3] 2) *ᵥ (pt x).1) (jFin j) =
      trip (apNv (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x)) j := by
  obtain ⟨a10, a20, a21⟩ := sym_entries h1
  obtain ⟨b10, b20, b21⟩ := sym_entries h2
  obtain ⟨c10, c20, c21⟩ := sym_entries h3
  rcases j with _ | _ | j <;>
  simp only [jFin, trip, apNv, pt, Sym3.mulVec, Sym3.ofMatrix, APIn.ofPoint, mulVec, dotProduct,
    Fin.sum_univ_three, fo_add, fo_sub, fo_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, a10, a20, a21, b10, b20, b21, c10, c20, c21] <;> ring

/-- The inverted minor is the constant entry `(l, 3)` of `⋆A`. -/
theorem hodge_eq (x : DPoint L M1 M2 M3 δ) (T : Vec5 L) (l : ℕ) :
    hodge (plucker (plk (pt x)) (plk T.toV5)) (lFin l) 3 =
      C (minor2 (fieldOps L) (x.p 0) (x.p 1) (x.p 2) T.c0 T.c1 T.c2 l) := by
  rcases l with _ | _ | l
  · rw [show lFin 0 = 0 from rfl, hodge_plk_03]; rfl
  · rw [show lFin (0 + 1) = 1 from rfl, hodge_plk_13]; rfl
  · rw [show lFin (l + 1 + 1) = 2 from rfl, hodge_plk_23]; rfl

theorem lFin_ne (l : ℕ) : lFin l ≠ 3 := by
  rcases l with _ | _ | l <;> simp only [lFin] <;> decide


/-- The entry `(l, 3)` of `G A G` for `l < 3`. -/
theorem gram_plucker_gram_l3 (M1 M2 M3 : Matrix (Fin 3) (Fin 3) L) (δ : L) (a b : Fin 4 → L[X])
    (l : ℕ) : (gram M1 M2 M3 δ * plucker a b * gram M1 M2 M3 δ) (lFin l) 3 =
      -C δ * (pencil M1 M2 M3 (jFin l) 0 * (a 0 * b 3 - b 0 * a 3) +
        pencil M1 M2 M3 (jFin l) 1 * (a 1 * b 3 - b 1 * a 3) +
        pencil M1 M2 M3 (jFin l) 2 * (a 2 * b 3 - b 2 * a 3)) := by
  rcases l with _ | _ | l
  · show (gram M1 M2 M3 δ * plucker a b * gram M1 M2 M3 δ) 0 3 = -C δ * (pencil M1 M2 M3 0 0 *
      (a 0 * b 3 - b 0 * a 3) + pencil M1 M2 M3 0 1 * (a 1 * b 3 - b 1 * a 3) +
        pencil M1 M2 M3 0 2 * (a 2 * b 3 - b 2 * a 3))
    simp [M3a.AbelPrym.gram, plucker, Matrix.mul_apply, Fin.sum_univ_four, vecMulVec, Matrix.vecHead,
      Matrix.vecTail]
    ring
  · show (gram M1 M2 M3 δ * plucker a b * gram M1 M2 M3 δ) 1 3 = -C δ * (pencil M1 M2 M3 1 0 *
      (a 0 * b 3 - b 0 * a 3) + pencil M1 M2 M3 1 1 * (a 1 * b 3 - b 1 * a 3) +
        pencil M1 M2 M3 1 2 * (a 2 * b 3 - b 2 * a 3))
    simp [M3a.AbelPrym.gram, plucker, Matrix.mul_apply, Fin.sum_univ_four, vecMulVec, Matrix.vecHead,
      Matrix.vecTail]
    ring
  · show (gram M1 M2 M3 δ * plucker a b * gram M1 M2 M3 δ) 2 3 = -C δ * (pencil M1 M2 M3 2 0 *
      (a 0 * b 3 - b 0 * a 3) + pencil M1 M2 M3 2 1 * (a 1 * b 3 - b 1 * a 3) +
        pencil M1 M2 M3 2 2 * (a 2 * b 3 - b 2 * a 3))
    simp [M3a.AbelPrym.gram, plucker, Matrix.mul_apply, Fin.sum_univ_four, vecMulVec, Matrix.vecHead,
      Matrix.vecTail]
    ring

/-- **The cubic**: `(G A G)_{l3} = e₀ + e₁ t + e₂ t² + e₃ t³` with the `e` of the program. -/
theorem gAg_eq (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (x : DPoint L M1 M2 M3 δ)
    (T : Vec5 L) (l : ℕ) :
    (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T.toV5) * gram M1 M2 M3 δ) (lFin l) 3 =
      C (apE (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) T l).c0 +
        C (apE (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) T l).c1 * X +
        C (apE (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) T l).c2 * X ^ 2 +
        C (apE (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) T l).c3 * X ^ 3 := by
  obtain ⟨a10, a20, a21⟩ := sym_entries h1
  obtain ⟨b10, b20, b21⟩ := sym_entries h2
  obtain ⟨c10, c20, c21⟩ := sym_entries h3
  rw [gram_plucker_gram_l3]
  rcases l with _ | _ | l <;>
  simp only [jFin, apE, dot3, Sym3.row, Sym3.ofMatrix, APIn.ofPoint, plk, pt, Vec5.toV5, pencil,
    Matrix.of_apply, fo_add, fo_sub, fo_mul, fo_neg, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    a10, a20, a21, b10, b20, b21, c10, c20, c21, map_add, map_sub, map_mul, map_neg] <;> ring

/-- **Division by `U`**: a cubic minus its remainder modulo `X² + u₁ X + u₀`. -/
theorem dvd_cubic_sub_rem (u0 u1 e0 e1 e2 e3 : L) :
    X ^ 2 + C u1 * X + C u0 ∣ C e0 + C e1 * X + C e2 * X ^ 2 + C e3 * X ^ 3 -
      (C (e1 - e2 * u1 + e3 * (u1 * u1 - u0)) * X + C (e0 - e2 * u0 + e3 * (u1 * u0))) :=
  ⟨C e3 * X + C (e2 - e3 * u1), by simp only [map_sub, map_add, map_mul]; ring⟩

theorem symm_fin3 (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) :
    ∀ i, (![M1, M2, M3] i)ᵀ = ![M1, M2, M3] i := by
  intro i; fin_cases i
  · exact h1
  · exact h2
  · exact h3

/-! ## The certificate -/

theorem minor2_disj {x : DPoint L M1 M2 M3 δ} {T : Vec5 L} {l : ℕ}
    (hc : minor2 (fieldOps L) (x.p 0) (x.p 1) (x.p 2) T.c0 T.c1 T.c2 l ≠ 0) :
    (pt x).1 1 * T.toV5.1 2 - (pt x).1 2 * T.toV5.1 1 ≠ 0 ∨
      (pt x).1 2 * T.toV5.1 0 - (pt x).1 0 * T.toV5.1 2 ≠ 0 ∨
      (pt x).1 0 * T.toV5.1 1 - (pt x).1 1 * T.toV5.1 0 ≠ 0 := by
  rcases l with _ | _ | l
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- **Soundness of the Abel-Prym program over a field.** A successful exact run at a point `x` of
`D_δ` gives a certificate of Bruin's construction at `x` whose `U` and `V` are the Mumford pair of the
run. -/
theorem apPhi_cert (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    (hδ : δ ≠ 0) {f : L[X]} (hf : f = -C δ * (pencil M1 M2 M3).det) (x : DPoint L M1 M2 M3 δ)
    {prm : APPrm} {m : Mum L} (h : apPhi (fieldOps L) prm (APIn.ofPoint M1 M2 M3 δ x) = some m) :
    ∃ c : Cert M1 M2 M3 δ f x, bruinU M1 M2 M3 δ c.T = m.u ∧ c.V = m.v := by
  obtain ⟨hN0, ha3, hc, hm⟩ := apPhi_field h
  simp only at hm
  obtain ⟨q0, q1, q2⟩ := quadD_eq h1 h2 h3 x (apT (fieldOps L) (APIn.ofPoint M1 M2 M3 δ x) prm.kd)
  set xi := APIn.ofPoint M1 M2 M3 δ x
  set T := apT (fieldOps L) xi prm.kd
  set a := apA (fieldOps L) xi T
  set e := apE (fieldOps L) xi T prm.l
  set c := minor2 (fieldOps L) xi.p0 xi.p1 xi.p2 T.c0 T.c1 T.c2 prm.l
  -- tangent, rank, independence
  have hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T.toV5 = 0 := apT_tangent h1 h2 h3 x prm.kd
  have hN : ((pt x).2.2 ^ 2 • ![M1, M2, M3] 0 - (2 * (pt x).2.1 * (pt x).2.2) • ![M1, M2, M3] 1 +
      (pt x).2.1 ^ 2 • ![M1, M2, M3] 2) *ᵥ (pt x).1 ≠ 0 := by
    intro h0
    apply hN0
    rw [← nv_eq h1 h2 h3 x prm.jN, h0, Pi.zero_apply]
  have hrs : (pt x).2.1 ≠ 0 ∨ (pt x).2.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hN
    rw [hcon.1, hcon.2]
    simp
  have hrank := rank_of (symm_fin3 h1 h2 h3) hδ h2ne (pt x) hrs hN
  have hmin : (pt x).1 1 * T.toV5.1 2 - (pt x).1 2 * T.toV5.1 1 ≠ 0 ∨
      (pt x).1 2 * T.toV5.1 0 - (pt x).1 0 * T.toV5.1 2 ≠ 0 ∨
      (pt x).1 0 * T.toV5.1 1 - (pt x).1 1 * T.toV5.1 0 ≠ 0 := by
    exact minor2_disj (x := x) (T := T) (l := prm.l) hc
  have hind : LinearIndependent L ![T.toV5, pt x] := indep_of_minor x.ne_zero hmin
  have ha3' : quadD ![M1, M2, M3] δ 2 T.toV5 ≠ 0 := by rw [q2]; exact ha3
  have hl := hodge_eq x T prm.l
  -- the entry
  have hU : bruinU M1 M2 M3 δ T.toV5 = m.u := by
    rw [hm, bruinU, q0, q1, q2]
    simp only [Mum.u]
    congr 3 <;> ring
  have hent : bruinU M1 M2 M3 δ T.toV5 ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T.toV5) * gram M1 M2 M3 δ) (lFin prm.l) 3 -
        m.v * hodge (plucker (plk (pt x)) (plk T.toV5)) (lFin prm.l) 3 := by
    rw [hU, hl, gAg_eq h1 h2 h3 x T prm.l, hm]
    simp only [Mum.u, Mum.v]
    have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    convert dvd_cubic_sub_rem (a.1 * a.2.2⁻¹) ((a.2.1 + a.2.1) * a.2.2⁻¹) e.c0 e.c1 e.c2 e.c3
      using 2
    rw [show minor2 (fieldOps L) (x.p 0) (x.p 1) (x.p 2) T.c0 T.c1 T.c2 prm.l = c from rfl]
    have hk : ∀ A : L, C (A * c⁻¹) * C c = C A := fun A => by
      rw [← map_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [add_mul, mul_right_comm (C _) X (C c), hk, hk]
  refine ⟨Cert.ofEntry h1 h2 h3 h2ne hf x T.toV5 hT hrank hind ha3' (lFin prm.l) (lFin_ne prm.l) hc
    hl m.v (degree_lin_lt _ _) hent, hU, rfl⟩


end FurioLombardo.Discharge.M4Box
