import Mathlib
import FurioLombardo.Discharge.M3a.AbelPrymRuling
import FurioLombardo.M3a.BaseChange

/-!
# Base change of Bruin's certificates

For a field embedding `σ : L →+* L'`, the image of a certificate of Bruin's construction at a point
`x` of `D_δ(L)` is a certificate at the image of `x` in `D_{σ δ}(L')` (`Cert.map`), and its class is
the image of the class (`Cert.cls_map`). Hence `phiRev` commutes with base change at every point
that has a certificate (`phiRev_map`). Lane lean-m4box uses it at the known lifts: `φ_v` at the image
of `x_i` in `D_δ(K_v)` is the image of `φ(x_i)`.
-/

open Polynomial Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

/-- The base change of the class `[⟨u, Y - v⟩]` along `σ` is `[⟨u^σ, Y - v^σ⟩]`. -/
theorem FurioLombardo.M3a.Genus2.picMap_mumford {k kv : Type*} [Field k] [Field kv] (σ : k →+* kv)
    (f : k[X]) [GoodSextic f] [GoodSextic (f.map σ)] {u : k[X]} (hu : u ≠ 0) (hu' : u.map σ ≠ 0)
    (v : k[X]) :
    picMap σ f (ClassGroup.mk0 (mumford0 f hu v)) =
      ClassGroup.mk0 (mumford0 (f.map σ) hu' (v.map σ)) := by
  apply picMap_mk0 σ f (mumford0 f hu v) (mumford0 (f.map σ) hu' (v.map σ))
  change mumford (f.map σ) (u.map σ) (v.map σ) = (mumford f u v).map (baseChange σ f)
  rw [mumford, mumford, Ideal.map_span, Set.image_pair, baseChange_algebraMap, map_sub,
    baseChange_Yc, baseChange_algebraMap]

namespace FurioLombardo.Discharge.M3a.AbelPrym

variable {L L' : Type*} [Field L] [Field L'] (σ : L →+* L')

/-- The image of a vector of `V5 L` in `V5 L'`. -/
def mapV (W : V5 L) : V5 L' := (fun i => σ (W.1 i), σ W.2.1, σ W.2.2)

variable {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

/-- The image of a point of `D_δ(L)` in `D_{σ δ}(L')`. -/
def mapPt (x : DPoint L M1 M2 M3 δ) : DPoint L' (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) where
  p := fun i => σ (x.p i)
  r := σ x.r
  s := σ x.s
  ne_zero := by
    intro h
    apply x.ne_zero
    funext i
    have := congrFun h i
    exact σ.injective (by simpa using this)
  eq1 := by
    have := congrArg σ x.eq1
    rw [RingHom.map_dotProduct, map_mul, map_pow] at this
    rw [← this]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ M1 x.p i).symm
  eq2 := by
    have := congrArg σ x.eq2
    rw [RingHom.map_dotProduct, map_mul, map_mul] at this
    rw [← this]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ M2 x.p i).symm
  eq3 := by
    have := congrArg σ x.eq3
    rw [RingHom.map_dotProduct, map_mul, map_pow] at this
    rw [← this]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ M3 x.p i).symm

theorem pt_mapPt (x : DPoint L M1 M2 M3 δ) : pt (mapPt σ x) = mapV σ (pt x) := rfl

theorem swapPt_mapPt (x : DPoint L M1 M2 M3 δ) : swapPt (mapPt σ x) = mapPt σ (swapPt x) := rfl

theorem inv_mapPt (x : DPoint L M1 M2 M3 δ) : (mapPt σ x).inv = mapPt σ x.inv := by
  cases x
  simp only [DPoint.inv, mapPt, map_neg]

/-! ## The forms and the polynomial layer commute with `σ` -/

theorem quadD_mapV (i : Fin 3) (W : V5 L) :
    quadD ![M1.map σ, M2.map σ, M3.map σ] (σ δ) i (mapV σ W) = σ (quadD ![M1, M2, M3] δ i W) := by
  unfold quadD mapV
  dsimp
  have hmulvec (M : Matrix (Fin 3) (Fin 3) L) (v : Fin 3 → L) : (M.map σ) *ᵥ (σ ∘ v) = σ ∘ (M *ᵥ v) := by
    funext j; simp [RingHom.map_mulVec]
  have hdot (M : Matrix (Fin 3) (Fin 3) L) : (σ ∘ W.1) ⬝ᵥ ((M.map σ) *ᵥ (σ ∘ W.1)) = σ (W.1 ⬝ᵥ (M *ᵥ W.1)) := by
    rw [hmulvec M W.1, RingHom.map_dotProduct]
  have hsq (a b : L) : ![σ a ^ 2, σ a * σ b, σ b ^ 2] i = σ (![a ^ 2, a * b, b ^ 2] i) := by
    fin_cases i <;> simp
  have hM : ![M1.map σ, M2.map σ, M3.map σ] i = (![M1, M2, M3] i).map σ := by
    fin_cases i <;> rfl
  have hcomp : (fun i => σ (W.1 i)) = σ ∘ W.1 := rfl
  rw [hM, hcomp, hdot (![M1, M2, M3] i), hsq W.2.1 W.2.2]
  rw [← RingHom.map_mul, ← RingHom.map_sub]

theorem polarD_mapV (i : Fin 3) (P W : V5 L) :
    polarD ![M1.map σ, M2.map σ, M3.map σ] (σ δ) i (mapV σ P) (mapV σ W) =
      σ (polarD ![M1, M2, M3] δ i P W) := by
  match i with
  | 0 =>
    unfold polarD mapV
    dsimp
    have h1 : (fun i => σ (P.1 i)) = (σ ∘ P.1) := rfl
    have h2 : (fun i => σ (W.1 i)) = (σ ∘ W.1) := rfl
    rw [h1, h2]
    have hvec : (M1.map (σ : L →+* L')).mulVec (σ ∘ W.1) = σ ∘ (M1.mulVec W.1) := by
      ext j; simp [RingHom.map_mulVec]
    have hvec2 : (M1.map (σ : L →+* L')).mulVec (σ ∘ P.1) = σ ∘ (M1.mulVec P.1) := by
      ext j; simp [RingHom.map_mulVec]
    rw [hvec, hvec2]
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_dotProduct, RingHom.map_dotProduct]
    have h2nat : σ (2 : L) = (2 : L') := by simpa using map_natCast σ 2
    rw [h2nat]
  | 1 =>
    unfold polarD mapV
    dsimp
    have h1 : (fun i => σ (P.1 i)) = (σ ∘ P.1) := rfl
    have h2 : (fun i => σ (W.1 i)) = (σ ∘ W.1) := rfl
    rw [h1, h2]
    have hvec : (M2.map (σ : L →+* L')).mulVec (σ ∘ W.1) = σ ∘ (M2.mulVec W.1) := by
      ext j; simp [RingHom.map_mulVec]
    have hvec2 : (M2.map (σ : L →+* L')).mulVec (σ ∘ P.1) = σ ∘ (M2.mulVec P.1) := by
      ext j; simp [RingHom.map_mulVec]
    rw [hvec, hvec2]
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_add, RingHom.map_mul,
      RingHom.map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
  | 2 =>
    unfold polarD mapV
    dsimp
    have h1 : (fun i => σ (P.1 i)) = (σ ∘ P.1) := rfl
    have h2 : (fun i => σ (W.1 i)) = (σ ∘ W.1) := rfl
    rw [h1, h2]
    have hvec : (M3.map (σ : L →+* L')).mulVec (σ ∘ W.1) = σ ∘ (M3.mulVec W.1) := by
      ext j; simp [RingHom.map_mulVec]
    have hvec2 : (M3.map (σ : L →+* L')).mulVec (σ ∘ P.1) = σ ∘ (M3.mulVec P.1) := by
      ext j; simp [RingHom.map_mulVec]
    rw [hvec, hvec2]
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_dotProduct, RingHom.map_dotProduct]
    have h2nat : σ (2 : L) = (2 : L') := by simpa using map_natCast σ 2
    rw [h2nat]

/-- A surjective tangent map stays surjective: the images of preimages of the standard basis. -/
theorem rank_mapV {P : V5 L} (h : Function.Surjective (tangentMap ![M1, M2, M3] δ P)) :
    Function.Surjective (tangentMap ![M1.map σ, M2.map σ, M3.map σ] (σ δ) (mapV σ P)) := by
  set t := tangentMap ![M1, M2, M3] δ P with ht
  set t' := tangentMap ![M1.map σ, M2.map σ, M3.map σ] (σ δ) (mapV σ P) with ht'
  have h_surj (j : Fin 3) : ∃ W, t W = Pi.single j (1 : L) := by
    apply h
  choose W hW using h_surj
  have h_t'_mapV (W : V5 L) (i : Fin 3) : t' (mapV σ W) i = σ (t W i) := by
    calc
      t' (mapV σ W) i = polarD ![M1.map σ, M2.map σ, M3.map σ] (σ δ) i (mapV σ P) (mapV σ W) := by
        rw [tangentMap_apply]
      _ = σ (polarD ![M1, M2, M3] δ i P W) := by rw [polarD_mapV]
      _ = σ (t W i) := by rw [tangentMap_apply]
  intro w
  refine ⟨∑ j : Fin 3, w j • mapV σ (W j), ?_⟩
  ext i
  have h_sum : t' (∑ j : Fin 3, w j • mapV σ (W j)) = ∑ j : Fin 3, w j • t' (mapV σ (W j)) := by
    rw [map_sum t']
    simp [map_smul t']
  have h_eq : (∑ j : Fin 3, w j • t' (mapV σ (W j))) i = w i := by
    simp [h_t'_mapV, hW, Pi.single_apply, smul_eq_mul]
  rw [h_sum, h_eq]

/-- Two independent vectors stay independent: some `2 × 2` minor of their coordinates is nonzero. -/
theorem indep_mapV {T P : V5 L} (h : LinearIndependent L ![T, P]) :
    LinearIndependent L' ![mapV σ T, mapV σ P] := by
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t h_eq
  -- h_eq: s • mapV σ T + t • mapV σ P = 0
  -- goal: s = 0 ∧ t = 0

  -- Define coordinate extraction
  let c : V5 L → Fin 5 → L := λ W i =>
    match i with
    | 0 => W.1 0
    | 1 => W.1 1
    | 2 => W.1 2
    | 3 => W.2.1
    | 4 => W.2.2

  let c' : V5 L' → Fin 5 → L' := λ W i =>
    match i with
    | 0 => W.1 0
    | 1 => W.1 1
    | 2 => W.1 2
    | 3 => W.2.1
    | 4 => W.2.2

  have hc_mapV : ∀ (W : V5 L) (i : Fin 5), c' (mapV σ W) i = σ (c W i) := by
    intro W i
    cases' i using Fin.cases with i
    · simp [c, c', mapV]
    · cases' i using Fin.cases with i
      · simp [c, c', mapV]
      · cases' i using Fin.cases with i
        · simp [c, c', mapV]
        · cases' i using Fin.cases with i
          · simp [c, c', mapV]
          · cases' i using Fin.cases with i
            · simp [c, c', mapV]
            · exact Fin.elim0 i

  -- Embed Fin 3 into Fin 5
  let embed (i : Fin 3) : Fin 5 :=
    match i with
    | 0 => 0
    | 1 => 1
    | 2 => 2

  have h_embed_T : ∀ i : Fin 3, c T (embed i) = T.1 i := by
    intro i; fin_cases i <;> simp [c, embed]
  have h_embed_P : ∀ i : Fin 3, c P (embed i) = P.1 i := by
    intro i; fin_cases i <;> simp [c, embed]

  -- From h, there exist a, b such that the minor is nonzero
  have h_exists_minor : ∃ (a b : Fin 5), c T a * c P b - c T b * c P a ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    have h_all' : ∀ a b, c T a * c P b = c T b * c P a := by
      intro a b
      apply sub_eq_zero.mp
      exact h_all a b

    by_cases hPzero : ∀ i : Fin 5, c P i = 0
    · have h0 : P.1 0 = 0 := by simpa [c] using hPzero 0
      have h1 : P.1 1 = 0 := by simpa [c] using hPzero 1
      have h2 : P.1 2 = 0 := by simpa [c] using hPzero 2
      have h3 : P.2.1 = 0 := by simpa [c] using hPzero 3
      have h4 : P.2.2 = 0 := by simpa [c] using hPzero 4
      have hPzero' : P = 0 := by
        apply Prod.ext
        · ext i; fin_cases i <;> assumption
        · apply Prod.ext <;> assumption
      have h_contra := h 0 1 (by simp [hPzero'])
      exact one_ne_zero h_contra.2
    · push_neg at hPzero
      rcases hPzero with ⟨b, hb⟩
      have h_dep : c P b • T - c T b • P = 0 := by
        apply Prod.ext
        · ext i
          simp [Pi.smul_apply, smul_eq_mul]
          have hrel := h_all' (embed i) b
          have h_eq_coords : T.1 i * c P b = c T b * P.1 i := by
            simpa [h_embed_T, h_embed_P] using hrel
          calc
            c P b * T.1 i - c T b * P.1 i = T.1 i * c P b - c T b * P.1 i := by ring
            _ = c T b * P.1 i - c T b * P.1 i := by rw [h_eq_coords]
            _ = 0 := by ring
        · apply Prod.ext
          · -- c P b * T.2.1 - c T b * P.2.1 = 0
            have hrel := h_all' 3 b
            have h_eq_coords : T.2.1 * c P b = c T b * P.2.1 := by
              simpa [c] using hrel
            calc
              c P b * T.2.1 - c T b * P.2.1 = T.2.1 * c P b - c T b * P.2.1 := by ring
              _ = c T b * P.2.1 - c T b * P.2.1 := by rw [h_eq_coords]
              _ = 0 := by ring
          · -- c P b * T.2.2 - c T b * P.2.2 = 0
            have hrel := h_all' 4 b
            have h_eq_coords : T.2.2 * c P b = c T b * P.2.2 := by
              simpa [c] using hrel
            calc
              c P b * T.2.2 - c T b * P.2.2 = T.2.2 * c P b - c T b * P.2.2 := by ring
              _ = c T b * P.2.2 - c T b * P.2.2 := by rw [h_eq_coords]
              _ = 0 := by ring
      have h_contra := h (c P b) (-c T b) (by simpa [sub_eq_add_neg] using h_dep)
      rcases h_contra with ⟨hPb, hTb⟩
      exact hb hPb

  rcases h_exists_minor with ⟨a, b, h_minor⟩

  -- Extract coordinate equations from h_eq for specific indices a, b
  have ha : s * c' (mapV σ T) a + t * c' (mapV σ P) a = 0 := by
    have h := congrArg (λ W : V5 L' => c' W a) h_eq
    fin_cases a <;> simp [c'] at h ⊢ <;> exact h

  have hb_eq : s * c' (mapV σ T) b + t * c' (mapV σ P) b = 0 := by
    have h := congrArg (λ W : V5 L' => c' W b) h_eq
    fin_cases b <;> simp [c'] at h ⊢ <;> exact h

  -- Rewrite using hc_mapV
  have ha' : s * σ (c T a) + t * σ (c P a) = 0 := by
    simpa [hc_mapV] using ha

  have hb_eq' : s * σ (c T b) + t * σ (c P b) = 0 := by
    simpa [hc_mapV] using hb_eq

  -- ha': s * σ (c T a) + t * σ (c P a) = 0
  -- hb_eq': s * σ (c T b) + t * σ (c P b) = 0

  -- From ha': s * σ (c T a) = -t * σ (c P a)
  have ha_eq : s * σ (c T a) = -t * σ (c P a) := by
    calc
      s * σ (c T a) = (s * σ (c T a) + t * σ (c P a)) - t * σ (c P a) := by ring
      _ = 0 - t * σ (c P a) := by rw [ha']
      _ = -t * σ (c P a) := by simp

  -- From hb_eq': s * σ (c T b) = -t * σ (c P b)
  have hb_eq'' : s * σ (c T b) = -t * σ (c P b) := by
    calc
      s * σ (c T b) = (s * σ (c T b) + t * σ (c P b)) - t * σ (c P b) := by ring
      _ = 0 - t * σ (c P b) := by rw [hb_eq']
      _ = -t * σ (c P b) := by simp

  -- Compute s * σ(minor) = 0
  have h_s_minor : s * σ (c T a * c P b - c T b * c P a) = 0 := by
    calc
      s * σ (c T a * c P b - c T b * c P a) =
        s * (σ (c T a) * σ (c P b) - σ (c T b) * σ (c P a)) := by
          simp [map_mul, map_sub]
      _ = (s * σ (c T a)) * σ (c P b) - (s * σ (c T b)) * σ (c P a) := by ring
      _ = (-t * σ (c P a)) * σ (c P b) - (-t * σ (c P b)) * σ (c P a) := by
        rw [ha_eq, hb_eq'']
      _ = (-t) * (σ (c P a) * σ (c P b) - σ (c P b) * σ (c P a)) := by ring
      _ = (-t) * 0 := by ring
      _ = 0 := by ring

  -- Since σ(minor) ≠ 0 (σ is injective and minor ≠ 0), we have s = 0
  have h_sigma_minor_ne_zero : σ (c T a * c P b - c T b * c P a) ≠ 0 := by
    intro hzero
    apply h_minor
    apply σ.injective
    simpa using hzero

  have hs : s = 0 := by
    have := mul_eq_zero.mp h_s_minor
    rcases this with (hs | hsigma)
    · exact hs
    · exact absurd hsigma h_sigma_minor_ne_zero

  -- Similarly, compute t * σ(minor) = 0
  -- From ha': t * σ (c P a) = -s * σ (c T a)
  have ha_t : t * σ (c P a) = -s * σ (c T a) := by
    calc
      t * σ (c P a) = (s * σ (c T a) + t * σ (c P a)) - s * σ (c T a) := by ring
      _ = 0 - s * σ (c T a) := by rw [ha']
      _ = -s * σ (c T a) := by simp

  -- From hb_eq': t * σ (c P b) = -s * σ (c T b)
  have hb_t : t * σ (c P b) = -s * σ (c T b) := by
    calc
      t * σ (c P b) = (s * σ (c T b) + t * σ (c P b)) - s * σ (c T b) := by ring
      _ = 0 - s * σ (c T b) := by rw [hb_eq']
      _ = -s * σ (c T b) := by simp

  have h_t_minor : t * σ (c T a * c P b - c T b * c P a) = 0 := by
    calc
      t * σ (c T a * c P b - c T b * c P a) =
        t * (σ (c T a) * σ (c P b) - σ (c T b) * σ (c P a)) := by
          simp [map_mul, map_sub]
      _ = t * σ (c T a) * σ (c P b) - t * σ (c T b) * σ (c P a) := by ring
      _ = σ (c T a) * (t * σ (c P b)) - σ (c T b) * (t * σ (c P a)) := by ring
      _ = σ (c T a) * (-s * σ (c T b)) - σ (c T b) * (-s * σ (c T a)) := by
        rw [ha_t, hb_t]
      _ = (-s) * (σ (c T a) * σ (c T b) - σ (c T b) * σ (c T a)) := by ring
      _ = (-s) * 0 := by ring
      _ = 0 := by ring

  have ht : t = 0 := by
    have := mul_eq_zero.mp h_t_minor
    rcases this with (ht | hsigma)
    · exact ht
    · exact absurd hsigma h_sigma_minor_ne_zero

  exact ⟨hs, ht⟩

theorem pencil_map :
    pencil (M1.map σ) (M2.map σ) (M3.map σ) = (pencil M1 M2 M3).map (Polynomial.mapRingHom σ) := by
  ext a b
  simp [pencil, Matrix.map_apply, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

theorem gram_map :
    gram (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) = (gram M1 M2 M3 δ).map (Polynomial.mapRingHom σ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, pencil, Matrix.map_apply, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_neg]

theorem bruinU_mapV (T : V5 L) :
    bruinU (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (mapV σ T) = (bruinU M1 M2 M3 δ T).map σ := by
  unfold bruinU
  rw [quadD_mapV σ 0 T, quadD_mapV σ 1 T, quadD_mapV σ 2 T]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, map_div₀, map_mul, map_ofNat]

theorem plk_mapV (W : V5 L) : plk (mapV σ W) = fun k => (plk W k).map σ := by
  funext k
  fin_cases k <;> simp [plk, mapV, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]

/-! ## The certificate -/

theorem ruling_mapV {x : DPoint L M1 M2 M3 δ} {T : V5 L} {V : L[X]} (i j : Fin 4)
    (h : bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j -
        V * hodge (plucker (plk (pt x)) (plk T)) i j) :
    bruinU (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (mapV σ T) ∣
      (gram (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) *
          plucker (plk (pt (mapPt σ x))) (plk (mapV σ T)) *
          gram (M1.map σ) (M2.map σ) (M3.map σ) (σ δ)) i j -
        V.map σ * hodge (plucker (plk (pt (mapPt σ x))) (plk (mapV σ T))) i j := by
  have hpt : pt (mapPt σ x) = mapV σ (pt x) := pt_mapPt σ x
  have hplk1 : plk (pt (mapPt σ x)) = (Polynomial.mapRingHom σ) ∘ plk (pt x) := by
    rw [hpt, plk_mapV]
    funext k; rfl
  have hplk2 : plk (mapV σ T) = (Polynomial.mapRingHom σ) ∘ plk T := by
    rw [plk_mapV]
    funext k; rfl
  have hplucker : plucker (plk (pt (mapPt σ x))) (plk (mapV σ T)) =
      (plucker (plk (pt x)) (plk T)).map (Polynomial.mapRingHom σ) := by
    rw [hplk1, hplk2, plucker_map (Polynomial.mapRingHom σ) (plk (pt x)) (plk T)]
  have hgram : gram (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) = (gram M1 M2 M3 δ).map (Polynomial.mapRingHom σ) := by
    rw [gram_map]
  have hbruin : bruinU (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (mapV σ T) =
      (bruinU M1 M2 M3 δ T).map σ := by
    rw [bruinU_mapV]
  have hhodge : hodge (plucker (plk (pt (mapPt σ x))) (plk (mapV σ T))) =
      (hodge (plucker (plk (pt x)) (plk T))).map (Polynomial.mapRingHom σ) := by
    rw [hplucker, hodge_map (Polynomial.mapRingHom σ) (plucker (plk (pt x)) (plk T))]
  rw [hbruin, hhodge, hplucker, hgram]
  have h_mat_eq : ((gram M1 M2 M3 δ).map (Polynomial.mapRingHom σ) * (plucker (plk (pt x)) (plk T)).map (Polynomial.mapRingHom σ) * (gram M1 M2 M3 δ).map (Polynomial.mapRingHom σ)) i j =
      Polynomial.map σ ((gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, Polynomial.coe_mapRingHom]
  have h_dvd := Polynomial.map_dvd σ h
  rw [Polynomial.map_sub, Polynomial.map_mul] at h_dvd
  rw [h_mat_eq]
  simpa [Matrix.map_apply, Polynomial.coe_mapRingHom] using h_dvd

theorem unit_mapV {x : DPoint L M1 M2 M3 δ} {T : V5 L}
    (h : ∃ i j, ∃ w : L[X], bruinU M1 M2 M3 δ T ∣ w * hodge (plucker (plk (pt x)) (plk T)) i j - 1) :
    ∃ i j, ∃ w : L'[X], bruinU (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (mapV σ T) ∣
      w * hodge (plucker (plk (pt (mapPt σ x))) (plk (mapV σ T))) i j - 1 := by
  obtain ⟨i, j, w, hw⟩ := h
  refine ⟨i, j, w.map σ, ?_⟩
  have h_bruinU : bruinU (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (mapV σ T) = (bruinU M1 M2 M3 δ T).map σ :=
    bruinU_mapV σ T
  have h_hodge : hodge (plucker (plk (pt (mapPt σ x))) (plk (mapV σ T))) i j = (hodge (plucker (plk (pt x)) (plk T)) i j).map σ := by
    calc
      hodge (plucker (plk (pt (mapPt σ x))) (plk (mapV σ T))) i j
          = hodge (plucker (plk (mapV σ (pt x))) (plk (mapV σ T))) i j := by rfl
      _ = hodge (plucker (fun k => (plk (pt x) k).map σ) (fun k => (plk T k).map σ)) i j := by
        rw [plk_mapV σ (pt x), plk_mapV σ T]
      _ = hodge ((plucker (plk (pt x)) (plk T)).map (Polynomial.mapRingHom σ)) i j := by
        have h_eq : plucker (fun k => (plk (pt x) k).map σ) (fun k => (plk T k).map σ) =
            (plucker (plk (pt x)) (plk T)).map (Polynomial.mapRingHom σ) := by
          rw [plucker_map (Polynomial.mapRingHom σ) (plk (pt x)) (plk T)]
          rfl
        rw [h_eq]
      _ = (hodge (plucker (plk (pt x)) (plk T))).map (Polynomial.mapRingHom σ) i j := by
        rw [hodge_map (Polynomial.mapRingHom σ) (plucker (plk (pt x)) (plk T))]
      _ = (hodge (plucker (plk (pt x)) (plk T)) i j).map σ := by rfl
  rw [h_bruinU, h_hodge]
  have h_dvd := Polynomial.map_dvd σ hw
  simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one] using h_dvd

theorem sq_mapV {f : L[X]} {T : V5 L} {V : L[X]} (h : bruinU M1 M2 M3 δ T ∣ V ^ 2 - f) :
    bruinU (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (mapV σ T) ∣ V.map σ ^ 2 - f.map σ := by
  rw [bruinU_mapV]
  have := Polynomial.map_dvd σ h
  simpa [Polynomial.map_sub, Polynomial.map_pow] using this

/-- The image of a certificate at `x`: a certificate at the image of `x`. -/
noncomputable def Cert.map {f : L[X]} {x : DPoint L M1 M2 M3 δ} (c : Cert M1 M2 M3 δ f x) :
    Cert (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (f.map σ) (mapPt σ x) where
  T := mapV σ c.T
  tangent i := by
    have h := polarD_mapV σ (M1 := M1) (M2 := M2) (M3 := M3) (δ := δ) i (pt x) c.T
    rw [c.tangent i, map_zero] at h
    exact h
  rank := by rw [pt_mapPt]; exact rank_mapV σ c.rank
  indep := by rw [pt_mapPt]; exact indep_mapV σ c.indep
  a3_ne := fun h => c.a3_ne (σ.injective (by rw [← quadD_mapV, map_zero]; exact h))
  V := c.V.map σ
  degree_V := by rw [Polynomial.degree_map]; exact c.degree_V
  ruling i j := ruling_mapV σ i j (c.ruling i j)
  unit := unit_mapV σ c.unit
  sq := sq_mapV σ c.sq

theorem Cert.map_T {f : L[X]} {x : DPoint L M1 M2 M3 δ} (c : Cert M1 M2 M3 δ f x) :
    (c.map σ).T = mapV σ c.T := rfl

theorem Cert.map_V {f : L[X]} {x : DPoint L M1 M2 M3 δ} (c : Cert M1 M2 M3 δ f x) :
    (c.map σ).V = c.V.map σ := rfl

/-- **The class of the image certificate is the image of the class.** -/
theorem Cert.cls_map {f : L[X]} [GoodSextic f] [GoodSextic (f.map σ)] {x : DPoint L M1 M2 M3 δ}
    (c : Cert M1 M2 M3 δ f x) : (c.map σ).cls = jacMap σ f c.cls := by
  apply Subtype.ext
  have hu : bruinU M1 M2 M3 δ c.T ≠ 0 := (bruinU_monic M1 M2 M3 δ c.T).ne_zero
  have hmonic_map : Monic ((bruinU M1 M2 M3 δ c.T).map σ) :=
    (bruinU_monic M1 M2 M3 δ c.T).map σ
  have hu' : (bruinU M1 M2 M3 δ c.T).map σ ≠ 0 := hmonic_map.ne_zero
  calc
    ((c.map σ).cls : Pic (f.map σ)) = ClassGroup.mk0 (mumford0 (f.map σ)
      (bruinU_monic (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (c.map σ).T).ne_zero (c.map σ).V) := by
      rw [Cert.coe_cls]
    _ = ClassGroup.mk0 (mumford0 (f.map σ)
      (bruinU_monic (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (mapV σ c.T)).ne_zero (c.V.map σ)) := by
      rw [Cert.map_T, Cert.map_V]
    _ = ClassGroup.mk0 (mumford0 (f.map σ) hu' (c.V.map σ)) := by
      congr 1
      apply Subtype.ext
      change mumford (f.map σ) _ (c.V.map σ) = mumford (f.map σ) _ (c.V.map σ)
      rw [bruinU_mapV]
    _ = picMap σ f (ClassGroup.mk0 (mumford0 f hu c.V)) := by
      rw [← picMap_mumford σ f hu hu' c.V]
    _ = picMap σ f (c.cls : Pic f) := by rw [Cert.coe_cls c]
    _ = (jacMap σ f c.cls : Pic (f.map σ)) := rfl

/-- **`phiRev` commutes with base change** at a point with a certificate. -/
theorem phiRev_map {f : L[X]} [GoodSextic f] [GoodSextic (f.map σ)] {x : DPoint L M1 M2 M3 δ}
    (c : Cert M3 M2 M1 δ f (swapPt x)) :
    phiRev (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) (f.map σ) (mapPt σ x) =
      jacMap σ f (phiRev M1 M2 M3 δ f x) := by
  rw [phiRev_eq_of_cert c, ← Cert.cls_map]
  exact phiRev_eq_of_cert (x := mapPt σ x) (c.map σ)

end FurioLombardo.Discharge.M3a.AbelPrym
