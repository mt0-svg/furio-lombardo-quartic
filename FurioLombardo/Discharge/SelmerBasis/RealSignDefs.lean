import FurioLombardo.Discharge.SelmerBasis.RealRoots
import FurioLombardo.Discharge.SelmerBasis.RealCoord
import FurioLombardo.Discharge.SelmerBasis.RealSignData
import FurioLombardo.Discharge.SelmerBasis.SUnitData
import FurioLombardo.Discharge.SelmerBasis.AssemblyData

/-!
# The sign checkers at the real places 5 and 6 (item C)

The generators have zk coordinates: `gensL i = a0 + a1 w` over `K21` (`w² = ε`), and
`gensN j = A + B' z` over `L42` (`z² = eN`), `A = a0 + a1 w`, `B' = 2 (b0 + b1 w)`. The sign of such an
element at a real embedding of the tower is read off the signs of its norms and of one coordinate
(`sgn_extend`, RealCoord.lean); each sign over `K21` is an `elemCertAt` certificate at `realEmb k`.

* `certL k sw a0 a1 n pos t`: the certificates that `t · ψ(a0 + a1 w) > 0` for `ψ = extendHom σ w'` whenever
  `sw w' > 0`, from `N = a0² - ε a1²` (zk list `n`) positive (`pos`, then the sign of `a0`) or negative
  (then the sign of `a1`, times `sw`);
* `normE`, `m0E`, `m1E`: the Kronecker expressions of the norms and of `M = A² - eN B'² = m0 + m1 w`;
* `tBit k s j`: the sign `±1` of the bit `j` of `Assembly.SgRows k` at the generator `s`;
* the per-generator checkers `ckLf`, `ckMf`, `ckNf`, `ckBf`, the tower checker `ckTf` and the identity
  checkers `idLf`, `idNf`, `idBeta`, all decided by the kernel in RealSignCheck.lean;
* `certL_sound`, `certL_sound_neg`: the soundness of `certL` at `w'` and at `-w'`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.RealRoots

open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis
  RealSignData

/-- The sign certificates of `a0 + a1 w` at `realEmb k`, `w ↦ w'` with `sw w' > 0`, target sign `t`. -/
def certL (k : Fin 3) (sw : ℤ) (a0 a1 n : List ℤ) (pos : Bool) (t : ℤ) : Bool :=
  if pos then elemCertAt n 1 k && elemCertAt a0 t k else elemCertAt n (-1) k && elemCertAt a1 (t * sw) k

/-- `a0² - ε a1²`. -/
def normE (a0 a1 : List ℤ) : KE :=
  .sub (.mul (.lin a0) (.lin a0)) (.mul (.lin epsL) (.mul (.lin a1) (.lin a1)))

/-- `m0 = a0² + ε a1² - 2 ea (b0² + ε b1²) - 4 ε eb b0 b1`. -/
def m0E (a0 a1 b0 b1 : List ℤ) : KE :=
  .sub (.sub (.add (.mul (.lin a0) (.lin a0)) (.mul (.lin epsL) (.mul (.lin a1) (.lin a1))))
      (.mul (.int 2) (.mul (.lin eaL) (.add (.mul (.lin b0) (.lin b0)) (.mul (.lin epsL) (.mul (.lin b1) (.lin b1)))))))
    (.mul (.int 4) (.mul (.lin epsL) (.mul (.lin ebL) (.mul (.lin b0) (.lin b1)))))

/-- `m1 = 2 a0 a1 - 4 ea b0 b1 - 2 eb (b0² + ε b1²)`. -/
def m1E (a0 a1 b0 b1 : List ℤ) : KE :=
  .sub (.sub (.mul (.int 2) (.mul (.lin a0) (.lin a1))) (.mul (.int 4) (.mul (.lin eaL) (.mul (.lin b0) (.lin b1)))))
    (.mul (.int 2) (.mul (.lin ebL) (.add (.mul (.lin b0) (.lin b0)) (.mul (.lin epsL) (.mul (.lin b1) (.lin b1))))))

/-- Coordinate `c` of `gensL i`. -/
def gLl (i c : ℕ) : List ℤ := (SUnitData.gL.getD i []).getD c []

/-- Coordinate `c` of `gensN j`. -/
def gNl (j c : ℕ) : List ℤ := (SUnitData.gN.getD j []).getD c []

/-- The sign `±1` of the table bit: `-1` for bit `1` (negative). -/
def tBit (k : Fin 2) (s j : ℕ) : ℤ := if ((Assembly.SgRows k).getD s 0).testBit j then -1 else 1

/-- The signs of `u`, `u'`, `v` and the branch flags. -/
def sAlk (k : Fin 2) : ℤ := sAl.getD k 0
def sEbk (k : Fin 2) : ℤ := sEb.getD k 0
def sVk (k : Fin 2) : ℤ := sV.getD k 0
def posLk (k : Fin 2) (i : ℕ) : Bool := (posL.getD k []).getD i true
def posMk (k : Fin 2) (j : ℕ) : Bool := (posM.getD k []).getD j true
def posMTk (k : Fin 2) (j : ℕ) : Bool := (posMT.getD k []).getD j true
def posABk (k : Fin 2) (j : ℕ) : Bool := (posAB.getD k []).getD j true
def posBk (k : Fin 2) : Bool := posBeta.getD k true

/-- `gensL i` at `embQ k hu 0`. -/
def ckLf (k : Fin 2) (i : ℕ) : Bool :=
  certL (Fin.castSucc k) (sAlk k) (gLl i 0) (gLl i 1) (nL.getD i []) (posLk k i) (tBit k i (qIdx k 0))

/-- `M` of `gensN j` at `τ'`, sign `+1` iff `posMT`. -/
def ckMf (k : Fin 2) (j : ℕ) : Bool :=
  certL (Fin.castSucc k) (sEbk k) (mN0.getD j []) (mN1.getD j []) (nMN.getD j []) (posMk k j)
    (if posMTk k j then 1 else -1)

/-- `gensN j` at `embH k hu' hv 0`: `A` at `τ'` (norm positive) or `b0 + b1 w` at `τ'` (norm negative). -/
def ckNf (k : Fin 2) (j : ℕ) : Bool :=
  if posMTk k j then
    certL (Fin.castSucc k) (sEbk k) (gNl j 0) (gNl j 1) (nAN.getD j []) (posABk k j) (tBit k (29 + j) (hIdx k 0))
  else
    certL (Fin.castSucc k) (sEbk k) (gNl j 2) (gNl j 3) (nBN.getD j []) (posABk k j)
      (tBit k (29 + j) (hIdx k 0) * sVk k)

/-- The table bits: at the other factor's roots `+1`, at the second root of the factor the sign of the first
one (norm positive) or its opposite. -/
def ckBf (k : Fin 2) : Bool :=
  (List.range 29).all (fun i =>
    tBit k i (hIdx k 0) == 1 && tBit k i (hIdx k 1) == 1 &&
      tBit k i (qIdx k 1) == (if posLk k i then tBit k i (qIdx k 0) else -tBit k i (qIdx k 0))) &&
  (List.range 53).all (fun j =>
    tBit k (29 + j) (qIdx k 0) == 1 && tBit k (29 + j) (qIdx k 1) == 1 &&
      tBit k (29 + j) (hIdx k 1) ==
        (if posMTk k j then tBit k (29 + j) (hIdx k 0) else -tBit k (29 + j) (hIdx k 0)))

/-- The tower: signs `±1`, `u σ(αR.im) < 0`, `u' σ(eb) > 0`, `v τ'(βR.im) < 0`. -/
def ckTf (k : Fin 2) : Bool :=
  (sAlk k * sAlk k == 1) && (sEbk k * sEbk k == 1) && (sVk k * sVk k == 1) &&
    elemCertAt (SUnitData.alphaL.getD 1 []) (-sAlk k) (Fin.castSucc k) &&
    elemCertAt ebL (sEbk k) (Fin.castSucc k) &&
    certL (Fin.castSucc k) (sEbk k) (SUnitData.betaN.getD 2 []) (SUnitData.betaN.getD 3 []) nBeta (posBk k) (-sVk k)

/-- The norm of `gensL i`. -/
def idLf (i : ℕ) : Bool := checkK 2048 (.sub (.lin (nL.getD i [])) (normE (gLl i 0) (gLl i 1)))

/-- The identities of `gensN j`: `m0`, `m1`, `N(M)`, `N(A)`, `N(b0 + b1 w)`. -/
def idNf (j : ℕ) : Bool :=
  checkK 2048 (.sub (.lin (mN0.getD j [])) (m0E (gNl j 0) (gNl j 1) (gNl j 2) (gNl j 3))) &&
  checkK 2048 (.sub (.lin (mN1.getD j [])) (m1E (gNl j 0) (gNl j 1) (gNl j 2) (gNl j 3))) &&
  checkK 2048 (.sub (.lin (nMN.getD j [])) (normE (mN0.getD j []) (mN1.getD j []))) &&
  checkK 2048 (.sub (.lin (nAN.getD j [])) (normE (gNl j 0) (gNl j 1))) &&
  checkK 2048 (.sub (.lin (nBN.getD j [])) (normE (gNl j 2) (gNl j 3)))

/-- The norm of `βR.im · betaDen`. -/
def idBeta : Bool := checkK 2048 (.sub (.lin nBeta) (normE (SUnitData.betaN.getD 2 []) (SUnitData.betaN.getD 3 [])))

/-! ## Soundness -/

theorem zkE_normE {a0 a1 n : List ℤ} (h : checkK 2048 (.sub (.lin n) (normE a0 a1)) = true) :
    zkE n = zkE a0 * zkE a0 - epsK * (zkE a1 * zkE a1) := by
  have := evK_eq_of_check _ _ _ h
  simpa [normE, epsK_eq] using this

theorem certL_sound {k : Fin 3} {w : ℝ} (hw : w * w = realEmb k epsK) {sw : ℤ} (hsw : 0 < (sw : ℝ) * w)
    (hsw1 : sw * sw = 1) {a0 a1 n : List ℤ} (hn : zkE n = zkE a0 * zkE a0 - epsK * (zkE a1 * zkE a1))
    {pos : Bool} {t : ℤ} (h : certL k sw a0 a1 n pos t = true) :
    0 < (t : ℝ) * extendHom (realEmb k) w hw (⟨zkE a0, zkE a1⟩ : L42) := by
  have hsw1' : (sw : ℝ) * sw = 1 := by exact_mod_cast hsw1
  apply sgn_extend (realEmb k) w hw
  show (0 < realEmb k (zkE a0 * zkE a0 - epsK * (zkE a1 * zkE a1)) ∧ 0 < (t : ℝ) * realEmb k (zkE a0)) ∨
    (realEmb k (zkE a0 * zkE a0 - epsK * (zkE a1 * zkE a1)) < 0 ∧
      0 < (t : ℝ) * (w * realEmb k (zkE a1)))
  rw [← hn]
  cases pos with
  | true =>
    simp only [certL, if_true, Bool.and_eq_true] at h
    exact Or.inl ⟨pos_of_cert h.1, elemAt_sign h.2⟩
  | false =>
    simp only [certL, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
    refine Or.inr ⟨neg_of_cert h.1, ?_⟩
    have h2 := elemAt_sign h.2
    push_cast at h2
    have : (t : ℝ) * (w * realEmb k (zkE a1)) = ((t : ℝ) * sw * realEmb k (zkE a1)) * ((sw : ℝ) * w) := by
      linear_combination (-(t : ℝ) * w * realEmb k (zkE a1)) * hsw1'
    rw [this]
    exact mul_pos h2 hsw

theorem certL_sound_neg {k : Fin 3} {w : ℝ} (hw : w * w = realEmb k epsK) {sw : ℤ} (hsw : 0 < (sw : ℝ) * w)
    (hsw1 : sw * sw = 1) {a0 a1 n : List ℤ} (hn : zkE n = zkE a0 * zkE a0 - epsK * (zkE a1 * zkE a1))
    {pos : Bool} {t : ℤ} (h : certL k sw a0 a1 n pos t = true) :
    0 < ((if pos then t else -t : ℤ) : ℝ) *
      extendHom (realEmb k) (-w) (neg_mul_self_eq hw) (⟨zkE a0, zkE a1⟩ : L42) := by
  have hsw' : 0 < ((-sw : ℤ) : ℝ) * (-w) := by push_cast; linarith
  have hsw1' : (-sw) * (-sw) = 1 := by linarith [hsw1, neg_mul_neg sw sw]
  refine certL_sound (neg_mul_self_eq hw) hsw' hsw1' hn (pos := pos) ?_
  cases pos with
  | true => simpa [certL] using h
  | false =>
    simp only [certL, Bool.false_eq_true, if_false] at h ⊢
    rwa [show -t * -sw = t * sw by ring]

end FurioLombardo.Discharge.SelmerBasis.RealRoots
