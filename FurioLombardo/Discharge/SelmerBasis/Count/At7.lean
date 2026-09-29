import FurioLombardo.Discharge.SelmerBasis.Count.AtPlace
import FurioLombardo.Discharge.SelmerBasis.Count.Cert
import FurioLombardo.Discharge.SelmerBasis.Count.KE
import FurioLombardo.Discharge.SelmerBasis.Count.CertData
import FurioLombardo.Discharge.SelmerBasis.AdicPlace

/-!
# Count lane: `CountBound` at the place above 7 (twist 1)

At `w7 = (al7)` (`e = 7`, `f = 3`, AdicPlace.lean), `σ = adicCoe w7`:

* `norm_two_w7`: `‖2‖ = 1` (`2 · 4 = 1 + al7 · w7two`);
* `4 c_1 = al7⁷ · (unit)` and `46² ndK 1 = al7²³ · (unit)` (odd valuations, `ck_not_isSquare_odd`), so
  `σ(c 1)` and `σ(ndK 1)` are not squares and `#A(K_w7)[2] ≤ 8` (`tors_irrFactor`);
* base abscissa `w7k1x` (count_base_point_w7.gp): `4 fRev_1(x)` is a square (`cert_isSquare` with `e = 0`,
  `64 < 65`, the power `al7^64` as the atom `w7P64`) and `nAt 1 x ≠ 0`;
* `countBound_w7 : CountBound ((fRev 1).map (adicCoe w7)) 3` (`countBound_odd`).

Data: Count/CertData.lean (code/selmer-local-conditions/count_certs.gp).
-/

set_option autoImplicit false

open Polynomial NumberField
open scoped FurioLombardo.Discharge.SelmerBasis.Adic
open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M3a.Bruin (fRev FE c zL)
open FurioLombardo.Discharge.SelmerBasis.Count.Data
open FurioLombardo.M2.Special (al7)

namespace FurioLombardo.Discharge.SelmerBasis.Count

/-! ## Powers of `al7`

`w7P<2^i> = al7^(2^i)` (code/selmer-local-conditions/count_square_powers_w7.gp, log count_square_powers_w7.out): `al7^64` enters the square certificate
as one atom (a chain of 64 products in `checkK` costs over 7 GB in the kernel). -/

def w7P2 : List ℤ := [-4, 1, 0, 1, -2, 0, 2, 0, 0, 1, 2, 0, 1, -1, 2, 3, -2, 0, 0, 0, -1]

def w7P4 : List ℤ := [-39, 20, 16, -24, -28, 6, 18, -4, -2, -30, 10, -26, 0, 20, 14, 14, -20, 8, 32, -6, 4]

def w7P8 : List ℤ := [5313, -5544, 2380, 2464, 4144, 1568, -2240, 3416, 1848, 2884, -5068, -504, -2072, -560, -5264, -7336, 2884, 2464, -4312, -168, 2212]

def w7P16 : List ℤ := [-683139919, 352246496, 481653928, -132521088, -285192544, 303476992, 392265776, 238869904, -76098176, -272011544, -43279544, -510224064, 89630800, 172287136, 116938304, 54211248, -129586184, 152112464, 238009072, -174636000, 286673912]

def w7P32 : List ℤ := [1921332909403474721, -1064219223775232896, -1178408438397259888, 400123790494898176, 838457242795663680, -730080715933234176, -1069366284333310432, -507710518660173920, 232582746840646720, 774823321220340560, -28138009646497520, 1284401538527084096, -292813861659799648, -453112372411953856, -456353172012245760, -362359559004137632, 421689708899780272, -321966499486675232, -737809889622707104, 437877912467747584, -675713092742747472]

def w7P64 : List ℤ := [13181395458190055325769665184470689089, -8269362121572576692168112411009731584, -5785333548816340643431230676219287520, 3125805796002841875515793083727000576, 6216933007454031704704127906761583232, -3365719827414235469360528534787966976, -6858618548860788943072167972733625536, -1310723843329513568958576928259962560, 1847668713771678961052260467016328576, 5469292761478950981741388510160735392, -2190439879890044739505797139420793824, 6820222509574464527913953028546491264, -2519098956728510710850761098788957376, -2727791514147900534864807260520109440, -4816808213151179469105395129447422976, -5304741674854404926187938324751317312, 3629839582437029734430731386063802464, -809046885430291590034508424129151296, -6022460260494034079584683173343231296, 2291069306208083343303257480384129280, -2953416781250471202907936133318442912]

theorem ck_w7p2 : checkK 256 (.sub (.mul (.lin al7) (.lin al7)) (.lin w7P2)) = true := by
  decide +kernel

theorem ck_w7p4 : checkK 256 (.sub (.mul (.lin w7P2) (.lin w7P2)) (.lin w7P4)) = true := by
  decide +kernel

theorem ck_w7p8 : checkK 256 (.sub (.mul (.lin w7P4) (.lin w7P4)) (.lin w7P8)) = true := by
  decide +kernel

theorem ck_w7p16 : checkK 256 (.sub (.mul (.lin w7P8) (.lin w7P8)) (.lin w7P16)) = true := by
  decide +kernel

theorem ck_w7p32 : checkK 256 (.sub (.mul (.lin w7P16) (.lin w7P16)) (.lin w7P32)) = true := by
  decide +kernel

theorem ck_w7p64 : checkK 320 (.sub (.mul (.lin w7P32) (.lin w7P32)) (.lin w7P64)) = true := by
  decide +kernel

/-! ## Kronecker tests -/

theorem ck_w7two : checkK 256 (.sub (.mul (.int 2) (.int 4)) (.add (.int 1) (.mul (.lin al7) (.lin w7two)))) =
    true := by
  decide +kernel

theorem ck_w7k1c1 : checkK 1024 (.sub (FE 1 0) (.mul ((KE.lin al7).pow w7k1cn) (.lin w7k1cA))) = true := by
  decide +kernel

theorem ck_w7k1c2 : checkK 256 (.sub (.mul (.lin w7k1cA) (.lin w7k1cAi))
    (.add (.int 1) (.mul (.lin al7) (.lin w7k1cCa)))) = true := by
  decide +kernel

theorem ck_w7k1nd1 : checkK 4096 (.sub (.lin (zL 1 2)) (.mul ((KE.lin al7).pow w7k1ndn) (.lin w7k1ndA))) =
    true := by
  decide +kernel

theorem ck_w7k1nd2 : checkK 512 (.sub (.mul (.lin w7k1ndA) (.lin w7k1ndAi))
    (.add (.int 1) (.mul (.lin al7) (.lin w7k1ndCa)))) = true := by
  decide +kernel

theorem ck_w7k1sq1 : checkK 1152 (.sub (.sub (gE 1 (.lin w7k1x) 0) (.mul (.lin w7k1sqT) (.lin w7k1sqT)))
    (.mul (.mul (.lin w7P64) (.lin al7)) (.lin w7k1sqA))) = true := by
  decide +kernel

theorem ck_w7k1sq2 : checkK 640 (.sub (.mul (.lin w7k1sqT) (.lin w7k1sqT))
    (.mul (.lin w7P64) (.lin w7k1sqB))) = true := by
  decide +kernel

theorem ck_w7k1sq3 : checkK 512 (.sub (.mul (.lin w7k1sqB) (.lin w7k1sqBi))
    (.add (.int 1) (.mul (.lin al7) (.lin w7k1sqCb)))) = true := by
  decide +kernel

theorem ck_w7k1N : checkK 10944 (.sub (.mul (nE 1 (.lin w7k1x)) (.lin w7k1Nu)) (.int w7k1D)) = true := by
  decide +kernel

/-! ## The inputs at `w7` -/

theorem ne_zero_w7 : eltO al7 ≠ 0 := elt_ne_zero_of_absNorm absNorm_eltO_al7 (by norm_num)

/-- The atom `w7P64` is `al7 ^ 64` (six squarings). -/
theorem w7P64_eq : zkE w7P64 = zkE al7 ^ 64 := by
  have e2 := evK_eq_of_check _ _ _ ck_w7p2
  have e4 := evK_eq_of_check _ _ _ ck_w7p4
  have e8 := evK_eq_of_check _ _ _ ck_w7p8
  have e16 := evK_eq_of_check _ _ _ ck_w7p16
  have e32 := evK_eq_of_check _ _ _ ck_w7p32
  have e64 := evK_eq_of_check _ _ _ ck_w7p64
  simp only [evK_mul, evK_lin] at e2 e4 e8 e16 e32 e64
  rw [← e64, ← e32, ← e16, ← e8, ← e4, ← e2]; ring

/-- **`‖2‖ = 1` at `w7`.** -/
theorem norm_two_w7 : ‖(2 : w7.adicCompletion K21)‖ =
    ‖(((eltO al7 : 𝓞 K21) : K21) : w7.adicCompletion K21)‖ ^ 0 := by
  have e1 := evK_eq_of_check _ _ _ ck_w7two
  simp only [evK_mul, evK_lin, evK_add, evK_int, Int.cast_one, Int.cast_ofNat] at e1
  have c2 : ((2 : 𝓞 K21) : K21) = 2 := map_ofNat (algebraMap (𝓞 K21) K21) 2
  have c4 : ((4 : 𝓞 K21) : K21) = 4 := map_ofNat (algebraMap (𝓞 K21) K21) 4
  have ha : (2 : 𝓞 K21) * 4 = 1 + eltO al7 * zkO w7two := by
    have h3 : ((2 : 𝓞 K21) : K21) * ((4 : 𝓞 K21) : K21) =
        1 + ((eltO al7 : 𝓞 K21) : K21) * ((zkO w7two : 𝓞 K21) : K21) := by
      rw [M1.coe_zkO, coe_elt, c2, c4, e1]
    exact RingOfIntegers.ext (by push_cast; exact h3)
  have hb : (1 : 𝓞 K21) * 1 = 1 + eltO al7 * 0 := by ring
  have hx : (2 : K21) * ((1 : 𝓞 K21) : K21) =
      ((eltO al7 : 𝓞 K21) : K21) ^ ((0 : ℕ) : ℤ) * ((2 : 𝓞 K21) : K21) := by
    rw [c2, zpow_natCast, pow_zero, one_mul]; simp
  have h := primeOf_norm (hP := span_eltO_al7_isPrime) (hα := ne_zero_w7) ha hb hx
  rw [zpow_natCast] at h
  have h' : ‖((2 : K21) : w7.adicCompletion K21)‖ =
      ‖(((eltO al7 : 𝓞 K21) : K21) : w7.adicCompletion K21)‖ ^ 0 := h
  rw [← h', adic_coe_ofNat]

/-- `σ(c 1)` is not a square at `w7` (`4 c_1` has odd valuation 7). -/
theorem not_isSquare_c_w7 : ¬ IsSquare (adicCoe w7 (c 1)) := by
  have h : ¬ IsSquare (adicCoe w7 (evK (FE ((1 : Fin 2) : ℕ) 0))) :=
    ck_not_isSquare_odd _ _ _ _ _ ck_w7k1c1 ck_w7k1c2 (by decide)
  refine not_isSquare_of_sq_mul (u := (2 : w7.adicCompletion K21)) ?_ h
  rw [← four_mul_c, map_mul, map_ofNat]; norm_num

/-- `σ(ndK 1)` is not a square at `w7` (`46² ndK 1` has odd valuation 23). -/
theorem not_isSquare_ndK_w7 : ¬ IsSquare (adicCoe w7 (ndK 1)) := by
  have h : ¬ IsSquare (adicCoe w7 (evK (.lin (zL 1 2)))) :=
    ck_not_isSquare_odd _ _ _ _ _ ck_w7k1nd1 ck_w7k1nd2 (by decide)
  refine not_isSquare_of_sq_mul (u := (46 : w7.adicCompletion K21)) ?_ h
  rw [evK_lin, ← ndK_mul, map_mul, map_pow, map_ofNat]

/-- **`CountBound` at `w7`, twist 1** (base abscissa `w7k1x`). -/
theorem countBound_w7 [GoodSextic ((fRev 1).map (adicCoe w7))] :
    CountBound ((fRev 1).map (adicCoe w7)) 3 := by
  have c1 := evK_eq_of_check _ _ _ ck_w7k1sq1
  have c2 := evK_eq_of_check _ _ _ ck_w7k1sq2
  simp only [evK_sub, evK_mul, evK_lin] at c1 c2
  have hy : evK (gE ((1 : Fin 2) : ℕ) (.lin w7k1x) 0) - zkE w7k1sqT ^ 2 =
      ((eltO al7 : 𝓞 K21) : K21) ^ 65 * ((zkO w7k1sqA : 𝓞 K21) : K21) := by
    rw [coe_elt, M1.coe_zkO, sq, pow_succ, ← w7P64_eq]; exact c1
  have hs : zkE w7k1sqT ^ 2 = ((eltO al7 : 𝓞 K21) : K21) ^ 64 * ((zkO w7k1sqB : 𝓞 K21) : K21) := by
    rw [coe_elt, M1.coe_zkO, sq, ← w7P64_eq]; exact c2
  have hsq : IsSquare (adicCoe w7 (evK (gE ((1 : Fin 2) : ℕ) (.lin w7k1x) 0))) :=
    cert_isSquare norm_two_w7 hy hs (ck_unit ck_w7k1sq3) (by norm_num)
  have hne : evK (gE ((1 : Fin 2) : ℕ) (.lin w7k1x) 0) ≠ 0 :=
    cert_ne_zero span_eltO_al7_isPrime ne_zero_w7 hy hs (ck_unit ck_w7k1sq3) (by norm_num)
  have hsq' : IsSquare (adicCoe w7 ((fRev 1).eval (evK (.lin w7k1x)))) := by
    refine isSquare_of_sq_mul (u := (2 : w7.adicCompletion K21)) two_ne_zero ?_ hsq
    rw [← fRev_eval_eq, map_mul, map_ofNat]; norm_num
  have hx0 : (fRev 1).eval (evK (.lin w7k1x)) ≠ 0 := fun h => hne (by rw [← fRev_eval_eq, h, mul_zero])
  exact countBound_odd (adicCoe w7) isUniformizer_w7 (p := 7) (by norm_num) (by decide) (by norm_num)
    seven_eq_pow_mul_unit_w7 1 (evK (.lin w7k1x)) hsq' hx0 not_isSquare_c_w7
    (nAt_ne_zero_of_check 1 _ _ _ (by decide) _ ck_w7k1N) (tors_irrFactor _ 1 not_isSquare_ndK_w7)

end FurioLombardo.Discharge.SelmerBasis.Count
