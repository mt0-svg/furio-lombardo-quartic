import FurioLombardo.Discharge.SelmerBasis.SUnitRank
import FurioLombardo.Discharge.SelmerBasis.SUnitSpan
import FurioLombardo.Discharge.SelmerBasis.SUnitRes
import FurioLombardo.Discharge.SelmerBasis.SUnitMem
import FurioLombardo.Discharge.SelmerBasis.SUnitIndep

/-! Axioms of the SUnitSpan lemmas. Run from lean/:
`lake env lean ../code/selmer-global-bound/sunit_axioms.lean > ../code/selmer-global-bound/sunit_axioms.out 2>&1` -/

open FurioLombardo.Discharge.SelmerBasis

#print axioms sUnitSpan_L42
#print axioms sUnitSpan_N84
#print axioms gensL_ne_zero
#print axioms gensN_ne_zero
#print axioms gensL_mem
#print axioms gensN_mem
#print axioms gensL_indep
#print axioms gensN_indep

#print axioms rank_L42_le
#print axioms rank_N84_le
#print axioms S27_L42_finite
#print axioms ncard_S27_L42
#print axioms S27_N84_finite
#print axioms ncard_S27_N84
#print axioms clTwo_L42
#print axioms clTwo_N84
#print axioms sUnitSpan_of
#print axioms sUnitSpan_L42_of
#print axioms sUnitSpan_N84_of
#print axioms isSquare_mul_prod_of_mod_two
#print axioms isSquare_of_chars
#print axioms ncard_primesOver_mul_le
#print axioms two_le_ramificationIdx_of_eisenstein
#print axioms two_le_inertiaDeg_of_inert
#print axioms inertiaDeg_eq_one_of_two_le_ramificationIdx
#print axioms mem_of_quadratic_mem
#print axioms ncard_biUnion_le
#print axioms mem_selmerGroup_of_even_count
#print axioms mem_selmerGroup_of_mul_eq
#print axioms quad_coords_integral
#print axioms isSquare_of_isSquare_map
#print axioms leftInv_apply
#print axioms coord_of_chars
#print axioms indep_of_chars
#print axioms SU.ιL_injective
#print axioms SU.exists_DL_mul
#print axioms SU.ιN_injective
#print axioms SU.exists_DN_mul
#print axioms SU.ρK_zkO
#print axioms SU.ρL_mk
#print axioms SU.ρN_mk
#print axioms SU.isSquare_ρL
#print axioms SU.isSquare_ρN
#print axioms SU.rowL_spec
#print axioms SU.rowN_spec
