/- local_axioms.lean: `#print axioms` of the local layer.
   Run from lean/, after `lake build` of the imported modules:
     lake env lean ../code/selmer-local-conditions/local_axioms.lean \
       > ../code/selmer-local-conditions/local_axioms.out 2>&1 -/
import FurioLombardo.Discharge.SelmerBasis.PlaceV
import FurioLombardo.Discharge.SelmerBasis.PlaceReal
import FurioLombardo.Discharge.SelmerBasis.LocalGlue
import FurioLombardo.Discharge.SelmerBasis.LocalLemmas
import FurioLombardo.Discharge.SelmerBasis.QuadField
import FurioLombardo.Discharge.SelmerBasis.QuadLocal
import FurioLombardo.Discharge.SelmerBasis.Spanning

#print axioms FurioLombardo.Discharge.SelmerBasis.indepImage_v
#print axioms FurioLombardo.Discharge.SelmerBasis.indepImage_of_coords
#print axioms FurioLombardo.Discharge.SelmerBasis.coordCond_of_coords
#print axioms FurioLombardo.Discharge.SelmerBasis.hcert_indep_of_bits
#print axioms FurioLombardo.Discharge.SelmerBasis.hcert_coord_of_bits
#print axioms FurioLombardo.Discharge.SelmerBasis.indep_of_components
#print axioms FurioLombardo.Discharge.SelmerBasis.goodSextic_map
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_coord
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_mem_iff
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_indep_of_echelonOK
#print axioms FurioLombardo.Discharge.SelmerBasis.eq_zero_of_leftInvOK
#print axioms FurioLombardo.Discharge.SelmerBasis.ann_of_mem_sup
#print axioms FurioLombardo.Discharge.SelmerBasis.dotRow_sound
#print axioms FurioLombardo.Discharge.SelmerBasis.isSquare_one_add_four_mul
#print axioms FurioLombardo.Discharge.SelmerBasis.isSquare_of_norm_div_sq_sub_one_lt
#print axioms FurioLombardo.Discharge.SelmerBasis.res_F2
#print axioms FurioLombardo.Discharge.SelmerBasis.res_F4
#print axioms FurioLombardo.Discharge.SelmerBasis.vs_residue_eq_iff
#print axioms FurioLombardo.Discharge.SelmerBasis.adic_normUnif
#print axioms FurioLombardo.Discharge.SelmerBasis.adic_residue_card
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_depth_step
#print axioms FurioLombardo.Discharge.SelmerBasis.compOK_odd
#print axioms FurioLombardo.Discharge.SelmerBasis.compOK_F2
#print axioms FurioLombardo.Discharge.SelmerBasis.comp_test
#print axioms FurioLombardo.Discharge.SelmerBasis.mem_span_of_kerSpanOK
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_span_dyadic
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_span_odd
#print axioms FurioLombardo.Discharge.SelmerBasis.compOK_F4
#print axioms FurioLombardo.Discharge.SelmerBasis.goodSextic_real
#print axioms FurioLombardo.Discharge.SelmerBasis.realEmb_lc_neg
#print axioms FurioLombardo.Discharge.SelmerBasis.coordCond_real
#print axioms FurioLombardo.Discharge.SelmerBasis.prod_pow_sign
#print axioms FurioLombardo.Discharge.SelmerBasis.QF.norm_sq
#print axioms FurioLombardo.Discharge.SelmerBasis.QF.norm_conj
#print axioms FurioLombardo.Discharge.SelmerBasis.qf_norm_mk
#print axioms FurioLombardo.Discharge.SelmerBasis.qfE_norm
#print axioms FurioLombardo.Discharge.SelmerBasis.qfE_norm_Y
#print axioms FurioLombardo.Discharge.SelmerBasis.qfE_two
#print axioms FurioLombardo.Discharge.SelmerBasis.no_root_eisen
#print axioms FurioLombardo.Discharge.SelmerBasis.qfU_norm_form
#print axioms FurioLombardo.Discharge.SelmerBasis.no_root_unram'
#print axioms FurioLombardo.Discharge.SelmerBasis.qfU_norm
#print axioms FurioLombardo.Discharge.SelmerBasis.qfU_omega
#print axioms FurioLombardo.Discharge.SelmerBasis.qfU_two
#print axioms FurioLombardo.Discharge.SelmerBasis.sq_cert_perturb
#print axioms FurioLombardo.Discharge.SelmerBasis.dfact_one_chr
#print axioms FurioLombardo.Discharge.SelmerBasis.dfact_odd_std
#print axioms FurioLombardo.Discharge.SelmerBasis.dfact_four_std
#print axioms FurioLombardo.Discharge.SelmerBasis.dfact_one_four
#print axioms FurioLombardo.Discharge.SelmerBasis.dfact_pi
#print axioms FurioLombardo.Discharge.SelmerBasis.liftW_zero
#print axioms FurioLombardo.Discharge.SelmerBasis.liftW_two_pow
#print axioms FurioLombardo.Discharge.SelmerBasis.no_root_ram
#print axioms FurioLombardo.Discharge.SelmerBasis.no_root_unram
#print axioms FurioLombardo.Discharge.SelmerBasis.norm_eval_sub_le
#print axioms FurioLombardo.Discharge.SelmerBasis.norm_sq_add_mul_add_sq
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_prod_sub_lt
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_prod_one_add_mul
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_test_odd
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_test_four
#print axioms FurioLombardo.Discharge.SelmerBasis.sb_test_chr
#print axioms FurioLombardo.Discharge.SelmerBasis.qfE_norm_form
#print axioms FurioLombardo.Discharge.SelmerBasis.qfE_normUnif
#print axioms FurioLombardo.Discharge.SelmerBasis.qfE_res
#print axioms FurioLombardo.Discharge.SelmerBasis.qfU_normUnif
#print axioms FurioLombardo.Discharge.SelmerBasis.qfU_res
