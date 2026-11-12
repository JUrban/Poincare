(* ========================================================================= *)
(* Unit pc_p2c_c1116u (Part 2C): MT Corollary 11.16 in flow form without     *)
(* hypotheses, P2C_COR_11_16_FLOW.  The five route inputs of                 *)
(* P2C_COR_11_16_FLOW_ROUTE are proved elsewhere: P2AE_REQ_HARNACK           *)
(* (pc_p2a_harn), P2AD_REQ_DIST_DISTORTION (pc_p2a_dd), CMP_A7_LEMMA_11_13   *)
(* (pc_cmp_a7), RFA_P2C_REQ_SCALAR_MIN (pc_rfa_screq) and                    *)
(* APX_NO_CAP_IN_NECK_UNCOND (pc_apx_neck).                                  *)
(* ========================================================================= *)

needs "src/pc_p2c_c1116.ml";;
needs "src/pc_p2a_harn.ml";;
needs "src/pc_p2a_dd.ml";;
needs "src/pc_cmp_a7.ml";;
needs "src/pc_rfa_screq.ml";;
needs "src/pc_apx_neck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The unconditional corollary.                                              *)
(* ------------------------------------------------------------------------- *)

let P2C_COR_11_16_FLOW = prove
 (`!w:B->bool. P2C_COR_11_16_FLOW_STATEMENT w`,
  GEN_TAC THEN
  MP_TAC(SPEC `w:B->bool` P2C_COR_11_16_FLOW_ROUTE) THEN
  REWRITE_TAC[P2C_COR_11_16_FLOW_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2AE_REQ_HARNACK; P2AD_REQ_DIST_DISTORTION; RFA_P2C_REQ_SCALAR_MIN;
              APX_NO_CAP_IN_NECK_UNCOND] THEN
  MP_TAC(ISPEC `w:B->bool` CMP_A7_LEMMA_11_13) THEN
  REWRITE_TAC[CMP_A7_LEMMA_11_13_STATEMENT; P2C_REQ_LEMMA_11_13_STATEMENT]);;

