(* ========================================================================= *)
(* Unit pc_p2c_chainx (Part 2C): the chain P2CX_CHAIN_OPEN of                *)
(* pc_p2c_chainasm with the hypotheses proved in the units loaded here       *)
(* discharged, at D = real^4 (the carrier of STDS_PARTIAL_EXISTS_ROUTE).     *)
(* P2CX_CHAIN_OPEN2 keeps eleven hypotheses, discharged in pc_p2c_chainx2    *)
(* and pc_p2c_final: the Thm 11.8 view route (two instances), the Lemma      *)
(* 11.30 and Thm 11.31 routes, STD_PROPS_ROUTE (:real^4), the Thm 10.2 view  *)
(* (two instances), and the Part 2B kappa-solution statements                *)
(* COR_9_95_VIEW_FIX, NONNEG_BOUNDED_SLICE, KAPPA_NECKS_ROUND_L_FIX and      *)
(* AVR_ZERO_FIX.                                                             *)
(* ========================================================================= *)

needs "src/pc_p2c_chainasm.ml";;
needs "src/pc_p2c_blowup.ml";;
needs "src/pc_p2c_sing.ml";;
needs "src/pc_p2c_sing2.ml";;
needs "src/pc_p2c_sing3.ml";;
needs "src/pc_p2c_stdflow.ml";;
needs "src/pc_p2c_hfl.ml";;
needs "src/pc_p2c_mxr.ml";;
needs "src/pc_apx_twoendsreq.ml";;
needs "src/pc_p2a_harn.ml";;
needs "src/pc_p2a_dd.ml";;
needs "src/pc_p2a_l314.ml";;
needs "src/pc_apx_ncends.ml";;
needs "src/pc_p2b_flatfwd.ml";;
needs "src/pc_p2b_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The two bridges (same bodies) and the chain P2CX_CHAIN_OPEN2.             *)
(* ------------------------------------------------------------------------- *)

(* P2B_FLAT_FORWARD_BODY has exactly the body of P2B_REQ_FLAT_FORWARD. *)

let P2CX_REQ_FLAT_FORWARD = prove
 (`!u:A->bool. P2B_REQ_FLAT_FORWARD_STATEMENT u`,
  REWRITE_TAC[P2B_REQ_FLAT_FORWARD_STATEMENT; P2B_FLAT_FORWARD_BODY]);;

(* P2C_REQ_NONNEG_BOUNDED_FIX and P2B_NONNEG_BOUNDED_FIX have the same body;  *)
(* P2B_NONNEG_BOUNDED_SLICE_IMP_FIX reduces both to the slice form.           *)

let P2CX_NONNEG_BOUNDED_FIX_FROM_SLICE = prove
 (`!u:A->bool. P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT u
               ==> P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT u`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2B_NONNEG_BOUNDED_SLICE_IMP_FIX) THEN
  REWRITE_TAC[P2B_NONNEG_BOUNDED_FIX_STATEMENT; P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT]);;

let P2CX_CHAIN_OPEN2 = prove
 (`!(u:A->bool).
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT u (:real^3) /\
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_LEMMA_11_30_ROUTE_STATEMENT u /\
     P2C_THM_11_31_ROUTE_STATEMENT u /\
     P2C_STD_PROPS_ROUTE_STATEMENT (:real^4) /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT (:real^3) /\
     P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (:real^3) /\
     P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\
     P2B_AVR_ZERO_FIX_STATEMENT (:real^3)
     ==> P2_THM_5_11_STATEMENT u (:real^3) /\
         P2C_THM_5_15_STATEMENT u (:real^3) /\
         P2C_LEMMA_11_2_STATEMENT u /\
         P2C_THM_11_8_STATEMENT u (:real^3) /\
         P2C_LEMMA_11_23_STATEMENT u /\
         P2C_THM_11_19_STATEMENT u /\
         P2C_LEMMA_11_30_STATEMENT u /\
         P2C_THM_11_31_STATEMENT u /\
         P2_LEMMA_12_3_STATEMENT /\
         P2_THM_12_5_STATEMENT /\
         P2_STD_EXTEND_STATEMENT /\
         P2_PROP_12_7_STATEMENT /\
         P2_PROP_12_31_STATEMENT /\
         P2C_THM_12_32_STATEMENT /\
         P2_LEMMA_12_37_STATEMENT`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`u:A->bool`; `(:real^4)`] P2CX_CHAIN_OPEN) THEN
  ASM_SIMP_TAC[P2BU_THM_11_1_VIEW_ROUTE; P2C_LEMMA_11_21_ROUTE; P2C_LEMMA_11_23_ROUTE;
               P2C_LEMMA_11_23_MAXEXT_ROUTE; STDS_UNIQUE_ROUTE; STDS_PARTIAL_EXISTS_ROUTE;
               P2UF_HIST_FLOWLINE_PERSIST; P2UM_MAXEXT_REGULAR; APXT_TWO_ENDS_NO_CAP;
               P2AE_REQ_HARNACK; P2AD_REQ_DIST_DISTORTION; P2AR_LEMMA_3_14;
               APXN_A25_NC_ENDS; P2CX_REQ_FLAT_FORWARD; P2CX_NONNEG_BOUNDED_FIX_FROM_SLICE]);;

