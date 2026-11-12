(* ========================================================================= *)
(* Unit pc_p2c_chainasm (Part 2C): the chain assembly.  P2C_FULL_CHAIN       *)
(* (pc_p2c_iface) is applied to every hypothesis that the units loaded here  *)
(* prove (in Part 2C and in the other layers); the result, P2CX_CHAIN_OPEN,  *)
(* derives the Part 2C theorems from the hypotheses listed in its statement, *)
(* which pc_p2c_chainx, pc_p2c_chainx2 and pc_p2c_final discharge.           *)
(* ========================================================================= *)

needs "src/pc_apx_a21.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_smt_sep.ml";;
needs "src/pc_apx_event.ml";;
needs "src/pc_cmp_relvol.ml";;
needs "src/pc_p2c_cderiv.ml";;
needs "src/pc_p2c_cg.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_p2c_hreg.ml";;
needs "src/pc_p2c_l112.ml";;
needs "src/pc_p2c_fl514.ml";;
needs "src/pc_p2b_capfix.ml";;
needs "src/pc_rfa_screq.ml";;
needs "src/pc_rfa_secpres.ml";;
needs "src/pc_rfa_smppos.ml";;
needs "src/pc_p2c_fl511.ml";;
needs "src/pc_p3_s13rot.ml";;
needs "src/pc_p2c_stdinit.ml";;
needs "src/pc_rfa_shi328.ml";;
needs "src/pc_rfa_shi329.ml";;
needs "src/pc_p3_s14glue.ml";;
needs "src/pc_pde_final.ml";;
needs "src/pc_rf_glue.ml";;
needs "src/pc_cmp_cgt.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_cmp_a7.ml";;
needs "src/pc_p2b_979s.ml";;
needs "src/pc_rf_unique_a14u.ml";;
needs "src/pc_p2c_fl515.ml";;
needs "src/pc_p2c_t533.ml";;
needs "src/pc_p2c_stdgeom.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Bridges to the statements proved under other names, and the chain         *)
(* P2CX_CHAIN_OPEN.                                                          *)
(* ------------------------------------------------------------------------- *)

let P2CX_REQ_CGT = prove
 (`!u:A->bool. P2C_REQ_CGT_STATEMENT u`,
  GEN_TAC THEN MP_TAC(SPEC `u:A->bool` CMP_T2_CGT) THEN
  REWRITE_TAC[CMP_T2_CGT_STATEMENT; P2C_REQ_CGT_STATEMENT]);;

let P2CX_REQ_BISHOP_GROMOV = prove
 (`!u:A->bool. P2C_REQ_BISHOP_GROMOV_STATEMENT u`,
  GEN_TAC THEN MP_TAC(SPEC `u:A->bool` CMP_T1_BISHOP_GROMOV) THEN
  REWRITE_TAC[CMP_T1_BISHOP_GROMOV_STATEMENT; P2C_REQ_BISHOP_GROMOV_STATEMENT]);;

let P2CX_REQ_LEMMA_11_13 = prove
 (`!u:A->bool. P2C_REQ_LEMMA_11_13_STATEMENT u`,
  GEN_TAC THEN MP_TAC(SPEC `u:A->bool` CMP_A7_LEMMA_11_13) THEN
  REWRITE_TAC[CMP_A7_LEMMA_11_13_STATEMENT; P2C_REQ_LEMMA_11_13_STATEMENT]);;

let P2CX_REQ_NECK_FIX = prove
 (`!(u:A->bool) (w:B->bool). P2C_REQ_NECK_FIX_STATEMENT u w`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL [`u:A->bool`; `w:B->bool`] P2B_PROP_9_79_NECK_FIX) THEN
  REWRITE_TAC[P2B_PROP_9_79_NECK_FIX_STATEMENT; P2C_REQ_NECK_FIX_STATEMENT]);;

let P2CX_REQ_UNIQ_COMPLETE = prove
 (`P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3)`,
  REWRITE_TAC[P2C_REQ_UNIQ_COMPLETE_STATEMENT] THEN MATCH_ACCEPT_TAC RFU_A14);;

let P2CX_HISTORY_REGULAR_ROUTE = prove
 (`!u:A->bool. P2C_HISTORY_REGULAR_ROUTE_STATEMENT u`,
  REWRITE_TAC[P2C_HISTORY_REGULAR_ROUTE_STATEMENT; P2CY_HISTORY_REGULAR]);;

let P2CX_PROP_5_14_ROUTE = prove
 (`!(u:A->bool) (w:B->bool). P2C_PROP_5_14_ROUTE_STATEMENT u w`,
  REWRITE_TAC[P2C_PROP_5_14_ROUTE_STATEMENT; P2CR_PROP_5_14]);;

(* The Part 2C theorems from the hypotheses below (discharged in             *)
(* pc_p2c_chainx, pc_p2c_chainx2 and pc_p2c_final); the proof uses Thm 5.15  *)
(* from pc_p2c_fl515, Thm 5.33 from pc_p2c_t533 and the bounded geometry of  *)
(* the standard initial metrics from pc_p2c_stdgeom.                         *)

let P2CX_CHAIN_OPEN = prove
 (`!(u:A->bool) (d:D->bool).
     P2C_THM_11_1_VIEW_ROUTE_STATEMENT u (:real^3) /\
     P2C_THM_11_1_VIEW_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT u (:real^3) /\
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_LEMMA_11_21_ROUTE_STATEMENT u /\
     P2C_LEMMA_11_23_ROUTE_STATEMENT u /\
     P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT u /\
     P2C_LEMMA_11_30_ROUTE_STATEMENT u /\
     P2C_THM_11_31_ROUTE_STATEMENT u /\
     P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT d /\
     P2C_STD_UNIQUE_ROUTE_STATEMENT /\
     P2C_STD_PROPS_ROUTE_STATEMENT d /\
     P2C_HIST_FLOWLINE_PERSIST_STATEMENT u /\
     P2C_MAXEXT_REGULAR_STATEMENT u /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT (:real^3) /\
     P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
     P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT (:real^3) /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (:real^3) /\
     P2B_REQ_FLAT_FORWARD_STATEMENT (:real^3) /\
     P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\
     P2B_AVR_ZERO_FIX_STATEMENT (:real^3) /\
     P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT (:real^3) /\
     P2C_REQ_HARNACK_STATEMENT (:real^3) /\
     P2C_REQ_DIST_DISTORTION_STATEMENT (:real^3) /\
     APX_A25_NC_ENDS_STATEMENT u /\
     P2_LEMMA_3_14_STATEMENT (:real^3)
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
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC P2C_FULL_CHAIN THEN
  ASM_REWRITE_TAC[P2CO_THM_5_15_ROUTE; P2CP_THM_5_33; P2CN_STD_BOUNDED_GEOM;
                  APX_A21; APX_NECK_CURV; APX_NO_CAP_IN_NECK_UNCOND; SMT_SC_SPHERE_SEP;
                  APX_SEP_OPEN; CMP_RELVOL; P2C_CANON_DERIV; P2CK_CG_COMPACT_ROUTE;
                  P2C_FLOW_VIEW_REGULAR; P2C_FLOW_VIEW_REGULAR_UPTO; P2CX_HISTORY_REGULAR_ROUTE;
                  P2C_LEMMA_11_2_DB; P2CX_PROP_5_14_ROUTE; P2C_REQ_CAP_FIX;
                  RFA_P2C_REQ_SCALAR_MIN; RFA_P2C_REQ_SEC_PRESERVED; P2C_REQ_SLICE_FIX;
                  P2C_REQ_SLICE_LOCAL; RFA_P2C_REQ_SMP_POS; P2CW_THM_5_11_ROUTE;
                  P3S_LEMMA_12_37; P2C_LEMMA_12_3; RFA_P2_THM_3_28; RFA_P2_THM_3_29;
                  P3_LEMMA_14_11; PDEF_CURVATURE_TIME; PDE_GLUE; P2CX_REQ_CGT;
                  P2CX_REQ_BISHOP_GROMOV; P2CX_REQ_LEMMA_11_13; P2CX_REQ_NECK_FIX;
                  P2CX_REQ_UNIQ_COMPLETE] THEN
  EXISTS_TAC `d:D->bool` THEN ASM_REWRITE_TAC[]);;

