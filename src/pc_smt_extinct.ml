(* ========================================================================= *)
(* pc_smt_extinct: finite extinction for the Ricci flow with surgery,        *)
(* RFS_EXTINCTION (RFS_EXTINCTION_STATEMENT of pc_rfs_top, T2, at every      *)
(* type). It is P3_FULL_CHAIN_2 of pc_p3_route2 at w = (:real^3): the Part 2 *)
(* statements come from P2CFN_P2_ALL (pc_p2c_final) at (:A+num#num#real^3),  *)
(* the C2 bounds from RFA_P3_HIST_C2_BOUND (pc_rfa_histc2c) with             *)
(* P2CY_HISTORY_REGULAR and RFA_P3_STD_C2_BOUND (pc_rfa_stdc2) with 12.5,    *)
(* 12.32 and 12.31, and the other hypotheses from their proving theorems     *)
(* (P2CR_PROP_5_14 for 5.14 at (:A+num#num#real^3) (:real^3),                *)
(* P4_EXTINCTION_ALL for the extinction step at every type).                 *)
(* ========================================================================= *)

needs "src/pc_p3_route2.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_p2a_c712w.ml";;
needs "src/pc_p2a_l314.ml";;
needs "src/pc_p2a_l72w.ml";;
needs "src/pc_p2a_norm.ml";;
needs "src/pc_p2a_t81u.ml";;
needs "src/pc_p2a_vgrow.ml";;
needs "src/pc_p2b_cap.ml";;
needs "src/pc_p2b_capfix.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2c_final.ml";;
needs "src/pc_p2c_fl514.ml";;
needs "src/pc_p2c_fview.ml";;
needs "src/pc_p2c_hreg.ml";;
needs "src/pc_p3_c1712r.ml";;
needs "src/pc_p3_c171e.ml";;
needs "src/pc_p3_c172f.ml";;
needs "src/pc_p3_c177e.ml";;
needs "src/pc_p3_s13thm.ml";;
needs "src/pc_p3_s14glue.ml";;
needs "src/pc_p3_s161.ml";;
needs "src/pc_p3_s1621.ml";;
needs "src/pc_p3_s1624.ml";;
needs "src/pc_p3_s164.ml";;
needs "src/pc_p3_s16l15.ml";;
needs "src/pc_p3_s16len.ml";;
needs "src/pc_p3_s16prop5.ml";;
needs "src/pc_p3_s16small.ml";;
needs "src/pc_p3e_152h.ml";;
needs "src/pc_p3e_15_11.ml";;
needs "src/pc_p3e_flowext.ml";;
needs "src/pc_p3e_start.ml";;
needs "src/pc_p4_final.ml";;
needs "src/pc_pde_final.ml";;
needs "src/pc_pv411.ml";;
needs "src/pc_rf_glue.ml";;
needs "src/pc_rf_unique.ml";;
needs "src/pc_rfa_histc2c.ml";;
needs "src/pc_rfa_pinch.ml";;
needs "src/pc_rfa_shi328.ml";;
needs "src/pc_rfa_shi329.ml";;
needs "src/pc_rfa_stdc2.ml";;
needs "src/pc_rfs_ccsc.ml";;
needs "src/pc_smt_orient.ml";;
needs "src/pc_smt_sep.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The assembly of RFS_EXTINCTION from P3_FULL_CHAIN_2 at w = (:real^3), the *)
(* Part 2 statements P2CFN_P2_ALL at (:A+num#num#real^3), the C2 bounds      *)
(* RFA_P3_HIST_C2_BOUND and RFA_P3_STD_C2_BOUND, and the other leaves of the *)
(* chain.                                                                    *)
(* ========================================================================= *)

let RFS_EXTINCTION = prove
 (`!u:A->bool. RFS_EXTINCTION_STATEMENT u`,
  GEN_TAC THEN
  MATCH_MP_TAC(ISPECL [`u:A->bool`; `(:real^3)`] P3_FULL_CHAIN_2) THEN
  MP_TAC(ISPEC `(:A+num#num#real^3)` P2CFN_P2_ALL) THEN STRIP_TAC THEN
  SUBGOAL_THEN `P3_STD_C2_BOUND_STATEMENT` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_P3_STD_C2_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_HIST_C2_BOUND_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_P3_HIST_C2_BOUND THEN REWRITE_TAC[P2CY_HISTORY_REGULAR];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[P3E_START_ROUTE; P3E_FLOW_EXTENSION_ROUTE; P3_THM_13_2_ROUTE;
                  P3_LEMMA_14_11_ROUTE; P3E_LEMMA_15_11_ROUTE; P3E_PROP_15_2_ROUTE;
                  P3N_PROP_16_5_ROUTE; P3N_PROP_16_13_ROUTE; P3N_LEMMA_16_15_ROUTE;
                  P3N_PROP_16_21_ROUTE; P3N_COR_16_24_ROUTE; P3N_PROP_16_4_ROUTE;
                  P3L_PROP_16_1_ROUTE; P3_LEMMA_17_2_ROUTE; P3_LEMMA_17_7_ROUTE;
                  P3_PROP_17_1_ROUTE_2; P3_LEMMA_17_12_ROUTE; P3N_SMALL_SCALE;
                  PDEF_CURVATURE_TIME; PDEF_MAXIMAL_FLOW; PDE_UNIQUENESS; PDE_GLUE;
                  RFA_P2_THM_3_28; RFA_P2_THM_3_29; P2AR_LEMMA_3_14;
                  PV411_PROP_4_11_VOLUME; RFA_P2_THM_4_32; P2AQ_VOLUME_GROWTH;
                  P2AT_THM_8_1; P2AY_LEMMA_7_2; P2AY_COR_7_12; P2_PROP_9_79_SLICE;
                  P2CFN_PROP_9_79_NECK; P2CR_PROP_5_14; P2CY_HISTORY_REGULAR;
                  RFS_CUTCAP_SC; SMT_SC_SPHERE_SEP; P2AS_PROP_2_19_SEP; P2B_SEP_LIMIT;
                  P2_PROP_9_79_OPEN; P2C_FLOW_VIEW_REGULAR; P4_EXTINCTION_ALL;
                  P2AN_NORMALIZE; SMT_ORIENTABLE]);;

