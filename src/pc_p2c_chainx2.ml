(* ========================================================================= *)
(* Unit pc_p2c_chainx2 (Part 2C): the chain P2CX_CHAIN_OPEN2 of              *)
(* pc_p2c_chainx with more hypotheses discharged.  P2CX2_CHAIN_OPEN3         *)
(* discharges P2C_REQ_NONNEG_BOUNDED_SLICE at real^3                         *)
(* (P2B_NONNEG_BOUNDED_SLICE_ROUTE of pc_p2b_a4s with P2AS_PROP_2_19_SEP of  *)
(* pc_p2a_219), P2C_STD_PROPS_ROUTE at real^4 (STDS_PROPS_ROUTE,             *)
(* pc_p2c_stdc4) and P2C_LEMMA_11_30_ROUTE (P2HN_LEMMA_11_30_ROUTE,          *)
(* pc_p2c_horns); P2CX2_CHAIN_OPEN4 and P2CX2_CHAIN_OPEN5 discharge the 11.8 *)
(* view route, the 10.2 view and the 11.31 route and reduce AVR_ZERO_FIX to  *)
(* ASYM_SOLITON.  The three hypotheses of P2CX2_CHAIN_OPEN5 are discharged   *)
(* in pc_p2c_final.                                                          *)
(* ========================================================================= *)

needs "src/pc_p2c_chainx.ml";;
needs "src/pc_p2b_a4s.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_p2c_stdc4.ml";;
needs "src/pc_p2c_horns.ml";;
needs "src/pc_p2c_blowup3.ml";;
needs "src/pc_p2c_horns2.ml";;
needs "src/pc_p2b_tuberoute.ml";;
needs "src/pc_p2b_avrz.ml";;
needs "src/pc_p2a_asv.ml";;
needs "src/pc_cmp_bg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The slice statement and the chain with eight hypotheses.                  *)
(* ------------------------------------------------------------------------- *)

let P2CX2_NONNEG_BOUNDED_SLICE = prove
 (`P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (:real^3)`,
  MATCH_MP_TAC(ISPEC `(:real^3)` P2B_NONNEG_BOUNDED_SLICE_ROUTE) THEN
  REWRITE_TAC[P2AS_PROP_2_19_SEP]);;

let P2CX2_CHAIN_OPEN3 = prove
 (`!(u:A->bool).
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT u (:real^3) /\
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_THM_11_31_ROUTE_STATEMENT u /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT (:real^3) /\
     P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
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
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2CX_CHAIN_OPEN2 THEN
  ASM_REWRITE_TAC[P2HN_LEMMA_11_30_ROUTE; STDS_PROPS_ROUTE; P2CX2_NONNEG_BOUNDED_SLICE]);;

(* ------------------------------------------------------------------------- *)
(* Five more hypotheses discharged.  The 11.8 view route at both instances   *)
(* (P2BU_THM_11_8_VIEW_ROUTE, pc_p2c_blowup3), the 10.2 view at both         *)
(* instances (P2BT_THM_10_2_VIEW, pc_p2b_tuberoute), the 11.31 route         *)
(* (P2HN_THM_11_31_ROUTE, pc_p2c_horns2); AVR_ZERO_FIX reduced to            *)
(* ASYM_SOLITON through P2B_AVR_ZERO_ROUTE (pc_p2b_avrz) and                 *)
(* P2AV9_THM_9_59_ROUTE (pc_p2a_asv), with Bishop-Gromov from                *)
(* CMP_T3_BISHOP_GROMOV_P2B (pc_cmp_bg) and DIST_DISTORTION from             *)
(* P2AD_REQ_DIST_DISTORTION.  The hypotheses of P2CX2_CHAIN_OPEN5 are the    *)
(* Part 2B statements COR_9_95_VIEW_FIX, KAPPA_NECKS_ROUND_L_FIX and         *)
(* ASYM_SOLITON at real^3.                                                   *)
(* ------------------------------------------------------------------------- *)

let P2CX2_CHAIN_OPEN4 = prove
 (`!(u:A->bool).
     P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
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
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2CX2_CHAIN_OPEN3 THEN
  ASM_REWRITE_TAC[P2BU_THM_11_8_VIEW_ROUTE; P2HN_THM_11_31_ROUTE; P2BT_THM_10_2_VIEW]);;

let P2CX2_AVR_ZERO_FIX = prove
 (`P2B_ASYM_SOLITON_STATEMENT (:real^3) ==> P2B_AVR_ZERO_FIX_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_AVR_ZERO_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_AVR_ZERO_ROUTE)) THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_THM_9_59_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2AV9_THM_9_59_ROUTE)) THEN
  ASM_REWRITE_TAC[P2AD_REQ_DIST_DISTORTION] THEN
  MP_TAC(ISPEC `(:real^3)` CMP_T3_BISHOP_GROMOV_P2B) THEN
  REWRITE_TAC[CMP_T3_BISHOP_GROMOV_P2B_STATEMENT; P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT]);;

let P2CX2_CHAIN_OPEN5 = prove
 (`!(u:A->bool).
     P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
     P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\
     P2B_ASYM_SOLITON_STATEMENT (:real^3)
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
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2CX2_CHAIN_OPEN4 THEN
  ASM_SIMP_TAC[P2CX2_AVR_ZERO_FIX]);;

