(* ========================================================================= *)
(* Unit pc_p2b_close95 (Part 2B): the closed form of the Part 2C leaf        *)
(* P2B_COR_9_95_VIEW_FIX at (:real^3) (:real^3).  The routes of the inputs   *)
(* of COR_9_94_L (P2BC4C_COR_9_94_L_SPLIT_ROUND, pc_p2b_c994c) are           *)
(* discharged at real^3 with the closed theorems of pc_p2b_close9            *)
(* (ANCIENT_COMPACT, SPLIT_ROUND, ASYM_SOLITON, ASYM_SOLITON_AT, COR_9_10,   *)
(* KSOL_DRDT, BISHOP_GROMOV): THM_9_59 (pc_p2a_asv), LEMMA_9_65              *)
(* (pc_p2a_l965), the final-slice X0, X2 and COR_9_53 (pc_p2b_x0f,           *)
(* pc_p2b_shrinkfin), THM_9_64 (pc_p2a_t964), COR_9_44 (pc_rfa_c944 with     *)
(* pc_rfa_pinch3), PROP_9_58 (pc_p2a_kap0), COR_9_71 (pc_rfa_c971); then     *)
(* P2B_COR_9_95_VIEW_FROM_PARTS (pc_p2b_defs) with the limit parts of        *)
(* pc_p2b_ltr and pc_p2b_lim.                                                *)
(* Headlines: P2BZ5_COR_9_95_VIEW_FIX                                       *)
(*   |- P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3), and             *)
(*   P2BZ5_COR_9_95 |- !u. P2_COR_9_95_STATEMENT u (:real^3) (used in Part 3, *)
(*   with P2BCV_COR_9_95 of pc_p2b_canonv).                                  *)
(* ========================================================================= *)

needs "src/pc_p2b_close9.ml";;
needs "src/pc_p2b_c994c.ml";;
needs "src/pc_rfa_c944.ml";;
needs "src/pc_rfa_pinch3.ml";;
needs "src/pc_p2a_asv.ml";;
needs "src/pc_p2a_l965.ml";;
needs "src/pc_p2a_t964.ml";;
needs "src/pc_p2a_kap0.ml";;
needs "src/pc_rfa_c971.ml";;
needs "src/pc_p2b_x0f.ml";;
needs "src/pc_p2b_shrinkfin.ml";;
needs "src/pc_p2b_flatknc.ml";;
needs "src/pc_p2b_flatfwdreq.ml";;
needs "src/pc_p2a_flfin.ml";;
needs "src/pc_p2a_flow.ml";;
needs "src/pc_p2a_dd.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_rfa_splitend.ml";;
needs "src/pc_p2b_ltr.ml";;
needs "src/pc_p2b_lim.ml";;
needs "src/pc_p2b_defs.ml";;
needs "src/pc_p2b_canonv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The inputs of COR_9_94_L at (:real^3), then COR_9_94_L and the headline.  *)
(* Each step instantiates a route at (:real^3) and discharges its hypotheses *)
(* by closed theorems.                                                       *)
(* ========================================================================= *)

let P2BZ5_COR_9_44 = prove
 (`P2B_COR_9_44_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` RFA_P2B_COR_9_44_ROUTE) THEN
  REWRITE_TAC[P2B_COR_9_44_ROUTE_STATEMENT; RFA_P2B_REQ_PINCH_ROUND3]);;

let P2BZ5_THM_9_59 = prove
 (`P2B_THM_9_59_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` P2AV9_THM_9_59_ROUTE) THEN
  REWRITE_TAC[P2B_THM_9_59_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2BZ9_ASYM_SOLITON; P2BZ9_BISHOP_GROMOV; P2AD_REQ_DIST_DISTORTION]);;

let P2BZ5_LEMMA_9_65 = prove
 (`P2B_LEMMA_9_65_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` P2AL65_LEMMA_9_65_ROUTE) THEN
  REWRITE_TAC[P2B_LEMMA_9_65_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2BZ5_THM_9_59; P2BZ9_ANCIENT_COMPACT; P2BZ9_BISHOP_GROMOV; P2BZ9_KSOL_DRDT;
              RFA_P2B_REQ_SMP_SPLIT_PT; P2B_REQ_FLAT_KNC]);;

let P2BZ5_SPLIT_AT_INFINITY_FINAL = prove
 (`P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` P2B_SPLIT_AT_INFINITY_FINAL_ROUTE) THEN
  REWRITE_TAC[P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT; P2BZ9_ANCIENT_COMPACT]);;

let P2BZ5_CYL_AT_INFINITY_FINAL = prove
 (`P2B_CYL_AT_INFINITY_FINAL_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` P2B_CYL_AT_INFINITY_FINAL_ROUTE) THEN
  REWRITE_TAC[P2B_CYL_AT_INFINITY_FINAL_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2BZ5_SPLIT_AT_INFINITY_FINAL; P2BZ9_SPLIT_ROUND; P2B_REQ_FLAT_FORWARD]);;

let P2BZ5_COR_9_53_FINAL = prove
 (`P2B_COR_9_53_FINAL_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` P2B_COR_9_53_FINAL_ROUTE) THEN
  REWRITE_TAC[P2B_COR_9_53_FINAL_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2BZ5_CYL_AT_INFINITY_FINAL; P2AS_PROP_2_19_SEP]);;

let P2BZ5_THM_9_64 = prove
 (`P2B_THM_9_64_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` P2AT64_THM_9_64_ROUTE) THEN
  REWRITE_TAC[P2B_THM_9_64_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2BZ5_LEMMA_9_65; P2BZ9_KSOL_DRDT; P2BZ9_ANCIENT_COMPACT; P2BZ5_COR_9_53_FINAL]);;

let P2BZ5_PROP_9_58 = prove
 (`P2B_PROP_9_58_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` P2AK0_PROP_9_58_ROUTE) THEN
  REWRITE_TAC[P2B_PROP_9_58_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2BZ9_ASYM_SOLITON_AT; P2BZ5_COR_9_44; P2BZ9_COR_9_10; P2AU_FLOW_THM_8_1_3;
              P2AU_FLOW_SCALING]);;

let P2BZ5_COR_9_71 = prove
 (`P2B_COR_9_71_STATEMENT (:real^3)`,
  MATCH_MP_TAC(ISPEC `(:real^3)` RFA_C971_MAIN) THEN
  REWRITE_TAC[P2BZ5_LEMMA_9_65; P2BZ5_PROP_9_58]);;

let P2BZ5_COR_9_94_L = prove
 (`P2B_COR_9_94_L_STATEMENT (:real^3)`,
  MATCH_MP_TAC(ISPEC `(:real^3)` P2BC4C_COR_9_94_L_SPLIT_ROUND) THEN
  REWRITE_TAC[P2BZ9_SPLIT_ROUND; P2BZ5_THM_9_64; P2BZ5_PROP_9_58; P2BZ5_LEMMA_9_65;
              P2BZ5_COR_9_71; P2BZ5_COR_9_44; P2BZ9_ASYM_SOLITON]);;

let P2BZ5_COR_9_95_VIEW_FIX = prove
 (`P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3)`,
  MATCH_MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`] P2B_COR_9_95_VIEW_FROM_PARTS) THEN
  REWRITE_TAC[P2BZ5_COR_9_94_L; P2B_LIMIT_TRANSFER_VIEW; P2B_SEP_LIMIT_VIEW;
              P2B_LORIENT_LIMIT_VIEW]);;

(* ========================================================================= *)
(* MT Cor 9.95 for histories in canonv form at w = (:real^3) (Part 3 uses    *)
(* the instance u = (:A+num#num#real^3)).                                    *)
(* ========================================================================= *)

let P2BZ5_COR_9_95 = prove
 (`!u:A->bool. P2_COR_9_95_STATEMENT u (:real^3)`,
  GEN_TAC THEN MATCH_MP_TAC P2BCV_COR_9_95 THEN
  REWRITE_TAC[P2BZ5_COR_9_94_L; P2BZ5_PROP_9_58]);;

