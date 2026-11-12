(* ========================================================================= *)
(* Unit pc_p2b_close9: the closing composition of Part 2 Chapter 9 at the    *)
(* carrier real^3.  The route theorems of the Ch 9 units are instantiated at *)
(* w = (:real^3) and chained.  First every result is proved conditional on   *)
(* P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3) (the theorems with the    *)
(* suffix _COND); then that hypothesis comes from                            *)
(* P2BAC_ANCIENT_COMPACT_ROUTE (pc_p2b_ancc) and P2CK_CG_COMPACT (pc_p2c_cg) *)
(* and the unconditional finals follow, among them                           *)
(*   T1 = P2B_ASYM_SOLITON_STATEMENT (:real^3), P2BZ9_ASYM_SOLITON: MT Thm   *)
(*        9.11 with Cors 9.53, 9.54 (the asymptotic gradient shrinking       *)
(*        soliton, compact round or the cylinder model), and                 *)
(*   T2 = P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3),                   *)
(*        P2BZ9_KAPPA_NECKS_ROUND_L_FIX (evolving necks of every normalized  *)
(*        length L >= 1).                                                    *)
(* Each statement that pc_p2b_close95 reuses is a separate theorem of the    *)
(* plain form |- STATEMENT (:real^3), with the (:real^3) (:real^3) instance  *)
(* for statements with two arguments.                                        *)
(* ========================================================================= *)

needs "src/pc_p2b_chainstmts.ml";;
needs "src/pc_p2b_ancc.ml";;
needs "src/pc_p2c_cg.ml";;
needs "src/pc_p2b_w920g.ml";;
needs "src/pc_p2b_c910.ml";;
needs "src/pc_p2b_l925.ml";;
needs "src/pc_p2b_c914.ml";;
needs "src/pc_p2b_g1.ml";;
needs "src/pc_p2b_g3.ml";;
needs "src/pc_p2b_p920.ml";;
needs "src/pc_p2b_fchart.ml";;
needs "src/pc_p2a_weak.ml";;
needs "src/pc_p2a_fl8fin.ml";;
needs "src/pc_p2a_l72f.ml";;
needs "src/pc_p2a_wk9.ml";;
needs "src/pc_p2a_flw3.ml";;
needs "src/pc_rfa_dist.ml";;
needs "src/pc_cmp_bg.ml";;
needs "src/pc_p2b_sol.ml";;
needs "src/pc_p2b_flatg.ml";;
needs "src/pc_p2b_ksolcyl.ml";;
needs "src/pc_p2c_fl514.ml";;
needs "src/pc_p2b_t911.ml";;
needs "src/pc_p2b_t911at.ml";;
needs "src/pc_p2b_x0lim.ml";;
needs "src/pc_rfa_s2.ml";;
needs "src/pc_s2ent_flow.ml";;
needs "src/pc_p2b_sround.ml";;
needs "src/pc_p2b_x1.ml";;
needs "src/pc_p2b_a5l.ml";;
needs "src/pc_p2b_flatfwdreq.ml";;
needs "src/pc_p2b_x2.ml";;
needs "src/pc_p2b_x2s.ml";;
needs "src/pc_rfa_htrace.ml";;
needs "src/pc_p2b_p946.ml";;
needs "src/pc_p2c_chainasm.ml";;
needs "src/pc_p2a_219.ml";;
needs "src/pc_p2b_shrinkcl.ml";;
needs "src/pc_p2b_lim.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The inputs of Thm 9.11 that do not need ANCIENT_COMPACT, at real^3.       *)
(* Bishop-Gromov from CMP_T3_BISHOP_GROMOV_P2B (pc_cmp_bg; the two statement *)
(* bodies are identical); Prop 9.20 and Cor 9.10 from the chain              *)
(* P2B_W920G_CHAIN (pc_p2b_w920g) with u = w = (:real^3) and its route and   *)
(* leaf inputs; SOLITON_FROM_LINF_FIX from its route (pc_p2b_sol) and        *)
(* FLAT_GAUSS (P2AU_FLAT_GAUSS, pc_p2b_flatg); Prop 5.14 (P2CR_PROP_5_14,    *)
(* pc_p2c_fl514) and KSOL_DRDT (P2BKC_KSOL_DRDT, pc_p2b_ksolcyl).            *)
(* ========================================================================= *)

let P2BZ9_BISHOP_GROMOV = prove
 (`P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT (:real^3)`,
  MP_TAC(ISPEC `(:real^3)` CMP_T3_BISHOP_GROMOV_P2B) THEN
  REWRITE_TAC[CMP_T3_BISHOP_GROMOV_P2B_STATEMENT;
              P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT]);;

let P2BZ9_W920 = prove
 (`P2B_PROP_9_20_STATEMENT (:real^3) (:real^3) /\
   P2B_COR_9_10_STATEMENT (:real^3)`,
  MATCH_MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`] P2B_W920G_CHAIN) THEN
  REWRITE_TAC[P2B_COR_9_10_ROUTE; P2B_LEMMA_9_25_ROUTE; P2B_COR_9_14_ROUTE;
              P2B_W920_G1_ROUTE; P2B_W920_G3_ROUTE; P2B_PROP_9_20_ROUTE;
              P2B_FLOW_CHART; P2AW_W3; P2AU_FLOW_PROP_9_9_3;
              P2AK_FLOW_MIN_EXISTS_3; P2AW_FL9; P2AU_FLOW_RV_3;
              P2AU_FLOW_RV_RIGID_3; RFA_P2B_REQ_RFA_DIST_LOCAL;
              P2BZ9_BISHOP_GROMOV]);;

let P2BZ9_PROP_9_20 = prove
 (`P2B_PROP_9_20_STATEMENT (:real^3) (:real^3)`,
  REWRITE_TAC[P2BZ9_W920]);;

let P2BZ9_COR_9_10 = prove
 (`P2B_COR_9_10_STATEMENT (:real^3)`,
  REWRITE_TAC[P2BZ9_W920]);;

let P2BZ9_SOLITON_FROM_LINF_FIX = prove
 (`P2B_SOLITON_FROM_LINF_FIX_STATEMENT (:real^3)`,
  MATCH_MP_TAC(REWRITE_RULE[P2B_SOLITON_FROM_LINF_FIX_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_SOLITON_FROM_LINF_FIX_ROUTE)) THEN
  REWRITE_TAC[P2AU_FLAT_GAUSS]);;

let P2BZ9_PROP_5_14 = prove
 (`P2C_PROP_5_14_STATEMENT (:real^3) (:real^3)`,
  REWRITE_TAC[P2CR_PROP_5_14]);;

let P2BZ9_KSOL_DRDT = prove
 (`P2B_KSOL_DRDT_STATEMENT (:real^3)`,
  REWRITE_TAC[P2BKC_KSOL_DRDT]);;

(* ========================================================================= *)
(* The chain conditional on ANCIENT_COMPACT at real^3.  Thm 9.11 and its AT  *)
(* form (routes in pc_p2b_t911 and pc_p2b_t911at); X0 = SPLIT_AT_INFINITY    *)
(* (pc_p2b_x0lim); SPLIT_ROUND (pc_p2b_sround, with                          *)
(* RFA_P2B_REQ_SHRINKER_ROUND and S2E_S2_ENTROPY); SPLIT_CYL (pc_p2b_x1); T2 *)
(* (P2BA5_FIX_FROM_X1, pc_p2b_a5l); X2 = CYL_AT_INFINITY and X2s =           *)
(* SHRINKER_CYL_AT_INFINITY (pc_p2b_x2, pc_p2b_x2s, with                     *)
(* P2B_REQ_FLAT_FORWARD); Prop 9.46 (pc_p2b_p946, with                       *)
(* RFA_P2B_REQ_RFA_HARNACK); Thm 9.42F, Cor 9.53 and SOLITON_CLASS           *)
(* (pc_p2b_shrinkcl, with P2CX_REQ_UNIQ_COMPLETE and P2AS_PROP_2_19_SEP);    *)
(* ASYM_SOLITON_AT (P2B_ASYM_AT_FROM_PARTS with P2B_KSEP_LIMIT) and T1       *)
(* (P2B_ASYM_SOLITON_AT_IMP).                                                *)
(* ========================================================================= *)

let P2BZ9_THM_9_11_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_THM_9_11_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_THM_9_11_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_THM_9_11_ROUTE)) THEN
  ASM_REWRITE_TAC[P2AU_FLOW_THM_7_10_3; P2BZ9_W920;
                  P2BZ9_SOLITON_FROM_LINF_FIX; P2BZ9_KSOL_DRDT;
                  P2BZ9_PROP_5_14]);;

let P2BZ9_THM_9_11_AT_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_THM_9_11_AT_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_THM_9_11_AT_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_THM_9_11_AT_ROUTE)) THEN
  ASM_REWRITE_TAC[P2AU_FLOW_THM_7_10_3; P2BZ9_W920;
                  P2BZ9_SOLITON_FROM_LINF_FIX; P2BZ9_KSOL_DRDT;
                  P2BZ9_PROP_5_14]);;

let P2BZ9_SPLIT_AT_INFINITY_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_SPLIT_AT_INFINITY_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_SPLIT_AT_INFINITY_ROUTE)) THEN
  ASM_REWRITE_TAC[]);;

let P2BZ9_SPLIT_ROUND_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_SPLIT_ROUND_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_SPLIT_ROUND_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_SPLIT_ROUND_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_SPLIT_AT_INFINITY_COND; P2BZ9_THM_9_11_COND;
               RFA_P2B_REQ_SHRINKER_ROUND; S2E_S2_ENTROPY]);;

let P2BZ9_SPLIT_CYL_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_SPLIT_CYL_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_SPLIT_CYL_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_SPLIT_CYL_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_SPLIT_ROUND_COND]);;

let P2BZ9_KAPPA_NECKS_ROUND_L_FIX_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3)`,
  DISCH_TAC THEN MATCH_MP_TAC(ISPEC `(:real^3)` P2BA5_FIX_FROM_X1) THEN
  ASM_SIMP_TAC[P2BZ9_SPLIT_CYL_COND]);;

let P2BZ9_CYL_AT_INFINITY_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_CYL_AT_INFINITY_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_CYL_AT_INFINITY_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2BX2_CYL_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_SPLIT_AT_INFINITY_COND; P2BZ9_SPLIT_ROUND_COND;
               P2B_REQ_FLAT_FORWARD]);;

let P2BZ9_SHRINKER_CYL_AT_INFINITY_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2BX2_SCYL_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_SPLIT_AT_INFINITY_COND; P2BZ9_SPLIT_ROUND_COND;
               P2B_REQ_FLAT_FORWARD]);;

let P2BZ9_PROP_9_46_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_PROP_9_46_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_PROP_9_46_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2BX2_P946_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_SHRINKER_CYL_AT_INFINITY_COND;
               RFA_P2B_REQ_RFA_HARNACK]);;

let P2BZ9_THM_9_42F_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_THM_9_42F_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_THM_9_42F_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_THM_9_42F_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_PROP_9_46_COND; RFA_P2B_REQ_SHRINKER_ROUND;
               P2BZ9_SPLIT_CYL_COND; P2CX_REQ_UNIQ_COMPLETE]);;

let P2BZ9_COR_9_53_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_COR_9_53_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_COR_9_53_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_COR_9_53_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_SPLIT_CYL_COND; P2BZ9_CYL_AT_INFINITY_COND;
               P2AS_PROP_2_19_SEP]);;

let P2BZ9_SOLITON_CLASS_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_SOLITON_CLASS_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[P2B_SOLITON_CLASS_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2B_SOLITON_CLASS_ROUTE)) THEN
  ASM_SIMP_TAC[P2BZ9_COR_9_53_COND; P2BZ9_THM_9_42F_COND]);;

let P2BZ9_ASYM_SOLITON_AT_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_ASYM_SOLITON_AT_STATEMENT (:real^3)`,
  DISCH_TAC THEN MATCH_MP_TAC(ISPEC `(:real^3)` P2B_ASYM_AT_FROM_PARTS) THEN
  ASM_SIMP_TAC[P2BZ9_THM_9_11_AT_COND; P2B_KSEP_LIMIT;
               P2BZ9_SOLITON_CLASS_COND]);;

let P2BZ9_ASYM_SOLITON_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_ASYM_SOLITON_STATEMENT (:real^3)`,
  DISCH_TAC THEN MATCH_MP_TAC(ISPEC `(:real^3)` P2B_ASYM_SOLITON_AT_IMP) THEN
  ASM_SIMP_TAC[P2BZ9_ASYM_SOLITON_AT_COND]);;

let P2BZ9_CLOSE9_COND = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)
   ==> P2B_ASYM_SOLITON_STATEMENT (:real^3) /\
       P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\
       P2B_SPLIT_ROUND_STATEMENT (:real^3) /\
       P2B_THM_9_11_STATEMENT (:real^3)`,
  DISCH_TAC THEN
  ASM_SIMP_TAC[P2BZ9_ASYM_SOLITON_COND; P2BZ9_KAPPA_NECKS_ROUND_L_FIX_COND;
               P2BZ9_SPLIT_ROUND_COND; P2BZ9_THM_9_11_COND]);;

(* ========================================================================= *)
(* ANCIENT_COMPACT at real^3 from P2BAC_ANCIENT_COMPACT_ROUTE (pc_p2b_ancc)  *)
(* and P2CK_CG_COMPACT (pc_p2c_cg), and the unconditional finals: each _COND *)
(* theorem above with its hypothesis discharged, Cor 9.10, Prop 9.20 and     *)
(* KSOL_DRDT from the first section, and the summary P2BZ9_CLOSE9 (T1, T2,   *)
(* SPLIT_ROUND and THM_9_11 at real^3).                                      *)
(* ========================================================================= *)

let P2BZ9_ANCIENT_COMPACT = prove
 (`P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT (:real^3)`,
  MATCH_MP_TAC(REWRITE_RULE[P2B_ANCIENT_COMPACT_ROUTE_STATEMENT]
                 (ISPEC `(:real^3)` P2BAC_ANCIENT_COMPACT_ROUTE)) THEN
  REWRITE_TAC[P2CK_CG_COMPACT]);;

let P2BZ9_THM_9_11 = prove
 (`P2B_THM_9_11_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_THM_9_11_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_THM_9_11_AT = prove
 (`P2B_THM_9_11_AT_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_THM_9_11_AT_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_SPLIT_AT_INFINITY = prove
 (`P2B_SPLIT_AT_INFINITY_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_SPLIT_AT_INFINITY_COND THEN
  ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_SPLIT_ROUND = prove
 (`P2B_SPLIT_ROUND_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_SPLIT_ROUND_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_SPLIT_CYL = prove
 (`P2B_SPLIT_CYL_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_SPLIT_CYL_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_KAPPA_NECKS_ROUND_L_FIX = prove
 (`P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_KAPPA_NECKS_ROUND_L_FIX_COND THEN
  ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_CYL_AT_INFINITY = prove
 (`P2B_CYL_AT_INFINITY_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_CYL_AT_INFINITY_COND THEN
  ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_SHRINKER_CYL_AT_INFINITY = prove
 (`P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_SHRINKER_CYL_AT_INFINITY_COND THEN
  ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_PROP_9_46 = prove
 (`P2B_PROP_9_46_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_PROP_9_46_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_THM_9_42F = prove
 (`P2B_THM_9_42F_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_THM_9_42F_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_COR_9_53 = prove
 (`P2B_COR_9_53_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_COR_9_53_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_SOLITON_CLASS = prove
 (`P2B_SOLITON_CLASS_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_SOLITON_CLASS_COND THEN
  ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_ASYM_SOLITON_AT = prove
 (`P2B_ASYM_SOLITON_AT_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_ASYM_SOLITON_AT_COND THEN
  ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_ASYM_SOLITON = prove
 (`P2B_ASYM_SOLITON_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_ASYM_SOLITON_COND THEN
  ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

let P2BZ9_CLOSE9 = prove
 (`P2B_ASYM_SOLITON_STATEMENT (:real^3) /\
   P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\
   P2B_SPLIT_ROUND_STATEMENT (:real^3) /\
   P2B_THM_9_11_STATEMENT (:real^3)`,
  MATCH_MP_TAC P2BZ9_CLOSE9_COND THEN ACCEPT_TAC P2BZ9_ANCIENT_COMPACT);;

