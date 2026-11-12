(* ========================================================================= *)
(* Unit pc_p2b_c994c (Part 2B): MT Cor 9.94 in the length-L form composed    *)
(* from its pieces, the chain theorem P2B_C994_CHAIN of pc_p2b_c994req and   *)
(* X1.                                                                       *)
(*   (a) P2BPK_PROP_9_83K_ROUTE (pc_p2b_p983k)                               *)
(*   (b) P2A985D_PROP_9_85L_ROUTE (pc_p2a_985d)                              *)
(*   (c) SOULT_SOUL_TOPOLOGY (pc_soul_topo)                                  *)
(*   (d) KNCL_ROUTE (pc_p2b_kncl4)                                           *)
(*   (e) P2KC_KSOL_COMPACT_CANON_L_ROUTE (pc_p2c_e994)                       *)
(*   (f) P2B_COR_9_94_L_CASES_ROUTE (pc_p2b_c994)                            *)
(*   (g) P2BAN_ALL_NECK_LINE (pc_p2b_allneck; loaded, not used by the chain) *)
(*   (h) P2BCY_CYL_MODEL_NECKS (pc_p2b_cylnecks)                             *)
(*   X1  P2B_SPLIT_CYL_ROUTE (pc_p2b_x1)                                     *)
(* Headlines:                                                                *)
(*   P2BC4C_COR_9_94_L_ROUTE |- !w. P2B_COR_9_94_L_ROUTE_STATEMENT w         *)
(*   P2BC4C_COR_9_94_L_SPLIT_ROUND: the route with X1 replaced by its route *)
(*     input SPLIT_ROUND (P2B_SPLIT_CYL_ROUTE).                              *)
(* ========================================================================= *)

needs "src/pc_p2b_p983k.ml";;
needs "src/pc_p2a_985d.ml";;
needs "src/pc_soul_topo.ml";;
needs "src/pc_p2b_kncl4.ml";;
needs "src/pc_p2c_e994.ml";;
needs "src/pc_p2b_c994.ml";;
needs "src/pc_p2b_allneck.ml";;
needs "src/pc_p2b_cylnecks.ml";;
needs "src/pc_p2b_x1.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The composition.  The pieces discharge every hypothesis of                *)
(* P2B_C994_CHAIN, so the top route holds outright; its inputs are X1,       *)
(* THM_9_64, PROP_9_58, LEMMA_9_65, COR_9_71, COR_9_44 and ASYM_SOLITON, and *)
(* X1 reduces to SPLIT_ROUND.                                                *)
(* ========================================================================= *)

let P2BC4C_COR_9_94_L_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_94_L_ROUTE_STATEMENT w`,
  GEN_TAC THEN MATCH_MP_TAC P2B_C994_CHAIN THEN
  REWRITE_TAC[P2BPK_PROP_9_83K_ROUTE; P2BCY_CYL_MODEL_NECKS; SOULT_SOUL_TOPOLOGY;
              P2A985D_PROP_9_85L_ROUTE; KNCL_ROUTE; P2KC_KSOL_COMPACT_CANON_L_ROUTE;
              P2B_COR_9_94_L_CASES_ROUTE]);;

let P2BC4C_COR_9_94_L_SPLIT_ROUND = prove
 (`!w:B->bool.
     P2B_SPLIT_ROUND_STATEMENT w /\ P2B_THM_9_64_STATEMENT w /\
     P2B_PROP_9_58_STATEMENT w /\ P2B_LEMMA_9_65_STATEMENT w /\
     P2B_COR_9_71_STATEMENT w /\ P2B_COR_9_44_STATEMENT w /\
     P2B_ASYM_SOLITON_STATEMENT w
     ==> P2B_COR_9_94_L_STATEMENT w`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `w:B->bool` P2BC4C_COR_9_94_L_ROUTE) THEN
  REWRITE_TAC[P2B_COR_9_94_L_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `w:B->bool` P2B_SPLIT_CYL_ROUTE) THEN
  REWRITE_TAC[P2B_SPLIT_CYL_ROUTE_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

