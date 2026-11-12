(* ========================================================================= *)
(* Unit pc_p3_c171e: MT Prop 17.1, the route without P2_LEMMA_11_23 (the     *)
(* route statement of pc_p3_route2):                                         *)
(*   P3_PROP_17_1_ROUTE_2 |- !u. P3_PROP_17_1_ROUTE_2_STATEMENT u (:real^3)  *)
(* by P3H_PROP_17_1_CORE (pc_p3_c171d), whose 14 hypotheses do not include   *)
(* 11.23; the proof is the one of P3_PROP_17_1_ROUTE.                        *)
(* ========================================================================= *)

needs "src/pc_p3_c171d.ml";;
needs "src/pc_p3_route2.ml";;

prioritize_real();;
type_invention_error := true;;

let P3_PROP_17_1_ROUTE_2 = prove
 (`!u:A->bool. P3_PROP_17_1_ROUTE_2_STATEMENT u (:real^3)`,
  GEN_TAC THEN REWRITE_TAC[P3_PROP_17_1_ROUTE_2_STATEMENT] THEN STRIP_TAC THEN
  MATCH_MP_TAC P3H_PROP_17_1_CORE THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APX_SC_SPHERE_SEP_STATEMENT; RFS_CUTCAP_SC_STATEMENT]) THEN
  ASM_REWRITE_TAC[APX_SC_SPHERE_SEP_STATEMENT; RFS_CUTCAP_SC_STATEMENT]);;

