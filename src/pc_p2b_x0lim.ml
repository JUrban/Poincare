(* ========================================================================= *)
(* pc_p2b_x0lim: X0 of the Part 2B chain (MT Prop 9.11, split at infinity)   *)
(* with the proved limit-geometry statements: P2B_SPLIT_AT_INFINITY_ROUTE    *)
(* proves P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT w with no hypotheses, from   *)
(* P2B_SPLIT_AT_INFINITY_ROUTE_LIM (pc_p2b_x0), LIM_DIST and LIM_BALL        *)
(* (pc_lim_dist), LIM_FLOW_COMPLETE_BACK (pc_lim_back), LIM_KNC (pc_lim_vol) *)
(* and LIM_CURV (pc_lim_curv).                                               *)
(* ========================================================================= *)

needs "src/pc_p2b_x0.ml";;
needs "src/pc_lim_dist.ml";;
needs "src/pc_lim_back.ml";;
needs "src/pc_lim_vol.ml";;
needs "src/pc_lim_curv.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_SPLIT_AT_INFINITY_ROUTE = prove
 (`!w:B->bool. P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT w`,
  GEN_TAC THEN MATCH_MP_TAC P2B_SPLIT_AT_INFINITY_ROUTE_LIM THEN
  REWRITE_TAC[LIM_DIST; LIM_BALL; LIM_KNC; LIM_CURV; LIM_FLOW_COMPLETE_BACK]);;

