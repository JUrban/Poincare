(* ========================================================================= *)
(* Unit pc_p2a_wk9: FL9 P2A_FLOW_MIN_GRAD_STATEMENT (pc_p2a_fldefs) for      *)
(* 3-dimensional flows (P2AW_FL9): P2AW_FL9_FROM_FL2 (pc_p2a_wk8) with FL2 = *)
(* P2AK_FLOW_MIN_EXISTS_3 (pc_p2a_l72f, Lemma 7.2 for flows).                *)
(* ========================================================================= *)

needs "src/pc_p2a_wk8.ml";;
needs "src/pc_p2a_l72f.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* FL9 at N = 3.                                                             *)
(* ------------------------------------------------------------------------- *)

let P2AW_FL9 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_MIN_GRAD_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AW_FL9_FROM_FL2 THEN
  REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3]);;

