(* ========================================================================= *)
(* Unit pc_p2a_weak: the statement W3, P2B_REQ_P2A_WEAK_STATEMENT            *)
(* (pc_p2b_w3iface), for 3-dimensional flows (P2AW_W3): P2AW_W3_FROM_FL2     *)
(* (pc_p2a_wk7) with FL2 = P2AK_FLOW_MIN_EXISTS_3 (pc_p2a_l72f, Lemma 7.2    *)
(* for flows).                                                               *)
(* ========================================================================= *)

needs "src/pc_p2a_wk7.ml";;
needs "src/pc_p2a_l72f.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The headline |- !u:A->bool. P2B_REQ_P2A_WEAK_STATEMENT u.                 *)
(* ------------------------------------------------------------------------- *)

let P2AW_W3 = prove
 (`!u:A->bool. P2B_REQ_P2A_WEAK_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC P2AW_W3_FROM_FL2 THEN EXISTS_TAC `(:3)` THEN
  REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3]);;

