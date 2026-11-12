(* ========================================================================= *)
(* Unit pc_p2b_flatfwdreq (Part 2B): P2B_REQ_FLAT_FORWARD proves the         *)
(* statement P2B_REQ_FLAT_FORWARD_STATEMENT of pc_p2b_kreq (a flat slice of  *)
(* a complete Ricci flow with sec >= 0 and bounded curvature stays flat      *)
(* forward in time) from the theorem P2B_FLAT_FORWARD_BODY (pc_p2b_flatfwd), *)
(* whose statement is its body.                                              *)
(* ========================================================================= *)

needs "src/pc_p2b_kreq.ml";;
needs "src/pc_p2b_flatfwd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The statement P2B_REQ_FLAT_FORWARD_STATEMENT.                             *)
(* ========================================================================= *)

let P2B_REQ_FLAT_FORWARD = prove
 (`!u:A->bool. P2B_REQ_FLAT_FORWARD_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_FLAT_FORWARD_STATEMENT] THEN
  MATCH_ACCEPT_TAC P2B_FLAT_FORWARD_BODY);;

