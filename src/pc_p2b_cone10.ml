(* ========================================================================= *)
(* Unit pc_p2b_cone10: the route theorem of MT Thm 10.2 (no bad tube),       *)
(* P2BK_NO_BAD_TUBE_ROUTE |- !w. P2B_NO_BAD_TUBE_ROUTE_STATEMENT w: the      *)
(* local compactness of regular views (the statement                         *)
(* P2B_REQ_P2C_LOCAL_COMPACT_N_STATEMENT, proved in pc_p2c_lcn) implies      *)
(* P2B_NO_BAD_TUBE_STATEMENT.  It follows by P2BK_NO_BAD_TUBE_PARTS from the *)
(* blow-up P2BK_BLOWUP (pc_p2b_cone9), the end-cone data P2BK_END_CONE       *)
(* (pc_p2b_cone4) and the regularity of cone functions P2BK_CONE_REGULAR     *)
(* (pc_p2b_cone5).                                                           *)
(* ========================================================================= *)

needs "src/pc_p2b_cone4.ml";;
needs "src/pc_p2b_cone5.ml";;
needs "src/pc_p2b_cone9.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The route theorem.                                                        *)
(* ------------------------------------------------------------------------- *)

let P2BK_NO_BAD_TUBE_ROUTE = prove
 (`!w:B->bool. P2B_NO_BAD_TUBE_ROUTE_STATEMENT w`,
  GEN_TAC THEN MATCH_MP_TAC P2BK_NO_BAD_TUBE_PARTS THEN
  REWRITE_TAC[P2BK_BLOWUP; P2BK_END_CONE; P2BK_CONE_REGULAR]);;

