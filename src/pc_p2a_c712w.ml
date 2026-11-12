(* ========================================================================= *)
(* pc_p2a_c712w: MT Cor 7.12, P2AY_COR_7_12 : |-                             *)
(* !u. P2_COR_7_12_STATEMENT u.  P2AX_T3 (pc_p2a_defs4) reduces              *)
(* P2_COR_7_12_STATEMENT to the view form P2A_COR_7_12_VIEW_FIX_STATEMENT    *)
(* and the history bridge P2A_HIST_VIEW_X_STATEMENT (P2AB_HIST_VIEW_X,       *)
(* pc_p2a_brg); the view form follows from the barrier L13 FIX               *)
(* (P2A_COR_7_12_FIX_FROM_BARRIER in pc_p2a_c712, P2A_BARRIER_FIX in         *)
(* pc_p2a_bar).                                                              *)
(* ========================================================================= *)

needs "src/pc_p2a_brg.ml";;
needs "src/pc_p2a_c712.ml";;
needs "src/pc_p2a_bar.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AY_COR_7_12 = prove
 (`!u:A->bool. P2_COR_7_12_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC P2AX_T3 THEN REWRITE_TAC[P2AB_HIST_VIEW_X] THEN
  MATCH_MP_TAC P2A_COR_7_12_FIX_FROM_BARRIER THEN
  REWRITE_TAC[P2A_BARRIER_FIX]);;

