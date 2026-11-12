(* ========================================================================= *)
(* pc_p2a_l72w: MT Lemma 7.2, P2AY_LEMMA_7_2 : |-                            *)
(* !u. P2_LEMMA_7_2_STATEMENT u.  P2AX_T2 (pc_p2a_defs4) reduces             *)
(* P2_LEMMA_7_2_STATEMENT to the view-X form P2A_LEMMA_7_2_VIEW_X_STATEMENT  *)
(* (proved in pc_p2a_l72i) and the history bridge P2A_HIST_VIEW_X_STATEMENT  *)
(* (proved in pc_p2a_brg).                                                   *)
(* ========================================================================= *)

needs "src/pc_p2a_l72i.ml";;
needs "src/pc_p2a_brg.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AY_LEMMA_7_2 = prove
 (`!u:A->bool. P2_LEMMA_7_2_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC P2AX_T2 THEN
  REWRITE_TAC[P2A_LEMMA_7_2_VIEW_X; P2AB_HIST_VIEW_X]);;

