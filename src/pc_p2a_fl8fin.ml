(* ========================================================================= *)
(* pc_p2a_fl8fin: FL8 (P2A_FLOW_PROP_9_9, MT Prop 9.9) at N = 3 without      *)
(* hypotheses: P2AU_FLOW_PROP_9_9_H (pc_p2a_fl99) reduces FL8 to Hamilton's  *)
(* trace Harnack inequality, RFA_P2B_REQ_RFA_HARNACK of pc_rfa_htrace.       *)
(* ========================================================================= *)

needs "src/pc_p2a_fl99.ml";;
needs "src/pc_rfa_htrace.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The unconditional FL8 at N = 3.                                           *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLOW_PROP_9_9_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_PROP_9_9_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AU_FLOW_PROP_9_9_H THEN
  REWRITE_TAC[RFA_P2B_REQ_RFA_HARNACK]);;

