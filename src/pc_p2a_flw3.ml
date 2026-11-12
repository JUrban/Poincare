(* ========================================================================= *)
(* pc_p2a_flw3: with W3 (P2AW_W3, pc_p2a_weak) the flow-level theorems that  *)
(* assume W3 hold unconditionally at N = 3: FL3 (P2AU_FLOW_LX_CONT,          *)
(* pc_p2a_flow2), FL4 and FL5 (P2AU_FLOW_THM_7_10_W3, P2AU_FLOW_RV_W3,       *)
(* pc_p2a_flfin) and FL5R (P2AU_FLOW_RV_RIGID_W3, pc_p2a_rigr2).             *)
(* ========================================================================= *)

needs "src/pc_p2a_rigr2.ml";;
needs "src/pc_p2a_flfin.ml";;
needs "src/pc_p2a_weak.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The unconditional forms at N = 3.                                         *)
(* ------------------------------------------------------------------------- *)

let P2AU_FLOW_LX_CONT_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_LX_CONT_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AU_FLOW_LX_CONT THEN REWRITE_TAC[P2AW_W3]);;

let P2AU_FLOW_THM_7_10_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_THM_7_10_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AU_FLOW_THM_7_10_W3 THEN REWRITE_TAC[P2AW_W3]);;

let P2AU_FLOW_RV_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_RV_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AU_FLOW_RV_W3 THEN REWRITE_TAC[P2AW_W3]);;

let P2AU_FLOW_RV_RIGID_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_RV_RIGID_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AU_FLOW_RV_RIGID_W3 THEN REWRITE_TAC[P2AW_W3]);;

