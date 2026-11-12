(* ========================================================================= *)
(* pc_p2a_flfin: FL2 discharged in the flow-level theorems of pc_p2a_flow2   *)
(* (FL4), pc_p2a_flow3 (FL6) and pc_p2a_frv (FL5), with                      *)
(* P2AK_FLOW_MIN_EXISTS_3 of pc_p2a_l72f.  At N = 3: FL6 holds               *)
(* unconditionally; FL4 and FL5 need only W3.  FL3 needs only W3             *)
(* (pc_p2a_flow2); the FL5R and FL8 corollaries are in pc_p2a_rigid and      *)
(* pc_p2a_fl99.                                                              *)
(* ========================================================================= *)

needs "src/pc_p2a_flow2.ml";;
needs "src/pc_p2a_flow3.ml";;
needs "src/pc_p2a_frv.ml";;
needs "src/pc_p2a_l72f.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The corollaries.                                                          *)
(* ------------------------------------------------------------------------- *)

(* FL6 (MT Thm 8.1 for complete flows of bounded curvature) at N = 3. *)

let P2AU_FLOW_THM_8_1_3 = prove
 (`!(u:A->bool) (n:3->bool). P2A_FLOW_THM_8_1_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC P2AU_FLOW_THM_8_1 THEN
  REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3]);;

(* FL4 (MT Thm 7.10) at N = 3 from W3. *)

let P2AU_FLOW_THM_7_10_W3 = prove
 (`!(u:A->bool) (n:3->bool).
     P2B_REQ_P2A_WEAK_STATEMENT u ==> P2A_FLOW_THM_7_10_STATEMENT u n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AU_FLOW_THM_7_10 THEN
  ASM_REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3]);;

(* FL5 (MT Thm 7.26) at N = 3 from W3. *)

let P2AU_FLOW_RV_W3 = prove
 (`!(u:A->bool) (n:3->bool).
     P2B_REQ_P2A_WEAK_STATEMENT u ==> P2A_FLOW_RV_STATEMENT u n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AU_FLOW_RV THEN
  ASM_REWRITE_TAC[P2AK_FLOW_MIN_EXISTS_3]);;

