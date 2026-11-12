(* ========================================================================= *)
(* pc_apx_a25sch: MT Proposition A.25 (APX_A25_STATEMENT) from the base case *)
(* SCH_BASE1_STATEMENT of the smooth Schoenflies chain: APX_A25_FROM_BASE1.  *)
(* APX_A25_FROM_SCHREQ (pc_apx_a25) reduces A.25 to the collared Schoenflies *)
(* statement APX_SCHOENFLIES_REQ_STATEMENT, and SCH8_REQ_FROM_BASES          *)
(* (pc_sch_main) reduces that to the base cases SCH_BASE0_STATEMENT (proved  *)
(* as SCH_BASE0 in pc_sch_base0) and SCH_BASE1_STATEMENT (proved as          *)
(* SCH_BASE1 in pc_sch_base1; pc_apx_a25top combines the two).               *)
(* ========================================================================= *)

needs "src/pc_apx_a25.ml";;
needs "src/pc_sch_main.ml";;
needs "src/pc_sch_base0.ml";;

prioritize_real();;
type_invention_error := true;;

let APX_A25_FROM_BASE1 = prove
 (`SCH_BASE1_STATEMENT ==> !u:A->bool. APX_A25_STATEMENT u`,
  DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC APX_A25_FROM_SCHREQ THEN
  SPEC_TAC(`u:A->bool`,`u:A->bool`) THEN MATCH_MP_TAC SCH8_REQ_FROM_BASES THEN
  ASM_REWRITE_TAC[SCH_BASE0]);;

