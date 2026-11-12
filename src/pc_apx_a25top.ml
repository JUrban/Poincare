(* ========================================================================= *)
(* Unit pc_apx_a25top: MT Prop A.25 (APX_A25_STATEMENT), unconditional:      *)
(* APX_A25 is APX_A25_FROM_BASE1 (pc_apx_a25sch: SCH_BASE1_STATEMENT implies *)
(* every APX_A25_STATEMENT u) discharged by SCH_BASE1 (pc_sch_base1).        *)
(* ========================================================================= *)

needs "src/pc_apx_a25sch.ml";;
needs "src/pc_sch_base1.ml";;

prioritize_real();;
type_invention_error := true;;

let APX_A25 = prove
 (`!u:A->bool. APX_A25_STATEMENT u`,
  ACCEPT_TAC(MP APX_A25_FROM_BASE1 SCH_BASE1));;

