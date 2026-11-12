(* ========================================================================= *)
(* pc_sch_main: the smooth Schoenflies theorem in R^3 in the collared form   *)
(* APX_SCHOENFLIES_REQ_STATEMENT, SCH_SCHOENFLIES_REQ, by the statement      *)
(* chain SCH_REQ_CHAIN of pc_sch_stmt. The links of the chain: SCH_GENERIC   *)
(* (pc_sch_generic), SCH_COLLAR3 (pc_sch_collar), SCH_LEVEL_FINITE           *)
(* (pc_sch_level), SCH_LEVEL_NECK and SCH_LEVEL_INNERMOST (pc_sch_level2),   *)
(* the surgery (pc_sch_surg and pc_sch_glue), SCH_BASE0 (pc_sch_base0) and   *)
(* SCH_BASE1 (pc_sch_base1).                                                 *)
(*                                                                           *)
(* The needs lines load pc_sch_base1 first, so that its dependencies load in *)
(* their own order; the other lines record the direct dependencies.          *)
(* ========================================================================= *)

needs "src/pc_sch_base1.ml";;
needs "src/pc_sch_surg.ml";;
needs "src/pc_sch_glue.ml";;
needs "src/pc_sch_level2.ml";;
needs "src/pc_sch_base0.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The chain. Surgery = construction (pc_sch_surg) plus gluing               *)
(* (pc_sch_glue); generic position (SCH_GENERIC), collars (SCH_COLLAR3) and  *)
(* the finiteness of level components (SCH_LEVEL_FINITE) are proved in their *)
(* own files.                                                                *)
(* ------------------------------------------------------------------------- *)

let SCH8_SURGERY_FROM_LEVELS = prove
 (`SCH_LEVEL_NECK_STATEMENT /\ SCH_LEVEL_INNERMOST_STATEMENT ==> SCH_SURGERY_STATEMENT`,
  STRIP_TAC THEN MATCH_MP_TAC SCH_SURGERY_FROM_SLAB THEN REWRITE_TAC[SCH6_SLAB_GLUE] THEN
  MATCH_MP_TAC SCH5_SURG_CONSTRUCT THEN ASM_REWRITE_TAC[SCH_LEVEL_FINITE]);;

let SCH8_REQ_FROM_REMAINING = prove
 (`SCH_LEVEL_NECK_STATEMENT /\ SCH_LEVEL_INNERMOST_STATEMENT /\
   SCH_BASE0_STATEMENT /\ SCH_BASE1_STATEMENT
   ==> !u:A->bool. APX_SCHOENFLIES_REQ_STATEMENT u`,
  STRIP_TAC THEN MATCH_MP_TAC SCH_REQ_CHAIN THEN
  ASM_SIMP_TAC[SCH_GENERIC; SCH_COLLAR3; SCH8_SURGERY_FROM_LEVELS]);;

(* ------------------------------------------------------------------------- *)
(* With the two level statements of pc_sch_level2, the smooth Schoenflies    *)
(* theorem follows from the two base cases.                                  *)
(* ------------------------------------------------------------------------- *)

let SCH8_REQ_FROM_BASES = prove
 (`SCH_BASE0_STATEMENT /\ SCH_BASE1_STATEMENT ==> !u:A->bool. APX_SCHOENFLIES_REQ_STATEMENT u`,
  STRIP_TAC THEN MATCH_MP_TAC SCH8_REQ_FROM_REMAINING THEN
  ASM_REWRITE_TAC[SCH4L_LEVEL_NECK; SCH4L_LEVEL_INNERMOST]);;

(* ------------------------------------------------------------------------- *)
(* The smooth Schoenflies theorem, from the base cases SCH_BASE0, SCH_BASE1. *)
(* ------------------------------------------------------------------------- *)

let SCH_SCHOENFLIES_REQ = prove
 (`!u:A->bool. APX_SCHOENFLIES_REQ_STATEMENT u`,
  MATCH_MP_TAC SCH8_REQ_FROM_BASES THEN REWRITE_TAC[SCH_BASE0; SCH_BASE1]);;

