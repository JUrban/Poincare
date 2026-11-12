(* ========================================================================= *)
(* Unit pc_poincare_top: the topological Poincare headline POINCARE_TOP,     *)
(* |- POINCARE_STATEMENT (:A) for a type variable A, and its embedded form   *)
(* POINCARE_EMBEDDED, |- POINCARE_EMBEDDED_STATEMENT (:N), with both         *)
(* statements the constants of poincare_statement.ml.  POINCARE_TOP is       *)
(* POINCARE_FROM_SMOOTH_AND_MOISE of pc_interfaces applied to the smooth     *)
(* headline POINCARE_SMOOTH (pc_smt_smooth) and the Moise smoothing theorem  *)
(* MOI_SST_HEADLINE (pc_moi_status); POINCARE_EMBEDDED is                    *)
(* POINCARE_STATEMENT_IMP_EMBEDDED of poincare_statement_sanity at real^N.   *)
(* ========================================================================= *)

needs "src/pc_interfaces.ml";;
needs "src/poincare_statement_sanity.ml";;
needs "src/pc_smt_smooth.ml";;
needs "src/pc_moi_status.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The two headline theorems.                                                *)
(* ========================================================================= *)

let POINCARE_TOP = prove
 (`POINCARE_STATEMENT (:A)`,
  MATCH_MP_TAC POINCARE_FROM_SMOOTH_AND_MOISE THEN
  REWRITE_TAC[POINCARE_SMOOTH; MOI_SST_HEADLINE]);;

let POINCARE_EMBEDDED = prove
 (`POINCARE_EMBEDDED_STATEMENT (:N)`,
  MATCH_MP_TAC POINCARE_STATEMENT_IMP_EMBEDDED THEN
  ACCEPT_TAC(INST_TYPE [`:real^N`,`:A`] POINCARE_TOP));;

