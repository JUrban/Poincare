(* ========================================================================= *)
(* Unit pc_smt_smooth: the smooth Poincare theorem POINCARE_SMOOTH,          *)
(* |- POINCARE_SMOOTH_STATEMENT (:A) for a type variable A, with             *)
(* POINCARE_SMOOTH_STATEMENT the constant of poincare_statement.ml.  It is   *)
(* RFS_POINCARE_SMOOTH of pc_rfs_assembly applied to its seven hypotheses:   *)
(* METRIC_EXISTENCE (pc_mfd_metric_exists), RFS_EXTINCTION                   *)
(* (pc_smt_extinct), EVENT_TOPOLOGY (pc_smt_evtop), RFS_CUTCAP_SC            *)
(* (pc_rfs_ccsc), RFS_LISTED_SC_S3 (pc_smt_listed), RFS_SPHERE_SYSTEM        *)
(* (pc_smt_system) and SMT_POINCARE_CONVERSION (pc_smt_glue).                *)
(* ========================================================================= *)

needs "src/pc_rfs_assembly.ml";;
needs "src/pc_mfd_metric_exists.ml";;
needs "src/pc_smt_extinct.ml";;
needs "src/pc_smt_evtop.ml";;
needs "src/pc_rfs_ccsc.ml";;
needs "src/pc_smt_listed.ml";;
needs "src/pc_smt_system.ml";;
needs "src/pc_smt_glue.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The main theorem.  POINCARE_SMOOTH_STATEMENT (:A) of                     *)
(* poincare_statement.ml at a type variable A, from RFS_POINCARE_SMOOTH of   *)
(* pc_rfs_assembly and its seven hypotheses.                                 *)
(* ========================================================================= *)

let POINCARE_SMOOTH = prove
 (`POINCARE_SMOOTH_STATEMENT (:A)`,
  MATCH_MP_TAC(ISPEC `(:A)` RFS_POINCARE_SMOOTH) THEN
  REWRITE_TAC[METRIC_EXISTENCE; RFS_EXTINCTION; EVENT_TOPOLOGY; RFS_CUTCAP_SC;
              RFS_LISTED_SC_S3; RFS_SPHERE_SYSTEM; SMT_POINCARE_CONVERSION]);;

