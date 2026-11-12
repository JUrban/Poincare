(* ========================================================================= *)
(* The independent formalization of audit/poincare_blind.ml is proved: the  *)
(* equivalences of audit/pc_audit_equiv.ml applied to the headline theorems *)
(* POINCARE_TOP and POINCARE_SMOOTH of the development.                      *)
(* ========================================================================= *)

needs "audit/pc_audit_equiv.ml";;
needs "src/pc_poincare_top.ml";;

prioritize_real();;
type_invention_error := true;;

let BLIND_POINCARE_TOP_PROVED = prove
 (`BLIND_POINCARE_TOP (:A)`,
  REWRITE_TAC[GSYM POINCARE_TOP_BLIND_EQUIV; POINCARE_TOP]);;

let BLIND_POINCARE_SMOOTH_PROVED = prove
 (`BLIND_POINCARE_SMOOTH (:A)`,
  REWRITE_TAC[GSYM POINCARE_SMOOTH_BLIND_EQUIV; POINCARE_SMOOTH]);;
