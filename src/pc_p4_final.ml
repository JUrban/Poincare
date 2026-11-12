(* ========================================================================= *)
(* Unit pc_p4_final: finite extinction in the Part 3 form.                  *)
(*   P4_EXTINCTION      |- P4_EXTINCTION_STATEMENT (:A)                      *)
(*   P4_EXTINCTION_ALL  |- !u:A->bool. P4_EXTINCTION_STATEMENT u             *)
(* with no hypothesis: P4_EXTINCTION_FROM_CUTCAP (pc_p4_wire) and the        *)
(* instance (:A+num#num#real^3) (:A+num#num#real^3) of RFS_CUTCAP_SC         *)
(* (pc_rfs_ccsc).  P4_EXTINCTION_STATEMENT is defined in pc_p3_core.         *)
(* ========================================================================= *)

needs "src/pc_p4_wire.ml";;
needs "src/pc_rfs_ccsc.ml";;

prioritize_real();;
type_invention_error := true;;

let P4_EXTINCTION = prove
 (`P4_EXTINCTION_STATEMENT (:A)`,
  MATCH_MP_TAC P4_EXTINCTION_FROM_CUTCAP THEN REWRITE_TAC[RFS_CUTCAP_SC]);;

let P4_EXTINCTION_ALL = prove
 (`!u:A->bool. P4_EXTINCTION_STATEMENT u`,
  MP_TAC P4_EXTINCTION THEN REWRITE_TAC[P4_EXTINCTION_STATEMENT]);;

