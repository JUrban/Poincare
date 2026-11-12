(* ========================================================================= *)
(* pc_pde_final: the final assembly of the PDE layer.  These statements of   *)
(* pc_pde_iface hold without hypotheses: uniform Ricci-DeTurck existence     *)
(* (PDE_RDT_FROM_MLIN with PDE_MLIN_HOLDS), uniform short-time existence     *)
(* (with the gauge PDE_GAUGE), short-time existence, the extension criterion *)
(* (with PDE_UNIQUENESS and the chart derivative bounds RFA_R1), maximal     *)
(* flows, and the existence time controlled by curvature (with the           *)
(* doubling-time estimate RFA_R2), by the assemblies of pc_rf_extend.  Every *)
(* statement for all carrier types A and dimensions N, and at N = 3 as the   *)
(* route units use it.                                                       *)
(* ========================================================================= *)

needs "src/pc_rf_extend.ml";;
needs "src/pc_pde_rdt_limit.ml";;
needs "src/pc_pde_mexist.ml";;
needs "src/pc_pde_gauge.ml";;
needs "src/pc_rf_unique.ml";;
needs "src/pc_rfa_r1.ml";;
needs "src/pc_rfa_doubling.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The statements of pc_pde_iface without hypotheses.                        *)
(* ------------------------------------------------------------------------- *)

let PDEF_RDT_UNIFORM = prove
 (`!(u:A->bool) (n:N->bool). PDE_RDT_UNIFORM_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_RDT_FROM_MLIN THEN REWRITE_TAC[PDE_MLIN_HOLDS]);;

let PDEF_STE_UNIFORM = prove
 (`!(u:A->bool) (n:N->bool). PDE_STE_UNIFORM_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_STE_UNIFORM_FROM_RDT THEN
  REWRITE_TAC[PDEF_RDT_UNIFORM; PDE_GAUGE]);;

let PDEF_STE = prove
 (`!(u:A->bool) (n:N->bool). PDE_STE_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_STE_FROM_UNIFORM THEN REWRITE_TAC[PDEF_STE_UNIFORM]);;

let PDEF_EXTENSION = prove
 (`!(u:A->bool) (n:N->bool). PDE_EXTENSION_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_EXTENSION_FROM THEN
  REWRITE_TAC[PDEF_STE_UNIFORM; PDE_UNIQUENESS; RFA_R1]);;

let PDEF_MAXIMAL_FLOW = prove
 (`!(u:A->bool) (n:N->bool). PDE_MAXIMAL_FLOW_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_MAXIMAL_FROM THEN
  REWRITE_TAC[PDEF_STE; PDE_UNIQUENESS; PDEF_EXTENSION]);;

let PDEF_CURVATURE_TIME = prove
 (`!(u:A->bool) (n:N->bool). PDE_CURVATURE_TIME_STATEMENT u n`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC PDE_CURVATURE_TIME_FROM THEN
  REWRITE_TAC[PDEF_MAXIMAL_FLOW; RFA_R2]);;

(* The forms used by the route units: any carrier type, dimension 3. *)

let PDEF_RDT_UNIFORM_3 = prove
 (`!(u:A->bool). PDE_RDT_UNIFORM_STATEMENT u (:3)`,
  REWRITE_TAC[PDEF_RDT_UNIFORM]);;

let PDEF_STE_UNIFORM_3 = prove
 (`!(u:A->bool). PDE_STE_UNIFORM_STATEMENT u (:3)`,
  REWRITE_TAC[PDEF_STE_UNIFORM]);;

let PDEF_STE_3 = prove
 (`!(u:A->bool). PDE_STE_STATEMENT u (:3)`,
  REWRITE_TAC[PDEF_STE]);;

let PDEF_EXTENSION_3 = prove
 (`!(u:A->bool). PDE_EXTENSION_STATEMENT u (:3)`,
  REWRITE_TAC[PDEF_EXTENSION]);;

let PDEF_MAXIMAL_FLOW_3 = prove
 (`!(u:A->bool). PDE_MAXIMAL_FLOW_STATEMENT u (:3)`,
  REWRITE_TAC[PDEF_MAXIMAL_FLOW]);;

let PDEF_CURVATURE_TIME_3 = prove
 (`!(u:A->bool). PDE_CURVATURE_TIME_STATEMENT u (:3)`,
  REWRITE_TAC[PDEF_CURVATURE_TIME]);;

