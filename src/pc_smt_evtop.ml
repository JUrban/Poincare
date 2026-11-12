(* ========================================================================= *)
(* Unit pc_smt_evtop: the topology of one surgery event, EVENT_TOPOLOGY      *)
(* (EVENT_TOPOLOGY_STATEMENT of pc_rfs_top, T3, at every type).  It is       *)
(* APX_EVENT_TOPOLOGY_FROM_LEAVES of pc_apx_event applied to its six         *)
(* leaves: APX_STRONG_NECK_EARLIER and APX_EXCLUDE (pc_apx_neck),            *)
(* SMT_SC_SPHERE_SEP (pc_smt_sep), APX_REGION (pc_apx_tight), APX_A25        *)
(* (pc_apx_a25top) and SMT_TWISTED_SPHERE_ALL (pc_smt_straight).            *)
(* ========================================================================= *)

needs "src/pc_apx_event.ml";;
needs "src/pc_apx_neck.ml";;
needs "src/pc_smt_sep.ml";;
needs "src/pc_apx_tight.ml";;
needs "src/pc_apx_a25top.ml";;
needs "src/pc_smt_straight.ml";;

prioritize_real();;
type_invention_error := true;;

let EVENT_TOPOLOGY = prove
 (`!w:A->bool. EVENT_TOPOLOGY_STATEMENT w`,
  GEN_TAC THEN MATCH_MP_TAC APX_EVENT_TOPOLOGY_FROM_LEAVES THEN
  REWRITE_TAC[APX_STRONG_NECK_EARLIER; SMT_SC_SPHERE_SEP; APX_REGION; APX_A25;
              APX_EXCLUDE; SMT_TWISTED_SPHERE_ALL]);;

