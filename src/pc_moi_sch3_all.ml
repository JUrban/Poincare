(* ========================================================================= *)
(* pc_moi_sch3_all: the PL Schoenflies theorem assembled.  Loads the         *)
(* Schoenflies units and derives both PL Schoenflies statements of           *)
(* pc_moi_stmt.ml (MOI_SCH3_ALL_SCHOENFLIES and                              *)
(* MOI_SCH3_ALL_SCHOENFLIES_AMBIENT), with no hypotheses, from the leaf      *)
(* closure MOI_SCD_CLOSURE_LEAVES of pc_moi_sch3_stmt.ml.  The nine leaf     *)
(* theorems, in the order of MOI_SCD_LEAF_TARGETS: REDUCE (tilt, from        *)
(* CAP_COUNT of capc), SINGULAR_POLYGONS and LEVEL_POLYGONS_FINITE (lev),    *)
(* THM11 (glue), GENERIC_NEAR, FILLING_TRIANGULATION and CROSSINGS_STABLE    *)
(* (gen), SADDLE_FREE_FIBRED (fib), FIBRED_SIMPLE (slab, from SLAB_STMT of   *)
(* slabb, from STAR_STMT of slabc).                                          *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_amb2.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_free.ml";;
needs "src/pc_moi_sch3_push.ml";;
needs "src/pc_moi_sch3_glue.ml";;
needs "src/pc_moi_sch3_gen.ml";;
needs "src/pc_moi_sch3_lev.ml";;
needs "src/pc_moi_sch3_cvx.ml";;
needs "src/pc_moi_sch3_tilt.ml";;
needs "src/pc_moi_sch3_capc.ml";;
needs "src/pc_moi_sch3_fib.ml";;
needs "src/pc_moi_sch3_slab.ml";;
needs "src/pc_moi_sch3_slabb.ml";;
needs "src/pc_moi_sch3_slabc.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_SCH3_ALL_REDUCE = MP REDUCE_FROM_COUNT CAP_COUNT;;

let MOI_SCH3_ALL_FIBRED_SIMPLE =
  MP MOI_SSL_FIBRED_FROM_SLAB (MP MOI_SSL_SLAB_FROM_STAR MOI_SSC_STAR);;

let MOI_SCH3_ALL_LEAVES =
  [MOI_SCH3_ALL_REDUCE; SINGULAR_POLYGONS; LEVEL_POLYGONS_FINITE; THM11;
   GENERIC_NEAR; FILLING_TRIANGULATION; CROSSINGS_STABLE; SADDLE_FREE_FIBRED;
   MOI_SCH3_ALL_FIBRED_SIMPLE];;

let MOI_SCH3_ALL_LEAVES_OK =
  List.length MOI_SCH3_ALL_LEAVES = List.length MOI_SCD_LEAF_TARGETS &&
  List.for_all2 (fun th tm -> aconv (concl th) tm && hyp th = [])
    MOI_SCH3_ALL_LEAVES MOI_SCD_LEAF_TARGETS;;

let MOI_SCH3_ALL_BOTH =
  MP MOI_SCD_CLOSURE_LEAVES (end_itlist CONJ MOI_SCH3_ALL_LEAVES);;

let MOI_SCH3_ALL_SCHOENFLIES = prove
 (`PL_SCHOENFLIES_3_STATEMENT`,
  ACCEPT_TAC(CONJUNCT2 MOI_SCH3_ALL_BOTH));;

let MOI_SCH3_ALL_SCHOENFLIES_AMBIENT = prove
 (`PL_SCHOENFLIES_3_AMBIENT_STATEMENT`,
  ACCEPT_TAC(CONJUNCT1 MOI_SCH3_ALL_BOTH));;

(MOI_SCH3_ALL_LEAVES_OK, hyp MOI_SCH3_ALL_SCHOENFLIES, hyp MOI_SCH3_ALL_SCHOENFLIES_AMBIENT);;

