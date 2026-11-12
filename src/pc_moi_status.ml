(* ========================================================================= *)
(* pc_moi_status: the Moise chain assembled.                                 *)
(* MOI_SST_SMOOTH_CORE: the smooth core COMBINATORIAL_SMOOTHING from the     *)
(* route M leaves C7 (MOI_SMO_LINK_PD_STATEMENT) and D6                      *)
(* (MOI_SMO_PD2_STATEMENT); MOI_SST_SMOOTH_CORE_D6: from D6 alone, with C7   *)
(* (MOI_SMO_LINK_PD).                                                        *)
(* MOI_SST_SMOOTH: COMBINATORIAL_SMOOTHING, with D6 from D1-D5 and C1.       *)
(* MOI_SST_HEADLINE : |- !u:A->bool. MOISE_SMOOTHING_STATEMENT u, from       *)
(* MOI_SST_SMOOTH and MOI_CORE_STATUS : |- MOISE_352_COMPLEX_STATEMENT (:7)  *)
(* of pc_moi_core_status.ml.  The file checks that the list                  *)
(* MOI_CORE_REMAINING of hypotheses of the PL core is empty.                 *)
(* ========================================================================= *)

needs "src/pc_moi_chain.ml";;
needs "src/pc_moi_smo_edge.ml";;
needs "src/pc_moi_smo_vertex.ml";;
needs "src/pc_moi_smo_lpd.ml";;
needs "src/pc_moi_pd2_loc.ml";;
needs "src/pc_moi_pd2_top.ml";;
needs "src/pc_moi_pd2_glob.ml";;
needs "src/pc_moi_core_status.ml";;

prioritize_real();;
type_invention_error := true;;

let MOI_SST_SMOOTH_CORE = prove
 (`!u:N->bool. MOI_SMO_LINK_PD_STATEMENT u /\ MOI_SMO_PD2_STATEMENT u
              ==> COMBINATORIAL_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SMO_TOP_FROM_PARTS THEN
  REWRITE_TAC[MOI_SMO_PUNCTURED] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SMO_LINK_SMOOTH_FROM_PARTS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SMO_LINK_ATLAS_FROM_EDGE THEN REWRITE_TAC[MOI_SMO_EDGE];
    MATCH_MP_TAC MOI_SMO_VERTEX_FROM_EDGE THEN REWRITE_TAC[MOI_SMO_EDGE]]);;

(* With C7 (pc_moi_smo_lpd, MOI_SMO_LINK_PD) the smooth core needs D6 only. *)

let MOI_SST_SMOOTH_CORE_D6 = prove
 (`!u:N->bool. MOI_SMO_PD2_STATEMENT u ==> COMBINATORIAL_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_SST_SMOOTH_CORE THEN
  ASM_REWRITE_TAC[MOI_SMO_LINK_PD]);;

(* D6 from D1-D5 and C1 (pc_moi_pd2_glob, MOI_SMO_PD2_FROM_LEAVES): the     *)
(* smooth core COMBINATORIAL_SMOOTHING is a theorem.                         *)

let MOI_SST_SMOOTH = prove
 (`!u:N->bool. COMBINATORIAL_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN MATCH_MP_TAC MOI_SST_SMOOTH_CORE_D6 THEN
  MATCH_MP_TAC MOI_SMO_PD2_FROM_LEAVES THEN
  REWRITE_TAC[MOI_SMO_LIN; MOI_SMO_VERTEX2; MOI_SMO_CREASE; MOI_SMO_CREASE_ORIENT;
              MOI_SMO_VERTEX_DEGREE; MOI_SMO_LOCAL_HOMEO_SPHERE;
              MOI_SMO_SURFACE_COMPLEX]);;

let MOI_SST_OPEN_ITEMS = MOI_CORE_REMAINING;;

if not (MOI_SST_OPEN_ITEMS = []) then failwith "pc_moi_status final: open items left";;

let MOI_SST_HEADLINE = prove
 (`!u:A->bool. MOISE_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN
  MATCH_MP_TAC MOI_MOISE_SMOOTHING_FROM_CORES THEN CONJ_TAC THENL
   [MATCH_ACCEPT_TAC MOI_CORE_STATUS;
    REWRITE_TAC[MOI_SST_SMOOTH]]);;

(length MOI_SST_OPEN_ITEMS, length (hyp MOI_SST_HEADLINE));;

