(* ========================================================================= *)
(* pc_moi_chain: the top of the Moise chain.  The four PL leaves of          *)
(* pc_moi_glue2 are proved by pc_moi_ptri, pc_moi_cone with pc_moi_lfopen,   *)
(* and pc_moi_comb; the theorems here take the two cores as hypotheses:      *)
(*   MOISE_352_COMPLEX_STATEMENT (:7)    (PL core, Moise Secs 25-35,         *)
(*                                        proved in pc_moi_core_status),     *)
(*   COMBINATORIAL_SMOOTHING_STATEMENT (:7)   (smooth core, pc_moi_status).  *)
(* The triangulation theorem (compact case of Moise 35.3) needs only the PL  *)
(* core, the PL smoothing theorem only the smooth core, and                  *)
(* MOISE_SMOOTHING_STATEMENT both.                                           *)
(* ========================================================================= *)

needs "src/pc_moi_glue2.ml";;
needs "src/pc_moi_ptri.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_lfopen.ml";;
needs "src/pc_moi_comb.ml";;

prioritize_real();;
type_invention_error := true;;

(* The four PL leaves.                                                       *)

let MOI_LEAF_TRI_NBHD_THM = prove
 (`!(u:A->bool) (v:N->bool). MOI_LEAF_TRI_NBHD u v`,
  REWRITE_TAC[MOI_LEAF_TRI_NBHD; PL_TRIANGULATION_COMPACT_NBHD]);;

let MOI_LEAF_TRI_EXISTS_THM = prove
 (`!(u:A->bool) (v:N->bool). MOI_LEAF_TRI_EXISTS u v`,
  REWRITE_TAC[MOI_LEAF_TRI_EXISTS; PL_TRIANGULATION_COMPACT_EXISTS]);;

let LF_TRIANGULATION_OPEN_SUBSET = prove
 (`!(c:(real^N->bool)->bool) u.
     simplicial_complex c /\ open_in (subtopology euclidean (UNIONS c)) u
     ==> ?d. lf_simplicial_complex d /\ UNIONS d = u /\
             (!s. s IN d ==> ?t. t IN c /\ s SUBSET t)`,
  MATCH_MP_TAC LF_TRIANGULATION_OPEN_SUBSET_FROM_EXTEND THEN
  REWRITE_TAC[SIMPLICIAL_SUBDIVISION_EXTEND]);;

let MOI_LEAF_LF_OPEN_THM = prove
 (`!v:N->bool. MOI_LEAF_LF_OPEN v`,
  REWRITE_TAC[MOI_LEAF_LF_OPEN; LF_TRIANGULATION_OPEN_SUBSET]);;

let MOI_LEAF_COMBINATORIAL_THM = prove
 (`!(u:A->bool) (v:N->bool). MOI_LEAF_COMBINATORIAL u v`,
  REWRITE_TAC[MOI_LEAF_COMBINATORIAL; PL_TRIANGULATION_COMBINATORIAL]);;

(* The three top statements from the cores.                                  *)

let MOI_DIMINDEX_7_CHAIN = prove
 (`7 <= dimindex(:7)`,
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`; LE_REFL]);;

let MOI_PL_TRIANGULATION_THM = prove
 (`!(u:A->bool) (v:N->bool). PL_TRIANGULATION_STATEMENT u v`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_GLUE2_PL_TRIANGULATION THEN
  REWRITE_TAC[MOI_LEAF_TRI_EXISTS_THM; MOI_LEAF_COMBINATORIAL_THM]);;

let MOI_PL_ATLAS_FROM_PL_CORE = prove
 (`!u:A->bool.
     MOISE_352_COMPLEX_STATEMENT (:7) ==> MOISE_PL_ATLAS_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(INST_TYPE [`:7`,`:N`] (ISPEC `u:A->bool` MOI_GLUE2_CHART_GLUING)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[MOI_DIMINDEX_7_CHAIN; MOI_LEAF_TRI_NBHD_THM; MOI_LEAF_LF_OPEN_THM;
                  MOI_LEAF_COMBINATORIAL_THM]);;

let MOI_TRIANGULATION_FROM_PL_CORE = prove
 (`!u:A->bool.
     MOISE_352_COMPLEX_STATEMENT (:7) ==> MOISE_TRIANGULATION_STATEMENT u (:7)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_MOISE_TRIANGULATION_FROM_PARTS THEN
  ASM_SIMP_TAC[MOI_PL_ATLAS_FROM_PL_CORE; MOI_PL_TRIANGULATION_THM]);;

let MOI_PL_SMOOTHING_FROM_SMOOTH_CORE = prove
 (`!u:A->bool.
     COMBINATORIAL_SMOOTHING_STATEMENT (:7) ==> PL_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `(:7)`] MOI_PL_SMOOTHING_FROM_TRIANGULATION) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[MOI_DIMINDEX_7_CHAIN; MOI_PL_TRIANGULATION_THM]);;

let MOI_MOISE_SMOOTHING_FROM_CORES = prove
 (`!u:A->bool.
     MOISE_352_COMPLEX_STATEMENT (:7) /\ COMBINATORIAL_SMOOTHING_STATEMENT (:7)
     ==> MOISE_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_MOISE_SMOOTHING_FROM_LEAVES THEN
  ASM_REWRITE_TAC[MOI_LEAF_TRI_NBHD_THM; MOI_LEAF_TRI_EXISTS_THM;
                  MOI_LEAF_LF_OPEN_THM; MOI_LEAF_COMBINATORIAL_THM]);;

