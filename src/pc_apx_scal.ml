(* ========================================================================= *)
(* pc_apx_scal: continuity of the scalar curvature on a manifold            *)
(* (MFD_SCALAR_CONTINUOUS), a foundations-style lemma used by the Appendix   *)
(* layer (exclusion of C-components, N7) and by the pc_rfa units.  In each   *)
(* chart the scalar curvature is lscalar of the local metric                 *)
(* (MFD_SCALAR_CHART), which is smooth (LRG_LSCALAR_SMOOTH); charts are      *)
(* homeomorphisms.                                                           *)
(* ========================================================================= *)

needs "src/pc_mfd_riem.ml";;
needs "src/pc_lrg_evol.ml";;
needs "src/pc_top_cover.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* MFD_SCALAR_CONTINUOUS.                                                     *)
(* ------------------------------------------------------------------------- *)

let MFD_SCALAR_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> continuous_map (top,euclideanreal) (mfd_scalar atlas g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `\z:A. lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    BETA_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFD_SCALAR_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:A. lscalar (metric_local atlas (U,phi) (g:A->real^N^N)) (phi z)) =
    (\y. lscalar (metric_local atlas (U,phi) g) y) o (phi:A->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN
  UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
  REWRITE_TAC[riemannian_metric] THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND]);;

