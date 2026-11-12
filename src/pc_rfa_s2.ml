(* ========================================================================= *)
(* Unit pc_rfa_s2: the 2-dimensional case of the statement                   *)
(* P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT: a compact connected Hausdorff 2-d   *)
(* gradient shrinking soliton with positive curvature is round.  The         *)
(* potential is continuous (RFA_S2_F_CONTINUOUS); R > 0, R = C exp f, f has  *)
(* a maximum point p; if (C/2) e^f(p) <= 1/2 the metric is round             *)
(* (RFA_S2_FLAT_ROUND), and the other case is impossible (RFA_S2_NOT_STEEP): *)
(* RFA_S2_ROUND_2D.  With RFA_P2B_REQ_SHRINKER_ROUND_2D_ONLY (pc_rfa_shrink) *)
(* this proves the statement P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT            *)
(* (RFA_P2B_REQ_SHRINKER_ROUND).                                             *)
(* ========================================================================= *)

needs "src/pc_rfa_s2geo.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Assembly.                                                                 *)
(* ========================================================================= *)

let RFA_S2_F_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (f:A->real).
     p2b_shrinker (top,atlas) g f ==> continuous_map (top,euclideanreal) f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
  EXISTS_TAC `\z:A. (f:A->real)(chart_inv (U,phi) ((phi:A->real^N) z))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:A. (f:A->real)(chart_inv (U,phi) ((phi:A->real^N) z))) =
    (\y. f(chart_inv (U,phi) y)) o (phi:A->real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
  UNDISCH_TAC `mfd_smooth_on (atlas:((A->bool)#(A->real^N))->bool) (topspace top)
                 (\x. lift((f:A->real) x))` THEN
  REWRITE_TAC[mfd_smooth_on] THEN DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND; o_DEF] THEN
  SUBGOAL_THEN `U INTER topspace top = (U:A->bool)` SUBST1_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SET_RULE `!s t:A->bool. s SUBSET t ==> s INTER t = s`];
    SIMP_TAC[]]);;

let RFA_S2_ROUND_2D = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real).
     hausdorff_space top /\ compact_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\
     (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
              ==> &0 < mfd_sectional atlas g x u v)
     ==> p2b_round (top,atlas) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [REWRITE_TAC[p2b_round] THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> &0 < mfd_scalar atlas (g:A->real^2^2) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `x:A`; `basis 1:real^2`; `basis 2:real^2`] RFA_S2_MFD_SEC_SCAL) THEN
    ASM_REWRITE_TAC[RFA_S2_BASIS_NONCOLL] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`x:A`; `basis 1:real^2`; `basis 2:real^2`] (ASSUME
      `!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
               ==> &0 < mfd_sectional atlas (g:A->real^2^2) x u v`)) THEN
    REWRITE_TAC[ASSUME `(x:A) IN topspace top`; RFA_S2_BASIS_NONCOLL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`] RFA_S2_SCAL_EXPF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `f:A->real`] RFA_SH_GLOBAL_MAX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `f:A->real`] RFA_S2_F_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC)] THEN
  ASM_CASES_TAC `C / &2 * exp((f:A->real) p) <= &1 / &2` THENL
   [MATCH_MP_TAC RFA_S2_FLAT_ROUND THEN
    MAP_EVERY EXISTS_TAC [`f:A->real`; `C:real`; `p:A`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`] RFA_S2_NOT_STEEP) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let RFA_P2B_REQ_SHRINKER_ROUND = prove
 (`!w:B->bool. P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[RFA_P2B_REQ_SHRINKER_ROUND_2D_ONLY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC RFA_S2_ROUND_2D THEN
  EXISTS_TAC `f:B->real` THEN ASM_REWRITE_TAC[]);;

