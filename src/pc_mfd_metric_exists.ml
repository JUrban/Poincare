(* ========================================================================= *)
(* pc_mfd_metric_exists: every compact Hausdorff smooth manifold, of any     *)
(* dimension, carries a Riemannian metric: METRIC_EXISTENCE proves           *)
(* METRIC_EXISTENCE_STATEMENT of pc_rfs_top.  Route: the Whitney embedding   *)
(* MFD_EMBEDDING_EXISTS of pc_mfd_embed into real^(2N+1) and its induced     *)
(* metric J^T J, J the chart Jacobian mfd_emb_jac of the embedding.  In a    *)
(* chart c the induced metric is the Gram matrix of the derivative of f o    *)
(* chart_inv c (GRGE_EMB_JAC_FACTS), smooth by the matrix field lemmas of    *)
(* pc_mfd_embed and positive definite since that derivative is injective.    *)
(* RIEMANNIAN_METRIC_IMMERSION holds for every smooth immersion into real^K. *)
(* ========================================================================= *)

needs "src/pc_rfs_top.ml";;
needs "src/pc_mfd_embed.ml";;

prioritize_real();;
type_invention_error := true;;

(* Gram matrices of injective matrices are symmetric positive definite. *)

let MMEX_GRAM_FACTS = prove
 (`!D:real^N^K.
        (!v. D ** v = vec 0 ==> v = vec 0)
        ==> transp(transp D ** D) = transp D ** D /\
            !v. ~(v = vec 0) ==> &0 < v dot ((transp D ** D) ** v)`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL; DOT_POS_LT] THEN ASM_MESON_TAC[]);;

(* The induced metric of a smooth immersion into real^K. *)

let RIEMANNIAN_METRIC_IMMERSION = prove
 (`!top atlas (f:A->real^K).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_immersion_into atlas f
        ==> riemannian_metric atlas
              (\x. transp(mfd_emb_jac atlas f x) ** mfd_emb_jac atlas f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[riemannian_metric] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:A->real^K`; `c:(A->bool)#(A->real^N)`] GRGE_IMMERSION_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")) THEN
  ABBREV_TAC `D = \y:real^N. matrix(frechet_derivative ((f:A->real^K) o chart_inv c) (at y))` THEN
  SUBGOAL_THEN
   `!x:A. x IN FST c
          ==> (D:real^N->real^N^K) (SND c x) =
              mfd_emb_jac atlas (f:A->real^K) x **
              matrix(chart_jac c (chart_at atlas x) x) /\
              (!v. D (SND c x) ** v = vec 0 ==> v = vec 0)`
  (LABEL_TAC "D") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:A->real^K`; `c:(A->bool)#(A->real^N)`; `x:A`] GRGE_EMB_JAC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (LABEL_TAC "eq") (LABEL_TAC "lin")))) THEN
    EXPAND_TAC "D" THEN CONJ_TAC THENL
     [USE_THEN "eq" ACCEPT_TAC;
      X_GEN_TAC `v:real^N` THEN USE_THEN "lin" (fun th -> REWRITE_TAC[GSYM th]) THEN
      DISCH_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN
      EXISTS_TAC `SND (c:(A->bool)#(A->real^N)) x` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MFDR_METRIC_FIELD_EQ THEN
  EXISTS_TAC `\y:real^N. transp((D:real^N->real^N^K) y) ** D y` THEN CONJ_TAC THENL
   [REWRITE_TAC[metric_field] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGE_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
      SUBGOAL_THEN
       `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
          ((vectorize:real^N^K->real^(K,N)finite_prod) o (D:real^N->real^N^K))`
      ASSUME_TAC THENL
       [EXPAND_TAC "D" THEN MATCH_MP_TAC GRGE_SMOOTH_JACOBIAN THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC GRGE_SMOOTH_TRANSP THEN
      ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC MMEX_GRAM_FACTS THEN ASM_MESON_TAC[]];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    REWRITE_TAC[metric_local] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c x) = (x:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "D" (MP_TAC o SPEC `x:A`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[MATRIX_TRANSP_MUL; MATRIX_MUL_ASSOC]]);;

(* Every compact Hausdorff smooth manifold has a Riemannian metric. *)

let RIEMANNIAN_METRIC_EXISTS = prove
 (`!top atlas.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top
        ==> ?g. riemannian_metric atlas g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
    (INST_TYPE [`:((N,N)finite_sum,1)finite_sum`,`:K`] MFD_EMBEDDING_EXISTS)) THEN
  ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mfd_embedding] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->real^((N,N)finite_sum,1)finite_sum`
    STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:A. transp(mfd_emb_jac (atlas:((A->bool)#(A->real^N))->bool)
                      (f:A->real^((N,N)finite_sum,1)finite_sum) x) **
                    mfd_emb_jac atlas f x` THEN
  MATCH_MP_TAC RIEMANNIAN_METRIC_IMMERSION THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

let METRIC_EXISTENCE = prove
 (`!(u:A->bool) (n:N->bool). METRIC_EXISTENCE_STATEMENT u n`,
  REWRITE_TAC[METRIC_EXISTENCE_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RIEMANNIAN_METRIC_EXISTS THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

