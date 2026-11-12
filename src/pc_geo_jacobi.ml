(* ========================================================================= *)
(* pc_geo_jacobi: Jacobi fields along geodesics.  Existence and uniqueness   *)
(* (MFD_JACOBI_EXISTS_UNIQUE) by a parallel orthonormal frame (pc_cmp_frame) *)
(* and the global linear ODE a'' = -R a (ODE_LINEAR_GLOBAL); variations      *)
(* through geodesics, d(exp) by Jacobi fields, conjugate points.            *)
(* Its theorems belong to the geodesics API pc_geo_iface.                    *)
(*                                                                           *)
(* Orthonormal bases, parallel orthonormal frames.                           *)
(* ========================================================================= *)

needs "src/pc_geo_par.ml";;
needs "src/pc_cmp_frame.ml";;
needs "src/pc_cmp_comm.ml";;

prioritize_real();;
type_invention_error := true;;

let GEOJ_ONB = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> ?E:real^N^N. transp E ** g x ** E = mat 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `positive_definite((g:A->real^N^N) x)` MP_TAC THENL
   [REWRITE_TAC[positive_definite; symmetric_matrix] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
      ASM_REWRITE_TAC[metric_field] THEN MESON_TAC[];
      MATCH_MP_TAC GEOD_G_POS_DEF THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[POSITIVE_DEFINITE_COVARIANCE_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (SUBST1_TAC o SYM))) THEN
  EXISTS_TAC `matrix_inv(S:real^N^N)` THEN
  SUBGOAL_THEN `transp(matrix_inv(S:real^N^N)) ** transp S = mat 1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MATRIX_TRANSP_MUL] THEN ASM_SIMP_TAC[MATRIX_INV; TRANSP_MAT];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[MATRIX_MUL_LID] THEN
  ASM_SIMP_TAC[MATRIX_INV]);;

(* A parallel orthonormal frame along a C^1 curve. *)

let GEOJ_PFRAME_EXISTS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t0.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_curve_on (top,atlas) gamma J /\ t0 IN J
        ==> ?E. cmp_pframe atlas g gamma J E`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_curve_on]) THEN
  SUBGOAL_THEN `(gamma:real->A) t0 IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_C1_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t0`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `E0:real^N^N` ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!j. ?Y. mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) J Y /\
            Y t0 = column j (E0:real^N^N)`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `t0:real`;
                   `column j (E0:real^N^N)`] MFD_PARALLEL_EXISTS_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:num->real->real^N` (LABEL_TAC "E")) THEN
  EXISTS_TAC `E:num->real->real^N` THEN
  MATCH_MP_TAC CMPF_PFRAME_FROM_POINT THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `t0:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cmp_fmat (E:num->real->real^N) t0 = E0` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; cmp_fmat; LAMBDA_BETA] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "E" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `j:num` th)]) THEN
    ASM_SIMP_TAC[column; LAMBDA_BETA];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Fields in an arbitrary chart; continuity of trilinear                     *)
(* expressions along curves.                                                 *)
(* ========================================================================= *)

let GEOJ_FIELD_DIFF_IMP_CHART = prove
 (`!top atlas (gamma:real->A) J (Y:real->real^N) (c:(A->bool)#(A->real^N)) t.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_field_diff atlas gamma Y J /\ c IN atlas /\ t IN J /\ gamma t IN FST c
        ==> (\s. mfd_field_rep atlas gamma Y c (drop s)) differentiable at (lift t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal J,top) (gamma:real->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOC_C1_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN J ==> (gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclideanreal J,top) (gamma:real->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
           (chart_at atlas (gamma t)) (drop s)) differentiable at (lift t)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_field_diff atlas (gamma:real->A) (Y:real->real^N) J` THEN
    REWRITE_TAC[mfd_field_diff] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c0:(A->bool)#(A->real^N)) INTER FST(c:(A->bool)#(A->real^N))`;
                 `t:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC OPEN_IN_INTER) THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\r. frechet_derivative (chart_trans (c0:(A->bool)#(A->real^N)) c)
          (at (SND c0 ((gamma:real->A)(drop r))))
          (mfd_field_rep atlas gamma (Y:real->real^N) c0 (drop r))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop r` o check (fun th -> can (term_match []
      `!s. abs(s - t) < d ==> s IN J /\ (gamma:real->A) s IN W`) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A)(drop r)`] CHART_AT) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_field_rep; GSYM chart_jac] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                 ((gamma:real->A)(drop r)))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                 ((gamma:real->A)(drop r)))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `(gamma:real->A)(drop r)`] CHART_JAC_CHAIN) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[differentiable] THEN
  MP_TAC(ISPECL
   [`IMAGE (SND (c0:(A->bool)#(A->real^N)))
           (FST c0 INTER FST (c:(A->bool)#(A->real^N)))`;
    `chart_trans (c0:(A->bool)#(A->real^N)) c`;
    `\r. SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))`;
    `\r. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c0 (drop r)`;
    `vector_derivative (\r. SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r)))
       (at (lift t))`;
    `vector_derivative (\r. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c0 (drop r))
       (at (lift t))`;
    `lift t`] GEOL_FRECHET_ALONG) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[IN_INTER];
      MATCH_MP_TAC GEOC_C1_HAS_VD_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `J:real->bool`] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[has_vector_derivative] THEN MESON_TAC[]]);;

(* Continuity of trilinear expressions along curves. *)

let GEOJ_TRILINEAR_CONT = prove
 (`!(T0:real^1->real^N->real^N->real^N->real^M) (u:real^1->real^N) v w S.
        (!r. r IN S
             ==> (!v w. linear (\u. T0 r u v w)) /\
                 (!u w. linear (\v. T0 r u v w)) /\
                 (!u v. linear (\w. T0 r u v w))) /\
        (!a b c. (\r. T0 r (basis a) (basis b) (basis c)) continuous_on S) /\
        u continuous_on S /\ v continuous_on S /\ w continuous_on S
        ==> (\r. T0 r (u r) (v r) (w r)) continuous_on S`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\r. vsum(1..dimindex(:N))
          (\a. drop(lift(((u:real^1->real^N) r)$a)) %
               vsum(1..dimindex(:N))
                 (\b. drop(lift(((v:real^1->real^N) r)$b)) %
                      vsum(1..dimindex(:N))
                        (\c. drop(lift(((w:real^1->real^N) r)$c)) %
                             (T0:real^1->real^N->real^N->real^N->real^M) r
                               (basis a) (basis b) (basis c))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(r:real^1) IN S`) o check (fun th ->
      can (term_match [] `!r. r IN (S:real^1->bool) ==> P r`) (concl th))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. (T0:real^1->real^N->real^N->real^N->real^M) r x
                          ((v:real^1->real^N) r) ((w:real^1->real^N) r)`;
                   `(u:real^1->real^N) r`] GEOL_LINEAR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\y. (T0:real^1->real^N->real^N->real^N->real^M) r (basis a) y
                          ((w:real^1->real^N) r)`;
                   `(v:real^1->real^N) r`] GEOL_LINEAR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\z. (T0:real^1->real^N->real^N->real^N->real^M) r (basis a) (basis b) z`;
                   `(w:real^1->real^N) r`] GEOL_LINEAR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `c:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_SIMP_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE]);;

(* Curvature terms <R(X,V)V,W>_g at gamma s computed in a chart c. *)

let GEOJ_RIEMANN_DOT_CHART = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (c:(A->bool)#(A->real^N))
    (X:real->real^N) (W:real->real^N) s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ c IN atlas /\ s IN J /\
        gamma s IN FST c
        ==> W s dot (g(gamma s) **
                     mfd_riemann atlas g (gamma s) (X s) (mfd_vel atlas gamma s)
                                 (mfd_vel atlas gamma s)) =
            mfd_field_rep atlas gamma W c s dot
            (metric_local atlas c g (SND c (gamma s)) **
             lriemann (metric_local atlas c g) (SND c (gamma s))
               (mfd_field_rep atlas gamma X c s)
               (vector_derivative (\r. SND c (gamma(drop r))) (at (lift s)))
               (vector_derivative (\r. SND c (gamma(drop r))) (at (lift s))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_C1_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[mfd_geodesic]; ASM_MESON_TAC[CMPG_GEODESIC_C1]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) s`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `vector_derivative (\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r)))
      (at (lift s)) =
    chart_jac (chart_at atlas (gamma s)) c (gamma s)
      (mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gamma s)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN MATCH_MP_TAC MFD_GEODESIC_VEL_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_field_rep; mfd_riemann] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`; `(gamma:real->A) s`;
                 `(X:real->real^N) s`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) s`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) s`]
    LRIEMANN_CHART_TRANS) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(GSYM GEOC_BILIN_CHART) THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

(* The curvature matrix of a parallel orthonormal frame is continuous. *)

let GEOJ_RMAT_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_pframe atlas g gamma J E
        ==> !i j. (\r. lift(cmp_rmat atlas g gamma E (drop r) $i$j))
                  continuous_on IMAGE lift J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_geodesic]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. s IN J ==> (gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclideanreal J,top) (gamma:real->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> mfd_field_diff atlas (gamma:real->A) ((E:num->real->real^N) k) J`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o GEN_REWRITE_RULE I [cmp_pframe] o
      check (fun th -> can (term_match []
        `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N)`)
        (concl th))) THEN
    ASM_SIMP_TAC[mfd_parallel];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  MP_TAC(ISPEC `i:num` (INST_TYPE [`:real^N`,`:A`] FINITE_INDEX_INRANGE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `i':num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> ONCE_REWRITE_TAC[th])))) THEN
  MP_TAC(ISPEC `j:num` (INST_TYPE [`:real`,`:A`] FINITE_INDEX_INRANGE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> ONCE_REWRITE_TAC[th])))) THEN
  ASM_SIMP_TAC[cmp_rmat; LAMBDA_BETA] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t1`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t1)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `t1:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  ABBREV_TAC `a = t1 - d / &2` THEN ABBREV_TAC `b = t1 + d / &2` THEN
  SUBGOAL_THEN `a < t1 /\ t1 < b /\ a < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[a,b]
        ==> s IN J /\ (gamma:real->A) s IN FST(c:(A->bool)#(A->real^N))`
  (LABEL_TAC "inc") THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    USE_THEN "near" MATCH_MP_TAC THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!a b. a <= b /\ real_interval[a,b] SUBSET J
             ==> mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b`)
      (concl th))) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "inc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `s IN real_interval[a,b]`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r IN interval[lift a,lift b] /\
         (gamma:real->A)(drop r) IN FST(c:(A->bool)#(A->real^N))} =
    interval[lift a,lift b]`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real^1` THEN
    EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
    USE_THEN "inc" (fun th -> MP_TAC(MATCH_MP th (MATCH_MP GRGD_DROP_IN_REAL_INTERVAL
      (ASSUME `r IN interval[lift a,lift b]`)))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `G = metric_local (atlas:((A->bool)#(A->real^N))->bool)
                    (c:(A->bool)#(A->real^N)) (g:A->real^N^N)` THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) (G:real^N->real^N^N)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN
    UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `yc = \r. SND(c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))` THEN
  ABBREV_TAC `vc = \r. vector_derivative (yc:real^1->real^N)
                         (at r within interval[lift a,lift b])` THEN
  SUBGOAL_THEN `(yc:real^1->real^N) continuous_on interval[lift a,lift b]` ASSUME_TAC THENL
   [EXPAND_TAC "yc" THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)` o CONJUNCT2 o
      CONJUNCT2 o GEN_REWRITE_RULE I [mfd_c1_curve] o check (fun th ->
        can (term_match [] `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool)
                              (gamma:real->A) a b`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vc:real^1->real^N) continuous_on interval[lift a,lift b]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`; `c:(A->bool)#(A->real^N)`]
      GRGD_C1_CHART_VD_CONTINUOUS) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["vc"; "yc"] THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (yc:real^1->real^N) (interval[lift a,lift b]) SUBSET
    IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    EXPAND_TAC "yc" THEN REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "inc" (fun th -> MP_TAC(MATCH_MP th (MATCH_MP GRGD_DROP_IN_REAL_INTERVAL
      (ASSUME `r IN interval[lift a,lift b]`)))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> (\r. mfd_field_rep atlas (gamma:real->A) ((E:num->real->real^N) k)
                   (c:(A->bool)#(A->real^N)) (drop r))
            continuous_on interval[lift a,lift b]`
  (LABEL_TAC "repc") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    MATCH_MP_TAC GEOJ_FIELD_DIFF_IMP_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_SIMP_TAC[] THEN
    USE_THEN "inc" (fun th -> MP_TAC(MATCH_MP th (MATCH_MP GRGD_DROP_IN_REAL_INTERVAL
      (ASSUME `r IN interval[lift a,lift b]`)))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `h = \r. lift(mfd_field_rep atlas (gamma:real->A) ((E:num->real->real^N) i')
                   (c:(A->bool)#(A->real^N)) (drop r) dot
                 ((G:real^N->real^N^N)((yc:real^1->real^N) r) **
                  lriemann G (yc r) (mfd_field_rep atlas gamma (E j') c (drop r))
                           ((vc:real^1->real^N) r) (vc r)))` THEN
  SUBGOAL_THEN `(h:real^1->real^1) continuous_on interval[lift a,lift b]` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    CONJ_TAC THENL [USE_THEN "repc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\r. (G:real^N->real^N^N)((yc:real^1->real^N) r)) =
        (vectorize o G) o yc`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      UNDISCH_TAC `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                     (G:real^N->real^N^N)` THEN
      SIMP_TAC[metric_field];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\r. lriemann (G:real^N->real^N^N) ((yc:real^1->real^N) r)`;
      `\r. mfd_field_rep atlas (gamma:real->A) ((E:num->real->real^N) j')
             (c:(A->bool)#(A->real^N)) (drop r)`;
      `vc:real^1->real^N`; `vc:real^1->real^N`; `interval[lift a,lift b]`]
      GEOJ_TRILINEAR_CONT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
      MATCH_MP_TAC LRIEMANN_TRILINEAR THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`p:num`; `q:num`; `m:num`] THEN
      SUBGOAL_THEN
       `(\r. lriemann (G:real^N->real^N^N) ((yc:real^1->real^N) r)
               (basis p) (basis q) (basis m)) =
        (\y. lriemann G y (basis p) (basis q) (basis m)) o yc`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC LRG_LRIEMANN_SMOOTH THEN ASM_REWRITE_TAC[];
      USE_THEN "repc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* transfer *)
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  EXISTS_TAC `h:real^1->real^1` THEN EXISTS_TAC `d / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `drop r IN real_interval[a,b] /\ drop r IN real_interval(a,b)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "inc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `drop r IN real_interval[a,b]`))) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `c:(A->bool)#(A->real^N)`; `(E:num->real->real^N) j'`;
                   `(E:num->real->real^N) i'`; `drop r`] GEOJ_RIEMANN_DOT_CHART) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(yc:real^1->real^N) differentiable at r` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `J:real->bool`; `c:(A->bool)#(A->real^N)`;
                     `drop r`] GEOC_C1_HAS_VD_AT) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN
      DISCH_THEN(ACCEPT_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE);
      ALL_TAC] THEN
    SUBGOAL_THEN `vector_derivative (yc:real^1->real^N) (at r) = (vc:real^1->real^N) r`
    SUBST1_TAC THENL
     [EXPAND_TAC "vc" THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
      REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
        UNDISCH_TAC `drop r IN real_interval[a,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]];
      ALL_TAC] THEN
    EXPAND_TAC "yc" THEN REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
    EXISTS_TAC `interval[lift a,lift b]` THEN
    ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL_1; LIFT_DROP]]);;

(* ========================================================================= *)
(* The first-order system a' = b, b' = -R a with continuous                  *)
(* coefficients on an open interval: global existence and uniqueness        *)
(* (ODE_LINEAR_GLOBAL, ODE_MAXIMAL_SOLUTION, ODE_MAXIMAL_UNIQUE).           *)
(* ========================================================================= *)

(* Out-of-range entries of a square matrix repeat in-range ones. *)

let GEOJ_ENTRIES_CONTINUOUS = prove
 (`!(A:real^1->real^N^N) s.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> (\t. lift(A t$i$j)) continuous_on s)
        ==> !i j. (\t. lift(A t$i$j)) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `i:num` (INST_TYPE [`:real^N`,`:A`] FINITE_INDEX_INRANGE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `i':num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> ONCE_REWRITE_TAC[th])))) THEN
  MP_TAC(ISPEC `j:num` (INST_TYPE [`:real`,`:A`] FINITE_INDEX_INRANGE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `j':num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> ONCE_REWRITE_TAC[th])))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The block matrix of the system acts as (a,b) |-> (b,-R a). *)

let GEOJ_PAIR_MATRIX = prove
 (`!(R:real^N^N) (z:real^(N,N)finite_sum).
        matrix(\z:real^(N,N)finite_sum. pastecart (sndcart z) (--(R ** fstcart z))) ** z =
        pastecart (sndcart z) (--(R ** fstcart z))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `linear(\z:real^(N,N)finite_sum. pastecart (sndcart z) (--((R:real^N^N) ** fstcart z)))`
  (fun th -> REWRITE_TAC[MATCH_MP MATRIX_WORKS th]) THEN
  REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD; SNDCART_CMUL;
              MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

(* Components of a curve in a product space. *)

let GEOJ_HAS_VD_SPLIT = prove
 (`!(z:real^1->real^(M,N)finite_sum) (x:real^M) (y:real^N) t.
        (z has_vector_derivative pastecart x y) (at t)
        ==> ((\s. fstcart(z s)) has_vector_derivative x) (at t) /\
            ((\s. sndcart(z s)) has_vector_derivative y) (at t)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`fstcart:real^(M,N)finite_sum->real^M`;
                   `z:real^1->real^(M,N)finite_sum`;
                   `pastecart (x:real^M) (y:real^N)`; `t:real^1`]
      ODE_HAS_VECTOR_DERIVATIVE_LINEAR_AT);
    MP_TAC(ISPECL [`sndcart:real^(M,N)finite_sum->real^N`;
                   `z:real^1->real^(M,N)finite_sum`;
                   `pastecart (x:real^M) (y:real^N)`; `t:real^1`]
      ODE_HAS_VECTOR_DERIVATIVE_LINEAR_AT)] THEN
  ASM_REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART; FSTCART_PASTECART;
                  SNDCART_PASTECART]);;

(* Global existence and uniqueness for a' = b, b' = -R a on J. *)

let GEOJ_ODE_2N = prove
 (`!(R:real->real^N^N) J t0 (a0:real^N) (b0:real^N).
        real_open J /\ is_realinterval J /\ t0 IN J /\
        (!i j. (\r. lift(R(drop r)$i$j)) continuous_on IMAGE lift J)
        ==> ?a b. a t0 = a0 /\ b t0 = b0 /\
                  (!t. t IN J
                       ==> ((\s. a(drop s)) has_vector_derivative b t) (at (lift t)) /\
                           ((\s. b(drop s)) has_vector_derivative --(R t ** a t))
                           (at (lift t))) /\
                  (!a' b'. a' t0 = a0 /\ b' t0 = b0 /\
                           (!t. t IN J
                                ==> ((\s. a'(drop s)) has_vector_derivative b' t)
                                    (at (lift t)) /\
                                    ((\s. b'(drop s)) has_vector_derivative
                                     --(R t ** a' t)) (at (lift t)))
                           ==> !t. t IN J ==> a' t = a t /\ b' t = b t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `BA = \t:real^1. matrix(\z:real^(N,N)finite_sum.
                    pastecart (sndcart z) (--((R:real->real^N^N)(drop t) ** fstcart z)))` THEN
  SUBGOAL_THEN
   `!t z. (BA:real^1->real^(N,N)finite_sum^(N,N)finite_sum) t ** z =
          pastecart (sndcart z) (--((R:real->real^N^N)(drop t) ** fstcart z))`
  (LABEL_TAC "BA") THENL
   [EXPAND_TAC "BA" THEN REWRITE_TAC[GEOJ_PAIR_MATRIX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. (\t. lift((BA:real^1->real^(N,N)finite_sum^(N,N)finite_sum) t$i$j))
          continuous_on IMAGE lift J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOJ_ENTRIES_CONTINUOUS THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    EXPAND_TAC "BA" THEN ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[o_DEF; CONTINUOUS_ON_VECTORIZE_COMPONENTWISE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE lift J) /\ is_interval(IMAGE lift J) /\ lift t0 IN IMAGE lift J`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OPEN; GSYM IS_REALINTERVAL_IS_INTERVAL] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`BA:real^1->real^(N,N)finite_sum^(N,N)finite_sum`;
                 `(\t. vec 0):real^1->real^(N,N)finite_sum`; `IMAGE lift (J:real->bool)`;
                 `lift t0`; `pastecart (a0:real^N) (b0:real^N)`] ODE_LINEAR_GLOBAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`BA:real^1->real^(N,N)finite_sum^(N,N)finite_sum`;
                 `(\t. vec 0):real^1->real^(N,N)finite_sum`; `IMAGE lift (J:real->bool)`]
    ODE_LINEAR_FIELD_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_RID] THEN
  ABBREV_TAC `ff = \z:real^(1,(N,N)finite_sum)finite_sum.
                 (BA:real^1->real^(N,N)finite_sum^(N,N)finite_sum) (fstcart z) ** sndcart z` THEN
  ABBREV_TAC `D = IMAGE lift (J:real->bool) PCROSS (:real^(N,N)finite_sum)` THEN
  ABBREV_TAC `z0 = pastecart (lift t0) (pastecart (a0:real^N) (b0:real^N))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  DISCH_THEN(LABEL_TAC "mx") THEN
  SUBGOAL_THEN `open(D:real^(1,(N,N)finite_sum)finite_sum->bool) /\ z0 IN D`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "z0"] THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. (ff:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) (pastecart t x) =
          pastecart (sndcart x) (--((R:real->real^N^N)(drop t) ** fstcart x))`
  (LABEL_TAC "ff") THENL
   [EXPAND_TAC "ff" THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ff:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `z0:real^(1,(N,N)finite_sum)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "mx" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `fstcart(z0:real^(1,(N,N)finite_sum)finite_sum) = lift t0 /\
                sndcart z0 = pastecart (a0:real^N) (b0:real^N)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "z0" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "sol")))))) THEN
  EXISTS_TAC `\t. fstcart(ode_flow
    (ff:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (lift t) z0):real^N` THEN
  EXISTS_TAC `\t. sndcart(ode_flow
    (ff:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum) D (lift t) z0):real^N` THEN
  ASM_REWRITE_TAC[LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `lift t IN IMAGE lift (J:real->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    USE_THEN "sol" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `lift t IN IMAGE lift (J:real->bool)`))) THEN
    USE_THEN "ff" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GEOJ_HAS_VD_SPLIT o CONJUNCT2) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a':real->real^N`; `b':real->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ff:real^(1,(N,N)finite_sum)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(1,(N,N)finite_sum)finite_sum->bool`;
                 `z0:real^(1,(N,N)finite_sum)finite_sum`; `IMAGE lift (J:real->bool)`;
                 `\s. pastecart ((a':real->real^N)(drop s)) ((b':real->real^N)(drop s))`]
    ODE_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `fstcart(z0:real^(1,(N,N)finite_sum)finite_sum) = lift t0 /\
                sndcart z0 = pastecart (a0:real^N) (b0:real^N)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "z0" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [REWRITE_TAC[ode_solution] THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "D" THEN ASM_SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV; FUN_IN_IMAGE];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    USE_THEN "ff" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[LIFT_DROP; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC GEOL_HAS_VECTOR_DERIVATIVE_PASTECART THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

(* ========================================================================= *)
(* Fields given by frame coordinates.  If a has derivative b                 *)
(* then Y = sum_j a_j E_j (E a parallel frame) is differentiable along      *)
(* gamma with covariant derivative sum_j b_j E_j.                           *)
(* ========================================================================= *)

(* The zero field. *)

let GEOJ_FIELD_DIFF_ZERO = prove
 (`!top atlas (gamma:real->A) J.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b)
        ==> mfd_field_diff atlas gamma (\s. vec 0:real^N) J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_field_diff] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`; `\s:real. vec 0:real^N`;
                 `\s:real. &0`; `t:real`] CMPG_FIELD_REP_SCALAR) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `\s:real^1. vec 0:real^N` THEN EXISTS_TAC `d:real` THEN
  ASM_REWRITE_TAC[DIFFERENTIABLE_CONST] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
  REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP]);;

let GEOJ_COVD_ZERO = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J
        ==> mfd_covd atlas g gamma (\s. vec 0) t = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `\s:real. vec 0:real^N`; `\s:real. &0`; `&0`; `t:real`]
    CMPG_COVD_SCALAR) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; HAS_REAL_DERIVATIVE_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GEOJ_FIELD_DIFF_ZERO THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

(* Finite sums of scalar multiples of fields. *)

let GEOJ_FIELD_DIFF_VSUM = prove
 (`!top atlas (gamma:real->A) J (f:num->real->real) (E:num->real->real^N) n.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        (!j. 1 <= j /\ j <= n
             ==> mfd_field_diff atlas gamma (E j) J /\
                 !t. t IN J ==> f j real_differentiable atreal t)
        ==> mfd_field_diff atlas gamma (\s. vsum(1..n) (\j. f j s % E j s)) J`,
  REPLICATE_TAC 6 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC GEOJ_FIELD_DIFF_ZERO THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  STRIP_TAC THEN POP_ASSUM(LABEL_TAC "Ej") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`;
                 `\s. vsum(1..n) (\j. (f:num->real->real) j s % (E:num->real->real^N) j s)`;
                 `\s. (f:num->real->real) (SUC n) s % (E:num->real->real^N) (SUC n) s`;
                 `&1`; `&1`] CMPG_FIELD_DIFF_LIN) THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "IH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN USE_THEN "Ej" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    USE_THEN "Ej" (MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= SUC n`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPG_FIELD_DIFF_SCALAR THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

let GEOJ_COVD_VSUM = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (f:num->real->real) f'
    (E:num->real->real^N) n t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        (!j. 1 <= j /\ j <= n
             ==> mfd_field_diff atlas gamma (E j) J /\
                 !s. s IN J ==> (f j has_real_derivative f' j s) (atreal s)) /\
        t IN J
        ==> mfd_covd atlas g gamma (\s. vsum(1..n) (\j. f j s % E j s)) t =
            vsum(1..n) (\j. f' j t % E j t + f j t % mfd_covd atlas g gamma (E j) t)`,
  REPLICATE_TAC 8 GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_EQ] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GEOJ_COVD_ZERO THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "IH") THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  STRIP_TAC THEN POP_ASSUM(fun th -> POP_ASSUM(LABEL_TAC "Ej") THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n
        ==> mfd_field_diff atlas (gamma:real->A) ((E:num->real->real^N) j) J /\
            !s. s IN J ==> ((f:num->real->real) j has_real_derivative f' j s) (atreal s)`
  (LABEL_TAC "Ejn") THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN USE_THEN "Ej" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Ej" (MP_TAC o SPEC `SUC n`) THEN
  REWRITE_TAC[LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fd")) THEN
  SUBGOAL_THEN
   `mfd_field_diff atlas (gamma:real->A)
      (\s. vsum(1..n) (\j. (f:num->real->real) j s % (E:num->real->real^N) j s)) J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOJ_FIELD_DIFF_VSUM THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    USE_THEN "Ejn" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_differentiable] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_field_diff atlas (gamma:real->A)
      (\s. (f:num->real->real) (SUC n) s % (E:num->real->real^N) (SUC n) s) J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_FIELD_DIFF_SCALAR THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[real_differentiable] THEN EXISTS_TAC `(f':num->real->real) (SUC n) s` THEN
    USE_THEN "fd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `\s. vsum(1..n) (\j. (f:num->real->real) j s % (E:num->real->real^N) j s)`;
                 `\s. (f:num->real->real) (SUC n) s % (E:num->real->real^N) (SUC n) s`;
                 `&1`; `&1`; `t:real`] CMPG_COVD_LIN) THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [USE_THEN "IH" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    MATCH_MP_TAC CMPG_COVD_SCALAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN USE_THEN "fd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Components of a vector derivative are real derivatives. *)

let GEOJ_COMPONENT_REAL_DERIV = prove
 (`!(a:real->real^N) a' t j.
        1 <= j /\ j <= dimindex(:N) /\
        ((\s. a(drop s)) has_vector_derivative a') (at (lift t))
        ==> ((\s. a s$j) has_real_derivative a'$j) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT]) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]);;

(* The field with frame coordinates a. *)

let GEOJ_FRAME_FIELD = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_curve_on (top,atlas) gamma J /\ cmp_pframe atlas g gamma J E /\
        (!t. t IN J ==> ((\s. a(drop s)) has_vector_derivative b t) (at (lift t)))
        ==> mfd_field_diff atlas gamma (\s. cmp_fmat E s ** a s) J /\
            !t. t IN J
                ==> mfd_covd atlas g gamma (\s. cmp_fmat E s ** a s) t =
                    cmp_fmat E t ** b t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_curve_on] THEN STRIP_TAC THEN
  REWRITE_TAC[CMPF_FMAT_MUL] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) J
                         ((E:num->real->real^N) j)`
  (LABEL_TAC "par") THENL
   [UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) J
                            (E:num->real->real^N)` THEN
    SIMP_TAC[cmp_pframe];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j t. 1 <= j /\ j <= dimindex(:N) /\ t IN J
          ==> ((\s. (a:real->real^N) s$j) has_real_derivative (b:real->real^N) t$j)
              (atreal t)`
  (LABEL_TAC "rd") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOJ_COMPONENT_REAL_DERIV THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `J:real->bool`; `\j s. (a:real->real^N) s$j`;
                   `E:num->real->real^N`; `dimindex(:N)`] GEOJ_FIELD_DIFF_VSUM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "par" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[mfd_parallel]];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[real_differentiable] THEN
      EXISTS_TAC `(b:real->real^N) t$j` THEN USE_THEN "rd" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `\j s. (a:real->real^N) s$j`; `\j s. (b:real->real^N) s$j`;
                 `E:num->real->real^N`; `dimindex(:N)`; `t:real`] GEOJ_COVD_VSUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "par" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[mfd_parallel]];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "rd" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  USE_THEN "par" (MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[mfd_parallel]] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID]);;

(* ========================================================================= *)
(* Existence and uniqueness of Jacobi fields with given initial              *)
(* value and initial covariant derivative (MFD_JACOBI_EXISTS_UNIQUE), from    *)
(* the frame-coordinate system a' = b, b' = -R a (GEOJ_ODE_2N).              *)
(* ========================================================================= *)

(* Frame coordinates of the field F a are a. *)

let GEOJ_FCOORD_FMAT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) a t.
        cmp_pframe atlas g gamma J E /\ t IN J
        ==> cmp_fcoord g gamma E (\s. cmp_fmat E s ** a s) t = a t`,
  REWRITE_TAC[cmp_pframe; cmp_fcoord] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

(* A vector is recovered from its frame coordinates. *)

let GEOJ_FRAME_INVERT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) u t.
        cmp_pframe atlas g gamma J E /\ t IN J
        ==> cmp_fmat E t ** transp(cmp_fmat E t) ** g(gamma t) ** u = u`,
  REWRITE_TAC[cmp_pframe] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CMPF_FRAME_RIGHT_INVERSE) THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

(* The curvature term of the field F a is F (R a). *)

let GEOJ_RIEMANN_FMAT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:num->real->real^N) a t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        cmp_pframe atlas g gamma J E /\ t IN J /\ gamma t IN topspace top
        ==> mfd_riemann atlas g (gamma t) (cmp_fmat E t ** a t)
                        (mfd_vel atlas gamma t) (mfd_vel atlas gamma t) =
            cmp_fmat E t ** (cmp_rmat atlas g gamma E t ** a t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                 `\s. mfd_riemann atlas (g:A->real^N^N) ((gamma:real->A) s)
                        (cmp_fmat (E:num->real->real^N) s ** (a:real->real^N) s)
                        (mfd_vel atlas gamma s) (mfd_vel atlas gamma s)`;
                 `t:real`] CMPF_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`;
                 `\s. cmp_fmat (E:num->real->real^N) s ** (a:real->real^N) s`;
                 `t:real`] CMPF_RIEMANN_FCOORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC GEOJ_FCOORD_FMAT THEN EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
  EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[]);;

(* Existence and uniqueness of Jacobi fields. *)

let MFD_JACOBI_EXISTS_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t0 u w.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ t0 IN J
        ==> ?Y. mfd_jacobi atlas g gamma J Y /\ Y t0 = u /\
                mfd_covd atlas g gamma Y t0 = w /\
                !Y'. mfd_jacobi atlas g gamma J Y' /\ Y' t0 = u /\
                     mfd_covd atlas g gamma Y' t0 = w
                     ==> !t. t IN J ==> Y' t = Y t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cmp_curve_on (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPF_GEODESIC_CURVE_ON THEN EXISTS_TAC `g:A->real^N^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `t0:real`]
    GEOJ_PFRAME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:num->real->real^N`) THEN
  MP_TAC(ISPECL [`cmp_rmat atlas (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)`;
                 `J:real->bool`; `t0:real`;
                 `transp(cmp_fmat (E:num->real->real^N) t0) **
                  (g:A->real^N^N)((gamma:real->A) t0) ** (u:real^N)`;
                 `transp(cmp_fmat (E:num->real->real^N) t0) **
                  (g:A->real^N^N)((gamma:real->A) t0) ** (w:real^N)`]
    GEOJ_ODE_2N) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOJ_RMAT_CONTINUOUS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real->real^N` (X_CHOOSE_THEN `b:real->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ab") MP_TAC))))) THEN
  (* the fields F a and F b *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `a:real->real^N`; `b:real->real^N`]
    GEOJ_FRAME_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "ab" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real) IN J`)]);
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cY")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `E:num->real->real^N`; `b:real->real^N`;
                 `\t. --(cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                           (E:num->real->real^N) t ** (a:real->real^N) t)`]
    GEOJ_FRAME_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "ab" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real) IN J`)]);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cZ")) THEN
  DISCH_THEN(LABEL_TAC "uniq") THEN
  EXISTS_TAC `\s. cmp_fmat (E:num->real->real^N) s ** (a:real->real^N) s` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the Jacobi equation *)
    REWRITE_TAC[mfd_jacobi] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN
      EXISTS_TAC `\s. cmp_fmat (E:num->real->real^N) s ** (b:real->real^N) s` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "cY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
        (mfd_covd atlas g gamma
           (\s. cmp_fmat (E:num->real->real^N) s ** (a:real->real^N) s)) t =
      mfd_covd atlas g gamma (\s. cmp_fmat E s ** (b:real->real^N) s) t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CMPG_COVD_LOCAL THEN
      UNDISCH_TAC `real_open J` THEN REWRITE_TAC[real_open] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "cY" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "cZ" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real) IN J`)]) THEN
    SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `E:num->real->real^N`; `a:real->real^N`; `t:real`]
      GEOJ_RIEMANN_FMAT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; VECTOR_ADD_LINV];
    (* the initial value *)
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                   `u:real^N`; `t0:real`] GEOJ_FRAME_INVERT) THEN
    ASM_REWRITE_TAC[];
    (* the initial covariant derivative *)
    USE_THEN "cY" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t0:real) IN J`)]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                   `w:real^N`; `t0:real`] GEOJ_FRAME_INVERT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* uniqueness *)
  X_GEN_TAC `Y':real->real^N` THEN STRIP_TAC THEN
  USE_THEN "uniq" (MP_TAC o SPECL
   [`cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N) Y'`;
    `cmp_fcoord (g:A->real^N^N) (gamma:real->A) (E:num->real->real^N)
       (mfd_covd atlas g gamma Y')`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[cmp_fcoord]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[cmp_fcoord]; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC CMPF_JACOBI_FCOORD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(LABEL_TAC "eq")] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `gamma:real->A`; `J:real->bool`; `E:num->real->real^N`;
                 `Y':real->real^N`; `t:real`] CMPF_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  USE_THEN "eq" (MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

