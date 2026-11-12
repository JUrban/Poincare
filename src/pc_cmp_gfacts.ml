(* ========================================================================= *)
(* Unit pc_cmp_gfacts (comparison-geometry layer CMP): facts of the          *)
(* geodesics interface pc_geo_iface.ml, with the names and statements used   *)
(* there: MFD_PARALLEL_INNER (inner products of parallel fields are          *)
(* constant), MFD_JACOBI_TANGENTIAL ((a + b t) gamma' is a Jacobi field) and *)
(* MFD_JACOBI_LINEAR (Jacobi fields form a vector space), with the locality, *)
(* Leibniz and linearity rules for the covariant derivative along a curve.   *)
(* Needs only pc_geo_covd.ml (not pc_geo_iface.ml).                          *)
(* ========================================================================= *)

needs "src/pc_geo_covd.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Inner products of parallel fields are constant.                           *)
(* ========================================================================= *)

let MFD_PARALLEL_INNER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J Y1 Y2 s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\ is_realinterval J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_parallel atlas g gamma J Y1 /\ mfd_parallel atlas g gamma J Y2 /\
        s IN J /\ t IN J
        ==> Y1 s dot (g(gamma s) ** Y2 s) = Y1 t dot (g(gamma t) ** Y2 t)`,
  REWRITE_TAC[mfd_parallel] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (Y1:real->real^N) r dot ((g:A->real^N^N)((gamma:real->A) r) ** Y2 r)`;
                 `J:real->bool`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `Y1:real->real^N`; `Y2:real->real^N`; `x:real`] MFD_COVD_METRIC) THEN
    ASM_SIMP_TAC[DOT_LZERO; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_ADD_RID;
                 LIFT_NUM];
    DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN RULE_ASSUM_TAC BETA_RULE THEN
    ASM_SIMP_TAC[]]);;

(* ========================================================================= *)
(* Locality of the covariant derivative and of field differentiability; the  *)
(* Leibniz rule D(f Y) = f' Y + f DY.                                        *)
(* ========================================================================= *)

let CMPG_VECTOR_DERIVATIVE_LOCAL = prove
 (`!(f:real^1->real^N) h x d.
        &0 < d /\ (!y. dist(y,x) < d ==> f y = h y)
        ==> vector_derivative f (at x) = vector_derivative h (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_derivative] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THENL
   [EXISTS_TAC `f:real^1->real^N`; EXISTS_TAC `h:real^1->real^N`] THEN
  EXISTS_TAC `d:real` THEN ASM_SIMP_TAC[]);;

(* The covariant derivative at t depends only on the field near t. *)

let CMPG_COVD_LOCAL = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) (Y1:real->real^N) Y2 t d.
        &0 < d /\ (!s. abs(s - t) < d ==> Y1 s = Y2 s)
        ==> mfd_covd atlas g gamma Y1 t = mfd_covd atlas g gamma Y2 t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_covd] THEN
  SUBGOAL_THEN `(Y1:real->real^N) t = Y2 t` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CMPG_VECTOR_DERIVATIVE_LOCAL THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[mfd_field_rep] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `abs(drop y - t) < d`)]));;

(* Field differentiability on an open interval depends only on the values  *)
(* there.                                                                    *)

let CMPG_FIELD_DIFF_LOCAL = prove
 (`!atlas (gamma:real->A) (Y1:real->real^N) Y2 J.
        real_open J /\ (!s. s IN J ==> Y1 s = Y2 s) /\ mfd_field_diff atlas gamma Y1 J
        ==> mfd_field_diff atlas gamma Y2 J`,
  REWRITE_TAC[mfd_field_diff] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[differentiable] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `D:real^1->real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. mfd_field_rep atlas (gamma:real->A) (Y1:real->real^N)
                    (chart_at atlas (gamma t)) (drop s)` THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
  DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
  SUBGOAL_THEN `drop y IN J` (fun th -> ASM_SIMP_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Near t, the chart jacobians from the charts at gamma s to the chart at  *)
(* gamma t are linear.                                                       *)

let CMPG_CHART_JAC_NEAR = prove
 (`!top atlas (gamma:real->A) J t.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J
        ==> ?d. &0 < d /\
                !s. abs(s - t) < d
                    ==> linear(chart_jac (chart_at atlas (gamma s))
                                         (chart_at atlas (gamma t)) (gamma s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal J,top) (gamma:real->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOC_C1_CONTINUOUS THEN EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN J ==> (gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map]) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `t:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) s`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `(gamma:real->A) s`] CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER]);;

(* Near t, the representative of f Y in the chart at gamma t is f times the *)
(* representative of Y.                                                      *)

let CMPG_FIELD_REP_SCALAR = prove
 (`!top atlas (gamma:real->A) J (Y:real->real^N) (f:real->real) t.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J
        ==> ?d. &0 < d /\
                !s. abs(s - t) < d
                    ==> mfd_field_rep atlas gamma (\s. f s % Y s)
                          (chart_at atlas (gamma t)) s =
                        f s % mfd_field_rep atlas gamma Y (chart_at atlas (gamma t)) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`; `t:real`] CMPG_CHART_JAC_NEAR) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_field_rep] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL
    (MATCH_MP th (ASSUME `abs(s - t) < d`))]));;

(* The same for linear combinations p Y1 + q Y2. *)

let CMPG_FIELD_REP_LIN = prove
 (`!top atlas (gamma:real->A) J (Y1:real->real^N) Y2 p q t.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J
        ==> ?d. &0 < d /\
                !s. abs(s - t) < d
                    ==> mfd_field_rep atlas gamma (\s. p % Y1 s + q % Y2 s)
                          (chart_at atlas (gamma t)) s =
                        p % mfd_field_rep atlas gamma Y1 (chart_at atlas (gamma t)) s +
                        q % mfd_field_rep atlas gamma Y2 (chart_at atlas (gamma t)) s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`; `t:real`] CMPG_CHART_JAC_NEAR) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_field_rep] THEN
  FIRST_X_ASSUM(fun th ->
    let lth = MATCH_MP th (ASSUME `abs(s - t) < d`) in
    REWRITE_TAC[MATCH_MP LINEAR_ADD lth; MATCH_MP LINEAR_CMUL lth]));;

(* A C1 curve on J takes values in the space. *)

let CMPG_C1_IN_TOPSPACE = prove
 (`!top atlas (gamma:real->A) J t.
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b) /\
        t IN J
        ==> gamma t IN topspace top`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`] GEOC_C1_CONTINUOUS) THEN
  ASM_REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[]);;

(* The chart representative of f Y has derivative f Y' + f' Y at t.        *)

let CMPG_FIELD_REP_SCALAR_DERIV = prove
 (`!top atlas (gamma:real->A) J (Y:real->real^N) (f:real->real) f' t.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J /\
        (\s. mfd_field_rep atlas gamma Y (chart_at atlas (gamma t)) (drop s))
        differentiable at (lift t) /\
        (f has_real_derivative f') (atreal t)
        ==> ((\s. mfd_field_rep atlas gamma (\s. f s % Y s)
                    (chart_at atlas (gamma t)) (drop s)) has_vector_derivative
             (f t % vector_derivative
                      (\s. mfd_field_rep atlas gamma Y (chart_at atlas (gamma t))
                                         (drop s))
                      (at (lift t)) + f' % Y t)) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`; `Y:real->real^N`; `f:real->real`;
                 `t:real`] CMPG_FIELD_REP_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_C1_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
                  (chart_at atlas (gamma t)) t = Y t`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_field_rep] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))`;
                   `(gamma:real->A) t`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. (f:real->real)(drop s) %
                  mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
                    (chart_at atlas (gamma t)) (drop s)` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x y:real^N. drop x % y`; `lift o (f:real->real) o drop`;
    `\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
           (chart_at atlas (gamma t)) (drop s)`;
    `lift f'`;
    `vector_derivative
       (\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
              (chart_at atlas (gamma t)) (drop s)) (at (lift t))`;
    `lift t`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL; GSYM HAS_REAL_VECTOR_DERIVATIVE_AT;
                  GSYM VECTOR_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN ASM_REWRITE_TAC[]);;

(* Leibniz rule for field differentiability. *)

let CMPG_FIELD_DIFF_SCALAR = prove
 (`!top atlas (gamma:real->A) J (Y:real->real^N) (f:real->real).
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_field_diff atlas gamma Y J /\
        (!t. t IN J ==> f real_differentiable atreal t)
        ==> mfd_field_diff atlas gamma (\s. f s % Y s) J`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [mfd_field_diff] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[real_differentiable] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real`) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
  EXISTS_TAC
   `(f:real->real) t %
    vector_derivative
      (\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
             (chart_at atlas (gamma t)) (drop s)) (at (lift t)) + f' % Y t` THEN
  MATCH_MP_TAC CMPG_FIELD_REP_SCALAR_DERIV THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_field_diff]);;

(* The local metric in the preferred chart at a point. *)

let CMPG_LOCAL_METRIC = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> metric_field (IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x)))
                         (metric_local atlas (chart_at atlas x) g) /\
            SND(chart_at atlas x) x IN
            IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* The Christoffel form of the preferred chart is bilinear. *)

let CMPG_CHRISTOFFEL_AT = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> bilinear (christoffel (metric_local atlas (chart_at atlas x) g)
                                  (SND(chart_at atlas x) x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN
  EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                    (FST(chart_at atlas x))` THEN
  MATCH_MP_TAC CMPG_LOCAL_METRIC THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

(* Leibniz rule for the covariant derivative along gamma. *)

let CMPG_COVD_SCALAR = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) (f:real->real) f' t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J /\ mfd_field_diff atlas gamma Y J /\
        (f has_real_derivative f') (atreal t)
        ==> mfd_covd atlas g gamma (\s. f s % Y s) t =
            f' % Y t + f t % mfd_covd atlas g gamma Y t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`; `Y:real->real^N`; `f:real->real`;
                 `f':real`; `t:real`] CMPG_FIELD_REP_SCALAR_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_field_diff]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[mfd_covd; MATCH_MP VECTOR_DERIVATIVE_AT th]) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_C1_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`] CMPG_CHRISTOFFEL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[BILINEAR_RMUL] THEN VECTOR_ARITH_TAC);;

(* The chart representative of p Y1 + q Y2 has derivative p Y1' + q Y2'.   *)

let CMPG_FIELD_REP_LIN_DERIV = prove
 (`!top atlas (gamma:real->A) J (Y1:real->real^N) Y2 p q t.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J /\
        (\s. mfd_field_rep atlas gamma Y1 (chart_at atlas (gamma t)) (drop s))
        differentiable at (lift t) /\
        (\s. mfd_field_rep atlas gamma Y2 (chart_at atlas (gamma t)) (drop s))
        differentiable at (lift t)
        ==> ((\s. mfd_field_rep atlas gamma (\s. p % Y1 s + q % Y2 s)
                    (chart_at atlas (gamma t)) (drop s)) has_vector_derivative
             (p % vector_derivative
                    (\s. mfd_field_rep atlas gamma Y1 (chart_at atlas (gamma t))
                                       (drop s)) (at (lift t)) +
              q % vector_derivative
                    (\s. mfd_field_rep atlas gamma Y2 (chart_at atlas (gamma t))
                                       (drop s)) (at (lift t)))) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`; `Y1:real->real^N`; `Y2:real->real^N`;
                 `p:real`; `q:real`; `t:real`] CMPG_FIELD_REP_LIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. p % mfd_field_rep atlas (gamma:real->A) (Y1:real->real^N)
                       (chart_at atlas (gamma t)) (drop s) +
                  q % mfd_field_rep atlas gamma (Y2:real->real^N)
                       (chart_at atlas (gamma t)) (drop s)` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
    ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS]]);;

(* Linear combinations of differentiable fields are differentiable. *)

let CMPG_FIELD_DIFF_LIN = prove
 (`!top atlas (gamma:real->A) J (Y1:real->real^N) Y2 p q.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_field_diff atlas gamma Y1 J /\ mfd_field_diff atlas gamma Y2 J
        ==> mfd_field_diff atlas gamma (\s. p % Y1 s + q % Y2 s) J`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [mfd_field_diff] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
  EXISTS_TAC
   `p % vector_derivative
          (\s. mfd_field_rep atlas (gamma:real->A) (Y1:real->real^N)
                 (chart_at atlas (gamma t)) (drop s)) (at (lift t)) +
    q % vector_derivative
          (\s. mfd_field_rep atlas gamma (Y2:real->real^N)
                 (chart_at atlas (gamma t)) (drop s)) (at (lift t))` THEN
  MATCH_MP_TAC CMPG_FIELD_REP_LIN_DERIV THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_field_diff]);;

(* The covariant derivative along gamma is linear. *)

let CMPG_COVD_LIN = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y1:real->real^N) Y2 p q t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t IN J /\ mfd_field_diff atlas gamma Y1 J /\ mfd_field_diff atlas gamma Y2 J
        ==> mfd_covd atlas g gamma (\s. p % Y1 s + q % Y2 s) t =
            p % mfd_covd atlas g gamma Y1 t + q % mfd_covd atlas g gamma Y2 t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `J:real->bool`; `Y1:real->real^N`; `Y2:real->real^N`;
                 `p:real`; `q:real`; `t:real`] CMPG_FIELD_REP_LIN_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[mfd_field_diff]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[mfd_covd; MATCH_MP VECTOR_DERIVATIVE_AT th]) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_C1_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`] CMPG_CHRISTOFFEL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BILINEAR_RMUL; BILINEAR_RADD] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Tangential Jacobi fields (MFD_JACOBI_TANGENTIAL).                         *)
(* ========================================================================= *)

(* R(c w, w) u = 0 at every point of the manifold. *)

let CMPG_RIEMANN_TANGENT = prove
 (`!top atlas (g:A->real^N^N) x c w u.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> mfd_riemann atlas g x (c % w) w u = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPG_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_riemann] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
    LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`w:real^N`; `u:real^N`] o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_CMUL) THEN
  DISCH_THEN(MP_TAC o SPECL [`c:real`; `w:real^N`]) THEN REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `lriemann (metric_local atlas (chart_at atlas (x:A)) (g:A->real^N^N))
             (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) x) x) w w u = vec 0`
   (fun th -> REWRITE_TAC[th; VECTOR_MUL_RZERO]) THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                 `w:real^N`; `w:real^N`; `u:real^N`] LRIEMANN_ANTISYM) THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* The curvature is linear in its first argument. *)

let CMPG_RIEMANN_LIN = prove
 (`!top atlas (g:A->real^N^N) x p q u1 u2 v w.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> mfd_riemann atlas g x (p % u1 + q % u2) v w =
            p % mfd_riemann atlas g x u1 v w + q % mfd_riemann atlas g x u2 v w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPG_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[mfd_riemann] THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at atlas x) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
    LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `w:real^N`] o CONJUNCT1) THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP LINEAR_ADD th) THEN
                       MP_TAC(MATCH_MP LINEAR_CMUL th)) THEN
  REWRITE_TAC[] THEN SIMP_TAC[]);;

(* A geodesic is a C1 curve on every compact subinterval. *)

let CMPG_GEODESIC_C1 = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J
        ==> !a b. a <= b /\ real_interval[a,b] SUBSET J
                  ==> mfd_c1_curve (top,atlas) gamma a b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `a:real`; `b:real`]
    MFD_GEODESIC_C1_CURVE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* MFD_JACOBI_TANGENTIAL, as stated in pc_geo_iface.ml.                      *)

let MFD_JACOBI_TANGENTIAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J
        ==> mfd_jacobi atlas g gamma J (\t. (a + b * t) % mfd_vel atlas gamma t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOL_GEODESIC_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    MFD_GEODESIC_VEL_PARALLEL) THEN
  ASM_REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  (* affine multiples of the velocity are differentiable fields *)
  SUBGOAL_THEN
   `!p q. mfd_field_diff atlas (gamma:real->A)
            (\t. (p + q * t) % mfd_vel (atlas:((A->bool)#(A->real^N))->bool) gamma t) J`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `J:real->bool`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)`;
                   `\t:real. p + q * t`] CMPG_FIELD_DIFF_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `q:real` THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the first covariant derivative is b times the velocity *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
              (\t. (a + b * t) % mfd_vel atlas gamma t) t =
            b % mfd_vel atlas gamma t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
      `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)`;
      `\t:real. a + b * t`; `b:real`; `t:real`] CMPG_COVD_SCALAR)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID]];
    ALL_TAC] THEN
  (* the second covariant derivative vanishes *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
              (mfd_covd atlas g gamma (\t. (a + b * t) % mfd_vel atlas gamma t)) t =
            vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
        (mfd_covd atlas g gamma (\t. (a + b * t) % mfd_vel atlas gamma t)) t =
      mfd_covd atlas g gamma (\s. b % mfd_vel atlas gamma s) t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(s:real) IN J` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
      `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)`;
      `\s:real. (b:real)`; `&0`; `t:real`] CMPG_COVD_SCALAR)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID]];
    ALL_TAC] THEN
  (* the first covariant derivative is a differentiable field *)
  SUBGOAL_THEN
   `mfd_field_diff atlas (gamma:real->A)
      (mfd_covd atlas (g:A->real^N^N) gamma (\t. (a + b * t) % mfd_vel atlas gamma t)) J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN
    EXISTS_TAC `\t. (b + &0 * t) % mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                                           (gamma:real->A) t` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_jacobi] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[VECTOR_ADD_LID] THEN
  MATCH_MP_TAC CMPG_RIEMANN_TANGENT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]);;

(* MFD_JACOBI_LINEAR, as stated in pc_geo_iface.ml. *)

let MFD_JACOBI_LINEAR = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J Y1 Y2 a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\
        mfd_jacobi atlas g gamma J Y1 /\ mfd_jacobi atlas g gamma J Y2
        ==> mfd_jacobi atlas g gamma J (\t. a % Y1 t + b % Y2 t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_jacobi] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOL_GEODESIC_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the first covariant derivative *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
              (\t. a % (Y1:real->real^N) t + b % Y2 t) t =
            a % mfd_covd atlas g gamma Y1 t + b % mfd_covd atlas g gamma Y2 t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPG_COVD_LIN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_field_diff atlas (gamma:real->A) (\t. a % (Y1:real->real^N) t + b % Y2 t) J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_FIELD_DIFF_LIN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_field_diff atlas (gamma:real->A)
      (mfd_covd atlas (g:A->real^N^N) gamma (\t. a % (Y1:real->real^N) t + b % Y2 t)) J`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN
    EXISTS_TAC `\t. a % mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
                                 (Y1:real->real^N) t +
                    b % mfd_covd atlas g gamma Y2 t` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CMPG_FIELD_DIFF_LIN THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  (* the second covariant derivative *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
              (mfd_covd atlas g gamma (\t. a % (Y1:real->real^N) t + b % Y2 t)) t =
            a % mfd_covd atlas g gamma (mfd_covd atlas g gamma Y1) t +
            b % mfd_covd atlas g gamma (mfd_covd atlas g gamma Y2) t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
        (mfd_covd atlas g gamma (\t. a % (Y1:real->real^N) t + b % Y2 t)) t =
      mfd_covd atlas g gamma
        (\s. a % mfd_covd atlas g gamma Y1 s + b % mfd_covd atlas g gamma Y2 s) t`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(s:real) IN J` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC CMPG_COVD_LIN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`; `a:real`; `b:real`;
                 `(Y1:real->real^N) t`; `(Y2:real->real^N) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`;
                 `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`]
    CMPG_RIEMANN_LIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a % x + b % y) + (a % u + b % v):real^N = a % (x + u) + b % (y + v)`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID]);;

