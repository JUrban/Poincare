(* ========================================================================= *)
(* pc_geo_covd: the covariant derivative along curves.  Chart form          *)
(* (MFD_COVD_CHART), metric compatibility (MFD_COVD_METRIC), geodesics have *)
(* parallel velocity (MFD_GEODESIC_VEL_PARALLEL), and the symmetry lemma    *)
(* D_s d_t f = D_t d_s f for two-parameter maps (MFD_COVD_SYMMETRY).        *)
(* These are names of the geodesics API pc_geo_iface.                        *)
(*                                                                           *)
(* Curves that are C^1 on compact subintervals of an open                    *)
(* interval.                                                                 *)
(* ========================================================================= *)

needs "src/pc_geo_flow.ml";;

prioritize_real();;
type_invention_error := true;;

(* Chart velocities at interior times. *)

let GEOC_C1_HAS_VD_AT = prove
 (`!top atlas (gamma:real->A) J (c:(A->bool)#(A->real^N)) t.
        smooth_manifold_atlas top atlas /\ real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        c IN atlas /\ t IN J /\ gamma t IN FST c
        ==> ((\s. SND c (gamma(drop s))) has_vector_derivative
             vector_derivative (\s. SND c (gamma(drop s))) (at (lift t)))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t - e / &2`; `t + e / &2`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `t - e / &2`; `t + e / &2`;
                 `c:(A->bool)#(A->real^N)`; `t:real`] GRGD_C1_CHART_HAS_VD) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `interval(lift(t - e / &2),lift(t + e / &2))` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET)) THEN
  REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; has_vector_derivative] THEN
  SUBGOAL_THEN `lift t IN interval(lift(t - e / &2),lift(t + e / &2))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN; OPEN_INTERVAL] THEN
  MESON_TAC[differentiable]);;

(* Such curves are continuous on J. *)

let GEOC_C1_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) J.
        real_open J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b)
        ==> continuous_map (subtopology euclideanreal J,top) gamma`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `real_interval[t - e / &2,t + e / &2] SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `real_interval(t - e / &2,t + e / &2)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `real_interval(t - e / &2,t + e / &2)` THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL] THEN
    MP_TAC(ISPECL [`t - e / &2`; `t + e / &2`] REAL_INTERVAL_OPEN_SUBSET_CLOSED) THEN
    ASM SET_TAC[];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `J INTER real_interval(t - e / &2,t + e / &2) =
                  real_interval(t - e / &2,t + e / &2)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`t - e / &2`; `t + e / &2`] REAL_INTERVAL_OPEN_SUBSET_CLOSED) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `real_interval[t - e / &2,t + e / &2]` THEN
    REWRITE_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`t - e / &2`; `t + e / &2`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[mfd_c1_curve]]]);;

(* ========================================================================= *)
(* The chart form of the covariant derivative (MFD_COVD_CHART).              *)
(* ========================================================================= *)

(* Naturality of the Christoffel symbols under a chart transition. *)

let GEOC_CHRISTOFFEL_TRANS = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) c' x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ c' IN atlas /\ x IN FST c INTER FST c'
        ==> frechet_derivative (chart_trans c c') (at (SND c x))
              (christoffel (metric_local atlas c g) (SND c x) u v) =
            christoffel (metric_local atlas c' g) (SND c' x)
              (frechet_derivative (chart_trans c c') (at (SND c x)) u)
              (frechet_derivative (chart_trans c c') (at (SND c x)) v) +
            dd2 (chart_trans c c') (SND c x) u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tau = chart_trans (c:(A->bool)#(A->real^N)) c'` THEN
  ABBREV_TAC `W = IMAGE (SND (c:(A->bool)#(A->real^N)))
                        (FST c INTER FST (c':(A->bool)#(A->real^N)))` THEN
  ABBREV_TAC `y = SND (c:(A->bool)#(A->real^N)) (x:A)` THEN
  SUBGOAL_THEN `(y:real^N) IN W` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["y"; "W"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                (y:real^N) u v =
    christoffel (mpullback (tau:real^N->real^N) (metric_local atlas c' g)) y u v`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    EXPAND_TAC "tau" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`;
                   `SND(c':(A->bool)#(A->real^N))`; `g:A->real^N^N`; `z:A`]
      METRIC_LOCAL_TRANS) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND (c':(A->bool)#(A->real^N)) (x:A) = tau(y:real^N)`
  SUBST1_TAC THENL
   [EXPAND_TAC "y" THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x:A. x IN FST (c:(A->bool)#(A->real^N))
             ==> (tau:real^N->real^N) (SND c x) = SND (c':(A->bool)#(A->real^N)) x`)
      (concl th))) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LCHRISTOFFEL_PULLBACK THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (SND (c':(A->bool)#(A->real^N)))
           (FST (c:(A->bool)#(A->real^N)) INTER FST (c':(A->bool)#(A->real^N)))`;
    `W:real^N->bool`; `chart_trans (c':(A->bool)#(A->real^N)) c`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`] RIEMANNIAN_METRIC_OVERLAP) THEN
  ASM_REWRITE_TAC[PAIR] THEN REWRITE_TAC[INTER_COMM]);;

(* The covariant derivative read in any chart. *)

let MFD_COVD_CHART = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J Y c t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\ is_realinterval J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_field_diff atlas gamma Y J /\
        c IN atlas /\ t IN J /\ gamma t IN FST c
        ==> mfd_field_rep atlas gamma (mfd_covd atlas g gamma Y) c t =
            vector_derivative (\s. mfd_field_rep atlas gamma Y c (drop s)) (at (lift t)) +
            christoffel (metric_local atlas c g) (SND c (gamma t))
              (vector_derivative (\s. SND c (gamma(drop s))) (at (lift t)))
              (mfd_field_rep atlas gamma Y c t)`,
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
   [ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  (* the velocity in the preferred chart *)
  SUBGOAL_THEN
   `((\s. SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) has_vector_derivative
     mfd_vel atlas gamma t) (at (lift t))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_vel] THEN MATCH_MP_TAC GEOC_C1_HAS_VD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the field in the preferred chart is differentiable at t *)
  SUBGOAL_THEN
   `((\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c0 (drop s))
     has_vector_derivative
     vector_derivative (\s. mfd_field_rep atlas gamma Y c0 (drop s)) (at (lift t)))
    (at (lift t))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    UNDISCH_TAC `mfd_field_diff atlas (gamma:real->A) (Y:real->real^N) J` THEN
    REWRITE_TAC[mfd_field_diff] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tau = chart_trans (c0:(A->bool)#(A->real^N)) c` THEN
  ABBREV_TAC `W = IMAGE (SND (c0:(A->bool)#(A->real^N)))
                        (FST c0 INTER FST (c:(A->bool)#(A->real^N)))` THEN
  ABBREV_TAC `v0 = mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t` THEN
  ABBREV_TAC `Y0' = vector_derivative
                      (\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c0 (drop s))
                      (at (lift t))` THEN
  (* the field in c is the chart transition applied to the field in c0 *)
  SUBGOAL_THEN
   `!s. abs(s - t) < d
        ==> mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c s =
            frechet_derivative (tau:real^N->real^N)
              (at (SND (c0:(A->bool)#(A->real^N)) (gamma s)))
              (mfd_field_rep atlas gamma Y c0 s)`
  (LABEL_TAC "rep") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> can (term_match []
      `!s. abs(s - t) < d ==> s IN J /\ (gamma:real->A) s IN W`) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) s`] CHART_AT) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_field_rep] THEN EXPAND_TAC "tau" THEN
    REWRITE_TAC[GSYM chart_jac] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `(gamma:real->A) s`] CHART_JAC_CHAIN) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  (* its derivative *)
  SUBGOAL_THEN
   `((\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c (drop s))
     has_vector_derivative
     (dd2 (tau:real^N->real^N) (SND (c0:(A->bool)#(A->real^N)) (gamma t)) v0
          (mfd_field_rep atlas gamma Y c0 t) +
      frechet_derivative tau (at (SND c0 (gamma t))) Y0')) (at (lift t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC
     `\r. frechet_derivative (tau:real^N->real^N)
            (at (SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))))
            (mfd_field_rep atlas gamma (Y:real->real^N) c0 (drop r))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "rep" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[dd2] THEN
    MP_TAC(ISPECL
     [`W:real^N->bool`; `tau:real^N->real^N`;
      `\r. SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))`;
      `\r. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c0 (drop r)`;
      `v0:real^N`; `Y0':real^N`; `lift t`] GEOL_FRECHET_ALONG) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  (* the velocity in c *)
  SUBGOAL_THEN
   `((\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) has_vector_derivative
     chart_jac (c0:(A->bool)#(A->real^N)) c (gamma t) v0) (at (lift t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_CHART_CHANGE_VEL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `J:real->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  (* the field at t *)
  SUBGOAL_THEN
   `mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c0 t = Y t`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_field_rep] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `(gamma:real->A) t`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c t =
    frechet_derivative (tau:real^N->real^N)
      (at (SND (c0:(A->bool)#(A->real^N)) (gamma t))) (Y t)`
  SUBST1_TAC THENL
   [USE_THEN "rep" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c (drop s)) (at (lift t)) =
    dd2 (tau:real^N->real^N) (SND (c0:(A->bool)#(A->real^N)) (gamma t)) v0
        (mfd_field_rep atlas gamma Y c0 t) +
    frechet_derivative tau (at (SND c0 (gamma t))) Y0'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative (\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))
      (at (lift t)) =
    chart_jac (c0:(A->bool)#(A->real^N)) c (gamma t) v0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the left hand side *)
  GEN_REWRITE_TAC LAND_CONV [mfd_field_rep] THEN REWRITE_TAC[mfd_covd] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(frechet_derivative (tau:real^N->real^N)
                         (at (SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A) t))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "W" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  REWRITE_TAC[chart_jac] THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LINEAR_ADD] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c0:(A->bool)#(A->real^N)`; `c:(A->bool)#(A->real^N)`;
                 `(gamma:real->A) t`; `v0:real^N`; `(Y:real->real^N) t`]
    GEOC_CHRISTOFFEL_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Metric compatibility of the covariant derivative                          *)
(* (MFD_COVD_METRIC).                                                        *)
(* ========================================================================= *)

(* The metric read in a chart, on pairs of tangent vectors. *)

let GEOC_BILIN_CHART = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) p u v.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ p IN FST c /\
        p IN topspace top
        ==> chart_jac (chart_at atlas p) c p u dot
            (metric_local atlas c g (SND c p) ** chart_jac (chart_at atlas p) c p v) =
            u dot (g p ** v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[metric_local] THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `linear(chart_jac (c:(A->bool)#(A->real^N))
                     (chart_at (atlas:((A->bool)#(A->real^N))->bool) p) p)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `p:A`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL; MATRIX_WORKS] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `p:A`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN SIMP_TAC[]);;

(* Chart level: the derivative of a(t).(G(y(t)) b(t)). *)

let GEOC_DOT_DERIV = prove
 (`!U (G:real^N->real^N^N) (y:real->real^N) y' (a:real->real^N) a'
    (b:real->real^N) b' t.
        metric_field U G /\ y t IN U /\
        ((\s. y(drop s)) has_vector_derivative y') (at (lift t)) /\
        ((\s. a(drop s)) has_vector_derivative a') (at (lift t)) /\
        ((\s. b(drop s)) has_vector_derivative b') (at (lift t))
        ==> ((\s. lift(a(drop s) dot (G(y(drop s)) ** b(drop s))))
             has_vector_derivative
             lift((a' + christoffel G (y t) y' (a t)) dot (G(y t) ** b t) +
                  a t dot (G(y t) ** (b' + christoffel G (y t) y' (b t)))))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                differentiable at ((y:real->real^N) t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. (G:real^N->real^N^N)((y:real->real^N)(drop s))`;
    `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
       (at ((y:real->real^N) t)) o (\h:real^1. drop h % (y':real^N))`;
    `\s. (a:real->real^N)(drop s)`; `\h:real^1. drop h % (a':real^N)`;
    `\s. (b:real->real^N)(drop s)`; `\h:real^1. drop h % (b':real^N)`;
    `lift t`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[has_vector_derivative]) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\s. (G:real^N->real^N^N)((y:real->real^N)(drop s))) =
      (vectorize o G) o (\s. y(drop s))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; has_vector_derivative] THEN
  MATCH_MP_TAC(MESON[]
   `(f':real^1->real^1) = f''
    ==> ((f:real^1->real^1) has_derivative f') (net:(real^1)net)
        ==> (f has_derivative f'') net`) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(matrify:real^(N,N)finite_prod->real^N^N)
      (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
         (at ((y:real->real^N) t)) (drop h % (y':real^N))) =
    drop h %% mderiv G (y t) y'`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM mderiv] THEN ASM_MESON_TAC[LRG_MDERIV_LINEAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real->real^N) t`;
                 `(a:real->real^N) t`; `y':real^N`; `(b:real->real^N) t`]
    LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real->real^N) t`;
                 `christoffel (G:real^N->real^N^N) ((y:real->real^N) t) y'
                              ((a:real->real^N) t)`;
                 `(b:real->real^N) t`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL;
              DOT_LADD; DOT_RADD; MATRIX_VECTOR_MUL_ADD_LDISTRIB] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* Metric compatibility along curves. *)

let MFD_COVD_METRIC = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J Y1 Y2 t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\ is_realinterval J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_field_diff atlas gamma Y1 J /\ mfd_field_diff atlas gamma Y2 J /\
        t IN J
        ==> ((\s. lift(Y1(drop s) dot (g(gamma(drop s)) ** Y2(drop s))))
             has_vector_derivative
             lift(mfd_covd atlas g gamma Y1 t dot (g(gamma t) ** Y2 t) +
                  Y1 t dot (g(gamma t) ** mfd_covd atlas g gamma Y2 t)))
            (at (lift t))`,
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
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `t:real`] GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `((\s. SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) has_vector_derivative
     mfd_vel atlas gamma t) (at (lift t))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_vel] THEN MATCH_MP_TAC GEOC_C1_HAS_VD_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Y. mfd_field_diff atlas (gamma:real->A) (Y:real->real^N) J
        ==> ((\s. mfd_field_rep atlas gamma Y c0 (drop s)) has_vector_derivative
             vector_derivative (\s. mfd_field_rep atlas gamma Y c0 (drop s)) (at (lift t)))
            (at (lift t)) /\
            mfd_field_rep atlas gamma Y c0 t = Y t`
  ASSUME_TAC THENL
   [X_GEN_TAC `Y:real->real^N` THEN REWRITE_TAC[mfd_field_diff] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_DERIVATIVE_WORKS] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[mfd_field_rep] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `(gamma:real->A) t`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
    `mfd_field_diff atlas (gamma:real->A) (Y1:real->real^N) J`))) THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP th (ASSUME
    `mfd_field_diff atlas (gamma:real->A) (Y2:real->real^N) J`))) THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\s. lift(mfd_field_rep atlas (gamma:real->A) (Y1:real->real^N) c0 (drop s) dot
             (metric_local atlas c0 (g:A->real^N^N) (SND c0 (gamma(drop s))) **
              mfd_field_rep atlas gamma (Y2:real->real^N) c0 (drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop r` o check (fun th -> can (term_match []
      `!s. abs(s - t) < d ==> s IN J /\ (gamma:real->A) s IN W`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_field_rep] THEN MATCH_MP_TAC GEOC_BILIN_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)`;
    `metric_local atlas (c0:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
    `\s. SND (c0:(A->bool)#(A->real^N)) ((gamma:real->A) s)`;
    `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t`;
    `mfd_field_rep atlas (gamma:real->A) (Y1:real->real^N) c0`;
    `vector_derivative
       (\s. mfd_field_rep atlas (gamma:real->A) (Y1:real->real^N) c0 (drop s))
       (at (lift t))`;
    `mfd_field_rep atlas (gamma:real->A) (Y2:real->real^N) c0`;
    `vector_derivative
       (\s. mfd_field_rep atlas (gamma:real->A) (Y2:real->real^N) c0 (drop s))
       (at (lift t))`; `t:real`] GEOC_DOT_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN
      DISCH_THEN(MP_TAC o SPEC `c0:(A->bool)#(A->real^N)`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real^1) = y ==> ((f:real^1->real^1) has_vector_derivative x) net
                       ==> (f has_vector_derivative y) net`) THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[mfd_covd] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`] METRIC_LOCAL_AT) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Geodesics have parallel velocity (MFD_GEODESIC_VEL_PARALLEL).             *)
(* ========================================================================= *)

(* In the preferred chart at gamma t, the velocity field of a geodesic has  *)
(* derivative -Gamma(v,v) at t.                                              *)

let GEOC_GEODESIC_VEL_REP = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ t IN J
        ==> ((\s. mfd_field_rep atlas gamma (mfd_vel atlas gamma)
                    (chart_at atlas (gamma t)) (drop s)) has_vector_derivative
             --(christoffel (metric_local atlas (chart_at atlas (gamma t)) g)
                            (SND (chart_at atlas (gamma t)) (gamma t))
                            (mfd_vel atlas gamma t) (mfd_vel atlas gamma t)))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. s IN J ==> (gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c0:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (LABEL_TAC "v")) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `t:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!s. s IN J /\ (gamma:real->A) s IN FST (c0:(A->bool)#(A->real^N))
        ==> mfd_field_rep atlas gamma (mfd_vel atlas gamma) c0 s =
            (v:real->real^N) s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_CHART_VEL_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "v" (fun th -> MP_TAC(SPEC `s:real` th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real->real^N) t = mfd_vel atlas (gamma:real->A) t` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
      `!s. s IN J /\ (gamma:real->A) s IN FST (c0:(A->bool)#(A->real^N))
           ==> mfd_field_rep atlas gamma (mfd_vel atlas gamma) c0 s =
               (v:real->real^N) s`) (concl th))) THEN
    ASM_REWRITE_TAC[mfd_field_rep] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `(gamma:real->A) t`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\s. (v:real->real^N)(drop s)`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "v" (fun th -> MP_TAC(SPEC `t:real` th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MFD_GEODESIC_VEL_PARALLEL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J
        ==> mfd_parallel atlas g gamma J (mfd_vel atlas gamma)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_parallel; mfd_field_diff] THEN
  CONJ_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `t:real`]
    GEOC_GEODESIC_VEL_REP) THEN
  ASM_REWRITE_TAC[] THENL
   [MESON_TAC[differentiable; has_vector_derivative];
    DISCH_THEN(fun th -> REWRITE_TAC[mfd_covd; MATCH_MP VECTOR_DERIVATIVE_AT th]) THEN
    VECTOR_ARITH_TAC]);;

(* ========================================================================= *)
(* Two-parameter maps: chart partial derivatives and the                     *)
(* symmetry lemma (MFD_COVD_SYMMETRY).                                       *)
(* ========================================================================= *)

(* Change of chart for the velocity of a curve staying in both charts near *)
(* t.                                                                        *)

let GEOC_CHART_CHANGE_VEL_NEAR = prove
 (`!top atlas (gamma:real->A) (c:(A->bool)#(A->real^N)) c' v t d.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\ &0 < d /\
        (!r. abs(r - t) < d ==> gamma r IN FST c INTER FST c') /\
        ((\s. SND c (gamma(drop s))) has_vector_derivative v) (at (lift t))
        ==> ((\s. SND c' (gamma(drop s))) has_vector_derivative
             chart_jac c c' (gamma t) v) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN FST (c:(A->bool)#(A->real^N)) INTER FST (c':(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!r. abs(r - t) < d ==> (gamma:real->A) r IN W`) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `chart_trans (c:(A->bool)#(A->real^N)) c' o
              (\s. SND c ((gamma:real->A)(drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x:A. x IN FST (c:(A->bool)#(A->real^N))
             ==> chart_trans c c' (SND c x) = SND (c':(A->bool)#(A->real^N)) x`)
      (concl th))) THEN
    SUBGOAL_THEN `abs(drop s - t) < d` (fun th -> ASM_MESON_TAC[th; IN_INTER]) THEN
    UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN
  ASM_REWRITE_TAC[WITHIN_UNIV; LIFT_DROP] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Coordinate lines through a point of real^1 x real^1. *)

let GEOC_COORD_LINES = prove
 (`!(H:real^(1,1)finite_sum->real^N) a b.
        H differentiable at (pastecart a b)
        ==> ((\r. H(pastecart r b)) has_vector_derivative
             frechet_derivative H (at (pastecart a b)) (pastecart (vec 1) (vec 0)))
            (at a) /\
            ((\r. H(pastecart a r)) has_vector_derivative
             frechet_derivative H (at (pastecart a b)) (pastecart (vec 0) (vec 1)))
            (at b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
  ABBREV_TAC `D = frechet_derivative (H:real^(1,1)finite_sum->real^N)
                                     (at (pastecart a b))` THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `((\r. (H:real^(1,1)finite_sum->real^N)(pastecart r b)) has_derivative
       ((D:real^(1,1)finite_sum->real^N) o (\h. pastecart h (vec 0)))) (at a)`
    MP_TAC THENL
     [SUBGOAL_THEN
       `(\r. (H:real^(1,1)finite_sum->real^N)(pastecart r b)) =
        H o (\r. pastecart r b)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`at (a:real^1)`; `\r:real^1. r`; `\r:real^1. (b:real^1)`;
                     `\h:real^1. h`; `\h:real^1. vec 0:real^1`]
        HAS_DERIVATIVE_PASTECART) THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      DISCH_THEN(MP_TAC o MATCH_MP GRGD_HAS_DERIVATIVE_VECTOR) THEN
      REWRITE_TAC[o_THM]];
    SUBGOAL_THEN
     `((\r. (H:real^(1,1)finite_sum->real^N)(pastecart a r)) has_derivative
       ((D:real^(1,1)finite_sum->real^N) o (\h. pastecart (vec 0) h))) (at b)`
    MP_TAC THENL
     [SUBGOAL_THEN
       `(\r. (H:real^(1,1)finite_sum->real^N)(pastecart a r)) =
        H o (\r. pastecart a r)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`at (b:real^1)`; `\r:real^1. (a:real^1)`; `\r:real^1. r`;
                     `\h:real^1. vec 0:real^1`; `\h:real^1. h`]
        HAS_DERIVATIVE_PASTECART) THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
      DISCH_THEN(MP_TAC o MATCH_MP GRGD_HAS_DERIVATIVE_VECTOR) THEN
      REWRITE_TAC[o_THM]]]);;

(* Sets of parameter pairs. *)

let GEOC_IN_PAIR_SET = prove
 (`!S0 J (P:real->real->bool) s t.
        pastecart (lift s) (lift t) IN
        {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ P s t} <=>
        s IN S0 /\ t IN J /\ P s t`,
  REWRITE_TAC[IN_ELIM_THM; PASTECART_INJ; LIFT_EQ] THEN MESON_TAC[]);;

let GEOC_PAIR_DOMAIN_OPEN = prove
 (`!S0 J. real_open S0 /\ real_open J
          ==> open {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J} =
                IMAGE lift S0 PCROSS IMAGE lift J`
  SUBST1_TAC THENL
   [REWRITE_TAC[PCROSS; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[GSYM REAL_OPEN]]);;

let GEOC_PAIR_CHART_OPEN = prove
 (`!top (f:real->real->A) S0 J U.
        real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        open_in top U
        ==> open {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN U}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J}` THEN
  ASM_SIMP_TAC[GEOC_PAIR_DOMAIN_OPEN] THEN
  MP_TAC(ISPECL [`\z. (f:real->real->A) (drop(fstcart z)) (drop(sndcart z))`;
                 `subtopology euclidean
                    {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}`;
                 `top:A topology`; `U:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC(MESON[]
   `(s:real^(1,1)finite_sum->bool) = t
    ==> open_in (top:(real^(1,1)finite_sum)topology) s ==> open_in top t`) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP]);;

(* Near a point of an open set of pairs, the coordinate lines stay in it. *)

let GEOC_PAIR_NEAR = prove
 (`!O s t.
        open O /\ pastecart (lift s) (lift t) IN O
        ==> ?e. &0 < e /\
                (!r. abs(r - s) < e ==> pastecart (lift r) (lift t) IN O) /\
                (!r. abs(r - t) < e ==> pastecart (lift s) (lift r) IN O)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (lift t)` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[DIST_PASTECART_CANCEL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Velocities of two-parameter maps in charts, and the                       *)
(* symmetry lemma (MFD_COVD_SYMMETRY).                                       *)
(* ========================================================================= *)

(* The velocities of the coordinate curves, read in any chart, are the     *)
(* partial derivatives of the chart representative.                         *)

let GEOC_VEL_CHART2 = prove
 (`!top atlas (f:real->real->A) S0 J (c:(A->bool)#(A->real^N)) s t.
        smooth_manifold_atlas top atlas /\ real_open S0 /\ real_open J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                   (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
        c IN atlas /\ s IN S0 /\ t IN J /\ f s t IN FST c
        ==> chart_jac (chart_at atlas (f s t)) c (f s t)
              (mfd_vel atlas (\s'. f s' t) s) =
            frechet_derivative (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))
              (at (pastecart (lift s) (lift t))) (pastecart (vec 1) (vec 0)) /\
            chart_jac (chart_at atlas (f s t)) c (f s t) (mfd_vel atlas (f s) t) =
            frechet_derivative (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))
              (at (pastecart (lift s) (lift t))) (pastecart (vec 0) (vec 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real->A) s t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:real->real->A) s t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c' = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s t)` THEN
  STRIP_TAC THEN
  (* both charts near (s,t) *)
  MP_TAC(ISPECL [`top:A topology`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N)) INTER FST(c':(A->bool)#(A->real^N))`]
    GEOC_PAIR_CHART_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[MFDM_CHART];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
      (f:real->real->A) s t IN FST(c:(A->bool)#(A->real^N)) INTER FST(c':(A->bool)#(A->real^N))}`;
    `s:real`; `t:real`] GEOC_PAIR_NEAR) THEN
  ASM_REWRITE_TAC[GEOC_IN_PAIR_SET; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ns") (LABEL_TAC "nt")))) THEN
  (* differentiability of the two chart representatives at (s,t) *)
  SUBGOAL_THEN
   `!d:(A->bool)#(A->real^N).
        d IN atlas /\ (f:real->real->A) s t IN FST d
        ==> (\z. SND d (f (drop(fstcart z)) (drop(sndcart z))))
            differentiable at (pastecart (lift s) (lift t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `d:(A->bool)#(A->real^N)` THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `{pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                 (f:real->real->A) s t IN FST(d:(A->bool)#(A->real^N))}` THEN
    ASM_SIMP_TAC[GEOC_IN_PAIR_SET] THEN
    MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN EXISTS_TAC `top:A topology` THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. SND (c:(A->bool)#(A->real^N))
                        ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))`;
                 `lift s`; `lift t`] GEOC_COORD_LINES) THEN
  MP_TAC(ISPECL [`\z. SND (c':(A->bool)#(A->real^N))
                        ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))`;
                 `lift s`; `lift t`] GEOC_COORD_LINES) THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\r. SND (c:(A->bool)#(A->real^N)) ((f:real->real->A) (drop r) t)` THEN
    EXISTS_TAC `lift s` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `\r. (f:real->real->A) r t`; `c':(A->bool)#(A->real^N)`;
                   `c:(A->bool)#(A->real^N)`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (\s'. (f:real->real->A) s' t) s`;
                   `s:real`; `e:real`] GEOC_CHART_CHANGE_VEL_NEAR) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      USE_THEN "ns" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(r - s) < e`))) THEN
      REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
      ASM_REWRITE_TAC[mfd_vel] THEN
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
      ASM_MESON_TAC[differentiable; has_vector_derivative]];
    MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\r. SND (c:(A->bool)#(A->real^N)) ((f:real->real->A) s (drop r))` THEN
    EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(f:real->real->A) s`; `c':(A->bool)#(A->real^N)`;
                   `c:(A->bool)#(A->real^N)`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s) t`;
                   `t:real`; `e:real`] GEOC_CHART_CHANGE_VEL_NEAR) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      USE_THEN "nt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(r - t) < e`))) THEN
      REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
      ASM_REWRITE_TAC[mfd_vel] THEN
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
      ASM_MESON_TAC[differentiable; has_vector_derivative]]]);;

(* The symmetry lemma: D_s d_t f = D_t d_s f. *)

let MFD_COVD_SYMMETRY = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open S0 /\ is_realinterval S0 /\ real_open J /\ is_realinterval J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                   (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
        s IN S0 /\ t IN J
        ==> mfd_covd atlas g (\s'. f s' t) (\s'. mfd_vel atlas (f s') t) s =
            mfd_covd atlas g (f s) (\t'. mfd_vel atlas (\s'. f s' t') s) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real->real->A) s t IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `pastecart (lift s) (lift t)` o CONJUNCT1 o
      GEN_REWRITE_RULE I [continuous_map] o check (fun th -> can (term_match []
        `continuous_map (X,top:A topology) (h:real^(1,1)finite_sum->A)`) (concl th))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(f:real->real->A) s t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s t)` THEN
  STRIP_TAC THEN
  ABBREV_TAC `O0 = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\
                    (f:real->real->A) s t IN FST(c0:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN `open (O0:real^(1,1)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O0" THEN MATCH_MP_TAC GEOC_PAIR_CHART_OPEN THEN
    EXISTS_TAC `top:A topology` THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift s) (lift t) IN (O0:real^(1,1)finite_sum->bool)`
  ASSUME_TAC THENL [EXPAND_TAC "O0" THEN ASM_REWRITE_TAC[GEOC_IN_PAIR_SET]; ALL_TAC] THEN
  ABBREV_TAC `F0 = \z. SND (c0:(A->bool)#(A->real^N))
                         ((f:real->real->A) (drop(fstcart z)) (drop(sndcart z)))` THEN
  SUBGOAL_THEN `smooth_map_on O0 (F0:real^(1,1)finite_sum->real^N)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O0"; "F0"] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`O0:real^(1,1)finite_sum->bool`; `s:real`; `t:real`] GEOC_PAIR_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ns") (LABEL_TAC "nt")))) THEN
  (* the two partial derivative fields *)
  ABBREV_TAC `e1 = pastecart (vec 1:real^1) (vec 0:real^1)` THEN
  ABBREV_TAC `e2 = pastecart (vec 0:real^1) (vec 1:real^1)` THEN
  SUBGOAL_THEN
   `!w. (\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) w)
        differentiable at (pastecart (lift s) (lift t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `O0:real^(1,1)finite_sum->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  (* the velocities of the coordinate curves in the chart c0 *)
  SUBGOAL_THEN
   `!r. abs(r - s) < e
        ==> chart_jac (chart_at atlas ((f:real->real->A) r t))
              (c0:(A->bool)#(A->real^N)) (f r t) (mfd_vel atlas (f r) t) =
            frechet_derivative (F0:real^(1,1)finite_sum->real^N)
              (at (pastecart (lift r) (lift t))) e2`
  (LABEL_TAC "vs") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    USE_THEN "ns" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(r - s) < e`))) THEN
    EXPAND_TAC "O0" THEN REWRITE_TAC[GEOC_IN_PAIR_SET] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["F0"; "e2"] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `c0:(A->bool)#(A->real^N)`; `r:real`; `t:real`] GEOC_VEL_CHART2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. abs(r - t) < e
        ==> chart_jac (chart_at atlas ((f:real->real->A) s r))
              (c0:(A->bool)#(A->real^N)) (f s r) (mfd_vel atlas (\s'. f s' r) s) =
            frechet_derivative (F0:real^(1,1)finite_sum->real^N)
              (at (pastecart (lift s) (lift r))) e1`
  (LABEL_TAC "vt") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    USE_THEN "nt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(r - t) < e`))) THEN
    EXPAND_TAC "O0" THEN REWRITE_TAC[GEOC_IN_PAIR_SET] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["F0"; "e1"] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `c0:(A->bool)#(A->real^N)`; `s:real`; `r:real`] GEOC_VEL_CHART2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the velocities at (s,t) *)
  SUBGOAL_THEN
   `mfd_vel atlas (\s'. (f:real->real->A) s' t) s =
    frechet_derivative (F0:real^(1,1)finite_sum->real^N)
      (at (pastecart (lift s) (lift t))) e1 /\
    mfd_vel atlas (f s) t =
    frechet_derivative F0 (at (pastecart (lift s) (lift t))) e2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                   `c0:(A->bool)#(A->real^N)`; `s:real`; `t:real`] GEOC_VEL_CHART2) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `(f:real->real->A) s t`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXPAND_TAC ["F0"; "e1"; "e2"] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_covd] THEN ASM_REWRITE_TAC[] THEN
  (* the derivatives of the field representatives *)
  SUBGOAL_THEN
   `vector_derivative
      (\r. mfd_field_rep atlas (\s'. (f:real->real->A) s' t)
             (\s'. mfd_vel atlas (f s') t) (c0:(A->bool)#(A->real^N)) (drop r))
      (at (lift s)) =
    frechet_derivative
      (\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e2)
      (at (pastecart (lift s) (lift t))) e1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\r. frechet_derivative (F0:real^(1,1)finite_sum->real^N)
                      (at (pastecart r (lift t))) e2` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
      USE_THEN "vs" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(drop r - s) < e`))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      MP_TAC(ISPECL
       [`\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e2`;
        `lift s`; `lift t`] GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "e1" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\r. mfd_field_rep atlas ((f:real->real->A) s)
             (\t'. mfd_vel atlas (\s'. f s' t') s) (c0:(A->bool)#(A->real^N)) (drop r))
      (at (lift t)) =
    frechet_derivative
      (\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e1)
      (at (pastecart (lift s) (lift t))) e2`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\r. frechet_derivative (F0:real^(1,1)finite_sum->real^N)
                      (at (pastecart (lift s) r)) e1` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
      USE_THEN "vt" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(drop r - t) < e`))) THEN
      REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      MP_TAC(ISPECL
       [`\z. frechet_derivative (F0:real^(1,1)finite_sum->real^N) (at z) e1`;
        `lift s`; `lift t`] GEOC_COORD_LINES) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "e2" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  (* conclude by the symmetry of second derivatives and of the Christoffel *)
  (* symbols                                                                 *)
  MP_TAC(ISPECL [`O0:real^(1,1)finite_sum->bool`; `F0:real^(1,1)finite_sum->real^N`;
                 `pastecart (lift s) (lift t)`; `e1:real^(1,1)finite_sum`;
                 `e2:real^(1,1)finite_sum`] LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CHRISTOFFEL_SYM THEN
  EXISTS_TAC `IMAGE (SND (c0:(A->bool)#(A->real^N))) (FST c0)` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `c0:(A->bool)#(A->real^N)`) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

