(* ========================================================================= *)
(* pc_geo_par: parallel transport along C^1 curves                           *)
(* (MFD_PARALLEL_EXISTS_UNIQUE): uniqueness from the conservation of g-inner *)
(* products, local existence from the linear ODE in a chart                  *)
(* (ODE_LINEAR_INTERVAL), global existence by an open-closed argument on the *)
(* interval.  MFD_PARALLEL_EXISTS_UNIQUE belongs to the geodesics API        *)
(* pc_geo_iface.                                                             *)
(*                                                                           *)
(* Locality, uniqueness, clopen subsets of intervals.                        *)
(* ========================================================================= *)

needs "src/pc_geo_dist.ml";;
needs "src/pc_cmp_gfacts.ml";;

prioritize_real();;
type_invention_error := true;;

(* Being parallel is a pointwise condition. *)

let GEOT_PARALLEL_POINTWISE = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N).
        mfd_parallel atlas g gamma J Y <=>
        !t. t IN J ==> mfd_parallel atlas g gamma {t} Y`,
  REWRITE_TAC[mfd_parallel; mfd_field_diff; IN_SING] THEN MESON_TAC[]);;

let GEOT_PARALLEL_SUBSET = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J J' (Y:real->real^N).
        mfd_parallel atlas g gamma J Y /\ J' SUBSET J
        ==> mfd_parallel atlas g gamma J' Y`,
  REWRITE_TAC[mfd_parallel; mfd_field_diff; SUBSET] THEN MESON_TAC[]);;

(* ... and a local one. *)

let GEOT_PARALLEL_LOCAL = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) (W:real->real^N) Y t d.
        &0 < d /\ (!s. abs(s - t) < d ==> W s = Y s) /\
        mfd_parallel atlas g gamma {t} Y
        ==> mfd_parallel atlas g gamma {t} W`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_parallel; mfd_field_diff; IN_SING] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
    EXISTS_TAC `\s. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N)
                      (chart_at atlas (gamma t)) (drop s)` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
      `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t = vec 0`)
      (concl th))) THEN
    MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]]);;

(* Uniqueness of parallel fields with the same value at one time. *)

let GEOT_PARALLEL_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y1:real->real^N) Y2 t0.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\ is_realinterval J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        mfd_parallel atlas g gamma J Y1 /\ mfd_parallel atlas g gamma J Y2 /\
        t0 IN J /\ Y1 t0 = Y2 t0
        ==> !t. t IN J ==> Y1 t = Y2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  ABBREV_TAC `Z = \s. &1 % (Y1:real->real^N) s + --(&1) % Y2 s` THEN
  SUBGOAL_THEN `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) J (Z:real->real^N)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[mfd_parallel] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPG_FIELD_DIFF_LIN THEN EXISTS_TAC `top:A topology` THEN
      ASM_MESON_TAC[mfd_parallel];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                     `Y1:real->real^N`; `Y2:real->real^N`; `&1`; `--(&1)`; `s:real`]
        CMPG_COVD_LIN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[mfd_parallel]; DISCH_THEN SUBST1_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[mfd_parallel]) THEN
      ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `Z:real->real^N`; `Z:real->real^N`; `t0:real`; `t:real`]
    MFD_PARALLEL_INNER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Z:real->real^N) t0 = vec 0` SUBST1_TAC THENL
   [EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Z:real->real^N) t = vec 0` MP_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t`] GEOD_G_POS_DEF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMPG_C1_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o SPEC `(Z:real->real^N) t`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    EXPAND_TAC "Z" THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC]);;

(* A subset of an interval which is open and closed relative to it, and     *)
(* nonempty, is the whole interval.                                          *)

let GEOT_INTERVAL_CLOPEN = prove
 (`!J S t0.
        is_realinterval J /\ t0 IN S /\ S SUBSET J /\
        (!t. t IN S ==> ?e. &0 < e /\ !s. s IN J /\ abs(s - t) < e ==> s IN S) /\
        (!t. t IN J /\ ~(t IN S)
             ==> ?e. &0 < e /\ !s. s IN J /\ abs(s - t) < e ==> ~(s IN S))
        ==> S = J`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `connected_space (subtopology euclideanreal J)` MP_TAC THENL
   [MP_TAC(SPEC `J:real->bool` CONNECTED_IN_EUCLIDEANREAL) THEN
    ASM_REWRITE_TAC[connected_in] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
  DISCH_THEN(MP_TAC o SPEC `S:real->bool`) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[closed_in; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; GSYM MTOPOLOGY_SUBMETRIC;
                    OPEN_IN_MTOPOLOGY; SUBMETRIC; REAL_EUCLIDEAN_METRIC; INTER_UNIV;
                    SUBSET; IN_MBALL; IN_DIFF] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
        `!t. t IN (S:real->bool) ==> ?e. &0 < e /\ P t e`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
        `!t. t IN (J:real->bool) /\ ~(t IN (S:real->bool)) ==> ?e. &0 < e /\ P t e`)
        (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Fields differentiable in one chart; continuity of the                     *)
(* coefficients of the parallel transport equation in a chart.              *)
(* ========================================================================= *)

let GEOT_FIELD_DIFF_CHART = prove
 (`!top atlas (gamma:real->A) K (Y:real->real^N) (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ real_open K /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET K
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        c IN atlas /\ (!t. t IN K ==> gamma t IN FST c) /\
        (!t. t IN K
             ==> (\s. mfd_field_rep atlas gamma Y c (drop s)) differentiable at (lift t))
        ==> mfd_field_diff atlas gamma Y K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_field_diff] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `continuous_map (subtopology euclideanreal K,top) (gamma:real->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOC_C1_CONTINUOUS THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN K ==> (gamma:real->A) s IN topspace top` ASSUME_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology euclideanreal K,top) (gamma:real->A)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c0:(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `K:real->bool`;
                 `FST(c:(A->bool)#(A->real^N)) INTER FST(c0:(A->bool)#(A->real^N))`;
                 `t:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC OPEN_IN_INTER) THEN ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\r. frechet_derivative (chart_trans (c:(A->bool)#(A->real^N)) c0)
          (at (SND c ((gamma:real->A)(drop r))))
          (mfd_field_rep atlas gamma (Y:real->real^N) c (drop r))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop r` o check (fun th -> can (term_match []
      `!s. abs(s - t) < d ==> s IN K /\ (gamma:real->A) s IN W`) (concl th))) THEN
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
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `(gamma:real->A)(drop r)`] CHART_JAC_CHAIN) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[differentiable] THEN
  MP_TAC(ISPECL
   [`IMAGE (SND (c:(A->bool)#(A->real^N)))
           (FST c INTER FST (c0:(A->bool)#(A->real^N)))`;
    `chart_trans (c:(A->bool)#(A->real^N)) c0`;
    `\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))`;
    `\r. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c (drop r)`;
    `vector_derivative (\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r)))
       (at (lift t))`;
    `vector_derivative (\r. mfd_field_rep atlas (gamma:real->A) (Y:real->real^N) c (drop r))
       (at (lift t))`;
    `lift t`] GEOL_FRECHET_ALONG) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[IN_INTER];
      MATCH_MP_TAC GEOC_C1_HAS_VD_AT THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `K:real->bool`] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[has_vector_derivative] THEN MESON_TAC[]]);;

(* Continuity of the coefficients -christoffel(y)(v,.) along a curve. *)

let GEOT_COEFF_CONT = prove
 (`!U (G:real^N->real^N^N) (y:real^1->real^N) (v:real^1->real^N) S.
        metric_field U G /\ y continuous_on S /\ IMAGE y S SUBSET U /\
        v continuous_on S
        ==> !i j. (\r. lift((matrix(\w. --(christoffel G (y r) (v r) w)):real^N^N)$i$j))
                  continuous_on S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k j. (\r. christoffel (G:real^N->real^N^N) ((y:real^1->real^N) r)
                 (basis k) (basis j)) continuous_on S`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `(\r. christoffel (G:real^N->real^N^N) ((y:real^1->real^N) r) (basis k) (basis j)) =
      (\z. christoffel G z (basis k) (basis j)) o y`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. (\r. christoffel (G:real^N->real^N^N) ((y:real^1->real^N) r) (v r) (basis j))
        continuous_on S`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC
     `\r. vsum(1..dimindex(:N))
            (\k. drop(lift(((v:real^1->real^N) r)$k)) %
                 christoffel (G:real^N->real^N^N) ((y:real^1->real^N) r)
                   (basis k) (basis j))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`\w. christoffel (G:real^N->real^N^N) ((y:real^1->real^N) r) w
                            (basis j)`; `(v:real^1->real^N) r`] GEOL_LINEAR_EXPAND) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real^1->real^N) r`]
        CHRISTOFFEL_BILINEAR) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[bilinear]];
      MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  MP_TAC(ISPEC `j:num` (INST_TYPE [`:real`,`:A`] FINITE_INDEX_INRANGE)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> ONCE_REWRITE_TAC[th])))) THEN
  ASM_SIMP_TAC[MATRIX_COMPONENT] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; LIFT_NEG] THEN
  MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN ASM_REWRITE_TAC[]);;

(* Derivatives within [a,b] at interior points are two-sided. *)

let GEOT_WITHIN_TO_AT = prove
 (`!(f:real^1->real^N) f' a b t.
        t IN real_interval(a,b) /\
        (f has_vector_derivative f') (at (lift t) within interval[lift a,lift b])
        ==> (f has_vector_derivative f') (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `interval[lift a,lift b]`; `interval(lift a,lift b)`;
                 `lift t`] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET) THEN
  ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_OPEN THEN REWRITE_TAC[OPEN_INTERVAL] THEN
  UNDISCH_TAC `t IN real_interval(a,b)` THEN
  REWRITE_TAC[IN_INTERVAL_1; IN_REAL_INTERVAL; LIFT_DROP]);;

(* ========================================================================= *)
(* Local existence of parallel fields (linear ODE in a chart).               *)
(* ========================================================================= *)

let GEOT_LOCAL_EXISTS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J beta.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\ is_realinterval J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        beta IN J
        ==> ?a b. a < beta /\ beta < b /\ real_interval[a,b] SUBSET J /\
                  !s w. s IN real_interval(a,b)
                        ==> ?Y. mfd_parallel atlas g gamma (real_interval(a,b)) Y /\
                                Y s = w`,
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
                 `(gamma:real->A) beta`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) beta)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `beta:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`beta - d / &2`; `beta + d / &2`] THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ABBREV_TAC `a = beta - d / &2` THEN ABBREV_TAC `b = beta + d / &2` THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[a,b] ==> s IN J /\ (gamma:real->A) s IN FST(c:(A->bool)#(A->real^N))`
  (LABEL_TAC "inc") THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the chart data along [a,b] *)
  SUBGOAL_THEN
   `{r | r IN interval[lift a,lift b] /\
         (gamma:real->A)(drop r) IN FST(c:(A->bool)#(A->real^N))} =
    interval[lift a,lift b]`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
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
  SUBGOAL_THEN
   `!r. r IN interval[lift a,lift b]
        ==> ((yc:real^1->real^N) has_vector_derivative vc r)
            (at r within interval[lift a,lift b])`
  (LABEL_TAC "yvd") THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["vc"; "yc"] THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`; `c:(A->bool)#(A->real^N)`;
                   `drop r`] GRGD_C1_CHART_HAS_VD) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(yc:real^1->real^N) continuous_on interval[lift a,lift b]` ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h:real^1. drop h % (vc:real^1->real^N) r` THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN ASM_SIMP_TAC[];
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
    ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `G:real^N->real^N^N`;
                 `yc:real^1->real^N`; `vc:real^1->real^N`; `interval[lift a,lift b]`]
    GEOT_COEFF_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* solving the linear ODE *)
  MAP_EVERY X_GEN_TAC [`s:real`; `w:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `s IN real_interval[a,b]` ASSUME_TAC THENL
   [UNDISCH_TAC `s IN real_interval(a,b)` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\r. (matrix(\w. --(christoffel (G:real^N->real^N^N) ((yc:real^1->real^N) r)
                          ((vc:real^1->real^N) r) w)):real^N^N)`;
    `\r:real^1. vec 0:real^N`; `lift a`; `lift b`; `lift s`;
    `chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) s))
               (c:(A->bool)#(A->real^N)) (gamma s) (w:real^N)`] ODE_LINEAR_INTERVAL) THEN
  ASM_REWRITE_TAC[GRGD_IN_INTERVAL_LIFT; CONTINUOUS_ON_CONST; VECTOR_ADD_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ode") (K ALL_TAC)))) THEN
  EXISTS_TAC
   `\t. chart_jac (c:(A->bool)#(A->real^N))
          (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)) (gamma t)
          ((u:real^1->real^N)(lift t))` THEN
  (* basic chart facts at points of [a,b] *)
  SUBGOAL_THEN
   `!t. t IN real_interval[a,b]
        ==> chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t) IN atlas /\
            gamma t IN FST(chart_at atlas (gamma t)) /\
            gamma t IN FST(c:(A->bool)#(A->real^N))`
  (LABEL_TAC "ch") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "inc" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `t IN real_interval[a,b]`))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. t IN real_interval[a,b]
          ==> chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))
                (c:(A->bool)#(A->real^N)) (gamma t)
                (chart_jac c (chart_at atlas (gamma t)) (gamma t) x) = x /\
              chart_jac c (chart_at atlas (gamma t)) (gamma t)
                (chart_jac (chart_at atlas (gamma t)) c (gamma t) x) = x`
  (LABEL_TAC "inv") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "ch" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `t IN real_interval[a,b]`))) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                   ((gamma:real->A) t))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                   ((gamma:real->A) t))`;
                     `(gamma:real->A) t`] CHART_JAC_INVERSE);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                   ((gamma:real->A) t))`;
                     `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                   ((gamma:real->A) t))`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `(gamma:real->A) t`] CHART_JAC_INVERSE)] THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN
    DISCH_THEN(MP_TAC o C AP_THM `x:real^N`) THEN REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN
    USE_THEN "inv" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC_ALL(MATCH_MP th
      (ASSUME `s IN real_interval[a,b]`)))])] THEN
  (* the field in the chart c is u *)
  SUBGOAL_THEN
   `!t. t IN real_interval[a,b]
        ==> mfd_field_rep atlas (gamma:real->A)
              (\t. chart_jac (c:(A->bool)#(A->real^N))
                     (chart_at atlas (gamma t)) (gamma t) ((u:real^1->real^N)(lift t)))
              c t = u(lift t)`
  (LABEL_TAC "rep") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
    USE_THEN "inv" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC_ALL(MATCH_MP th
      (ASSUME `t IN real_interval[a,b]`)))]);
    ALL_TAC] THEN
  (* u is differentiable at interior points *)
  SUBGOAL_THEN
   `!t. t IN real_interval(a,b)
        ==> ((u:real^1->real^N) has_vector_derivative
             (matrix(\w. --(christoffel (G:real^N->real^N^N) ((yc:real^1->real^N)(lift t))
                              ((vc:real^1->real^N)(lift t)) w)):real^N^N) ** u(lift t))
            (at (lift t))`
  (LABEL_TAC "uat") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN MATCH_MP_TAC GEOT_WITHIN_TO_AT THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ode" MATCH_MP_TAC THEN REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN
    UNDISCH_TAC `t IN real_interval(a,b)` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval(a,b) ==> t IN real_interval[a,b]`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval(a,b)
        ==> ?e. &0 < e /\ !r. abs(r - t) < e ==> r IN real_interval(a,b)`
  ASSUME_TAC THENL
   [MESON_TAC[REAL_OPEN_REAL_INTERVAL; real_open]; ALL_TAC] THEN
  (* field differentiability *)
  SUBGOAL_THEN
   `mfd_field_diff atlas (gamma:real->A)
      (\t. chart_jac (c:(A->bool)#(A->real^N))
             (chart_at atlas (gamma t)) (gamma t) ((u:real^1->real^N)(lift t)))
      (real_interval(a,b))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOT_FIELD_DIFF_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `c:(A->bool)#(A->real^N)`] THEN
    ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval(a,b)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
      EXISTS_TAC `u:real^1->real^N` THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o C MATCH_MP
        (ASSUME `t IN real_interval(a,b)`)) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
        DISCH_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
        USE_THEN "rep" MATCH_MP_TAC THEN ASM_MESON_TAC[];
        REWRITE_TAC[differentiable] THEN
        USE_THEN "uat" (fun th -> MP_TAC(MATCH_MP th
          (ASSUME `t IN real_interval(a,b)`))) THEN
        REWRITE_TAC[has_vector_derivative] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_parallel] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  (* the covariant derivative in the chart c *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `real_interval(a,b)`;
                 `\t. chart_jac (c:(A->bool)#(A->real^N))
                        (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))
                        (gamma t) ((u:real^1->real^N)(lift t))`;
                 `c:(A->bool)#(A->real^N)`; `t:real`] MFD_COVD_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `real_interval(a,b)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\r. mfd_field_rep atlas (gamma:real->A)
             (\t. chart_jac (c:(A->bool)#(A->real^N))
                    (chart_at atlas (gamma t)) (gamma t) ((u:real^1->real^N)(lift t)))
             c (drop r)) (at (lift t)) =
    (matrix(\w. --(christoffel (G:real^N->real^N^N) ((yc:real^1->real^N)(lift t))
                     ((vc:real^1->real^N)(lift t)) w)):real^N^N) ** u(lift t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vector_derivative (u:real^1->real^N) (at (lift t))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CMPG_VECTOR_DERIVATIVE_LOCAL THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o C MATCH_MP
        (ASSUME `t IN real_interval(a,b)`)) THEN
      EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN REWRITE_TAC[] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      USE_THEN "rep" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      USE_THEN "uat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative (\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r)))
      (at (lift t)) = (vc:real^1->real^N)(lift t)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MATCH_MP_TAC GEOT_WITHIN_TO_AT THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop r))) = yc`
    SUBST1_TAC THENL [EXPAND_TAC "yc" THEN REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "yvd" MATCH_MP_TAC THEN REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "rep" (fun th -> REWRITE_TAC[MATCH_MP th
    (MATCH_MP (ASSUME `!t. t IN real_interval(a,b) ==> t IN real_interval[a,b]`)
              (ASSUME `t IN real_interval(a,b)`))]) THEN
  SUBGOAL_THEN
   `SND(c:(A->bool)#(A->real^N)) ((gamma:real->A) t) = (yc:real^1->real^N)(lift t)`
  SUBST1_TAC THENL [EXPAND_TAC "yc" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(\w. --(christoffel (G:real^N->real^N^N) ((yc:real^1->real^N)(lift t))
                    ((vc:real^1->real^N)(lift t)) w))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_NEG THEN
    MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`; `G:real^N->real^N^N`;
                   `(yc:real^1->real^N)(lift t)`] CHRISTOFFEL_BILINEAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (yc:real^1->real^N) (interval[lift a,lift b]) SUBSET
                   IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN ASM_MESON_TAC[];
      SIMP_TAC[bilinear; ETA_AX]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; VECTOR_ADD_LINV] THEN DISCH_TAC THEN
  USE_THEN "ch" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
    (MATCH_MP (ASSUME `!t. t IN real_interval(a,b) ==> t IN real_interval[a,b]`)
              (ASSUME `t IN real_interval(a,b)`)))) THEN
  USE_THEN "inv" (MP_TAC o SPECL [`t:real`; `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
     (\t. chart_jac (c:(A->bool)#(A->real^N))
            (chart_at (atlas:((A->bool)#(A->real^N))->bool) (gamma t)) (gamma t)
            ((u:real^1->real^N)(lift t))) t`]) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  UNDISCH_TAC
   `mfd_field_rep atlas (gamma:real->A)
      (mfd_covd atlas (g:A->real^N^N) gamma
        (\t. chart_jac (c:(A->bool)#(A->real^N))
               (chart_at atlas (gamma t)) (gamma t) ((u:real^1->real^N)(lift t))))
      c t = vec 0` THEN
  REWRITE_TAC[mfd_field_rep] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))`;
                 `(gamma:real->A) t`] CHART_JAC_LINEAR) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN MESON_TAC[LINEAR_0]);;

(* ========================================================================= *)
(* Global existence of parallel fields; MFD_PARALLEL_EXISTS_UNIQUE.          *)
(* ========================================================================= *)

(* Two parallel fields on overlapping subintervals agreeing at one point     *)
(* agree on the overlap.                                                     *)

let GEOT_UNIQUE_ON = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) Z a b a' b' s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        real_interval(a,b) SUBSET J /\ real_interval(a',b') SUBSET J /\
        mfd_parallel atlas g gamma (real_interval(a,b)) Y /\
        mfd_parallel atlas g gamma (real_interval(a',b')) Z /\
        s IN real_interval(a,b) /\ s IN real_interval(a',b') /\ Y s = Z s
        ==> !t. t IN real_interval(a,b) /\ t IN real_interval(a',b') ==> Y t = Z t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `real_interval(a,b) INTER real_interval(a',b') = real_interval(max a a',min b b')`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_INTER] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GEOT_PARALLEL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `gamma:real->A`; `s:real`] THEN
  ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval(max a a',min b b')` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (term_match [] `real_interval(a,b) INTER real_interval(a',b') = s`) (concl th))) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC GEOT_PARALLEL_SUBSET THEN
    EXISTS_TAC `real_interval(a,b)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (term_match [] `real_interval(a,b) INTER real_interval(a',b') = s`) (concl th))) THEN
    SET_TAC[];
    MATCH_MP_TAC GEOT_PARALLEL_SUBSET THEN
    EXISTS_TAC `real_interval(a',b')` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (term_match [] `real_interval(a,b) INTER real_interval(a',b') = s`) (concl th))) THEN
    SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (term_match [] `real_interval(a,b) INTER real_interval(a',b') = s`) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER]]);;

(* Gluing two parallel fields agreeing at a common point. *)

let GEOT_GLUE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) Z a b a' b' s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        real_interval(a,b) SUBSET J /\ real_interval(a',b') SUBSET J /\
        mfd_parallel atlas g gamma (real_interval(a,b)) Y /\
        mfd_parallel atlas g gamma (real_interval(a',b')) Z /\
        s IN real_interval(a,b) /\ s IN real_interval(a',b') /\ Y s = Z s
        ==> mfd_parallel atlas g gamma (real_interval(a,b) UNION real_interval(a',b'))
              (\t. if t IN real_interval(a,b) then Y t else Z t) /\
            (!t. t IN real_interval(a,b)
                 ==> (if t IN real_interval(a,b) then Y t else Z t) = Y t) /\
            (!t. t IN real_interval(a',b')
                 ==> (if t IN real_interval(a,b) then Y t else Z t) = Z t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `Z:real->real^N`; `a:real`; `b:real`; `a':real`; `b':real`; `s:real`]
    GEOT_UNIQUE_ON) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!t. t IN real_interval(a,b)
         ==> (if t IN real_interval(a,b) then (Y:real->real^N) t else Z t) = Y t) /\
    (!t. t IN real_interval(a',b')
         ==> (if t IN real_interval(a,b) then (Y:real->real^N) t else Z t) = Z t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GEOT_PARALLEL_POINTWISE] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [MATCH_MP_TAC GEOT_PARALLEL_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`Y:real->real^N`; `min (t - a) (b - t)`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_REAL_INTERVAL] o
      check (fun th -> concl th = `t IN real_interval(a,b)`)) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t IN real_interval(a,b) ==> (if t IN real_interval(a,b)
              then (Y:real->real^N) t else Z t) = Y t`) (concl th))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [GEOT_PARALLEL_POINTWISE] o
        check (fun th -> aconv (concl th)
          `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) (real_interval(a,b))
                        (Y:real->real^N)`)) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
    MATCH_MP_TAC GEOT_PARALLEL_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`Z:real->real^N`; `min (t - a') (b' - t)`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_REAL_INTERVAL] o
      check (fun th -> concl th = `t IN real_interval(a',b')`)) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!t. t IN real_interval(a',b') ==> (if t IN real_interval(a,b)
              then (Y:real->real^N) t else Z t) = Z t`) (concl th))) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [GEOT_PARALLEL_POINTWISE] o
        check (fun th -> aconv (concl th)
          `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) (real_interval(a',b'))
                        (Z:real->real^N)`)) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL]]]);;

(* Global existence: the set of times covered by a parallel field from t0   *)
(* is open and closed in J.                                                 *)

let GEOT_GLOBAL_EXISTS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t0 (u:real^N).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\ is_realinterval J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t0 IN J
        ==> ?Y. mfd_parallel atlas g gamma J Y /\ Y t0 = u`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `S = {tt | tt IN J /\
             ?a b Y. a < t0 /\ t0 < b /\ a < tt /\ tt < b /\
                     real_interval[a,b] SUBSET J /\
                     mfd_parallel atlas (g:A->real^N^N) (gamma:real->A)
                                  (real_interval(a,b)) Y /\
                     Y t0 = (u:real^N)}` THEN
  SUBGOAL_THEN `!a b. real_interval[a,b] SUBSET J ==> real_interval(a,b) SUBSET J`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `S:real->bool = J` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOT_INTERVAL_CLOPEN THEN EXISTS_TAC `t0:real` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `t0:real`]
        GEOT_LOCAL_EXISTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t0:real`; `u:real^N`]) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `Y:real->real^N` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `Y:real->real^N`] THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "S" THEN SET_TAC[];
      X_GEN_TAC `tt:real` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
          (X_CHOOSE_THEN `Y:real->real^N` STRIP_ASSUME_TAC)))) THEN
      EXISTS_TAC `min (tt - a) (b - tt)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `Y:real->real^N`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `tt:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `tt:real`]
      GEOT_LOCAL_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':real` (X_CHOOSE_THEN `b':real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))))) THEN
    EXISTS_TAC `min (tt - a') (b' - tt)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      (X_CHOOSE_THEN `Y:real->real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `s IN real_interval(a',b')` ASSUME_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP (SPECL [`s:real`; `(Y:real->real^N) s`] th)
      (ASSUME `s IN real_interval(a',b')`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `Z:real->real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                   `Z:real->real^N`; `a:real`; `b:real`; `a':real`; `b':real`; `s:real`]
      GEOT_GLUE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_interval(a,b) UNION real_interval(a',b') =
      real_interval(min a a',max b b')`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~((tt:real) IN S)` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC
     [`min a a'`; `max b b'`;
      `\t. if t IN real_interval(a,b) then (Y:real->real^N) t else Z t`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `a <= b /\ a' <= b'` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(a:real) IN J /\ b IN J /\ a' IN J /\ b' IN J` STRIP_ASSUME_TAC THENL
       [MP_TAC(SET_RULE `!a b x. real_interval[a,b] SUBSET (J:real->bool) /\
                                 x IN real_interval[a,b] ==> x IN J`) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
        REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[REAL_LE_REFL];
        ALL_TAC] THEN
      SUBGOAL_THEN `min a a' IN (J:real->bool) /\ max b b' IN J` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[real_min; real_max] THEN
        CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      UNDISCH_TAC `is_realinterval (J:real->bool)` THEN
      REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`min a a'`; `max b b'`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL]];
    ALL_TAC] THEN
  (* choosing the local fields and gluing them *)
  SUBGOAL_THEN
   `!tt. tt IN J
        ==> ?a b Y. a < t0 /\ t0 < b /\ a < tt /\ tt < b /\
                    real_interval[a,b] SUBSET J /\
                    mfd_parallel atlas (g:A->real^N^N) (gamma:real->A)
                                 (real_interval(a,b)) Y /\
                    Y t0 = (u:real^N)`
  MP_TAC THENL
   [X_GEN_TAC `tt:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(tt:real) IN S` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real->real` (X_CHOOSE_THEN `B:real->real`
    (X_CHOOSE_THEN `YY:real->real->real^N` (LABEL_TAC "yy")))) THEN
  EXISTS_TAC `\t. (YY:real->real->real^N) t t` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[] THEN
    USE_THEN "yy" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(t0:real) IN J`)))] THEN
  ONCE_REWRITE_TAC[GEOT_PARALLEL_POINTWISE] THEN X_GEN_TAC `t1:real` THEN DISCH_TAC THEN
  USE_THEN "yy" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(t1:real) IN J`))) THEN
  MATCH_MP_TAC GEOT_PARALLEL_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`(YY:real->real->real^N) t1`; `min (t1 - A t1) (B t1 - t1)`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `r IN (J:real->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `real_interval[(A:real->real) t1,B t1] SUBSET J` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "yy" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(r:real) IN J`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `(YY:real->real->real^N) r`; `(YY:real->real->real^N) t1`;
                   `(A:real->real) r`; `(B:real->real) r`; `(A:real->real) t1`;
                   `(B:real->real) t1`; `t0:real`] GEOT_UNIQUE_ON) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `t1:real` o GEN_REWRITE_RULE I [GEOT_PARALLEL_POINTWISE] o
      check (fun th -> can (term_match []
        `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A)
           (real_interval((A:real->real) t1,B t1)) ((YY:real->real->real^N) t1)`)
        (concl th))) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REWRITE_TAC[]]);;

let MFD_PARALLEL_EXISTS_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t0 u.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        real_open J /\ is_realinterval J /\
        (!a b. a <= b /\ real_interval[a,b] SUBSET J
               ==> mfd_c1_curve (top,atlas) gamma a b) /\
        t0 IN J
        ==> ?Y. mfd_parallel atlas g gamma J Y /\ Y t0 = u /\
                !Y'. mfd_parallel atlas g gamma J Y' /\ Y' t0 = u
                     ==> !t. t IN J ==> Y' t = Y t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `t0:real`; `u:real^N`]
    GEOT_GLOBAL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `Y:real->real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `Y':real->real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOT_PARALLEL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `gamma:real->A`; `t0:real`] THEN
  ASM_REWRITE_TAC[]);;

