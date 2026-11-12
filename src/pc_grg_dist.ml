(* ========================================================================= *)
(* pc_grg_dist: curves, speed and length, joinable points, the Riemannian    *)
(* distance, balls and the manifold topology, completeness in the           *)
(* Heine-Borel form, scaling of the metric and isometries.  Manifolds are    *)
(* (top,atlas) with smooth_manifold_atlas; metrics g : A -> real^N^N in      *)
(* preferred coordinates (pc_mfd_riem).                                      *)
(* ========================================================================= *)

needs "src/pc_mfd_riem.ml";;
needs "src/pc_mfd_maps.ml";;

prioritize_real();;
type_invention_error := true;;

(* C^1 curves over [a,b]: continuous into the manifold, and C^1 in every     *)
(* chart on the relatively open set of times mapped into the chart, with    *)
(* derivatives within that set (one-sided at the ends).  Unchanged.         *)

let mfd_c1_curve = new_definition
 `mfd_c1_curve (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (gamma:real->A) (a:real) (b:real) <=>
    a <= b /\
    continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
    !c. c IN atlas
        ==> continuously_differentiable 1
              {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN FST c}
              (\s. SND c (gamma(drop s)))`;;

(* Velocity in preferred coordinates, as a derivative within [a,b]: the     *)
(* one-sided velocity at the ends (the two-sided derivative would be junk   *)
(* at the ends).                                                            *)

let mfd_velocity = new_definition
 `mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A)
               (a:real) (b:real) (t:real) =
    vector_derivative (\s. SND (chart_at atlas (gamma t)) (gamma(drop s)))
                      (at (lift t) within interval[lift a,lift b])`;;

(* Speed |gamma'(t)|_g; g is given in preferred coordinates. *)

let mfd_speed = new_definition
 `mfd_speed (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
            (gamma:real->A) (a:real) (b:real) (t:real) =
    sqrt(mfd_velocity atlas gamma a b t dot
         (g(gamma t) ** mfd_velocity atlas gamma a b t))`;;

let mfd_length = new_definition
 `mfd_length (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
             (gamma:real->A) (a:real) (b:real) =
    real_integral (real_interval[a,b]) (mfd_speed atlas g gamma a b)`;;

(* Points joined by a C^1 curve (parametrized by [0,1]).  Unchanged. *)

let mfd_joinable = new_definition
 `mfd_joinable (top:A topology,atlas:((A->bool)#(A->real^N))->bool) x y <=>
    ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
            gamma(&0) = x /\ gamma(&1) = y`;;

(* Riemannian distance; meaningful for joinable points only.  Unchanged. *)

let mfd_dist = new_definition
 `mfd_dist (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
           (g:A->real^N^N) (x:A) (y:A) =
    inf {mfd_length atlas g gamma (&0) (&1) | gamma |
         mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
         gamma(&0) = x /\ gamma(&1) = y}`;;

let mfd_ball = new_definition
 `mfd_ball (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
           (g:A->real^N^N) (x:A) (r:real) =
    {y | mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y < r}`;;

let mfd_cball = new_definition
 `mfd_cball (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
            (g:A->real^N^N) (x:A) (r:real) =
    {y | mfd_joinable (top,atlas) x y /\ mfd_dist (top,atlas) g x y <= r}`;;

(* Completeness in the Heine-Borel form: closed metric balls are compact     *)
(* (written with mfd_cball).  Equivalent to completeness of the metric space *)
(* of every joinable class by Hopf-Rinow; the easy direction is              *)
(* MFD_COMPLETE_IMP_MCOMPLETE.                                               *)

let mfd_complete = new_definition
 `mfd_complete (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (g:A->real^N^N) <=>
    !x r. x IN topspace top ==> compact_in top (mfd_cball (top,atlas) g x r)`;;

(* The metric space (metric.ml) of the joinable class of x. *)

let mfd_metric = new_definition
 `mfd_metric (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
             (g:A->real^N^N) (x:A) =
    metric({y | mfd_joinable (top,atlas) x y},
           \(y,z). mfd_dist (top,atlas) g y z)`;;

(* Isometries (f,f') from (top,atlas,g) onto (top',atlas',g'): a           *)
(* diffeomorphism (mfd_diffeo of pc_mfd_maps, on the whole spaces) with g   *)
(* the pullback of g' in every chart pair (mpullback of pc_lrg).            *)

let mfd_isometry = new_definition
 `mfd_isometry (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
               (g:A->real^N^N)
               (top':B topology,atlas':((B->bool)#(B->real^N))->bool)
               (g':B->real^N^N) (f:A->B) (f':B->A) <=>
    mfd_diffeo top atlas (topspace top) top' atlas' (topspace top') f f' /\
    !c c'. c IN atlas /\ c' IN atlas'
           ==> !y. y IN IMAGE (SND c) {x | x IN FST c /\ f x IN FST c'}
                   ==> metric_local atlas c g y =
                       mpullback (SND c' o f o chart_inv c)
                                 (metric_local atlas' c' g') y`;;

(* ------------------------------------------------------------------------- *)
(* Curves: basic facts.                                                      *)
(* ------------------------------------------------------------------------- *)

let MFD_C1_CURVE_IN_TOPSPACE = prove
 (`!top atlas (gamma:real->A) a b t.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
        t IN real_interval[a,b]
        ==> gamma t IN topspace top`,
  REWRITE_TAC[mfd_c1_curve; continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  MESON_TAC[]);;

let MFD_C1_CURVE_CONST = prove
 (`!top atlas (x:A) a b.
        x IN topspace top /\ a <= b
        ==> mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool)
                         (\t. x) a b`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mfd_c1_curve; CONTINUOUS_MAP_CONST] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\(s:real^1) (h:real^1). vec 0:real^N` THEN BETA_TAC THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; CONTINUOUS_ON_CONST]);;

(* C^1 on an arbitrary set depends only on the values on the set. *)

let GRGD_C1_EQ = prove
 (`!s (f:real^M->real^N) g.
        (!x. x IN s ==> f x = g x) /\ continuously_differentiable 1 s f
        ==> continuously_differentiable 1 s g`,
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `f':real^M->real^M->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

let GRGD_IN_INTERVAL_LIFT = prove
 (`!a b t. lift t IN interval[lift a,lift b] <=> t IN real_interval[a,b]`,
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; IN_REAL_INTERVAL]);;

let GRGD_DROP_IN_REAL_INTERVAL = prove
 (`!a b s. s IN interval[lift a,lift b] ==> drop s IN real_interval[a,b]`,
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; IN_REAL_INTERVAL]);;

let MFD_C1_CURVE_EQ = prove
 (`!top atlas (gamma:real->A) gamma' a b.
        (!t. t IN real_interval[a,b] ==> gamma t = gamma' t)
        ==> (mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b <=>
             mfd_c1_curve (top,atlas) gamma' a b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s IN interval[lift a,lift b] ==> (gamma:real->A)(drop s) = gamma'(drop s)`
  ASSUME_TAC THENL [ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[mfd_c1_curve] THEN
  SUBGOAL_THEN
   `!c:(A->bool)#(A->real^N).
        {s | s IN interval[lift a,lift b] /\ (gamma:real->A)(drop s) IN FST c} =
        {s | s IN interval[lift a,lift b] /\ gamma'(drop s) IN FST c}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p <=> p') /\ (q <=> q') ==> (r /\ p /\ q <=> r /\ p' /\ q')`) THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THENL
     [EXISTS_TAC `gamma:real->A`; EXISTS_TAC `gamma':real->A`] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN ASM_MESON_TAC[];
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN
    DISCH_TAC THEN MATCH_MP_TAC GRGD_C1_EQ THENL
     [EXISTS_TAC `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
      EXISTS_TAC `\s. SND (c:(A->bool)#(A->real^N)) ((gamma':real->A)(drop s))`] THEN
    ASM_SIMP_TAC[IN_ELIM_THM]]);;

let GRGD_VECTOR_DERIVATIVE_EQ = prove
 (`!(f:real^1->real^N) g x s.
        x IN s /\ (!y. y IN s ==> f y = g y)
        ==> vector_derivative f (at x within s) =
            vector_derivative g (at x within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_derivative] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^N` THEN
  EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THENL
   [EXISTS_TAC `f:real^1->real^N`; EXISTS_TAC `g:real^1->real^N`] THEN
  EXISTS_TAC `&1` THEN ASM_SIMP_TAC[REAL_LT_01]);;

let MFD_LENGTH_EQ = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) gamma' a b.
        (!t. t IN real_interval[a,b] ==> gamma t = gamma' t)
        ==> mfd_length atlas g gamma a b = mfd_length atlas g gamma' a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_speed; mfd_velocity] THEN
  SUBGOAL_THEN `(gamma:real->A) t = gamma' t` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\s. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma':real->A) t))
               ((gamma:real->A)(drop s)))
      (at (lift t) within interval[lift a,lift b]) =
    vector_derivative (\s. SND (chart_at atlas (gamma' t)) (gamma'(drop s)))
      (at (lift t) within interval[lift a,lift b])`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_EQ THEN
  ASM_REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN
  ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]);;

(* The times at which a curve lies in an open set are relatively open. *)

let GRGD_CURVE_CONTINUOUS = prove
 (`!top atlas (gamma:real->A) a b.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b
        ==> continuous_map (subtopology euclidean (interval[lift a,lift b]),top)
                           (gamma o drop)`,
  REWRITE_TAC[mfd_c1_curve] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_REWRITE_TAC[GSYM CONTINUOUS_MAP_DROP_EQ_GEN]);;

let GRGD_CURVE_TIMES_OPEN_IN = prove
 (`!top atlas (gamma:real->A) a b W.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
        open_in top W
        ==> open_in (subtopology euclidean (interval[lift a,lift b]))
                    {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN W}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP GRGD_CURVE_CONTINUOUS) THEN
  DISCH_THEN(MP_TAC o SPEC `W:A->bool` o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] OPEN_IN_CONTINUOUS_MAP_PREIMAGE)) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM]);;

let GRGD_CURVE_TIMES_BALL = prove
 (`!top atlas (gamma:real->A) a b W t.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
        open_in top W /\ t IN real_interval[a,b] /\ gamma t IN W
        ==> ?d. &0 < d /\
                !s. s IN interval[lift a,lift b] /\ dist(s,lift t) < d
                    ==> gamma(drop s) IN W`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `W:A->bool`]
                GRGD_CURVE_TIMES_OPEN_IN) THEN
  ASM_REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `lift t` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_BALL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[DIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Chart velocities of C^1 curves, chart independence of the speed, its      *)
(* positivity and continuity, positivity of length.                          *)
(* ------------------------------------------------------------------------- *)

let GRGD_ATLAS_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> open_in top (FST c) /\ open (IMAGE (SND c) (FST c)) /\
            FST c SUBSET topspace top`,
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET]);;

let GRGD_HAS_DERIVATIVE_VECTOR = prove
 (`!(f:real^1->real^N) f' net.
        (f has_derivative f') net ==> (f has_vector_derivative f'(vec 1)) net`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  SUBGOAL_THEN `(\h:real^1. drop h % (f':real^1->real^N)(vec 1)) = f'`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_DROP]);;

let GRGD_VECTOR_DERIVATIVE_CHAIN = prove
 (`!(f:real^1->real^M) (g:real^M->real^N) f' g' x s.
        (f has_vector_derivative f') (at x within s) /\
        (g has_derivative g') (at (f x))
        ==> ((g o f) has_vector_derivative g' f') (at x within s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[has_vector_derivative]) THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN
   `(\h:real^1. drop h % (g':real^M->real^N) f') = g' o (\h. drop h % f')`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[LINEAR_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN]);;

(* A C^1 curve has a derivative within [a,b] in every chart at every time  *)
(* it spends in the chart domain.                                            *)

let GRGD_C1_CHART_HAS_VD = prove
 (`!top atlas (gamma:real->A) a b (c:(A->bool)#(A->real^N)) t.
        smooth_manifold_atlas top atlas /\ mfd_c1_curve (top,atlas) gamma a b /\
        c IN atlas /\ t IN real_interval[a,b] /\ gamma t IN FST c
        ==> ((\s. SND c (gamma(drop s))) has_vector_derivative
             vector_derivative (\s. SND c (gamma(drop s)))
               (at (lift t) within interval[lift a,lift b]))
            (at (lift t) within interval[lift a,lift b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS; differentiable] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1
      {s | s IN interval[lift a,lift b] /\ (gamma:real->A)(drop s) IN FST c}
      (\s. SND (c:(A->bool)#(A->real^N)) (gamma(drop s)))`
  MP_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N`
    (MP_TAC o SPEC `lift t` o CONJUNCT1)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
  DISCH_TAC THEN EXISTS_TAC `(f':real^1->real^1->real^N) (lift t)` THEN
  MP_TAC(ISPECL
   [`\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
    `(f':real^1->real^1->real^N) (lift t)`; `lift t`;
    `{s | s IN interval[lift a,lift b] /\
          (gamma:real->A)(drop s) IN FST (c:(A->bool)#(A->real^N))}`;
    `interval[lift a,lift b]`] HAS_DERIVATIVE_WITHIN_OPEN_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
    MATCH_MP_TAC GRGD_CURVE_TIMES_OPEN_IN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    DISCH_THEN(fun th -> ASM_MESON_TAC[th])]);;

(* For a < b the chart velocity is continuous on the times in the chart. *)

let GRGD_C1_CHART_VD_CONTINUOUS = prove
 (`!top atlas (gamma:real->A) a b (c:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\ mfd_c1_curve (top,atlas) gamma a b /\
        c IN atlas /\ a < b
        ==> (\s. vector_derivative (\s. SND c (gamma(drop s)))
                   (at s within interval[lift a,lift b])) continuous_on
            {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN FST c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable 1
      {s | s IN interval[lift a,lift b] /\ (gamma:real->A)(drop s) IN FST c}
      (\s. SND (c:(A->bool)#(A->real^N)) (gamma(drop s)))`
  MP_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\s. (f':real^1->real^1->real^N) s (vec 1)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  CONV_TAC SYM_CONV THEN BETA_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGD_HAS_DERIVATIVE_VECTOR THEN REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL
   [`\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
    `(f':real^1->real^1->real^N) s`; `s:real^1`;
    `{s | s IN interval[lift a,lift b] /\
          (gamma:real->A)(drop s) IN FST (c:(A->bool)#(A->real^N))}`;
    `interval[lift a,lift b]`] HAS_DERIVATIVE_WITHIN_OPEN_IN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_CURVE_TIMES_OPEN_IN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_MESON_TAC[GRGD_ATLAS_CHART];
    DISCH_THEN(fun th -> ASM_MESON_TAC[th])]);;

(* Chart velocities transform by the transition Jacobian. *)

let GRGD_VELOCITY_TRANS = prove
 (`!top atlas (gamma:real->A) a b U (phi:A->real^N) V psi t.
        smooth_manifold_atlas top atlas /\ mfd_c1_curve (top,atlas) gamma a b /\
        a < b /\ (U,phi) IN atlas /\ (V,psi) IN atlas /\
        t IN real_interval[a,b] /\ gamma t IN U INTER V
        ==> vector_derivative (\s. psi(gamma(drop s)))
              (at (lift t) within interval[lift a,lift b]) =
            chart_jac (U,phi) (V,psi) (gamma t)
              (vector_derivative (\s. phi(gamma(drop s)))
                 (at (lift t) within interval[lift a,lift b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC `chart_trans (U:A->bool,phi:A->real^N) (V,psi) o
              (\s. phi((gamma:real->A)(drop s)))` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `U:A->bool`; `t:real`]
                GRGD_CURVE_TIMES_BALL) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; IN_INTER]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    BETA_TAC THEN MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `a:real`; `b:real`;
                     `(U:A->bool,phi:A->real^N)`; `t:real`]
                    GRGD_C1_CHART_HAS_VD) THEN
      ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM SET_TAC[];
      BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

let GRGD_QUAD_CONGR = prove
 (`!J:real^N->real^N (G:real^N^N) w.
        linear J
        ==> J w dot (G ** J w) = w dot ((transp(matrix J) ** G ** matrix J) ** w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

(* The speed computed in any chart containing gamma(t). *)

let MFD_SPEED_CHART = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t U phi.
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
        t IN real_interval[a,b] /\ (U,phi) IN atlas /\ gamma t IN U
        ==> mfd_speed atlas g gamma a b t =
            sqrt(vector_derivative (\s. phi(gamma(drop s)))
                   (at (lift t) within interval[lift a,lift b]) dot
                 (metric_local atlas (U,phi) g (phi(gamma t)) **
                  vector_derivative (\s. phi(gamma(drop s)))
                   (at (lift t) within interval[lift a,lift b])))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_speed; mfd_velocity; metric_local] THEN BETA_TAC THEN
  ASM_REWRITE_TAC[SND] THEN
  SUBGOAL_THEN
   `chart_inv (U:A->bool,phi:A->real^N) (phi((gamma:real->A) t)) = gamma t`
  SUBST1_TAC THENL [ASM_MESON_TAC[CHART_INV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `U:A->bool`;
                 `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `t:real`]
                GRGD_VELOCITY_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC GRGD_QUAD_CONGR THEN
  MATCH_MP_TAC CHART_JAC_LINEAR THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let MFD_SPEED_POS_LE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ t IN real_interval[a,b]
        ==> &0 <= mfd_speed atlas g gamma a b t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_speed] THEN MATCH_MP_TAC SQRT_POS_LE THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`] RIEMANNIAN_METRIC_POS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    SPEC `mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b t` o
    CONJUNCT2) THEN
  ASM_CASES_TAC
   `mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b t = vec 0` THEN
  ASM_SIMP_TAC[DOT_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE]);;

(* On the times spent in one chart the speed is given by a continuous       *)
(* chart formula.                                                            *)

let GRGD_SPEED_CONTINUOUS_CHART = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b U phi.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b /\ (U,phi) IN atlas
        ==> (lift o mfd_speed atlas g gamma a b o drop) continuous_on
            {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN U}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `\s. lift(sqrt(vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
                    (at s within interval[lift a,lift b]) dot
                  (metric_local atlas (U,phi) (g:A->real^N^N) (phi(gamma(drop s))) **
                   vector_derivative (\s. phi(gamma(drop s)))
                    (at s within interval[lift a,lift b]))))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                   `drop s`; `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
    ASM_SIMP_TAC[LIFT_DROP; GRGD_DROP_IN_REAL_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`;
                 `(U:A->bool,phi:A->real^N)`] GRGD_C1_CHART_VD_CONTINUOUS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o
    (\s. metric_local atlas (U,phi) (g:A->real^N^N)
           ((phi:A->real^N)((gamma:real->A)(drop s)))) =
    (vectorize o metric_local atlas (U,phi) g) o (\s. phi(gamma(drop s)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    EXISTS_TAC `1` THEN
    FIRST_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)` o CONJUNCT2 o
      CONJUNCT2 o GEN_REWRITE_RULE I [mfd_c1_curve]) THEN
    ASM_REWRITE_TAC[FST; SND];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      RULE_ASSUM_TAC(REWRITE_RULE[riemannian_metric; metric_field]) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
      ASM_REWRITE_TAC[FST; SND] THEN MESON_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[FUN_IN_IMAGE]]]);;

let MFD_SPEED_CONTINUOUS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b
        ==> (mfd_speed atlas g gamma a b) real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[INTERVAL_SING; CONTINUOUS_ON_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_c1_curve; REAL_LT_LE]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(gamma:real->A)(drop s) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE; GRGD_DROP_IN_REAL_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A)(drop s)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                         ((gamma:real->A)(drop s))` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `U:A->bool`; `phi:A->real^N`] GRGD_SPEED_CONTINUOUS_CHART) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^1`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CONTINUOUS_WITHIN_OPEN_IN THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC GRGD_CURVE_TIMES_OPEN_IN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART]);;

let GRGD_SPEED_INTEGRABLE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b
        ==> (mfd_speed atlas g gamma a b) real_integrable_on real_interval[a,b]`,
  MESON_TAC[REAL_INTEGRABLE_CONTINUOUS; MFD_SPEED_CONTINUOUS]);;

let MFD_LENGTH_POS_LE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b
        ==> &0 <= mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  ASM_MESON_TAC[GRGD_SPEED_INTEGRABLE; MFD_SPEED_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Reparametrization, reversal, restriction and gluing of C^1 curves.        *)
(* ------------------------------------------------------------------------- *)

let GRGD_CONTINUOUS_MAP_REAL = prove
 (`!h s. continuous_map (subtopology euclideanreal s,euclideanreal) h <=>
         h real_continuous_on s`,
  REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; CONTINUOUS_MAP_EQ_LIFT;
              CONTINUOUS_MAP_EUCLIDEAN; REAL_CONTINUOUS_ON] THEN
  REWRITE_TAC[o_ASSOC]);;

let GRGD_REAL_DERIV_LIFT = prove
 (`!h h' t c d.
        (h has_real_derivative h') (atreal t within real_interval[c,d])
        ==> ((lift o h o drop) has_vector_derivative lift h')
            (at (lift t) within interval[lift c,lift d])`,
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; IMAGE_LIFT_REAL_INTERVAL]);;

let GRGD_REPARAM_CONTINUOUS = prove
 (`!h c d a b.
        (!s. s IN real_interval[c,d]
             ==> h s IN real_interval[a,b] /\ h real_differentiable
                 (atreal s within real_interval[c,d]))
        ==> continuous_map (subtopology euclideanreal (real_interval[c,d]),
                            subtopology euclideanreal (real_interval[a,b])) h /\
            h real_continuous_on real_interval[c,d]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `h real_continuous_on real_interval[c,d]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[real_differentiable_on] THEN
    ASM_MESON_TAC[real_differentiable];
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; GRGD_CONTINUOUS_MAP_REAL;
                    TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM SET_TAC[]]);;

(* The chart clause of a reparametrized curve. *)

let GRGD_C1_REPARAM_CHART = prove
 (`!top atlas (gamma:real->A) a b h h' c d (k:(A->bool)#(A->real^N)).
        mfd_c1_curve (top,atlas) gamma a b /\ k IN atlas /\
        (!s. s IN real_interval[c,d]
             ==> h s IN real_interval[a,b] /\
                 (h has_real_derivative h' s) (atreal s within real_interval[c,d])) /\
        h' real_continuous_on real_interval[c,d]
        ==> continuously_differentiable 1
              {s | s IN interval[lift c,lift d] /\ gamma(h(drop s)) IN FST k}
              (\s. SND k (gamma(h(drop s))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:(A->bool)#(A->real^N)` o CONJUNCT2 o
    CONJUNCT2 o GEN_REWRITE_RULE I [mfd_c1_curve]) THEN
  ASM_REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^1->real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(\s. SND (k:(A->bool)#(A->real^N)) ((gamma:real->A)(h(drop s)))) =
    (\s. SND k (gamma(drop s))) o (lift o h o drop)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (lift o h o drop)
      {s | s IN interval[lift c,lift d] /\ (gamma:real->A)(h(drop s)) IN FST k}
    SUBSET {s | s IN interval[lift a,lift b] /\
                gamma(drop s) IN FST (k:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM; LIFT_DROP] THEN
    REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN
    ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lift o h o drop) continuous_on interval[lift c,lift d] /\
    (lift o h' o drop) continuous_on interval[lift c,lift d]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; GSYM REAL_CONTINUOUS_ON] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[real_differentiable_on; real_differentiable] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\x. (f':real^1->real^1->real^N) (lift(h(drop x))) o
        (\v. drop v % lift(h'(drop x)))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[lift c,lift d]` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      REWRITE_TAC[GSYM has_vector_derivative] THEN
      MP_TAC(ISPECL [`h:real->real`; `(h':real->real)(drop x)`; `drop x`;
                     `c:real`; `d:real`] GRGD_REAL_DERIV_LIFT) THEN
      ASM_SIMP_TAC[LIFT_DROP; GRGD_DROP_IN_REAL_INTERVAL];
      REWRITE_TAC[o_THM] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC
       `{s | s IN interval[lift a,lift b] /\
             (gamma:real->A)(drop s) IN FST (k:(A->bool)#(A->real^N))}` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
      ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]];
    X_GEN_TAC `v:real^1` THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC
     `\x. (drop v * h'(drop x)) %
          (f':real^1->real^1->real^N) (lift(h(drop x))) (vec 1)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN
       `linear((f':real^1->real^1->real^N) (lift(h(drop x))))`
      ASSUME_TAC THENL
       [SUBGOAL_THEN
         `lift(h(drop x)) IN
          {s | s IN interval[lift a,lift b] /\
               (gamma:real->A)(drop s) IN FST (k:(A->bool)#(A->real^N))}`
        MP_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
          ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
          ASM_MESON_TAC[has_derivative]];
        SUBGOAL_THEN `lift((h':real->real)(drop x)) = h'(drop x) % vec 1`
        SUBST1_TAC THENL [REWRITE_TAC[LIFT_EQ_CMUL]; ALL_TAC] THEN
        ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_ASSOC]];
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[lift c,lift d]` THEN
        CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
        UNDISCH_TAC `(lift o h' o drop) continuous_on interval[lift c,lift d]` THEN
        REWRITE_TAC[o_DEF];
        SUBGOAL_THEN
         `(\x. (f':real^1->real^1->real^N) (lift(h(drop x))) (vec 1)) =
          (\y. f' y (vec 1)) o (lift o h o drop)`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `interval[lift c,lift d]` THEN ASM_REWRITE_TAC[] THEN
          SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC
           `{s | s IN interval[lift a,lift b] /\
                 (gamma:real->A)(drop s) IN FST (k:(A->bool)#(A->real^N))}` THEN
          ASM_REWRITE_TAC[]]]]]);;

let GRGD_C1_CURVE_REPARAM = prove
 (`!top atlas (gamma:real->A) a b h h' c d.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
        c <= d /\
        (!s. s IN real_interval[c,d]
             ==> h s IN real_interval[a,b] /\
                 (h has_real_derivative h' s) (atreal s within real_interval[c,d])) /\
        h' real_continuous_on real_interval[c,d]
        ==> mfd_c1_curve (top,atlas) (gamma o h) c d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_c1_curve] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclideanreal (real_interval[a,b])` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`h:real->real`; `c:real`; `d:real`; `a:real`; `b:real`]
                    GRGD_REPARAM_CONTINUOUS) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[real_differentiable]; SIMP_TAC[]];
      ASM_MESON_TAC[mfd_c1_curve]];
    X_GEN_TAC `k:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC GRGD_C1_REPARAM_CHART THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `a:real`; `b:real`; `h':real->real`] THEN
    ASM_REWRITE_TAC[]]);;

let GRGD_VELOCITY_REPARAM = prove
 (`!top atlas (gamma:real->A) a b h h' c d s.
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b /\
        c < d /\
        (!s. s IN real_interval[c,d]
             ==> h s IN real_interval[a,b] /\
                 (h has_real_derivative h' s) (atreal s within real_interval[c,d])) /\
        s IN real_interval[c,d]
        ==> mfd_velocity atlas (gamma o h) c d s =
            h' s % mfd_velocity atlas gamma a b (h s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_velocity; o_THM] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT] THEN
  SUBGOAL_THEN `(h:real->real) s IN real_interval[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)((h:real->real) s) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A)((h:real->real) s)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\u. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                       ((gamma:real->A)((h:real->real) s))) (gamma(h(drop u)))) =
    (\u. SND (chart_at atlas (gamma(h s))) (gamma(drop u))) o (lift o h o drop)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`lift o (h:real->real) o drop`;
    `\u. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                       ((gamma:real->A)((h:real->real) s))) (gamma(drop u))`;
    `lift((h':real->real) s)`;
    `vector_derivative
      (\u. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                         ((gamma:real->A)((h:real->real) s))) (gamma(drop u)))
      (at (lift(h s)) within interval[lift a,lift b])`;
    `interval[lift c,lift d]`; `lift s`] VECTOR_DIFF_CHAIN_WITHIN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_REAL_DERIV_LIFT THEN ASM_SIMP_TAC[];
    REWRITE_TAC[o_THM; LIFT_DROP] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift a,lift b]` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `a:real`; `b:real`;
                     `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                               ((gamma:real->A)((h:real->real) s))`;
                     `(h:real->real) s`] GRGD_C1_CHART_HAS_VD) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; LIFT_DROP] THEN
      REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN
      ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]]]);;

let GRGD_SPEED_REPARAM = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b h h' c d s.
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas) gamma a b /\ c < d /\
        (!s. s IN real_interval[c,d]
             ==> h s IN real_interval[a,b] /\
                 (h has_real_derivative h' s) (atreal s within real_interval[c,d])) /\
        s IN real_interval[c,d]
        ==> mfd_speed atlas g (gamma o h) c d s =
            abs(h' s) * mfd_speed atlas g gamma a b (h s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_speed] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `h:real->real`;
                 `h':real->real`; `c:real`; `d:real`; `s:real`]
                GRGD_VELOCITY_REPARAM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_THM; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS]);;

let MFD_LENGTH_REPARAM = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b h h' c d.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ c <= d /\
        h c = a /\ h d = b /\
        (!s. s IN real_interval[c,d]
             ==> h s IN real_interval[a,b] /\ &0 <= h' s /\
                 (h has_real_derivative h' s) (atreal s within real_interval[c,d])) /\
        h' real_continuous_on real_interval[c,d]
        ==> mfd_c1_curve (top,atlas) (gamma o h) c d /\
            mfd_length atlas g (gamma o h) c d = mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `h':real->real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `c:real = d` THENL
   [SUBGOAL_THEN `a:real = b` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `c < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mfd_length] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[c,d])
      (\s. mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b (h s) * h' s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                   `h:real->real`; `h':real->real`; `c:real`; `d:real`; `s:real`]
                  GRGD_SPEED_REPARAM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `abs((h':real->real) s) = h' s` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_REFL]; REWRITE_TAC[REAL_MUL_SYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b`;
                 `h:real->real`; `h':real->real`; `c:real`; `d:real`;
                 `a:real`; `b:real`; `{c:real,d}`] REAL_INTEGRAL_SUBSTITUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[COUNTABLE_INSERT; COUNTABLE_EMPTY] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MFD_SPEED_CONTINUOUS];
    MP_TAC(ISPECL [`h:real->real`; `c:real`; `d:real`; `a:real`; `b:real`]
                  GRGD_REPARAM_CONTINUOUS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[real_differentiable]; SIMP_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `s IN real_interval(c,d)` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real->real`; `(h':real->real) s`; `s:real`;
                   `real_interval(c,d)`] HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
    ASM_REWRITE_TAC[REAL_OPEN_REAL_INTERVAL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[c,d]` THEN
    ASM_SIMP_TAC[REAL_INTERVAL_OPEN_SUBSET_CLOSED]]);;

(* Reversal t -> a + b - t. *)

let GRGD_HAS_REAL_INTEGRAL_REVERSE_IMP = prove
 (`!f a b i.
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(a + b - x)) has_real_integral i) (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `i:real`; `a:real`; `b:real`; `-- &1`;
                 `a + b:real`] HAS_REAL_INTEGRAL_AFFINITY) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  SUBGOAL_THEN `(\x. f(-- &1 * x + a + b)) = (\x. (f:real->real)(a + b - x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_INV_1; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_INV_NEG; REAL_INV_1] THEN
  SUBGOAL_THEN `(\x. -- &1 * (x - (a + b))) = (\x. -- &1 * x + (a + b))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_AFFINITY_REAL_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `~(&0 <= -- &1)`] THEN
  SUBGOAL_THEN
   `real_interval[-- &1 * b + a + b,-- &1 * a + a + b] = real_interval[a,b]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[]]);;

let GRGD_REAL_INTEGRAL_REVERSE = prove
 (`!f a b. real_integral (real_interval[a,b]) (\x. f(a + b - x)) =
           real_integral (real_interval[a,b]) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_integral] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:real` THEN EQ_TAC THEN
  REWRITE_TAC[GRGD_HAS_REAL_INTEGRAL_REVERSE_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GRGD_HAS_REAL_INTEGRAL_REVERSE_IMP) THEN
  BETA_TAC THEN REWRITE_TAC[REAL_ARITH `a + b - (a + b - x) = x`; ETA_AX]);;

let GRGD_REVERSE_DERIV = prove
 (`!a b s t. ((\x. a + b - x) has_real_derivative -- &1) (atreal s within t)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `-- &1 = &0 + (&0 - &1)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID]);;

let MFD_LENGTH_REVERSE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ mfd_c1_curve (top,atlas) gamma a b
        ==> mfd_c1_curve (top,atlas) (\t. gamma(a + b - t)) a b /\
            mfd_length atlas g (\t. gamma(a + b - t)) a b =
            mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\t. (gamma:real->A)(a + b - t)) = gamma o (\t. a + b - t)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[a,b]
        ==> (\t. a + b - t) s IN real_interval[a,b] /\
            ((\t. a + b - t) has_real_derivative (\t:real. -- &1) s)
            (atreal s within real_interval[a,b])`
  ASSUME_TAC THENL
   [REWRITE_TAC[GRGD_REVERSE_DERIV; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `\t:real. -- &1`] THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mfd_length] THEN
  TRANS_TAC EQ_TRANS
   `real_integral (real_interval[a,b])
      (\s. mfd_speed atlas (g:A->real^N^N) (gamma:real->A) a b (a + b - s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                   `\t:real. a + b - t`; `\t:real. -- &1`; `a:real`; `b:real`;
                   `s:real`] GRGD_SPEED_REPARAM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_MUL_LID];
    REWRITE_TAC[GRGD_REAL_INTEGRAL_REVERSE; ETA_AX]]);;

(* Restriction to a subinterval. *)

let GRGD_C1_CURVE_SUBINTERVAL = prove
 (`!top atlas (gamma:real->A) a c p q.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a c /\
        a <= p /\ p <= q /\ q <= c
        ==> mfd_c1_curve (top,atlas) gamma p q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `c:real`; `\t:real. t`;
                 `\t:real. &1`; `p:real`; `q:real`] GRGD_C1_CURVE_REPARAM) THEN
  SUBGOAL_THEN `(gamma:real->A) o (\t. t) = gamma` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; REAL_CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC);;

let GRGD_LENGTH_SUBINTERVAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a c p q.
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas) gamma a c /\
        a <= p /\ p <= q /\ q <= c
        ==> mfd_length atlas g gamma p q =
            real_integral (real_interval[p,q]) (mfd_speed atlas g gamma a c)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `p:real = q` THENL
   [ASM_REWRITE_TAC[mfd_length; REAL_INTEGRAL_REFL]; ALL_TAC] THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_EQ THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `c:real`;
                 `\t:real. t`; `\t:real. &1`; `p:real`; `q:real`; `s:real`]
                GRGD_SPEED_REPARAM) THEN
  SUBGOAL_THEN `(gamma:real->A) o (\t. t) = gamma` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID]]);;

let MFD_LENGTH_COMBINE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a c /\ a <= b /\ b <= c
        ==> mfd_c1_curve (top,atlas) gamma a b /\
            mfd_c1_curve (top,atlas) gamma b c /\
            mfd_length atlas g gamma a c =
            mfd_length atlas g gamma a b + mfd_length atlas g gamma b c`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `c:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `c:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_length atlas (g:A->real^N^N) (gamma:real->A) a c =
      real_integral (real_interval[a,c]) (mfd_speed atlas g gamma a c) /\
    mfd_length atlas g gamma a b =
      real_integral (real_interval[a,b]) (mfd_speed atlas g gamma a c) /\
    mfd_length atlas g gamma b c =
      real_integral (real_interval[b,c]) (mfd_speed atlas g gamma a c)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC GRGD_LENGTH_SUBINTERVAL THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GRGD_SPEED_INTEGRABLE]);;

(* Gluing two C^1 pieces with equal one-sided velocities at the joint. *)

let GRGD_HAS_DERIVATIVE_WITHIN_UNION = prove
 (`!(f:real^M->real^N) f' x s t.
        (f has_derivative f') (at x within s) /\
        (f has_derivative f') (at x within t)
        ==> (f has_derivative f') (at x within (s UNION t))`,
  SIMP_TAC[has_derivative_within; LIM_WITHIN_UNION]);;

let GRGD_HAS_DERIVATIVE_TRIVIAL = prove
 (`!(f:real^M->real^N) f' net.
        trivial_limit net /\ linear f' ==> (f has_derivative f') net`,
  SIMP_TAC[has_derivative; LIM_TRIVIAL]);;

let GRGD_C1_CHART_FPRIME = prove
 (`!top atlas (gamma:real->A) a b (k:(A->bool)#(A->real^N)) f' x.
        smooth_manifold_atlas top atlas /\ mfd_c1_curve (top,atlas) gamma a b /\
        k IN atlas /\ a < b /\
        x IN {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN FST k} /\
        ((\s. SND k (gamma(drop s))) has_derivative f')
          (at x within {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN FST k})
        ==> f' = (\h. drop h % vector_derivative (\s. SND k (gamma(drop s)))
                                 (at x within interval[lift a,lift b]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\s. SND (k:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) has_derivative f')
    (at x within interval[lift a,lift b])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\s. SND (k:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
      `f':real^1->real^N`; `x:real^1`;
      `{s | s IN interval[lift a,lift b] /\
            (gamma:real->A)(drop s) IN FST (k:(A->bool)#(A->real^N))}`;
      `interval[lift a,lift b]`] HAS_DERIVATIVE_WITHIN_OPEN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GRGD_CURVE_TIMES_OPEN_IN THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_MESON_TAC[GRGD_ATLAS_CHART];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative (\s. SND (k:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))
      (at x within interval[lift a,lift b]) = (f':real^1->real^N)(vec 1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC GRGD_HAS_DERIVATIVE_VECTOR THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM LIFT_EQ_CMUL; LIFT_DROP]);;

let GRGD_JOIN_CONTINUOUS = prove
 (`!top (gamma:real->A) a b c.
        continuous_map (subtopology euclideanreal (real_interval[a,b]),top) gamma /\
        continuous_map (subtopology euclideanreal (real_interval[b,c]),top) gamma /\
        a <= b /\ b <= c
        ==> continuous_map (subtopology euclideanreal (real_interval[a,c]),top) gamma`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) = (\x. if x <= b then gamma x else gamma x)`
   (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
   [REWRITE_TAC[COND_ID; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID;
           CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
  SUBGOAL_THEN
   `real_interval[a,c] INTER {x | x IN real_interval[a,c] /\ x <= b} =
    real_interval[a,b] /\
    real_interval[a,c] INTER {x | x IN real_interval[a,c] /\ b <= x} =
    real_interval[b,c]`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ASM_REAL_ARITH_TAC);;

let GRGD_JOIN_FPRIME_EQ = prove
 (`!top atlas (gamma:real->A) a b c (k:(A->bool)#(A->real^N)) f1 f2.
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas) gamma a b /\
        mfd_c1_curve (top,atlas) gamma b c /\ a < b /\ b < c /\
        mfd_velocity atlas gamma a b b = mfd_velocity atlas gamma b c b /\
        k IN atlas /\ gamma b IN FST k /\
        ((\s. SND k (gamma(drop s))) has_derivative f1)
          (at (lift b) within
           {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN FST k}) /\
        ((\s. SND k (gamma(drop s))) has_derivative f2)
          (at (lift b) within
           {s | s IN interval[lift b,lift c] /\ gamma(drop s) IN FST k})
        ==> f1 = f2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `k:(A->bool)#(A->real^N)`;
                 `f1:real^1->real^N`; `lift b`] GRGD_C1_CHART_FPRIME) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `b:real`; `c:real`; `k:(A->bool)#(A->real^N)`;
                 `f2:real^1->real^N`; `lift b`] GRGD_C1_CHART_FPRIME) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GRGD_IN_INTERVAL_LIFT;
                  IN_REAL_INTERVAL; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) b IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE; IN_REAL_INTERVAL; REAL_LE_REFL;
                  REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) b`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_velocity]) THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) b)`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SND]) THEN
  MP_TAC(ISPEC `k:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  REWRITE_TAC[SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `U:A->bool`;
                 `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `b:real`]
                GRGD_VELOCITY_TRANS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `b:real`; `c:real`; `U:A->bool`;
                 `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `b:real`]
                GRGD_VELOCITY_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let GRGD_NOT_LIMPT_INTERVAL = prove
 (`!(x:real^N) s a b. s SUBSET interval[a,b] /\ ~(x IN interval[a,b])
                     ==> trivial_limit (at x within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) limit_point_of interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[LIMPT_SUBSET];
    ASM_MESON_TAC[CLOSED_LIMPT; CLOSED_INTERVAL]]);;

let GRGD_JOIN_CHART = prove
 (`!top atlas (gamma:real->A) a b c (k:(A->bool)#(A->real^N)).
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas) gamma a b /\
        mfd_c1_curve (top,atlas) gamma b c /\ a < b /\ b < c /\
        mfd_velocity atlas gamma a b b = mfd_velocity atlas gamma b c b /\
        k IN atlas
        ==> continuously_differentiable 1
              {s | s IN interval[lift a,lift c] /\ gamma(drop s) IN FST k}
              (\s. SND k (gamma(drop s)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:(A->bool)#(A->real^N)` (CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I
    [mfd_c1_curve] (ASSUME
    `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b`))))) THEN
  MP_TAC(SPEC `k:(A->bool)#(A->real^N)` (CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I
    [mfd_c1_curve] (ASSUME
    `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) b c`))))) THEN
  ASM_REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^1->real^1->real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^1->real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(gamma:real->A) b IN FST (k:(A->bool)#(A->real^N))
    ==> (f1:real^1->real^1->real^N) (lift b) = f2 (lift b)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC GRGD_JOIN_FPRIME_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `gamma:real->A`; `a:real`; `b:real`; `c:real`;
      `k:(A->bool)#(A->real^N)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP; GRGD_IN_INTERVAL_LIFT;
                    IN_REAL_INTERVAL; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN interval[lift a,lift c] /\
         (gamma:real->A)(drop s) IN FST (k:(A->bool)#(A->real^N))} =
    {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN FST k} UNION
    {s | s IN interval[lift b,lift c] /\ gamma(drop s) IN FST k}`
  (LABEL_TAC "SU") THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
    GEN_TAC THEN
    MATCH_MP_TAC(TAUT `(p <=> q \/ r) ==> (p /\ s <=> q /\ s \/ r /\ s)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `\x. if drop x <= b then (f1:real^1->real^1->real^N) x else f2 x` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    USE_THEN "SU" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    MATCH_MP_TAC GRGD_HAS_DERIVATIVE_WITHIN_UNION THEN
    SUBGOAL_THEN `(a <= drop x /\ drop x <= c) /\
                  (gamma:real->A)(drop x) IN FST (k:(A->bool)#(A->real^N))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC
       `x IN {s | s IN interval[lift a,lift c] /\
                  (gamma:real->A)(drop s) IN FST (k:(A->bool)#(A->real^N))}` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP];
      ALL_TAC] THEN
    BETA_TAC THEN COND_CASES_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP];
      ASM_CASES_TAC `drop x = b` THENL
       [SUBGOAL_THEN `x = lift b` SUBST_ALL_TAC THENL
         [ASM_MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC GRGD_HAS_DERIVATIVE_TRIVIAL THEN CONJ_TAC THENL
         [MATCH_MP_TAC GRGD_NOT_LIMPT_INTERVAL THEN
          MAP_EVERY EXISTS_TAC [`lift b`; `lift c`] THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
          SUBGOAL_THEN
           `((\s. SND (k:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) has_derivative
             (f1:real^1->real^1->real^N) x)
            (at x within {s | s IN interval[lift a,lift b] /\
                              gamma(drop s) IN FST k})`
          MP_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP];
            MESON_TAC[has_derivative]]]];
      MATCH_MP_TAC GRGD_HAS_DERIVATIVE_TRIVIAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC GRGD_NOT_LIMPT_INTERVAL THEN
        MAP_EVERY EXISTS_TAC [`lift a`; `lift b`] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN
         `((\s. SND (k:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))) has_derivative
           (f2:real^1->real^1->real^N) x)
          (at x within {s | s IN interval[lift b,lift c] /\
                            gamma(drop s) IN FST k})`
        MP_TAC THENL
         [FIRST_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
          ASM_REAL_ARITH_TAC;
          MESON_TAC[has_derivative]]];
      FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    X_GEN_TAC `h:real^1` THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC
     `\x. if drop x <= b then (f1:real^1->real^1->real^N) x h else f2 x h` THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_1 THEN
    SUBGOAL_THEN
     `{t | t IN {s | s IN interval[lift a,lift c] /\
                     (gamma:real->A)(drop s) IN FST (k:(A->bool)#(A->real^N))} /\
           drop t <= b} =
      {s | s IN interval[lift a,lift b] /\ gamma(drop s) IN FST k} /\
      {t | t IN {s | s IN interval[lift a,lift c] /\ gamma(drop s) IN FST k} /\
           b <= drop t} =
      {s | s IN interval[lift b,lift c] /\ gamma(drop s) IN FST k}`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP] THEN
      CONJ_TAC THEN GEN_TAC THEN
      MATCH_MP_TAC(TAUT `(p /\ t <=> q) ==> ((p /\ s) /\ t <=> q /\ s)`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM; LIFT_DROP] THEN
    STRIP_TAC THEN AP_THM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[]]);;

let MFD_C1_CURVE_JOIN = prove
 (`!top atlas (gamma:real->A) a b c.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_c1_curve (top,atlas) gamma a b /\
        mfd_c1_curve (top,atlas) gamma b c /\ a < b /\ b < c /\
        mfd_velocity atlas gamma a b b = mfd_velocity atlas gamma b c b
        ==> mfd_c1_curve (top,atlas) gamma a c`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [mfd_c1_curve] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC GRGD_JOIN_CONTINUOUS THEN EXISTS_TAC `b:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[mfd_c1_curve];
    X_GEN_TAC `k:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC GRGD_JOIN_CHART THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `b:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Joinable points and the metric axioms of the Riemannian distance.         *)
(* Concatenation uses the smoothstep 3 u^2 - 2 u^3 (zero end derivatives).   *)
(* Cf. Lee, Introduction to Smooth Manifolds (2nd ed.), Thm 13.29, p. 339.   *)
(* ------------------------------------------------------------------------- *)

let GRGD_VELOCITY_EQ = prove
 (`!atlas (gamma:real->A) gamma' a b t.
        (!s. s IN real_interval[a,b] ==> gamma s = gamma' s) /\
        t IN real_interval[a,b]
        ==> mfd_velocity (atlas:((A->bool)#(A->real^N))->bool) gamma a b t =
            mfd_velocity atlas gamma' a b t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_velocity] THEN
  SUBGOAL_THEN `(gamma:real->A) t = gamma' t` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_EQ THEN
  ASM_REWRITE_TAC[GRGD_IN_INTERVAL_LIFT] THEN
  ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]);;

let GRGD_SMOOTHSTEP_RANGE = prove
 (`!u. &0 <= u /\ u <= &1
       ==> &0 <= &3 * u pow 2 - &2 * u pow 3 /\
           &3 * u pow 2 - &2 * u pow 3 <= &1 /\
           &0 <= &12 * u - &12 * u pow 2`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&3 * u pow 2 - &2 * u pow 3 = u pow 2 * (&3 - &2 * u)`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    SUBGOAL_THEN
     `&1 - (&3 * u pow 2 - &2 * u pow 3) = (&1 - u) pow 2 * (&1 + &2 * u)`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&12 * u - &12 * u pow 2 = &12 * u * (&1 - u)`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

(* The smoothstep halves grgd_ss c (c = 0 on [0,1/2], c = 1 on [1/2,1]),   *)
(* their derivatives, and the concatenation of two curves on [0,1].         *)

let grgd_ss = new_definition
 `grgd_ss (c:real) (t:real) = &3 * (&2 * t - c) pow 2 - &2 * (&2 * t - c) pow 3`;;

let grgd_dss = new_definition
 `grgd_dss (c:real) (t:real) = &12 * (&2 * t - c) - &12 * (&2 * t - c) pow 2`;;

let grgd_concat = new_definition
 `grgd_concat (gamma1:real->A) (gamma2:real->A) (t:real) =
    if t <= &1 / &2 then gamma1(grgd_ss (&0) t) else gamma2(grgd_ss (&1) t)`;;

let GRGD_SS_ALT = prove
 (`!c. grgd_ss c = (\t. &3 * (&2 * t - c) pow 2 - &2 * (&2 * t - c) pow 3) /\
       grgd_dss c = (\t. &12 * (&2 * t - c) - &12 * (&2 * t - c) pow 2)`,
  REWRITE_TAC[FUN_EQ_THM; grgd_ss; grgd_dss]);;

let GRGD_SMOOTHSTEP_DERIV = prove
 (`!c t s.
        (grgd_ss c has_real_derivative grgd_dss c t) (atreal t within s) /\
        (grgd_dss c has_real_derivative (&24 - &48 * (&2 * t - c)))
        (atreal t within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GRGD_SS_ALT] THEN
  CONJ_TAC THEN REAL_DIFF_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING);;

let GRGD_SS_HALF = prove
 (`!c. (c = &0 \/ c = &1)
       ==> (!s. s IN real_interval[c / &2,(c + &1) / &2]
                ==> grgd_ss c s IN real_interval[&0,&1] /\ &0 <= grgd_dss c s /\
                    (grgd_ss c has_real_derivative grgd_dss c s)
                    (atreal s within real_interval[c / &2,(c + &1) / &2])) /\
           grgd_dss c real_continuous_on real_interval[c / &2,(c + &1) / &2] /\
           grgd_ss c (c / &2) = &0 /\ grgd_ss c ((c + &1) / &2) = &1 /\
           grgd_dss c (c / &2) = &0 /\ grgd_dss c ((c + &1) / &2) = &0`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[GRGD_SMOOTHSTEP_DERIV] THEN REWRITE_TAC[grgd_ss; grgd_dss] THEN
    MP_TAC(SPEC `&2 * s - c` GRGD_SMOOTHSTEP_RANGE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[real_differentiable_on; real_differentiable] THEN
    MESON_TAC[GRGD_SMOOTHSTEP_DERIV];
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[grgd_ss; grgd_dss] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[grgd_ss; grgd_dss] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[grgd_ss; grgd_dss] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[grgd_ss; grgd_dss] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let GRGD_SS_HALF0 = REWRITE_RULE[]
  (CONV_RULE REAL_RAT_REDUCE_CONV
    (MP (SPEC `&0` GRGD_SS_HALF) (REAL_ARITH `&0 = &0 \/ &0 = &1`)));;

let GRGD_SS_HALF1 = REWRITE_RULE[]
  (CONV_RULE REAL_RAT_REDUCE_CONV
    (MP (SPEC `&1` GRGD_SS_HALF) (REAL_ARITH `&1 = &0 \/ &1 = &1`)));;

let GRGD_CONCAT_PIECES = prove
 (`!top atlas (gamma1:real->A) gamma2.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma1 (&0) (&1) /\
        mfd_c1_curve (top,atlas) gamma2 (&0) (&1) /\ gamma1(&1) = gamma2(&0)
        ==> mfd_c1_curve (top,atlas) (gamma1 o grgd_ss (&0)) (&0) (&1 / &2) /\
            mfd_c1_curve (top,atlas) (gamma2 o grgd_ss (&1)) (&1 / &2) (&1) /\
            (!t. t IN real_interval[&0,&1 / &2]
                 ==> grgd_concat gamma1 gamma2 t = (gamma1 o grgd_ss (&0)) t) /\
            (!t. t IN real_interval[&1 / &2,&1]
                 ==> grgd_concat gamma1 gamma2 t = (gamma2 o grgd_ss (&1)) t)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`; `grgd_dss (&0)`] THEN
    ASM_SIMP_TAC[GRGD_SS_HALF0] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`; `grgd_dss (&1)`] THEN
    ASM_SIMP_TAC[GRGD_SS_HALF1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_REWRITE_TAC[grgd_concat; o_THM];
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_REWRITE_TAC[grgd_concat; o_THM] THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `t = &1 / &2` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GRGD_SS_HALF0; GRGD_SS_HALF1] THEN ASM_REWRITE_TAC[]]);;

let GRGD_CONCAT_C1 = prove
 (`!top atlas (gamma1:real->A) gamma2.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_c1_curve (top,atlas) gamma1 (&0) (&1) /\
        mfd_c1_curve (top,atlas) gamma2 (&0) (&1) /\ gamma1(&1) = gamma2(&0)
        ==> mfd_c1_curve (top,atlas) (grgd_concat gamma1 gamma2) (&0) (&1) /\
            grgd_concat gamma1 gamma2 (&0) = gamma1(&0) /\
            grgd_concat gamma1 gamma2 (&1) = gamma2(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma1:real->A`; `gamma2:real->A`] GRGD_CONCAT_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[grgd_concat] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GRGD_SS_HALF0; GRGD_SS_HALF1] THEN
  REWRITE_TAC[GSYM grgd_concat; ETA_AX] THEN
  MATCH_MP_TAC MFD_C1_CURVE_JOIN THEN EXISTS_TAC `&1 / &2` THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool)
       (grgd_concat (gamma1:real->A) gamma2) (&0) (&1 / &2) /\
    mfd_c1_curve (top,atlas) (grgd_concat gamma1 gamma2) (&1 / &2) (&1)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFD_C1_CURVE_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                 `grgd_concat (gamma1:real->A) gamma2`;
                 `(gamma1:real->A) o grgd_ss (&0)`; `&0`; `&1 / &2`; `&1 / &2`]
                GRGD_VELOCITY_EQ) THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`;
                 `grgd_concat (gamma1:real->A) gamma2`;
                 `(gamma2:real->A) o grgd_ss (&1)`; `&1 / &2`; `&1`; `&1 / &2`]
                GRGD_VELOCITY_EQ) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma1:real->A`; `&0`; `&1`; `grgd_ss (&0)`; `grgd_dss (&0)`;
                 `&0`; `&1 / &2`; `&1 / &2`] GRGD_VELOCITY_REPARAM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma2:real->A`; `&0`; `&1`; `grgd_ss (&1)`; `grgd_dss (&1)`;
                 `&1 / &2`; `&1`; `&1 / &2`] GRGD_VELOCITY_REPARAM) THEN
  ASM_SIMP_TAC[GRGD_SS_HALF0; GRGD_SS_HALF1] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GRGD_SS_HALF0; GRGD_SS_HALF1; VECTOR_MUL_LZERO]);;

let GRGD_CONCAT_LENGTH = prove
 (`!top atlas (g:A->real^N^N) (gamma1:real->A) gamma2.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma1 (&0) (&1) /\
        mfd_c1_curve (top,atlas) gamma2 (&0) (&1) /\ gamma1(&1) = gamma2(&0)
        ==> mfd_length atlas g (grgd_concat gamma1 gamma2) (&0) (&1) =
            mfd_length atlas g gamma1 (&0) (&1) +
            mfd_length atlas g gamma2 (&0) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma1:real->A`; `gamma2:real->A`] GRGD_CONCAT_PIECES) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma1:real->A`; `gamma2:real->A`] GRGD_CONCAT_C1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `grgd_concat (gamma1:real->A) gamma2`;
                 `&0`; `&1 / &2`; `&1`] MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2) THEN
  BINOP_TAC THENL
   [TRANS_TAC EQ_TRANS
     `mfd_length atlas (g:A->real^N^N) ((gamma1:real->A) o grgd_ss (&0))
                 (&0) (&1 / &2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_LENGTH_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma1:real->A`; `&0`; `&1`;
                   `grgd_ss (&0)`; `grgd_dss (&0)`; `&0`; `&1 / &2`]
                  MFD_LENGTH_REPARAM) THEN
    ASM_SIMP_TAC[GRGD_SS_HALF0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[];
    TRANS_TAC EQ_TRANS
     `mfd_length atlas (g:A->real^N^N) ((gamma2:real->A) o grgd_ss (&1))
                 (&1 / &2) (&1)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC MFD_LENGTH_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma2:real->A`; `&0`; `&1`;
                   `grgd_ss (&1)`; `grgd_dss (&1)`; `&1 / &2`; `&1`]
                  MFD_LENGTH_REPARAM) THEN
    ASM_SIMP_TAC[GRGD_SS_HALF1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[]]);;

(* Affine reparametrization to [0,1]. *)

let GRGD_AFFINE_DERIV = prove
 (`!a b t s. ((\x. a + (b - a) * x) has_real_derivative (b - a)) (atreal t within s)`,
  REPEAT GEN_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC);;

let GRGD_AFFINE_FACTS = prove
 (`!a b. a <= b
         ==> !s. s IN real_interval[&0,&1]
                 ==> (\x. a + (b - a) * x) s IN real_interval[a,b] /\
                     &0 <= (\x:real. b - a) s /\
                     ((\x. a + (b - a) * x) has_real_derivative (\x:real. b - a) s)
                     (atreal s within real_interval[&0,&1])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GRGD_AFFINE_DERIV] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  MP_TAC(SPECL [`b - a:real`; `s:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`b - a:real`; `s:real`; `&1`] REAL_LE_LMUL) THEN
  ASM_REAL_ARITH_TAC);;

let GRGD_AFFINE_CURVE = prove
 (`!top atlas (gamma:real->A) a b.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b
        ==> mfd_c1_curve (top,atlas) (gamma o (\x. a + (b - a) * x)) (&0) (&1) /\
            (gamma o (\x. a + (b - a) * x)) (&0) = gamma a /\
            (gamma o (\x. a + (b - a) * x)) (&1) = gamma b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  REWRITE_TAC[o_THM; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID;
              REAL_ARITH `a + (b - a) = b`] THEN
  MATCH_MP_TAC GRGD_C1_CURVE_REPARAM THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `\x:real. b - a`] THEN
  ASM_SIMP_TAC[GRGD_AFFINE_FACTS; REAL_CONTINUOUS_ON_CONST; REAL_POS]);;

let GRGD_AFFINE_LENGTH = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b
        ==> mfd_length atlas g (gamma o (\x. a + (b - a) * x)) (&0) (&1) =
            mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`;
                 `\x. a + (b - a) * x`; `\x:real. b - a`; `&0`; `&1`]
                MFD_LENGTH_REPARAM) THEN
  ASM_SIMP_TAC[GRGD_AFFINE_FACTS; REAL_CONTINUOUS_ON_CONST; REAL_POS] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID;
              REAL_ARITH `a + (b - a) = b`] THEN SIMP_TAC[]);;

(* Joinability. *)

let MFD_C1_CURVE_JOINABLE = prove
 (`!top atlas (gamma:real->A) a b.
        mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) gamma a b
        ==> mfd_joinable (top,atlas) (gamma a) (gamma b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_joinable] THEN
  EXISTS_TAC `(gamma:real->A) o (\x. a + (b - a) * x)` THEN
  ASM_MESON_TAC[GRGD_AFFINE_CURVE]);;

let MFD_JOINABLE_IN_TOPSPACE = prove
 (`!top atlas (x:A) y.
        mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x y
        ==> x IN topspace top /\ y IN topspace top`,
  REWRITE_TAC[mfd_joinable] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE; IN_REAL_INTERVAL; REAL_POS;
                REAL_LE_REFL]);;

let MFD_JOINABLE_REFL = prove
 (`!top atlas (x:A).
        mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x x <=>
        x IN topspace top`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    DISCH_TAC THEN REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `\t:real. (x:A)` THEN
    ASM_SIMP_TAC[MFD_C1_CURVE_CONST; REAL_POS]]);;

let GRGD_REVERSE_01 = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A).
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1)
        ==> mfd_c1_curve (top,atlas) (\t. gamma(&0 + &1 - t)) (&0) (&1) /\
            (\t. gamma(&0 + &1 - t)) (&0) = gamma(&1) /\
            (\t. gamma(&0 + &1 - t)) (&1) = gamma(&0) /\
            mfd_length atlas g (\t. gamma(&0 + &1 - t)) (&0) (&1) =
            mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`]
                MFD_LENGTH_REVERSE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let MFD_JOINABLE_SYM = prove
 (`!top atlas (x:A) y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)
        ==> (mfd_joinable (top,atlas) x y <=> mfd_joinable (top,atlas) y x)`,
  SUBGOAL_THEN
   `!top atlas (x:A) y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_joinable (top,atlas) x y
        ==> mfd_joinable (top,atlas) y x`
   (fun th -> MESON_TAC[th]) THEN
  REWRITE_TAC[mfd_joinable] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\t. (gamma:real->A)(&0 + &1 - t)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(\x. mat 1):A->real^N^N`; `gamma:real->A`] GRGD_REVERSE_01) THEN
  ASM_SIMP_TAC[]);;

let MFD_JOINABLE_TRANS = prove
 (`!top atlas (x:A) y z.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_joinable (top,atlas) x y /\ mfd_joinable (top,atlas) y z
        ==> mfd_joinable (top,atlas) x z`,
  REWRITE_TAC[mfd_joinable] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `grgd_concat (gamma:real->A) gamma'` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `gamma':real->A`] GRGD_CONCAT_C1) THEN
  ASM_SIMP_TAC[]);;

(* The Riemannian distance. *)

let GRGD_IN_LENGTHS = prove
 (`!top atlas (g:A->real^N^N) x y L.
        L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
              mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
              gamma(&0) = x /\ gamma(&1) = y} <=>
        ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                gamma(&0) = x /\ gamma(&1) = y /\
                L = mfd_length atlas g gamma (&0) (&1)`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let GRGD_LENGTHS_POS_LE = prove
 (`!top atlas (g:A->real^N^N) x y L.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
              mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
              gamma(&0) = x /\ gamma(&1) = y}
        ==> &0 <= L`,
  REWRITE_TAC[GRGD_IN_LENGTHS] THEN MESON_TAC[MFD_LENGTH_POS_LE]);;

let MFD_DIST_LE_LENGTH = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b
        ==> mfd_dist (top,atlas) g (gamma a) (gamma b) <=
            mfd_length atlas g gamma a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_INF_LE THEN
  MAP_EVERY EXISTS_TAC
   [`&0`; `mfd_length atlas (g:A->real^N^N) (gamma:real->A) a b`] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[GRGD_IN_LENGTHS] THEN
    EXISTS_TAC `(gamma:real->A) o (\x. a + (b - a) * x)` THEN
    ASM_MESON_TAC[GRGD_AFFINE_CURVE; GRGD_AFFINE_LENGTH];
    X_GEN_TAC `L:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) a`; `(gamma:real->A) b`;
                   `L:real`] GRGD_LENGTHS_POS_LE) THEN
    ASM_REWRITE_TAC[]]);;

let MFD_DIST_POS_LE = prove
 (`!top atlas (g:A->real^N^N) x y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_joinable (top,atlas) x y
        ==> &0 <= mfd_dist (top,atlas) g x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
    ASM_MESON_TAC[mfd_joinable];
    ASM_MESON_TAC[GRGD_LENGTHS_POS_LE]]);;

let GRGD_LENGTH_CONST = prove
 (`!atlas (g:A->real^N^N) (x:A).
        mfd_length (atlas:((A->bool)#(A->real^N))->bool) g (\t. x) (&0) (&1) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_length] THEN
  TRANS_TAC EQ_TRANS `real_integral (real_interval[&0,&1]) (\t. &0)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[REAL_INTEGRAL_0]] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  REWRITE_TAC[mfd_speed; mfd_velocity] THEN
  SUBGOAL_THEN
   `vector_derivative (\s. SND (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) (x:A))
      (at (lift t) within interval[lift(&0),lift(&1)]) = vec 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    ASM_REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT; HAS_VECTOR_DERIVATIVE_CONST] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[DOT_LZERO; SQRT_0]]);;

let MFD_DIST_REFL = prove
 (`!top atlas (g:A->real^N^N) x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> mfd_dist (top,atlas) g x x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GRGD_IN_LENGTHS] THEN EXISTS_TAC `\t:real. (x:A)` THEN
      ASM_SIMP_TAC[MFD_C1_CURVE_CONST; REAL_POS; GRGD_LENGTH_CONST];
      X_GEN_TAC `L:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `x:A`; `L:real`]
                    GRGD_LENGTHS_POS_LE) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[MFD_JOINABLE_REFL]]);;

let GRGD_LENGTHS_SYM = prove
 (`!top atlas (g:A->real^N^N) x y.
        smooth_manifold_atlas top atlas
        ==> {mfd_length atlas g gamma (&0) (&1) | gamma |
             mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
             gamma(&0) = x /\ gamma(&1) = y} =
            {mfd_length atlas g gamma (&0) (&1) | gamma |
             mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
             gamma(&0) = y /\ gamma(&1) = x}`,
  SUBGOAL_THEN
   `!top atlas (g:A->real^N^N) x y L.
        smooth_manifold_atlas top atlas /\
        L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
              mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
              gamma(&0) = x /\ gamma(&1) = y}
        ==> L IN {mfd_length atlas g gamma (&0) (&1) | gamma |
                  mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                  gamma(&0) = y /\ gamma(&1) = x}`
  ASSUME_TAC THENL
   [REWRITE_TAC[GRGD_IN_LENGTHS] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `\t. (gamma:real->A)(&0 + &1 - t)` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`] GRGD_REVERSE_01) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN ASM_MESON_TAC[]]);;

let MFD_DIST_SYM = prove
 (`!top atlas (g:A->real^N^N) x y.
        smooth_manifold_atlas top atlas
        ==> mfd_dist (top,atlas) g x y = mfd_dist (top,atlas) g y x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_dist] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC GRGD_LENGTHS_SYM THEN ASM_REWRITE_TAC[]);;

let MFD_DIST_TRIANGLE = prove
 (`!top atlas (g:A->real^N^N) x y z.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_joinable (top,atlas) x y /\ mfd_joinable (top,atlas) y z
        ==> mfd_dist (top,atlas) g x z <=
            mfd_dist (top,atlas) g x y + mfd_dist (top,atlas) g y z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!L1 L2. L1 IN {mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (x:A) /\ gamma(&1) = y} /\
            L2 IN {mfd_length atlas g gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = y /\ gamma(&1) = z}
            ==> mfd_dist (top,atlas) g x z <= L1 + L2`
  ASSUME_TAC THENL
   [REWRITE_TAC[GRGD_IN_LENGTHS] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_INF_LE THEN
    MAP_EVERY EXISTS_TAC [`&0`; `L1 + L2:real`] THEN REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GRGD_IN_LENGTHS] THEN
      EXISTS_TAC `grgd_concat (gamma:real->A) gamma'` THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `gamma':real->A`] GRGD_CONCAT_C1) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `gamma':real->A`]
                    GRGD_CONCAT_LENGTH) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[GRGD_LENGTHS_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!L2. L2 IN {mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                gamma(&0) = (y:A) /\ gamma(&1) = z}
         ==> mfd_dist (top,atlas) g x z - L2 <= mfd_dist (top,atlas) g x y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC (RAND_CONV) [mfd_dist] THEN
    MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      ASM_MESON_TAC[mfd_joinable];
      ASM_MESON_TAC[REAL_ARITH `d <= l1 + l2 ==> d - l2 <= l1`]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `d <= a + b <=> d - a <= b`] THEN
  GEN_REWRITE_TAC (RAND_CONV) [mfd_dist] THEN
  MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
    ASM_MESON_TAC[mfd_joinable];
    ASM_MESON_TAC[REAL_ARITH `d - l2 <= l1 ==> d - l1 <= l2`]]);;

(* ------------------------------------------------------------------------- *)
(* Local comparison with coordinate distances (Lee, Introduction to Smooth   *)
(* Manifolds, 2nd ed., Lemma 13.28 and the proof of Thm 13.29, p. 339).      *)
(* ------------------------------------------------------------------------- *)

let GRGD_CHART_INV_CONTINUOUS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N).
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas
        ==> continuous_map (subtopology euclidean (IMAGE phi U),top)
                           (chart_inv (U,phi))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `g:real^N->A` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^N) (phi x) = x` SUBST1_TAC THENL
     [MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET o
      check (fun th -> try fst(dest_const(rator(rator(concl th)))) = "open_in"
                       with Failure _ -> false)) THEN
    ASM SET_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[]]);;

(* Uniform comparison of the chart metric with the Euclidean one on a      *)
(* compact subset of a chart image.                                          *)

let GRGD_QUAD_HOMOG = prove
 (`!(G:real^N^N) v k. (k % v) dot (G ** (k % v)) = (k * k) * (v dot (G ** v))`,
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

let GRGD_METRIC_BOUNDS = prove
 (`!atlas (g:A->real^N^N) U phi K.
        riemannian_metric atlas g /\ (U,phi) IN atlas /\
        compact K /\ K SUBSET IMAGE phi U
        ==> ?c C. &0 < c /\ c <= C /\
                  !y v. y IN K
                        ==> c * norm v pow 2 <=
                            v dot (metric_local atlas (U,phi) g y ** v) /\
                            v dot (metric_local atlas (U,phi) g y ** v) <=
                            C * norm v pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^N) U) (metric_local atlas (U,phi) (g:A->real^N^N))`
  MP_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
  ASM_CASES_TAC `K:real^N->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&1`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LE_REFL; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize:real^N^N->real^(N,N)finite_prod) o
     metric_local atlas (U,phi) (g:A->real^N^N)) continuous_on K`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?B. &0 < B /\
        !y. y IN K ==> norm(vectorize(metric_local atlas (U,phi) (g:A->real^N^N) y))
                       <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE ((vectorize:real^N^N->real^(N,N)finite_prod) o
                        metric_local atlas (U,phi) (g:A->real^N^N)) K`
                 COMPACT_IMP_BOUNDED) THEN
    ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; o_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\p:real^(N,N)finite_sum.
       sndcart p dot (metric_local atlas (U,phi) (g:A->real^N^N) (fstcart p) **
                      sndcart p)`;
    `(K:real^N->bool) PCROSS sphere(vec 0:real^N,&1)`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_PCROSS THEN ASM_REWRITE_TAC[COMPACT_SPHERE];
      ASM_REWRITE_TAC[PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
      REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MATRIX_VECTOR_MUL THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART]] THEN
      SUBGOAL_THEN
       `(vectorize:real^N^N->real^(N,N)finite_prod) o
        (\p:real^(N,N)finite_sum.
           metric_local atlas (U,phi) (g:A->real^N^N) (fstcart p)) =
        (vectorize o metric_local atlas (U,phi) g) o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `K:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS;
                    FSTCART_PASTECART] THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_SPHERE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:real^N` (X_CHOOSE_THEN `u0:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `&0 < u0 dot (metric_local atlas (U,phi) (g:A->real^N^N) y0 ** u0)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(y0:real^N) IN IMAGE (phi:A->real^N) U /\ ~(u0:real^N = vec 0)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `norm(u0:real^N) = &1` THEN
        ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`u0 dot (metric_local atlas (U,phi) (g:A->real^N^N) y0 ** u0)`;
    `max B (u0 dot (metric_local atlas (U,phi) (g:A->real^N^N) y0 ** u0))`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `v:real^N`] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_CASES_TAC `v:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^N`; `inv(norm v) % v:real^N`]) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0; GRGD_QUAD_HOMOG] THEN
    SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    ABBREV_TAC `q = v dot (metric_local atlas (U,phi) (g:A->real^N^N) y ** v)` THEN
    ABBREV_TAC `n = norm(v:real^N)` THEN
    ABBREV_TAC `c0 = u0 dot (metric_local atlas (U,phi) (g:A->real^N^N) y0 ** u0)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `q = (inv n * inv n * q) * n pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REWRITE_TAC[REAL_MUL_ASSOC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B * norm(v:real^N) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(v:real^N) *
                  norm(metric_local atlas (U,phi) (g:A->real^N^N) y ** v)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(v:real^N) *
                  (norm(vectorize(metric_local atlas (U,phi) (g:A->real^N^N) y)) *
                   norm v)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE];
        REWRITE_TAC[REAL_POW_2] THEN
        SUBGOAL_THEN
         `norm(vectorize(metric_local atlas (U,phi) (g:A->real^N^N) y)) <= B`
        MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN
        ABBREV_TAC `n = norm(v:real^N)` THEN
        ABBREV_TAC `m = norm(vectorize(metric_local atlas (U,phi) (g:A->real^N^N) y))` THEN
        REPEAT DISCH_TAC THEN
        SUBGOAL_THEN `n * m * n = m * (n * n) /\ B * n * n = B * (n * n)`
         (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LE_MUL]];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC]]);;

let GRGD_SPEED_BOUNDS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t U phi c C K.
        smooth_manifold_atlas top atlas /\
        mfd_c1_curve (top,atlas) gamma a b /\ a < b /\
        t IN real_interval[a,b] /\ (U,phi) IN atlas /\ gamma t IN U /\
        phi(gamma t) IN K /\
        (!y v. y IN K
               ==> c * norm v pow 2 <= v dot (metric_local atlas (U,phi) g y ** v) /\
                   v dot (metric_local atlas (U,phi) g y ** v) <= C * norm v pow 2)
        ==> sqrt c * norm(vector_derivative (\s. phi(gamma(drop s)))
                            (at (lift t) within interval[lift a,lift b])) <=
            mfd_speed atlas g gamma a b t /\
            mfd_speed atlas g gamma a b t <=
            sqrt C * norm(vector_derivative (\s. phi(gamma(drop s)))
                            (at (lift t) within interval[lift a,lift b]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                 `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(phi:A->real^N)((gamma:real->A) t)`;
    `vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
       (at (lift t) within interval[lift a,lift b])`]) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
              (at (lift t) within interval[lift a,lift b])`,`w:real^N`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt c * norm(w:real^N) = sqrt(c * norm w pow 2) /\
                sqrt C * norm w = sqrt(C * norm w pow 2)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SQRT_MUL] THEN SIMP_TAC[POW_2_SQRT; NORM_POS_LE]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]);;

(* Lower bound for the length of a curve staying in a compact coordinate   *)
(* set: sqrt(c) times the coordinate distance of its end points.            *)

let GRGD_CHART_LENGTH_LOWER = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b U phi c C K.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_c1_curve (top,atlas) gamma a b /\ (U,phi) IN atlas /\ &0 <= c /\
        (!y v. y IN K
               ==> c * norm v pow 2 <= v dot (metric_local atlas (U,phi) g y ** v) /\
                   v dot (metric_local atlas (U,phi) g y ** v) <= C * norm v pow 2) /\
        (!t. t IN real_interval[a,b] ==> gamma t IN U /\ phi(gamma t) IN K)
        ==> sqrt c * dist(phi(gamma a),phi(gamma b)) <= mfd_length atlas g gamma a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a <= b` ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real = b` THENL
   [ASM_REWRITE_TAC[DIST_REFL; mfd_length; REAL_INTEGRAL_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN interval[lift a,lift b] /\
         (gamma:real->A)(drop s) IN FST(U:A->bool,phi:A->real^N)} =
    interval[lift a,lift b]`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; FST] THEN
    ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
           (at s within interval[lift a,lift b])) continuous_on
    interval[lift a,lift b]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`;
                   `(U:A->bool,phi:A->real^N)`] GRGD_C1_CHART_VD_CONTINUOUS) THEN
    ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
            (at s within interval[lift a,lift b])) has_integral
     (phi(gamma b) - phi(gamma a))) (interval[lift a,lift b])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. (phi:A->real^N)((gamma:real->A)(drop s))`;
                   `\s. vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
                          (at s within interval[lift a,lift b])`;
                   `lift a`; `lift b`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `gamma:real->A`; `a:real`; `b:real`;
                     `(U:A->bool,phi:A->real^N)`; `drop s`] GRGD_C1_CHART_HAS_VD) THEN
      ASM_REWRITE_TAC[FST; SND; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt c * drop(integral (interval[lift a,lift b])
      (\s. lift(norm(vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
                       (at s within interval[lift a,lift b])))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[integrable_on];
      MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. norm(vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
            (at (lift t) within interval[lift a,lift b])))
    real_continuous_on real_interval[a,b]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[lift a,lift b])
      (\s. lift(norm(vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
                       (at s within interval[lift a,lift b]))))) =
    real_integral (real_interval[a,b])
      (\t. norm(vector_derivative (\s. phi(gamma(drop s)))
                 (at (lift t) within interval[lift a,lift b])))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_INTEGRABLE_CONTINUOUS) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL) THEN
    REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_CONTINUOUS] THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS];
    ASM_MESON_TAC[GRGD_SPEED_INTEGRABLE];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                   `U:A->bool`; `phi:A->real^N`; `c:real`; `C:real`;
                   `K:real^N->bool`] GRGD_SPEED_BOUNDS) THEN
    ASM_SIMP_TAC[]]);;

(* Coordinate segments are C^1 curves with constant chart velocity. *)

let GRGD_SMOOTH_AFFINE_LINE = prove
 (`!(p:real^N) (v:real^N) s. open s ==> smooth_map_on s (\x:real^1. p + drop x % v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^1. p + drop x % v:real^N) =
    (\x. (\x. p) x + ((\x. drop x % v) o (\x. x)) x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID] THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

let GRGD_AFFINE_LINE_VD = prove
 (`!(p:real^N) (v:real^N) net.
        ((\s:real^1. p + drop s % v) has_vector_derivative v) net`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `((\s:real^1. p + drop s % v) has_vector_derivative (vec 0 + v:real^N)) net`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; has_vector_derivative] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC[LINEAR_ID];
    REWRITE_TAC[VECTOR_ADD_LID]]);;

let GRGD_CHART_SEGMENT = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) p q.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        segment[p,q] SUBSET IMAGE phi U
        ==> (!t. t IN real_interval[&0,&1]
                 ==> chart_inv (U,phi) (p + t % (q - p)) IN U /\
                     phi(chart_inv (U,phi) (p + t % (q - p))) = p + t % (q - p)) /\
            mfd_c1_curve (top,atlas)
              (\t. chart_inv (U,phi) (p + t % (q - p))) (&0) (&1) /\
            (!t. t IN real_interval[&0,&1]
                 ==> vector_derivative
                       (\s. phi(chart_inv (U,phi) (p + drop s % (q - p))))
                       (at (lift t) within interval[lift(&0),lift(&1)]) = q - p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1] ==> p + t % (q - p) IN IMAGE (phi:A->real^N) U`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,&1]
        ==> chart_inv (U,phi) (p + t % (q - p)) IN U /\
            (phi:A->real^N)(chart_inv (U,phi) (p + t % (q - p))) = p + t % (q - p)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    REWRITE_TAC[mfd_c1_curve; REAL_POS] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\t. chart_inv (U:A->bool,phi:A->real^N) (p + t % (q - p))) =
        chart_inv (U,phi) o (\t. p + t % (q - p))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC GRGD_CHART_INV_CONTINUOUS THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
        ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN DISCH_TAC THEN
    REWRITE_TAC[FST; SND] THEN
    SUBGOAL_THEN
     `(\s. (psi:A->real^N)(chart_inv (U:A->bool,phi:A->real^N)
                             (p + drop s % (q - p)))) =
      chart_trans (U,phi) (V,psi) o (\s. p + drop s % (q - p))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; chart_trans; SND]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `{s:real^1 | p + drop s % (q - p) IN
                            IMAGE (phi:A->real^N) (U INTER V)}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN
      BETA_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `drop s IN real_interval[&0,&1]` ASSUME_TAC THENL
       [ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (U:A->bool,phi:A->real^N) (p + drop s % (q - p))` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on {s:real^1 | p + drop s % (q - p) IN
                                IMAGE (phi:A->real^N) (U INTER V)}
        (chart_trans (U,phi) (V,psi) o (\s. p + drop s % (q - p)))`
    MP_TAC THENL [ALL_TAC; SIMP_TAC[smooth_map_on]] THEN
    SUBGOAL_THEN `open (IMAGE (phi:A->real^N) (U INTER V))` ASSUME_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`]
                 CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `open {s:real^1 | p + drop s % (q - p) IN IMAGE (phi:A->real^N) (U INTER V)}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
      REWRITE_TAC[LINEAR_ID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GRGD_SMOOTH_AFFINE_LINE] THEN SET_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    REWRITE_TAC[LIFT_DROP; GRGD_IN_INTERVAL_LIFT; REAL_LT_01] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    EXISTS_TAC `\s:real^1. p + drop s % (q - p):real^N` THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_LT_01; GRGD_IN_INTERVAL_LIFT; GRGD_AFFINE_LINE_VD] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `drop s IN real_interval[&0,&1]` ASSUME_TAC THENL
     [ASM_MESON_TAC[GRGD_DROP_IN_REAL_INTERVAL]; ASM_SIMP_TAC[]]]);;

let GRGD_SEGMENT_LENGTH_UPPER = prove
 (`!top atlas (g:A->real^N^N) (U:A->bool) phi p q c C K.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ segment[p,q] SUBSET K /\ K SUBSET IMAGE phi U /\
        (!y v. y IN K
               ==> c * norm v pow 2 <= v dot (metric_local atlas (U,phi) g y ** v) /\
                   v dot (metric_local atlas (U,phi) g y ** v) <= C * norm v pow 2)
        ==> mfd_length atlas g (\t. chart_inv (U,phi) (p + t % (q - p))) (&0) (&1)
            <= sqrt C * dist(p,q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `p:real^N`; `q:real^N`]
               GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[mfd_length] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,&1]) (\t:real. sqrt C * dist(p:real^N,q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `\t. chart_inv (U:A->bool,phi:A->real^N) (p + t % (q - p))`;
                   `&0`; `&1`; `t:real`; `U:A->bool`; `phi:A->real^N`;
                   `c:real`; `C:real`; `K:real^N->bool`] GRGD_SPEED_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_01] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th -> try (rand(concl th) = `K:real^N->bool`) with Failure _ -> false)) THEN
      REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN BETA_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[dist; NORM_SUB];
    SIMP_TAC[REAL_INTEGRAL_CONST; REAL_POS] THEN REAL_ARITH_TAC]);;

let GRGD_REAL_CLOSED_LEFT = prove
 (`!S t. real_closed S /\ &0 < t /\ (!s. &0 <= s /\ s < t ==> s IN S)
         ==> t IN S`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(t:real) IN S` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `real_closed (S:real->bool)` THEN
  REWRITE_TAC[real_closed; real_open; IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (&0) (t - e / &2)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (&0) (t - e / &2)`) THEN
  MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> p) ==> (b ==> ~p) ==> F`) THEN
  ASM_REAL_ARITH_TAC);;

let GRGD_CHART_PREIMAGE_OPEN = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) s.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ open s
        ==> open_in top {z | z IN U /\ phi z IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`phi:A->real^N`; `subtopology top (U:A->bool)`;
                 `subtopology euclidean (IMAGE (phi:A->real^N) U)`;
                 `IMAGE (phi:A->real^N) U INTER s`]
                OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]);;

let GRGD_CHART_CBALL_CLOSED = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) p r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        (U,phi) IN atlas /\ cball(p,r) SUBSET IMAGE phi U
        ==> closed_in top (IMAGE (chart_inv (U,phi)) (cball(p,r)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
  MATCH_MP_TAC GRGD_CHART_INV_CONTINUOUS THEN
  EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]);;

(* First time a continuous curve on [0,1] leaves an open set. *)

let GRGD_FIRST_TIME = prove
 (`!top (gamma:real->A) B.
        continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) gamma /\
        open_in top B /\ gamma(&0) IN B /\
        (?t. t IN real_interval[&0,&1] /\ ~(gamma t IN B))
        ==> ?t1. &0 < t1 /\ t1 <= &1 /\ ~(gamma t1 IN B) /\
                 !s. &0 <= s /\ s < t1 ==> gamma s IN B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_closed {s | s IN real_interval[&0,&1] /\ ~((gamma:real->A) s IN B)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_CLOSED_IN] THEN MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `{s | s IN real_interval[&0,&1] /\ ~((gamma:real->A) s IN B)} =
      {s | s IN topspace (subtopology euclideanreal (real_interval[&0,&1])) /\
           gamma s IN topspace top DIFF B}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF;
                  TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      X_GEN_TAC `s:real` THEN
      ASM_CASES_TAC `s IN real_interval[&0,&1]` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(gamma:real->A) s IN topspace top` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC
       `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                       (gamma:real->A)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~({s | s IN real_interval[&0,&1] /\ ~((gamma:real->A) s IN B)} = {}) /\
    !x. x IN {s | s IN real_interval[&0,&1] /\ ~((gamma:real->A) s IN B)}
        ==> &0 <= x`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t1. t1 IN {s | s IN real_interval[&0,&1] /\ ~((gamma:real->A) s IN B)} /\
         !s. s IN {s | s IN real_interval[&0,&1] /\ ~(gamma s IN B)} ==> t1 <= s`
  MP_TAC THENL
   [EXISTS_TAC
     `inf {s | s IN real_interval[&0,&1] /\ ~((gamma:real->A) s IN B)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CLOSED_CONTAINS_INF THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPEC
       `{s | s IN real_interval[&0,&1] /\ ~((gamma:real->A) s IN B)}` INF) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t1:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((gamma:real->A) t1 IN B)` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(gamma:real->A) s IN B` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let GRGD_CLOSED_LEFT_CURVE = prove
 (`!top (gamma:real->A) C t1.
        continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top) gamma /\
        closed_in top C /\ &0 < t1 /\ t1 <= &1 /\
        (!s. &0 <= s /\ s < t1 ==> gamma s IN C)
        ==> gamma t1 IN C`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t1 IN {s | s IN real_interval[&0,&1] /\ (gamma:real->A) s IN C}`
   (fun th -> MP_TAC th THEN SIMP_TAC[IN_ELIM_THM]) THEN
  MATCH_MP_TAC GRGD_REAL_CLOSED_LEFT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_CLOSED_IN] THEN MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    SUBGOAL_THEN
     `{s | s IN real_interval[&0,&1] /\ (gamma:real->A) s IN C} =
      {s | s IN topspace (subtopology euclideanreal (real_interval[&0,&1])) /\
           gamma s IN C}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* A curve from the centre that leaves the coordinate ball of radius r has  *)
(* length at least sqrt(c) r (Hausdorff: the closed coordinate ball is      *)
(* compact, hence closed).                                                   *)

let GRGD_FIRST_EXIT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) U phi r c C.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ (U,phi) IN atlas /\
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) IN U /\ &0 < r /\
        cball(phi(gamma(&0)),r) SUBSET IMAGE phi U /\ &0 <= c /\
        (!y v. y IN cball(phi(gamma(&0)),r)
               ==> c * norm v pow 2 <= v dot (metric_local atlas (U,phi) g y ** v) /\
                   v dot (metric_local atlas (U,phi) g y ** v) <= C * norm v pow 2) /\
        (?t. t IN real_interval[&0,&1] /\
             ~(gamma t IN U /\ phi(gamma t) IN ball(phi(gamma(&0)),r)))
        ==> sqrt c * r <= mfd_length atlas g gamma (&0) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclideanreal (real_interval[&0,&1]),top)
                   (gamma:real->A)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`;
                 `{z:A | z IN U /\ (phi:A->real^N) z IN ball(phi(gamma(&0)),r)}`]
                GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(gamma:real->A) t1 IN
    IMAGE (chart_inv (U:A->bool,phi:A->real^N)) (cball(phi(gamma(&0)),r))`
  MP_TAC THENL
   [MATCH_MP_TAC GRGD_CLOSED_LEFT_CURVE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC GRGD_CHART_CBALL_CLOSED THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(gamma:real->A) s IN U /\
        (phi:A->real^N)(gamma s) IN ball(phi(gamma(&0)),r)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `(phi:A->real^N)((gamma:real->A) s)` THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(gamma:real->A) t1 IN U /\ (phi:A->real^N)(gamma t1) = y1`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r <= dist((phi:A->real^N)((gamma:real->A)(&0)),y1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_BALL; REAL_NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_c1_curve (top,atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) (&0) t1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_C1_CURVE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t1:real`;
                 `U:A->bool`; `phi:A->real^N`; `c:real`; `C:real`;
                 `cball((phi:A->real^N)((gamma:real->A)(&0)),r)`]
                GRGD_CHART_LENGTH_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    ASM_CASES_TAC `u:real = t1` THENL
     [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(gamma:real->A) u IN U /\
      (phi:A->real^N)(gamma u) IN ball(phi(gamma(&0)),r)`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MESON_TAC[BALL_SUBSET_CBALL; SUBSET]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `t1:real`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `t1:real`; `&1`]
                MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`sqrt c`; `r:real`;
                 `dist((phi:A->real^N)((gamma:real->A)(&0)),y1)`] REAL_LE_LMUL) THEN
  ASM_SIMP_TAC[SQRT_POS_LE] THEN ASM_REAL_ARITH_TAC);;

(* Local comparison of the Riemannian distance with the coordinate distance. *)

let MFD_DIST_LOCAL_EUCLIDEAN = prove
 (`!top atlas (g:A->real^N^N) U phi x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ (U,phi) IN atlas /\ x IN U
        ==> ?r c1 c2.
              &0 < r /\ &0 < c1 /\ c1 <= c2 /\
              cball(phi x,r) SUBSET IMAGE phi U /\
              (!y. y IN U /\ phi y IN ball(phi x,r)
                   ==> mfd_joinable (top,atlas) x y /\
                       c1 * dist(phi x,phi y) <= mfd_dist (top,atlas) g x y /\
                       mfd_dist (top,atlas) g x y <= c2 * dist(phi x,phi y)) /\
              (!y. mfd_joinable (top,atlas) x y /\
                   ~(y IN U /\ phi y IN ball(phi x,r))
                   ==> c1 * r <= mfd_dist (top,atlas) g x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r. &0 < r /\ cball((phi:A->real^N) x,r) SUBSET IMAGE phi U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (IMAGE (phi:A->real^N) U)` THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `U:A->bool`; `phi:A->real^N`; `cball((phi:A->real^N) x,r)`]
                GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!gamma:real->A.
        mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ gamma(&0) = x /\
        (?t. t IN real_interval[&0,&1] /\
             ~(gamma t IN U /\ (phi:A->real^N)(gamma t) IN ball(phi x,r)))
        ==> sqrt c * r <= mfd_length atlas (g:A->real^N^N) gamma (&0) (&1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GRGD_FIRST_EXIT THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `U:A->bool`; `phi:A->real^N`; `C:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `sqrt c`; `sqrt C`] THEN
  ASM_SIMP_TAC[SQRT_POS_LT; SQRT_MONO_LE] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[(phi:A->real^N) x,phi y] SUBSET ball(phi x,r)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(phi:A->real^N) x`; `r:real`] CONVEX_BALL) THEN
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `U:A->bool`; `phi:A->real^N`; `(phi:A->real^N) x`;
                  `(phi:A->real^N) y`] GRGD_CHART_SEGMENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
      STRIP_TAC] THEN
    SUBGOAL_THEN
     `(\t. chart_inv (U:A->bool,phi:A->real^N) (phi x + t % (phi y - phi x))) (&0) = x /\
      (\t. chart_inv (U:A->bool,phi:A->real^N) (phi x + t % (phi y - phi x))) (&1) = y`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                  VECTOR_ARITH `x + (y - x):real^N = y`] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `\t. chart_inv (U:A->bool,phi:A->real^N) (phi x + t % (phi y - phi x))`;
        `&0`; `&1`] MFD_C1_CURVE_JOINABLE) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
        ASM_MESON_TAC[mfd_joinable];
        ALL_TAC] THEN
      X_GEN_TAC `L:real` THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN
      DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC
       `!t. t IN real_interval[&0,&1]
            ==> (gamma:real->A) t IN U /\ (phi:A->real^N)(gamma t) IN ball(phi x,r)`
      THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`;
                       `U:A->bool`; `phi:A->real^N`; `c:real`; `C:real`;
                       `cball((phi:A->real^N) x,r)`] GRGD_CHART_LENGTH_LOWER) THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET]; SIMP_TAC[]];
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt c * r` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN
          ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
          ASM_MESON_TAC[IN_BALL; REAL_LT_IMP_LE];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `mfd_length atlas (g:A->real^N^N)
         (\t. chart_inv (U:A->bool,phi:A->real^N) (phi x + t % (phi y - phi x)))
         (&0) (&1)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
          `g:A->real^N^N`;
          `\t. chart_inv (U:A->bool,phi:A->real^N) (phi x + t % (phi y - phi x))`;
          `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC GRGD_SEGMENT_LENGTH_UPPER THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `c:real`;
                              `cball((phi:A->real^N) x,r)`] THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]]];
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      ASM_MESON_TAC[mfd_joinable];
      ALL_TAC] THEN
    X_GEN_TAC `L:real` THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]);;

let MFD_DIST_EQ_0 = prove
 (`!top atlas (g:A->real^N^N) x y.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_joinable (top,atlas) x y
        ==> (mfd_dist (top,atlas) g x y = &0 <=> x = y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `U:A->bool`; `phi:A->real^N`; `x:A`]
               MFD_DIST_LOCAL_EUCLIDEAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `c1:real`
    (X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < d ==> ~(d = &0)`) THEN
  ASM_CASES_TAC `(y:A) IN U /\ (phi:A->real^N) y IN ball(phi x,r)` THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `c1 * dist((phi:A->real^N) x,phi y)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[GSYM DIST_NZ] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(x:A = y)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `U:A->bool`; `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `c1 * r` THEN
    ASM_SIMP_TAC[REAL_LT_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* Joinable classes, balls, and the manifold topology as the metric          *)
(* topology of each joinable class (Lee, ISM 2nd ed., Thm 13.29, p. 339).    *)
(* ------------------------------------------------------------------------- *)

(* Points joined by a coordinate segment. *)

let GRGD_CHART_JOINABLE = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) y z.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ y IN U /\ z IN U /\
        segment[phi y,phi z] SUBSET IMAGE phi U
        ==> mfd_joinable (top,atlas) y z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `(phi:A->real^N) y`;
                `(phi:A->real^N) z`] GRGD_CHART_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `\t. chart_inv (U:A->bool,phi:A->real^N) (phi y + t % (phi z - phi y))`;
    `&0`; `&1`] MFD_C1_CURVE_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
              VECTOR_ARITH `x + (y - x):real^N = y`] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_SIMP_TAC[]);;

(* A coordinate ball around a point of a chart, inside the chart image. *)

let GRGD_CHART_BALL = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) y.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ y IN U
        ==> ?r. &0 < r /\ ball(phi y,r) SUBSET IMAGE phi U /\
                open_in top {z | z IN U /\ phi z IN ball(phi y,r)} /\
                y IN {z | z IN U /\ phi z IN ball(phi y,r)} /\
                !z. z IN U /\ phi z IN ball(phi y,r) ==> mfd_joinable (top,atlas) y z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) y` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN MATCH_MP_TAC GRGD_CHART_JOINABLE THEN
    MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^N`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball((phi:A->real^N) y,r)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(phi:A->real^N) y`; `r:real`] CONVEX_BALL) THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL]]);;

let MFD_JOINABLE_OPEN = prove
 (`!top atlas (x:A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)
        ==> open_in top {y | mfd_joinable (top,atlas) x y}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) y`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `y:A`] GRGD_CHART_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{z:A | z IN U /\ (phi:A->real^N) z IN ball(phi y,r)}` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THEN
  EXISTS_TAC `y:A` THEN ASM_SIMP_TAC[]);;

let GRGD_JOINABLE_COMPLEMENT_OPEN = prove
 (`!top atlas (x:A).
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)
        ==> open_in top (topspace top DIFF {y | mfd_joinable (top,atlas) x y})`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `{y | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) z y}` THEN
  ASM_SIMP_TAC[MFD_JOINABLE_OPEN; IN_ELIM_THM; MFD_JOINABLE_REFL] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x (z:A)` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `w:A` THEN
  ASM_MESON_TAC[MFD_JOINABLE_SYM]);;

let MFD_JOINABLE_CONNECTED_COMPONENT = prove
 (`!top atlas (x:A) y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)
        ==> (mfd_joinable (top,atlas) x y <=> connected_component_of top x y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[mfd_joinable; connected_component_of] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (gamma:real->A) (real_interval[&0,&1])` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval[&0,&1])` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
      REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL;
                  CONNECTED_IN_EUCLIDEANREAL_INTERVAL];
      REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
       [EXISTS_TAC `&0`; EXISTS_TAC `&1`] THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    REWRITE_TAC[connected_component_of] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(c:A->bool) SUBSET
      {y | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y}`
     (fun th -> MP_TAC th THEN ASM SET_TAC[]) THEN
    MP_TAC(ISPECL [`top:A topology`;
       `{y | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y}`;
       `topspace top DIFF
        {y | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y}`;
                   `c:A->bool`] CONNECTED_IN_SUBSET_SEPARATED_UNION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[SEPARATED_IN_OPEN_SETS; MFD_JOINABLE_OPEN;
                     GRGD_JOINABLE_COMPLEMENT_OPEN] THEN SET_TAC[];
        FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE) THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MFD_JOINABLE_REFL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[]]);;

let MFD_JOINABLE_CONNECTED = prove
 (`!top atlas (x:A) y.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        connected_space top /\ x IN topspace top /\ y IN topspace top
        ==> mfd_joinable (top,atlas) x y`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MFD_JOINABLE_CONNECTED_COMPONENT] THEN
  REWRITE_TAC[connected_component_of] THEN EXISTS_TAC `topspace top:A->bool` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE]);;

(* The upper half of the local comparison needs no Hausdorff hypothesis. *)

let GRGD_DIST_LOCAL_UPPER = prove
 (`!top atlas (g:A->real^N^N) U phi y.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ y IN U
        ==> ?r c2. &0 < r /\ &0 <= c2 /\
                   !z. z IN U /\ phi z IN ball(phi y,r)
                       ==> mfd_joinable (top,atlas) y z /\
                           mfd_dist (top,atlas) g y z <= c2 * dist(phi y,phi z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r. &0 < r /\ cball((phi:A->real^N) y,r) SUBSET IMAGE phi U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (IMAGE (phi:A->real^N) U)` THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `U:A->bool`; `phi:A->real^N`; `cball((phi:A->real^N) y,r)`]
                GRGD_METRIC_BOUNDS) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `sqrt C`] THEN
  ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_TRANS; REAL_LT_IMP_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[(phi:A->real^N) y,phi z] SUBSET ball(phi y,r)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(phi:A->real^N) y`; `r:real`] CONVEX_BALL) THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `(phi:A->real^N) y`;
                `(phi:A->real^N) z`] GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `(\t. chart_inv (U:A->bool,phi:A->real^N) (phi y + t % (phi z - phi y))) (&0) = y /\
    (\t. chart_inv (U:A->bool,phi:A->real^N) (phi y + t % (phi z - phi y))) (&1) = z`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                VECTOR_ARITH `x + (y - x):real^N = y`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `\t. chart_inv (U:A->bool,phi:A->real^N) (phi y + t % (phi z - phi y))`;
      `&0`; `&1`] MFD_C1_CURVE_JOINABLE) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `mfd_length atlas (g:A->real^N^N)
       (\t. chart_inv (U:A->bool,phi:A->real^N) (phi y + t % (phi z - phi y)))
       (&0) (&1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `g:A->real^N^N`;
        `\t. chart_inv (U:A->bool,phi:A->real^N) (phi y + t % (phi z - phi y))`;
        `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC GRGD_SEGMENT_LENGTH_UPPER THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `c:real`;
                            `cball((phi:A->real^N) y,r)`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]]]);;

(* A neighbourhood of y on which d(y,.) < e. *)

let GRGD_DIST_SMALL_NBHD = prove
 (`!top atlas (g:A->real^N^N) y e.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        y IN topspace top /\ &0 < e
        ==> ?T. open_in top T /\ y IN T /\
                !z. z IN T ==> mfd_joinable (top,atlas) y z /\
                               mfd_dist (top,atlas) g y z < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) y`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `U:A->bool`; `phi:A->real^N`; `y:A`]
               GRGD_DIST_LOCAL_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{z:A | z IN U /\
                     (phi:A->real^N) z IN ball(phi y,min r (e / (c2 + &1)))}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GRGD_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; REAL_LT_MIN] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 <= c ==> &0 < c + &1`];
    X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL; REAL_LT_MIN] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[IN_BALL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c2 + &1) * dist((phi:A->real^N) y,phi z) < e` MP_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= c ==> &0 < c + &1`];
      MP_TAC(ISPECL [`(phi:A->real^N) y`; `(phi:A->real^N) z`] DIST_POS_LE) THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) y z <=
                   c2 * dist((phi:A->real^N) y,phi z)` THEN
      REAL_ARITH_TAC]]);;

let GRGD_JOINABLE_CLASS = prove
 (`!top atlas (x:A) y z.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        mfd_joinable (top,atlas) x y /\ mfd_joinable (top,atlas) x z
        ==> mfd_joinable (top,atlas) y z`,
  MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS]);;

let MFD_BALL_OPEN = prove
 (`!top atlas (g:A->real^N^N) x r.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> open_in top (mfd_ball (top,atlas) g x r)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `r - mfd_dist (top,atlas) (g:A->real^N^N) x y`]
                GRGD_DIST_SMALL_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LT] THEN ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:A->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MFD_CBALL_CLOSED = prove
 (`!top atlas (g:A->real^N^N) x r.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> closed_in top (mfd_cball (top,atlas) g x r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_cball; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `z:A` THEN
  REWRITE_TAC[IN_DIFF; mfd_cball; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) z` THENL
   [SUBGOAL_THEN `r < mfd_dist (top,atlas) (g:A->real^N^N) x z` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_NOT_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `z:A`;
                   `mfd_dist (top,atlas) (g:A->real^N^N) x z - r`]
                  GRGD_DIST_SMALL_NBHD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_SUB_LT]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w0:A->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `mfd_dist (top,atlas) (g:A->real^N^N) x z <=
      mfd_dist (top,atlas) g x w + mfd_dist (top,atlas) g w z`
    MP_TAC THENL
     [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_MESON_TAC[MFD_JOINABLE_SYM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `w:A`; `z:A`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC
     `{w | mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (z:A) w}` THEN
    ASM_SIMP_TAC[MFD_JOINABLE_OPEN; IN_ELIM_THM; MFD_JOINABLE_REFL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `w:A` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    UNDISCH_TAC
     `~mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) z` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_TRANS THEN EXISTS_TAC `w:A` THEN
    ASM_MESON_TAC[MFD_JOINABLE_SYM]]);;

let MFD_CENTRE_IN_BALL = prove
 (`!top atlas (g:A->real^N^N) x r.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g
        ==> (x IN mfd_ball (top,atlas) g x r <=> x IN topspace top /\ &0 < r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM; MFD_JOINABLE_REFL] THEN
  ASM_CASES_TAC `(x:A) IN topspace top` THEN ASM_SIMP_TAC[MFD_DIST_REFL]);;

let MFD_BALL_NEIGHBOURHOOD_BASE = prove
 (`!top atlas (g:A->real^N^N) W x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ open_in top W /\ x IN W
        ==> ?r. &0 < r /\ mfd_ball (top,atlas) g x r SUBSET W`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `U:A->bool`; `phi:A->real^N`; `x:A`]
               MFD_DIST_LOCAL_EUCLIDEAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `c1:real`
    (X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^N) (U INTER W))` MP_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real^N) x`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?rho. &0 < rho /\ rho <= r0 /\
          ball((phi:A->real^N) x,rho) SUBSET IMAGE phi (U INTER W)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min r0 rho0` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball((phi:A->real^N) x,rho0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `c1 * rho` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(y:A) IN U /\ (phi:A->real^N) y IN ball(phi x,r0)` THENL
   [SUBGOAL_THEN `(phi:A->real^N) y IN ball(phi x,rho)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN
      SUBGOAL_THEN
       `c1 * dist((phi:A->real^N) x,phi y) <
        c1 * rho` MP_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `mfd_dist (top,atlas) (g:A->real^N^N) x y` THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
      DISCH_TAC THEN
      SUBGOAL_THEN `(phi:A->real^N) y IN IMAGE phi (U INTER W)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:A) = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_CHART_INJ THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
        `U:A->bool`; `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `c1 * r0 <= mfd_dist (top,atlas) (g:A->real^N^N) x y`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `c1 * rho <= c1 * r0` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC]);;

(* Each joinable class is a metric space (metric.ml) for mfd_dist. *)

let MFD_METRIC = prove
 (`!top atlas (g:A->real^N^N) x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g
        ==> is_metric_space ({y | mfd_joinable (top,atlas) x y},
                             \(y,z). mfd_dist (top,atlas) g y z) /\
            mspace (mfd_metric (top,atlas) g x) =
            {y | mfd_joinable (top,atlas) x y} /\
            (!y z. mdist (mfd_metric (top,atlas) g x) (y,z) =
                   mfd_dist (top,atlas) g y z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[is_metric_space; IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN STRIP_TAC THENL
     [MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_MESON_TAC[GRGD_JOINABLE_CLASS];
      MATCH_MP_TAC MFD_DIST_EQ_0 THEN ASM_MESON_TAC[GRGD_JOINABLE_CLASS];
      MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_DIST_TRIANGLE THEN ASM_MESON_TAC[GRGD_JOINABLE_CLASS]];
    DISCH_THEN(MP_TAC o MATCH_MP METRIC) THEN SIMP_TAC[mfd_metric]]);;

let GRGD_MBALL_CLASS = prove
 (`!top atlas (g:A->real^N^N) x y r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_joinable (top,atlas) x y
        ==> mball (mfd_metric (top,atlas) g x) (y,r) = mfd_ball (top,atlas) g y r /\
            mcball (mfd_metric (top,atlas) g x) (y,r) = mfd_cball (top,atlas) g y r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `x:A`] MFD_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_MBALL; IN_MCBALL; mfd_ball; mfd_cball; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[GRGD_JOINABLE_CLASS; MFD_JOINABLE_TRANS]);;

let MFD_MTOPOLOGY = prove
 (`!top atlas (g:A->real^N^N) x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g
        ==> mtopology (mfd_metric (top,atlas) g x) =
            subtopology top {y | mfd_joinable (top,atlas) x y}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TOPOLOGY_EQ] THEN X_GEN_TAC `s:A->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; MFD_JOINABLE_OPEN] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `x:A`] MFD_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y`
    ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) y r` THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN; MFD_CENTRE_IN_BALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]; ALL_TAC] THEN
    ASM_MESON_TAC[GRGD_MBALL_CLASS];
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `g:A->real^N^N`; `s:A->bool`; `y:A`]
                 MFD_BALL_NEIGHBOURHOOD_BASE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) y`
    ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[GRGD_MBALL_CLASS]]);;

let MFD_BALL_MBALL = prove
 (`!top atlas (g:A->real^N^N) x r.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top
        ==> mfd_ball (top,atlas) g x r = mball (mfd_metric (top,atlas) g x) (x,r) /\
            mfd_cball (top,atlas) g x r = mcball (mfd_metric (top,atlas) g x) (x,r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `x:A`; `x:A`; `r:real`] GRGD_MBALL_CLASS) THEN
  ASM_REWRITE_TAC[MFD_JOINABLE_REFL] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Completeness, and sanity/teeth tests for open subsets of real^N with the  *)
(* flat metric (Lee, ISM 2nd ed., Example 13.26, p. 338).                     *)
(* ------------------------------------------------------------------------- *)

let MFD_COMPACT_IMP_COMPLETE = prove
 (`!top atlas (g:A->real^N^N).
        compact_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g
        ==> mfd_complete (top,atlas) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_complete] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_SIMP_TAC[MFD_CBALL_CLOSED]);;

let MFD_COMPLETE_IMP_MCOMPLETE = prove
 (`!top atlas (g:A->real^N^N) x.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g
        ==> mcomplete (mfd_metric (top,atlas) g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `g:A->real^N^N`; `x:A`] MFD_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mcomplete] THEN X_GEN_TAC `s:num->A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `&1` o CONJUNCT2 o GEN_REWRITE_RULE I [cauchy_in]) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN
   `!n. mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) (x:A) ((s:num->A) n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num` o CONJUNCT1 o GEN_REWRITE_RULE I [cauchy_in]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact_in (mtopology (mfd_metric (top,atlas) (g:A->real^N^N) x))
      (mcball (mfd_metric (top,atlas) g x) ((s:num->A) N,&1))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MFD_MTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
    MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                  `g:A->real^N^N`; `x:A`; `(s:num->A) N`; `&1`]
                 GRGD_MBALL_CLASS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_complete (top,atlas) (g:A->real^N^N)` THEN
      REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      REWRITE_TAC[mfd_cball; SUBSET; IN_ELIM_THM] THEN
      ASM_MESON_TAC[MFD_JOINABLE_TRANS]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IN_IMP_MCOMPLETE) THEN
  REWRITE_TAC[mcomplete] THEN
  DISCH_THEN(MP_TAC o SPEC `\n. (s:num->A)(n + N)`) THEN ANTS_TAC THENL
   [REWRITE_TAC[cauchy_in; SUBMETRIC; IN_INTER] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      UNDISCH_TAC
       `!n n'. N <= n /\ N <= n'
               ==> mdist (mfd_metric (top,atlas) (g:A->real^N^N) x)
                         ((s:num->A) n,s n') < &1` THEN
      DISCH_THEN(MP_TAC o SPECL [`N:num`; `n + N:num`]) THEN
      REWRITE_TAC[LE_REFL; LE_ADDR; IN_MCBALL] THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `e:real` o CONJUNCT2 o
        GEN_REWRITE_RULE I [cauchy_in]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
      EXISTS_TAC `M:num` THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:A` MP_TAC) THEN
  REWRITE_TAC[MTOPOLOGY_SUBMETRIC; LIMIT_SUBTOPOLOGY] THEN STRIP_TAC THEN
  EXISTS_TAC `l:A` THEN MATCH_MP_TAC LIMIT_SEQUENTIALLY_OFFSET_REV THEN
  EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[]);;

(* Open subsets of real^N with the identity chart and the flat metric. *)

let GRGD_EUCLID_ATLAS = prove
 (`!S:real^N->bool.
        open S ==> smooth_manifold_atlas (subtopology euclidean S) {(S,\x:real^N. x)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_manifold_atlas; IN_SING; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IMAGE_ID; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT;
                HOMEOMORPHIC_MAP_ID] THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST1_TAC)
      (CONJUNCTS_THEN SUBST1_TAC)) THEN
    EXISTS_TAC `\x:real^N. x` THEN REWRITE_TAC[SMOOTH_MAP_ON_ID]]);;

let GRGD_EUCLID_METRIC_LOCAL = prove
 (`!S:real^N->bool y.
        open S /\ y IN S
        ==> metric_local {(S,\x:real^N. x)} (S,\x. x) (\x. mat 1) y = mat 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean S) {(S,\x:real^N. x)}`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GRGD_EUCLID_ATLAS]; ALL_TAC] THEN
  REWRITE_TAC[metric_local] THEN
  SUBGOAL_THEN `chart_inv (S:real^N->bool,\x:real^N. x) y = y` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`; `{(S:real^N->bool,\x:real^N. x)}`;
                   `S:real^N->bool`; `\x:real^N. x`] CHART_INV) THEN
    ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_at {(S,\x:real^N. x)} (y:real^N) = (S,\x. x)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`; `{(S:real^N->bool,\x:real^N. x)}`;
                   `y:real^N`] CHART_AT) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_SING] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`; `{(S:real^N->bool,\x:real^N. x)}`;
                 `S:real^N->bool`; `\x:real^N. x`; `y:real^N`] CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

let MFD_EUCLIDEAN_OPEN = prove
 (`!S:real^N->bool.
        open S
        ==> hausdorff_space (subtopology euclidean S) /\
            smooth_manifold_atlas (subtopology euclidean S) {(S,\x:real^N. x)} /\
            riemannian_metric {(S,\x:real^N. x)} (\x. mat 1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
    REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN];
    ASM_SIMP_TAC[GRGD_EUCLID_ATLAS];
    REWRITE_TAC[riemannian_metric; IN_SING] THEN GEN_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND; IMAGE_ID; metric_field] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
      EXISTS_TAC `\y:real^N. (vectorize:real^N^N->real^(N,N)finite_prod) (mat 1)` THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; o_THM] THEN
      ASM_SIMP_TAC[GRGD_EUCLID_METRIC_LOCAL];
      ASM_SIMP_TAC[GRGD_EUCLID_METRIC_LOCAL; TRANSP_MAT; MATRIX_VECTOR_MUL_LID;
                   DOT_POS_LT]]]);;

let MFD_DIST_EUCLIDEAN = prove
 (`!S x y:real^N.
        open S /\ convex S /\ x IN S /\ y IN S
        ==> mfd_joinable (subtopology euclidean S,{(S,\z:real^N. z)}) x y /\
            mfd_dist (subtopology euclidean S,{(S,\z:real^N. z)}) (\z. mat 1) x y =
            dist(x,y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^N->bool` MFD_EUCLIDEAN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[x:real^N,y] SUBSET S` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z v:real^N.
        z IN S
        ==> &1 * norm v pow 2 <=
            v dot (metric_local {(S,\z:real^N. z)} (S,\z. z) (\z. mat 1) z ** v) /\
            v dot (metric_local {(S,\z:real^N. z)} (S,\z. z) (\z. mat 1) z ** v) <=
            &1 * norm v pow 2`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GRGD_EUCLID_METRIC_LOCAL; MATRIX_VECTOR_MUL_LID; NORM_POW_2;
                 REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_joinable (subtopology euclidean S,{(S,\z:real^N. z)}) x y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GRGD_CHART_JOINABLE THEN
    MAP_EVERY EXISTS_TAC [`S:real^N->bool`; `\z:real^N. z`] THEN
    ASM_REWRITE_TAC[IN_SING; IMAGE_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`;
                   `{(S:real^N->bool,\z:real^N. z)}`; `S:real^N->bool`;
                   `\z:real^N. z`; `x:real^N`; `y:real^N`] GRGD_CHART_SEGMENT) THEN
    ASM_REWRITE_TAC[IN_SING; IMAGE_ID] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `mfd_length {(S:real^N->bool,\z:real^N. z)} (\z. mat 1)
        (\t. chart_inv (S,\z:real^N. z) (x + t % (y - x))) (&0) (&1)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`;
                     `{(S:real^N->bool,\z:real^N. z)}`; `(\z. mat 1):real^N->real^N^N`;
                     `\t. chart_inv (S:real^N->bool,\z:real^N. z) (x + t % (y - x))`;
                     `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                  VECTOR_ARITH `x + (y - x):real^N = y`] THEN
      MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`;
                     `{(S:real^N->bool,\z:real^N. z)}`; `S:real^N->bool`;
                     `\z:real^N. z`] CHART_INV) THEN
      ASM_REWRITE_TAC[IN_SING] THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`;
                     `{(S:real^N->bool,\z:real^N. z)}`; `(\z. mat 1):real^N->real^N^N`;
                     `S:real^N->bool`; `\z:real^N. z`; `x:real^N`; `y:real^N`;
                     `&1`; `&1`; `S:real^N->bool`] GRGD_SEGMENT_LENGTH_UPPER) THEN
      ASM_REWRITE_TAC[IN_SING; IMAGE_ID; SUBSET_REFL; SQRT_1; REAL_MUL_LID]];
    REWRITE_TAC[mfd_dist] THEN MATCH_MP_TAC REAL_LE_INF THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN
      ASM_MESON_TAC[mfd_joinable];
      ALL_TAC] THEN
    X_GEN_TAC `L:real` THEN REWRITE_TAC[GRGD_IN_LENGTHS] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology euclidean (S:real^N->bool)`;
                   `{(S:real^N->bool,\z:real^N. z)}`; `(\z. mat 1):real^N->real^N^N`;
                   `gamma:real->real^N`; `&0`; `&1`; `S:real^N->bool`;
                   `\z:real^N. z`; `&1`; `&1`; `S:real^N->bool`]
                  GRGD_CHART_LENGTH_LOWER) THEN
    ASM_REWRITE_TAC[IN_SING; REAL_POS; SQRT_1; REAL_MUL_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gamma:real->real^N) t IN topspace (subtopology euclidean S)`
    MP_TAC THENL
     [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SIMP_TAC[]]]);;

let MFD_COMPLETE_EUCLIDEAN = prove
 (`mfd_complete (euclidean:(real^N)topology,{((:real^N),\x:real^N. x)})
                (\x. mat 1)`,
  REWRITE_TAC[mfd_complete; mfd_cball; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `r:real`] THEN
  MP_TAC(ISPEC `(:real^N)` MFD_DIST_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; CONVEX_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{y:real^N | mfd_joinable (euclidean,{((:real^N),\x:real^N. x)}) x y /\
                mfd_dist (euclidean,{((:real^N),\x:real^N. x)}) (\x. mat 1) x y <= r} =
    cball(x,r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CBALL] THEN ASM_MESON_TAC[];
    REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_CBALL]]);;

let MFD_NOT_COMPLETE_EUCLIDEAN_BALL = prove
 (`~mfd_complete (subtopology euclidean (ball(vec 0:real^N,&1)),
                  {(ball(vec 0:real^N,&1),\x:real^N. x)})
                 (\x. mat 1)`,
  REWRITE_TAC[mfd_complete; NOT_FORALL_THM; NOT_IMP] THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `&1`] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; CENTRE_IN_BALL; REAL_LT_01] THEN
  SUBGOAL_THEN
   `mfd_cball (subtopology euclidean (ball(vec 0:real^N,&1)),
               {(ball(vec 0:real^N,&1),\x:real^N. x)}) (\x. mat 1) (vec 0) (&1) =
    ball(vec 0,&1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; mfd_cball; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    EQ_TAC THENL
     [MESON_TAC[MFD_JOINABLE_IN_TOPSPACE; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`ball(vec 0:real^N,&1)`; `vec 0:real^N`; `y:real^N`]
                    MFD_DIST_EUCLIDEAN) THEN
      ASM_REWRITE_TAC[OPEN_BALL; CONVEX_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `(y:real^N) IN ball(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC];
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; SUBSET_REFL] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `ball(vec 0:real^N,&1)` CLOPEN) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; OPEN_BALL] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_UNIV; IN_BALL_0] THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `vec 0:real^N` THEN REWRITE_TAC[NORM_0; REAL_LT_01];
      EXISTS_TAC `basis 1:real^N` THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC]]);;

