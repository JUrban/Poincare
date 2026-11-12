(* ========================================================================= *)
(* Unit pc_geo_lisom (geodesics layer): local isometries.  They map          *)
(* geodesics to geodesics (MFD_LOCAL_ISOMETRY_GEODESIC, by the naturality of *)
(* the Christoffel symbols LCHRISTOFFEL_PULLBACK), commute with exp          *)
(* (MFD_LOCAL_ISOMETRY_EXP) and are determined by their 1-jet at a point     *)
(* (MFD_LOCAL_ISOMETRY_RIGID); Cartan's lemma for curvature 1                *)
(* (MFD_CARTAN_CONST1, from MFD_EXP_DIFFERENTIAL_CONST1).                    *)
(* ========================================================================= *)

needs "src/pc_geo_const.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Chart representatives of a local isometry: open domains,                  *)
(* smoothness, the metric as a pullback, and invertible derivatives.         *)
(* ========================================================================= *)

let GEOI_REP_FACTS = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f c c'.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\
        c IN atlas /\ c' IN atlas'
        ==> open (IMAGE (SND c) {x | x IN FST c INTER W /\ f x IN FST c'}) /\
            smooth_map_on (IMAGE (SND c) {x | x IN FST c INTER W /\ f x IN FST c'})
                          (SND c' o f o chart_inv c) /\
            !y. y IN IMAGE (SND c) {x | x IN FST c INTER W /\ f x IN FST c'}
                ==> metric_local atlas c g y =
                    mpullback (SND c' o f o chart_inv c) (metric_local atlas' c' g') y /\
                    (SND c' o f o chart_inv c) y IN IMAGE (SND c') (FST c') /\
                    ~(det(matrix(frechet_derivative (SND c' o f o chart_inv c) (at y))) =
                      &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_local_isometry]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                 `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^N))->bool) W (f:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N) y =
    mpullback (SND (c':(B->bool)#(B->real^N)) o (f:A->B) o chart_inv c)
              (metric_local atlas' c' (g':B->real^N^N)) y`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(REWRITE_RULE[IN_IMAGE; IN_ELIM_THM; IN_INTER]
   (ASSUME `(y:real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N)))
              {x | x IN FST c INTER W /\ (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the derivative is invertible since the pulled back metric is *)
  MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `SND (c:(A->bool)#(A->real^N)) (x:A)`] LRG_METRIC_INVERTIBLE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ASM_REWRITE_TAC[mpullback; DET_MUL; DET_TRANSP] THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]);;

(* ========================================================================= *)
(* The image of a geodesic under a local isometry satisfies the              *)
(* geodesic equation in every chart of the target (naturality of the        *)
(* Christoffel symbols under the chart representative, inverted locally by *)
(* SMOOTH_INVERSE_FUNCTION_THEOREM).                                         *)
(* ========================================================================= *)

let GEOI_GEODESIC_REP = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f (gamma:real->A) J c c'
    v t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\
        c IN atlas /\ c' IN atlas' /\ real_open J /\
        continuous_map (subtopology euclideanreal J,top) gamma /\
        (!t. t IN J ==> gamma t IN W) /\
        (!t. t IN J /\ gamma t IN FST c
             ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t) (at (lift t)) /\
                 ((\s. v(drop s)) has_vector_derivative
                  --(christoffel (metric_local atlas c g) (SND c (gamma t)) (v t) (v t)))
                 (at (lift t))) /\
        t IN J /\ gamma t IN FST c /\ f(gamma t) IN FST c'
        ==> ((\s. SND c' (f(gamma(drop s)))) has_vector_derivative
             frechet_derivative (SND c' o f o chart_inv c) (at (SND c (gamma t))) (v t))
            (at (lift t)) /\
            ((\s. frechet_derivative (SND c' o f o chart_inv c)
                                     (at (SND c (gamma(drop s)))) (v(drop s)))
             has_vector_derivative
             --(christoffel (metric_local atlas' c' g') (SND c' (f(gamma t)))
                  (frechet_derivative (SND c' o f o chart_inv c) (at (SND c (gamma t))) (v t))
                  (frechet_derivative (SND c' o f o chart_inv c) (at (SND c (gamma t)))
                                      (v t))))
            (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP
   (CONJ (ASSUME `(t:real) IN J`)
         (ASSUME `(gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))`))) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `W:A->bool`; `f:A->B`; `c:(A->bool)#(A->real^N)`;
                 `c':(B->bool)#(B->real^N)`] GEOI_REP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = IMAGE (SND (c:(A->bool)#(A->real^N)))
                    {x | x IN FST c INTER W /\ (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}` THEN
  ABBREV_TAC `Fr = SND (c':(B->bool)#(B->real^N)) o (f:A->B) o
                   chart_inv (c:(A->bool)#(A->real^N))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  MP_TAC(ASSUME `mfd_local_isometry (top,atlas:((A->bool)#(A->real^N))->bool)
                   (g:A->real^N^N) (top',atlas':((B->bool)#(B->real^N))->bool)
                   (g':B->real^N^N) W (f:A->B)`) THEN
  REWRITE_TAC[mfd_local_isometry] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                 `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t) IN D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the curve stays in the chart domains near t *)
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `{x | x IN FST (c:(A->bool)#(A->real^N)) INTER W /\
                       (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}`;
                 `t:real`] GEOL_CURVE_NEAR) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Fr:real^N->real^N) differentiable at
                (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `D:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `(Fr:real^N->real^N) o (\s. SND (c:(A->bool)#(A->real^N))
                                              ((gamma:real->A)(drop s)))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(drop s - t) < d` ASSUME_TAC THENL
       [UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
        ALL_TAC] THEN
      EXPAND_TAC "Fr" THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x:A. x IN FST (c:(A->bool)#(A->real^N)) ==> chart_inv c (SND c x) = x`)
        (concl th))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
    MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN
    ASM_REWRITE_TAC[WITHIN_UNIV; LIFT_DROP] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  (* the second order equation *)
  MP_TAC(ISPECL
   [`D:real^N->bool`; `Fr:real^N->real^N`;
    `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
    `\s. (v:real->real^N)(drop s)`; `(v:real->real^N) t`;
    `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    (SND c ((gamma:real->A) t)) ((v:real->real^N) t) (v t))`;
    `lift t`] GEOL_FRECHET_ALONG) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Fr:real^N->real^N)
                         (at (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* invert Fr near the point *)
  MP_TAC(ISPECL [`Fr:real^N->real^N`; `D:real^N->bool`;
                 `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` (X_CHOOSE_THEN `u0:real^N->bool`
    (X_CHOOSE_THEN `Fi:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(u0:real^N->bool) SUBSET IMAGE (SND (c':(B->bool)#(B->real^N))) (FST c')`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `diffeomorphism_on t0 u0 (Fr:real^N->real^N) Fi`) THEN
    REWRITE_TAC[diffeomorphism_on] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM(CONJUNCT1(CONJUNCT2(CONJUNCT2 th)))]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "pt" (MP_TAC o SPEC `z:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (Fr:real^N->real^N)
      (at (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)))
      (christoffel (metric_local atlas c (g:A->real^N^N))
                   (SND c (gamma t)) ((v:real->real^N) t) (v t)) =
    christoffel (metric_local atlas' (c':(B->bool)#(B->real^N)) (g':B->real^N^N))
                (Fr (SND c (gamma t)))
                (frechet_derivative Fr (at (SND c (gamma t))) (v t))
                (frechet_derivative Fr (at (SND c (gamma t))) (v t)) +
    dd2 Fr (SND c (gamma t)) (v t) (v t)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                  (SND c ((gamma:real->A) t)) ((v:real->real^N) t) (v t) =
      christoffel (mpullback (Fr:real^N->real^N)
                     (metric_local atlas' (c':(B->bool)#(B->real^N)) (g':B->real^N^N)))
                  (SND c (gamma t)) (v t) (v t)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `D:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o SPEC `z:real^N`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LCHRISTOFFEL_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`u0:real^N->bool`; `t0:real^N->bool`; `Fi:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c':(B->bool)#(B->real^N))) (FST c')` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `riemannian_metric atlas' (g':B->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Fr:real^N->real^N) (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)) =
    SND (c':(B->bool)#(B->real^N)) ((f:A->B)(gamma t))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Fr" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[dd2] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[LINEAR_NEG] THEN
  MATCH_MP_TAC(MESON[] `(a:real^N) = b ==> (f has_vector_derivative a) net
                                         ==> (f has_vector_derivative b) net`) THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Local isometries map geodesics to geodesics, with velocity                *)
(* the image under the differential (MFD_LOCAL_ISOMETRY_GEODESIC).            *)
(* ========================================================================= *)

let MFD_LOCAL_ISOMETRY_GEODESIC = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f (gamma:real->A) J.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\
        mfd_geodesic (top,atlas) g gamma J /\ (!t. t IN J ==> gamma t IN W)
        ==> mfd_geodesic (top',atlas') g' (f o gamma) J /\
            !t. t IN J
                ==> mfd_vel atlas' (f o gamma) t =
                    mfd_differential atlas atlas' f (gamma t) (mfd_vel atlas gamma t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `mfd_geodesic (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                   (gamma:real->A) J`) THEN
  REWRITE_TAC[mfd_geodesic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "geq")))) THEN
  MP_TAC(ASSUME `mfd_local_isometry (top,atlas:((A->bool)#(A->real^N))->bool)
                   (g:A->real^N^N) (top',atlas':((B->bool)#(B->real^N))->bool)
                   (g':B->real^N^N) W (f:A->B)`) THEN
  REWRITE_TAC[mfd_local_isometry] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN J ==> (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> (f:A->B)((gamma:real->A) t) IN topspace top'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map] o check
      (fun th -> can (term_match []
        `continuous_map (subtopology (top:A topology) W,top':B topology) f`) (concl th))) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the chart computation at a time t, in the preferred chart at gamma t *)
  SUBGOAL_THEN
   `!c' t. c' IN atlas' /\ t IN J /\ (f:A->B)((gamma:real->A) t) IN FST c'
           ==> ?v d. &0 < d /\
                     (!s. abs(s - t) < d
                          ==> s IN J /\
                              ((\r. SND (c':(B->bool)#(B->real^N))
                                       (f(gamma(drop r)))) has_vector_derivative v s)
                              (at (lift s))) /\
                     ((\s. v(drop s)) has_vector_derivative
                      --(christoffel (metric_local atlas' c' (g':B->real^N^N))
                           (SND c' (f(gamma t))) (v t) (v t))) (at (lift t)) /\
                     v t = frechet_derivative
                             (SND c' o f o
                              chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                                  (gamma t)))
                             (at (SND (chart_at atlas (gamma t)) (gamma t)))
                             (vector_derivative
                                (\s. SND (chart_at atlas (gamma t)) (gamma(drop s)))
                                (at (lift t)))`
  (LABEL_TAC "loc") THENL
   [MAP_EVERY X_GEN_TAC [`c':(B->bool)#(B->real^N)`; `t:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) t`] CHART_AT) THEN
    ASM_SIMP_TAC[] THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
    STRIP_TAC THEN
    USE_THEN "geq" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `vc:real->real^N` (LABEL_TAC "vc")) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                   `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                   `{x | x IN FST (c:(A->bool)#(A->real^N)) INTER W /\
                         (f:A->B) x IN FST (c':(B->bool)#(B->real^N))}`;
                   `t:real`] GEOL_CURVE_NEAR) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
    SUBGOAL_THEN
     `!s. abs(s - t) < d
          ==> ((\r. SND (c':(B->bool)#(B->real^N)) ((f:A->B)((gamma:real->A)(drop r))))
               has_vector_derivative
               frechet_derivative (SND c' o f o chart_inv (c:(A->bool)#(A->real^N)))
                 (at (SND c (gamma s))) ((vc:real->real^N) s)) (at (lift s)) /\
              ((\r. frechet_derivative (SND c' o f o chart_inv c)
                                       (at (SND c (gamma(drop r)))) (vc(drop r)))
               has_vector_derivative
               --(christoffel (metric_local atlas' c' (g':B->real^N^N))
                    (SND c' (f(gamma s)))
                    (frechet_derivative (SND c' o f o chart_inv c) (at (SND c (gamma s)))
                                        (vc s))
                    (frechet_derivative (SND c' o f o chart_inv c) (at (SND c (gamma s)))
                                        (vc s)))) (at (lift s))`
    (LABEL_TAC "rep") THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "near" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
      STRIP_TAC THEN MATCH_MP_TAC GEOI_GEODESIC_REP THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `top':B topology`; `W:A->bool`;
                            `J:real->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `\s. frechet_derivative (SND (c':(B->bool)#(B->real^N)) o (f:A->B) o
                                        chart_inv (c:(A->bool)#(A->real^N)))
                      (at (SND c ((gamma:real->A) s))) ((vc:real->real^N) s)` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      USE_THEN "near" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      USE_THEN "rep" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
      SIMP_TAC[];
      USE_THEN "rep" (MP_TAC o SPEC `t:real`) THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_SIMP_TAC[];
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      USE_THEN "vc" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_geodesic] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology (top:A topology) W` THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `c':(B->bool)#(B->real^N)` THEN DISCH_TAC THEN
    EXISTS_TAC `\t. vector_derivative (\s. SND (c':(B->bool)#(B->real^N))
                                             (((f:A->B) o (gamma:real->A))(drop s)))
                                      (at (lift t))` THEN
    X_GEN_TAC `t:real` THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    USE_THEN "loc" (MP_TAC o SPECL [`c':(B->bool)#(B->real^N)`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real->real^N` (X_CHOOSE_THEN `d:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dw")
        (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
    SUBGOAL_THEN
     `!s. abs(s - t) < d
          ==> vector_derivative (\r. SND (c':(B->bool)#(B->real^N))
                                       ((f:A->B)((gamma:real->A)(drop r))))
                                (at (lift s)) = (w:real->real^N) s`
    (LABEL_TAC "eqw") THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      USE_THEN "dw" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "eqw" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [USE_THEN "dw" (MP_TAC o SPEC `t:real`) THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\s. (w:real->real^N)(drop s)` THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN USE_THEN "eqw" MATCH_MP_TAC THEN
    UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
    ALL_TAC] THEN
  (* the velocity *)
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B)((gamma:real->A) t)`] CHART_AT) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  USE_THEN "loc" (MP_TAC o SPECL
    [`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B)((gamma:real->A) t))`;
     `t:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real->real^N` (X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dw")
      (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))))) THEN
  REWRITE_TAC[mfd_vel; mfd_differential; o_THM] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\s. SND (chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B)((gamma:real->A) t)))
             (f(gamma(drop s)))) (at (lift t)) = (w:real->real^N) t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    USE_THEN "dw" (MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* ========================================================================= *)
(* Local isometries commute with the exponential map                         *)
(* (MFD_LOCAL_ISOMETRY_EXP).                                                  *)
(* ========================================================================= *)

(* An open set of reals containing [a,b] contains (a - e, b + e). *)

let GEOI_INTERVAL_THICKEN = prove
 (`!O a b. real_open O /\ (!t. a <= t /\ t <= b ==> t IN O)
           ==> ?e. &0 < e /\ !t. a - e < t /\ t < b + e ==> t IN O`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^1) PCROSS IMAGE lift O`; `a:real`; `b:real`] CMPV_TUBE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; GSYM REAL_OPEN; PASTECART_IN_PCROSS; IN_UNIV;
                 FUN_IN_IMAGE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `t:real`]) THEN
  ASM_REWRITE_TAC[REAL_ABS_0; PASTECART_IN_PCROSS; IN_UNIV] THEN
  REWRITE_TAC[IN_IMAGE; LIFT_EQ] THEN MESON_TAC[]);;

let MFD_LOCAL_ISOMETRY_EXP = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f (x:A) v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f /\ x IN W /\
        v IN mfd_exp_dom (top,atlas) g x /\
        (!t. &0 <= t /\ t <= &1 ==> mfd_exp (top,atlas) g x (t % v) IN W)
        ==> mfd_differential atlas atlas' f x v IN mfd_exp_dom (top',atlas') g' (f x) /\
            f(mfd_exp (top,atlas) g x v) =
            mfd_exp (top',atlas') g' (f x) (mfd_differential atlas atlas' f x v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `mfd_local_isometry (top,atlas:((A->bool)#(A->real^N))->bool)
                   (g:A->real^N^N) (top',atlas':((B->bool)#(B->real^N))->bool)
                   (g':B->real^N^N) W (f:A->B)`) THEN
  REWRITE_TAC[mfd_local_isometry] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN (M:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    MP_TAC(ASSUME `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`) THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1 ==> t IN (M:real->bool)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ASSUME `is_realinterval (M:real->bool)`) THEN REWRITE_TAC[is_realinterval] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `&1`; `t:real`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN (M:real->bool) ==>
                    mfd_exp (top,atlas) (g:A->real^N^N) x (t % v) = gam t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* a neighbourhood J of [0,1] on which gam stays in W *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `M:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gam:real->A`; `M:real->bool`; `W:A->bool`]
    GEOL_CURVE_OPEN_TIMES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{s | s IN M /\ (gam:real->A) s IN W}`; `&0`; `&1`]
    GEOI_INTERVAL_THICKEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_SIMP_TAC[];
      SUBGOAL_THEN `(gam:real->A) t = mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_SUB_LZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `J = real_interval(--e,&1 + e)` THEN
  SUBGOAL_THEN
   `real_open J /\ is_realinterval J /\ &0 IN J /\ &1 IN J /\
    J SUBSET (M:real->bool) /\ (!t. t IN J ==> (gam:real->A) t IN W)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL;
                SUBSET] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g:A->real^N^N) gam J` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `M:real->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the image curve is the geodesic of f x in direction df(v) *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `W:A->bool`; `f:A->B`; `gam:real->A`; `J:real->bool`]
    MFD_LOCAL_ISOMETRY_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `&0`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(f:A->B) o (gam:real->A)`; `J:real->bool`;
                 `(f:A->B) x`;
                 `mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                    (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x v`]
    MFD_GEO_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_exp] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Injectivity balls shrink (MFD_INJ_BALL_MONO) and the                      *)
(* rigidity of local isometries (MFD_LOCAL_ISOMETRY_RIGID): the set of       *)
(* points near which f1 = f2 is open, closed in W (uniformly normal balls,   *)
(* MFD_UNIFORMLY_NORMAL, and exp balls are metric balls, MFD_EXP_BALL) and    *)
(* contains a.                                                                *)
(* ========================================================================= *)

(* Tangent balls of any radius are open. *)

let GEOI_TBALL_OPEN = prove
 (`!(g:A->real^N^N) x r. open(mfd_tball g x r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_tball; mfd_tnorm] THEN
  SUBGOAL_THEN
   `{v:real^N | sqrt(v dot ((g:A->real^N^N) x ** v)) < r} =
    {v | (\v. lift(sqrt(v dot (g x ** v)))) v IN {y:real^1 | y$1 < r}}`
  SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM; LIFT_COMPONENT]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT] THEN
  MP_TAC(ISPECL [`\v:real^N. lift(sqrt(v dot ((g:A->real^N^N) x ** v)))`;
                 `(:real^N)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let MFD_INJ_BALL_MONO = prove
 (`!top atlas (g:A->real^N^N) (x:A) r s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_inj_ball (top,atlas) g x r /\ s <= r
        ==> mfd_inj_ball (top,atlas) g x s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_inj_ball; mfd_param] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `e':A->real^N`)) ASSUME_TAC))) THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x s SUBSET mfd_tball g x r` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tball; SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `e':A->real^N` THEN MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`mfd_tball (g:A->real^N^N) x r`;
                        `IMAGE (mfd_exp (top,atlas) (g:A->real^N^N) x) (mfd_tball g x r)`] THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN; GEOI_TBALL_OPEN]);;

(* Maps agreeing near x have the same differential at x. *)

let GEOI_FRECHET_DERIVATIVE_LOCAL = prove
 (`!(f:real^M->real^N) h s x.
        open s /\ x IN s /\ (!y. y IN s ==> f y = h y)
        ==> frechet_derivative f (at x) = frechet_derivative h (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `h:real^M->real^N`] THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[]);;

let GEOI_DIFFERENTIAL_LOCAL = prove
 (`!top atlas atlas' (f1:A->B) f2 U x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        open_in top U /\ x IN U /\ (!z. z IN U ==> f1 z = f2 z)
        ==> mfd_differential atlas (atlas':((B->bool)#(B->real^M))->bool) f1 x =
            mfd_differential atlas atlas' f2 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_differential] THEN
  SUBGOAL_THEN `(f1:A->B) x = f2 x` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER U)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[]]);;

(* Metric balls: symmetry and the triangle inequality. *)

let GEOI_BALL_SYM = prove
 (`!top atlas (g:A->real^N^N) x y r.
        smooth_manifold_atlas top atlas /\
        y IN mfd_ball (top,atlas) g x r ==> x IN mfd_ball (top,atlas) g y r`,
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_SYM; MFD_DIST_SYM]);;

let GEOI_BALL_TRIANGLE = prove
 (`!top atlas (g:A->real^N^N) x y z r s.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        y IN mfd_ball (top,atlas) g x r /\ z IN mfd_ball (top,atlas) g y s
        ==> z IN mfd_ball (top,atlas) g x (r + s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `y:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Two local isometries with the same 1-jet at y agree on a normal ball     *)
(* around y contained in W.                                                   *)

let GEOI_RIGID_PROP = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f1 f2 y rho.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f1 /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f2 /\
        y IN W /\ f1 y = f2 y /\
        mfd_differential atlas atlas' f1 y = mfd_differential atlas atlas' f2 y /\
        mfd_inj_ball (top,atlas) g y rho /\ mfd_ball (top,atlas) g y rho SUBSET W
        ==> !z. z IN mfd_ball (top,atlas) g y rho ==> f1 z = f2 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_local_isometry; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `y:A`; `rho:real`] MFD_EXP_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MP_TAC(ASSUME `mfd_inj_ball (top,atlas:((A->bool)#(A->real^N))->bool)
                   (g:A->real^N^N) y rho`) THEN
  REWRITE_TAC[mfd_inj_ball] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t <= &1
        ==> mfd_exp (top,atlas) (g:A->real^N^N) y (t % v) IN W`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `mfd_ball (top,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) y rho
                 SUBSET W` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `rho:real`] MFD_EXP_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(v:real^N) IN mfd_tball (g:A->real^N^N) y rho` THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= n ==> n < rho ==> x < rho`) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) y` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `W:A->bool`; `f1:A->B`; `y:A`; `v:real^N`] MFD_LOCAL_ISOMETRY_EXP) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `top':B topology`;
                 `atlas':((B->bool)#(B->real^N))->bool`; `g':B->real^N^N`;
                 `W:A->bool`; `f2:A->B`; `y:A`; `v:real^N`] MFD_LOCAL_ISOMETRY_EXP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

(* Near any point x0 of W there is a radius rho such that the 1-jet         *)
(* agreement at any point of the rho-ball propagates to a neighbourhood of  *)
(* x0.                                                                       *)

let GEOI_RIGID_STEP = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f1 f2 x0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f1 /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f2 /\
        x0 IN W
        ==> ?rho. &0 < rho /\ mfd_ball (top,atlas) g x0 rho SUBSET W /\
                  !y. y IN mfd_ball (top,atlas) g x0 rho /\ f1 y = f2 y /\
                      mfd_differential atlas atlas' f1 y =
                      mfd_differential atlas atlas' f2 y
                      ==> ?U. open_in top U /\ x0 IN U /\ !z. z IN U ==> f1 z = f2 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_local_isometry]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x0:A`] MFD_UNIFORMLY_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:A->bool` (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `W INTER W0:A->bool`; `x0:A`]
    MFD_BALL_NEIGHBOURHOOD_BASE) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r0 (e / &2)` THEN
  SUBGOAL_THEN
   `!r. r <= e ==> mfd_ball (top,atlas) (g:A->real^N^N) x0 r SUBSET W INTER W0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x0 e` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mfd_ball; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W INTER W0:A->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN W /\ y IN W0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^N^N) x0 (min r0 (e / &2))
                  SUBSET W INTER W0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) y (min r0 (e / &2))` THEN
  ASM_SIMP_TAC[MFD_BALL_OPEN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOI_BALL_SYM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_RIGID_PROP THEN
  MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                        `g':B->real^N^N`; `W:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_INJ_BALL_MONO THEN EXISTS_TAC `r0:real` THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:A->real^N^N) x0 (min r0 (e / &2) + min r0 (e / &2))
                SUBSET W INTER W0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(z:A) IN s ==> s SUBSET W INTER W0 ==> z IN W`) THEN
  MATCH_MP_TAC GEOI_BALL_TRIANGLE THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]);;

let MFD_LOCAL_ISOMETRY_RIGID = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f1 f2 a.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f1 /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f2 /\
        connected_in top W /\ a IN W /\ f1 a = f2 a /\
        mfd_differential atlas atlas' f1 a = mfd_differential atlas atlas' f2 a
        ==> !x. x IN W ==> f1 x = f2 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (W:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_local_isometry]; ALL_TAC] THEN
  ABBREV_TAC
   `S2 = {x:A | x IN W /\
                ?U. open_in top U /\ x IN U /\ !z. z IN U ==> (f1:A->B) z = f2 z}` THEN
  SUBGOAL_THEN
   `!x0. x0 IN W
         ==> ?rho. &0 < rho /\
                   mfd_ball (top,atlas) (g:A->real^N^N) x0 rho SUBSET W /\
                   !y. y IN mfd_ball (top,atlas) g x0 rho /\ (f1:A->B) y = f2 y /\
                       mfd_differential atlas (atlas':((B->bool)#(B->real^N))->bool) f1 y =
                       mfd_differential atlas atlas' f2 y
                       ==> ?U. open_in top U /\ x0 IN U /\ !z. z IN U ==> f1 z = f2 z`
  (LABEL_TAC "step") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOI_RIGID_STEP THEN
    MAP_EVERY EXISTS_TAC [`top':B topology`; `g':B->real^N^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* points of S2 have equal 1-jets *)
  SUBGOAL_THEN
   `!y. y IN S2
        ==> (f1:A->B) y = f2 y /\
            mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
              (atlas':((B->bool)#(B->real^N))->bool) f1 y =
            mfd_differential atlas atlas' f2 y`
  (LABEL_TAC "jet") THENL
   [X_GEN_TAC `y:A` THEN EXPAND_TAC "S2" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC GEOI_DIFFERENTIAL_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `U:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* S2 is open *)
  SUBGOAL_THEN `open_in top (S2:A->bool)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
    EXPAND_TAC "S2" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `U INTER W:A->bool` THEN ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
    EXPAND_TAC "S2" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* W DIFF S2 is open *)
  SUBGOAL_THEN `open_in top (W DIFF S2:A->bool)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x0:A` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    USE_THEN "step" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x0:A) IN W`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "prop")))) THEN
    EXISTS_TAC `mfd_ball (top,atlas) (g:A->real^N^N) x0 rho` THEN
    ASM_SIMP_TAC[MFD_BALL_OPEN; MFD_CENTRE_IN_BALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x0:A) IN S2)` THEN REWRITE_TAC[] THEN
    EXPAND_TAC "S2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "prop" MATCH_MP_TAC THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "jet" (MP_TAC o SPEC `y:A`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* a is in S2 *)
  SUBGOAL_THEN `(a:A) IN S2` ASSUME_TAC THENL
   [USE_THEN "step" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(a:A) IN W`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `a:A`)))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MFD_CENTRE_IN_BALL] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ALL_TAC] THEN
    EXPAND_TAC "S2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* connectedness *)
  SUBGOAL_THEN `(W:A->bool) SUBSET S2` ASSUME_TAC THENL
   [MP_TAC(ASSUME `connected_in top (W:A->bool)`) THEN REWRITE_TAC[CONNECTED_IN] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`S2:A->bool`; `W DIFF S2:A->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(S2:A->bool) SUBSET W` MP_TAC THENL
     [EXPAND_TAC "S2" THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(a:A) IN S2` THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_THEN "jet" (MP_TAC o SPEC `x:A`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

(* ========================================================================= *)
(* Differentials of smooth maps: chart representatives are                   *)
(* differentiable, the chain rule (GEOI_DIFF_COMPOSE) and the change of      *)
(* charts (GEOI_DIFF_CHART).                                                 *)
(* ========================================================================= *)

let GEOI_SMOOTH_REP_DIFF = prove
 (`!top atlas top' atlas' W (f:A->B) c c' x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        c IN atlas /\ c' IN atlas' /\ x IN FST c /\ x IN W /\ f x IN FST c'
        ==> open (IMAGE (SND c) {z | z IN FST c INTER W /\ f z IN FST c'}) /\
            SND c x IN IMAGE (SND c) {z | z IN FST c INTER W /\ f z IN FST c'} /\
            smooth_map_on (IMAGE (SND c) {z | z IN FST c INTER W /\ f z IN FST c'})
                          (SND c' o f o chart_inv c) /\
            ((SND c' o f o chart_inv c) has_derivative
             frechet_derivative (SND c' o f o chart_inv c) (at (SND c x)))
            (at (SND c x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^M)`;
                 `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `SND (c:(A->bool)#(A->real^N)) x IN
    IMAGE (SND c) {z | z IN FST c INTER W /\ (f:A->B) z IN FST (c':(B->bool)#(B->real^M))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND (c:(A->bool)#(A->real^N)))
                    {z | z IN FST c INTER W /\ (f:A->B) z IN FST (c':(B->bool)#(B->real^M))})
                  (SND c' o f o chart_inv c)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool)
                   (atlas':((B->bool)#(B->real^M))->bool) W (f:A->B)` THEN
    REWRITE_TAC[mfd_smooth_map] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                {z | z IN FST c INTER W /\ (f:A->B) z IN FST (c':(B->bool)#(B->real^M))}` THEN
  ASM_REWRITE_TAC[]);;

(* The chain rule for differentials in preferred charts. *)

let GEOI_DIFF_COMPOSE = prove
 (`!top atlas top' atlas' top'' atlas'' W W' (f:A->B) (h:B->C) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        smooth_manifold_atlas top'' (atlas'':((C->bool)#(C->real^P))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        open_in top' W' /\ continuous_map (subtopology top' W',top'') h /\
        mfd_smooth_map atlas' atlas'' W' h /\
        x IN W /\ f x IN W'
        ==> mfd_differential atlas atlas'' (h o f) x =
            mfd_differential atlas' atlas'' h (f x) o mfd_differential atlas atlas' f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (f:A->B) x IN topspace top' /\
                (h:B->C)(f x) IN topspace top''`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      UNDISCH_TAC `continuous_map (subtopology top' W',top'') (h:B->C)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`; `(f:A->B) x`]
    CHART_AT) THEN
  MP_TAC(ISPECL [`top'':C topology`; `atlas'':((C->bool)#(C->real^P))->bool`;
                 `(h:B->C)((f:A->B) x)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `c1 = chart_at (atlas':((B->bool)#(B->real^M))->bool) ((f:A->B) x)` THEN
  ABBREV_TAC `c2 = chart_at (atlas'':((C->bool)#(C->real^P))->bool) ((h:B->C)((f:A->B) x))` THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_differential; o_THM] THEN ASM_REWRITE_TAC[] THEN
  (* the two chart representatives *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `W:A->bool`; `f:A->B`; `c0:(A->bool)#(A->real^N)`;
                 `c1:(B->bool)#(B->real^M)`; `x:A`] GEOI_SMOOTH_REP_DIFF) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `top'':C topology`; `atlas'':((C->bool)#(C->real^P))->bool`;
                 `W':B->bool`; `h:B->C`; `c1:(B->bool)#(B->real^M)`;
                 `c2:(C->bool)#(C->real^P)`; `(f:A->B) x`] GEOI_SMOOTH_REP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `c1:(B->bool)#(B->real^M)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. SND (c1:(B->bool)#(B->real^M)) ((f:A->B) (chart_inv (c0:(A->bool)#(A->real^N)) y))) =
    SND c1 o f o chart_inv c0 /\
    (\y. SND (c2:(C->bool)#(C->real^P)) ((h:B->C) (chart_inv c1 y))) =
    SND c2 o h o chart_inv c1`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  (* the composite agrees with H o F near SND c0 x *)
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `frechet_derivative ((SND (c2:(C->bool)#(C->real^P)) o (h:B->C) o chart_inv c1) o
                                  (SND (c1:(B->bool)#(B->real^M)) o (f:A->B) o
                                   chart_inv (c0:(A->bool)#(A->real^N))))
                                 (at (SND c0 x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
    EXISTS_TAC
     `IMAGE (SND (c0:(A->bool)#(A->real^N)))
        {z | z IN FST c0 INTER W /\
             (f:A->B) z IN {u | u IN FST (c1:(B->bool)#(B->real^M)) INTER W' /\
                                (h:B->C) u IN FST (c2:(C->bool)#(C->real^P))}}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top':B topology` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
        MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                       `top'':C topology`; `atlas'':((C->bool)#(C->real^P))->bool`;
                       `c1:(B->bool)#(B->real^M)`; `c2:(C->bool)#(C->real^P)`;
                       `W':B->bool`; `h:B->C`] MFDM_CHART_DOMAIN_OPEN) THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[o_THM]];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN MATCH_MP_TAC DIFF_CHAIN_AT THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(SND (c1:(B->bool)#(B->real^M)) o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N)))
      (SND c0 x) = SND c1 (f x)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[o_THM]; ASM_REWRITE_TAC[]]);;

(* Change of charts: the differential in arbitrary charts. *)

let GEOI_DIFF_CHART = prove
 (`!top atlas top' atlas' W (f:A->B) c c' x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        c IN atlas /\ c' IN atlas' /\ x IN FST c /\ x IN W /\ f x IN FST c'
        ==> frechet_derivative (SND c' o f o chart_inv c) (at (SND c x)) =
            chart_jac (chart_at atlas' (f x)) c' (f x) o
            mfd_differential atlas atlas' f x o
            chart_jac c (chart_at atlas x) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (f:A->B) x IN topspace top'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      UNDISCH_TAC `continuous_map (subtopology top W,top') (f:A->B)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`; `(f:A->B) x`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `c1 = chart_at (atlas':((B->bool)#(B->real^M))->bool) ((f:A->B) x)` THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_differential] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\y. SND (c1:(B->bool)#(B->real^M)) ((f:A->B) (chart_inv (c0:(A->bool)#(A->real^N)) y))) =
    SND c1 o f o chart_inv c0`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `W:A->bool`; `f:A->B`; `c0:(A->bool)#(A->real^N)`;
                 `c1:(B->bool)#(B->real^M)`; `x:A`] GEOI_SMOOTH_REP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c0:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `c1:(B->bool)#(B->real^M)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `c':(B->bool)#(B->real^M)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* derivatives of the two chart transitions *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`; `x:A`]
    CHART_TRANS_HAS_DERIVATIVE) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `FST(c1:(B->bool)#(B->real^M))`; `SND(c1:(B->bool)#(B->real^M))`;
                 `FST(c':(B->bool)#(B->real^M))`; `SND(c':(B->bool)#(B->real^M))`;
                 `(f:A->B) x`] CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `frechet_derivative
                (chart_trans (c1:(B->bool)#(B->real^M)) (c':(B->bool)#(B->real^M)) o
                 (SND c1 o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) o
                 chart_trans (c:(A->bool)#(A->real^N)) c0)
                (at (SND c x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
    EXISTS_TAC
     `IMAGE (SND (c:(A->bool)#(A->real^N)))
        {z | z IN FST c INTER (FST (c0:(A->bool)#(A->real^N)) INTER W) /\
             (f:A->B) z IN FST (c':(B->bool)#(B->real^M)) INTER FST (c1:(B->bool)#(B->real^M))}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN EXISTS_TAC `top':B topology` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[o_THM; chart_trans]];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_trans (c:(A->bool)#(A->real^N)) (c0:(A->bool)#(A->real^N))
                    (SND c x) = SND c0 x`
    SUBST1_TAC THENL [ASM_SIMP_TAC[chart_trans]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((SND (c1:(B->bool)#(B->real^M)) o (f:A->B) o chart_inv (c0:(A->bool)#(A->real^N))) o
     chart_trans (c:(A->bool)#(A->real^N)) c0) (SND c x) = SND c1 (f x)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[o_THM; chart_trans]; ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* A smooth map whose differential pulls g' back to g at every               *)
(* point (in preferred charts) is a local isometry (GEOI_LISOM_FROM_DIFF).   *)
(* ========================================================================= *)

let GEOI_LINEAR_CHART_JAC = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c' x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        x IN FST c /\ x IN FST c'
        ==> linear(chart_jac c c' x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`; `x:A`]
    CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN SIMP_TAC[has_derivative]);;

let GEOI_LISOM_FROM_DIFF = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        smooth_manifold_atlas top' atlas' /\ riemannian_metric atlas' g' /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\
        (!x. x IN W
             ==> g x = transp(matrix(mfd_differential atlas atlas' f x)) ** g'(f x) **
                       matrix(mfd_differential atlas atlas' f x))
        ==> mfd_local_isometry (top,atlas) g (top',atlas') g' W f`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mfd_local_isometry] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`; `y:real^N`] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (f:A->B) x IN topspace top'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      UNDISCH_TAC `continuous_map (subtopology top W,top') (f:A->B)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`; `(f:A->B) x`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  ABBREV_TAC `c1 = chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c':(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* the differential in the charts c, c' *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W:A->bool`; `f:A->B`; `c:(A->bool)#(A->real^N)`;
                 `c':(B->bool)#(B->real^N)`; `x:A`] GEOI_DIFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W:A->bool`; `f:A->B`; `c0:(A->bool)#(A->real^N)`;
                 `c1:(B->bool)#(B->real^N)`; `x:A`] GEOI_SMOOTH_REP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `linear(mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                                (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_differential] THEN
    SUBGOAL_THEN
     `(\y. SND (c1:(B->bool)#(B->real^N)) ((f:A->B) (chart_inv (c0:(A->bool)#(A->real^N)) y))) =
      SND c1 o f o chart_inv c0`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    ASM_MESON_TAC[has_derivative];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (c:(A->bool)#(A->real^N)) c0 x) /\
    linear(chart_jac (c1:(B->bool)#(B->real^N)) c' ((f:A->B) x)) /\
    linear(chart_jac (c':(B->bool)#(B->real^N)) c1 ((f:A->B) x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC GEOI_LINEAR_CHART_JAC THENL
     [MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`];
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`];
      MAP_EVERY EXISTS_TAC [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = matrix(chart_jac (c:(A->bool)#(A->real^N)) c0 x)` THEN
  ABBREV_TAC `T0 = matrix(chart_jac (c1:(B->bool)#(B->real^N)) c' ((f:A->B) x))` THEN
  ABBREV_TAC `K = matrix(chart_jac (c':(B->bool)#(B->real^N)) c1 ((f:A->B) x))` THEN
  ABBREV_TAC `D = matrix(mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                           (atlas':((B->bool)#(B->real^N))->bool) (f:A->B) x)` THEN
  SUBGOAL_THEN
   `matrix(frechet_derivative (SND (c':(B->bool)#(B->real^N)) o (f:A->B) o
                               chart_inv (c:(A->bool)#(A->real^N))) (at (SND c x))) =
    (T0:real^N^N) ** (D:real^N^N) ** (J:real^N^N)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^N^N) ** (T0:real^N^N) = mat 1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`chart_jac (c1:(B->bool)#(B->real^N)) c' ((f:A->B) x)`;
                   `chart_jac (c':(B->bool)#(B->real^N)) c1 ((f:A->B) x)`] MATRIX_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `FST(c1:(B->bool)#(B->real^N))`; `SND(c1:(B->bool)#(B->real^N))`;
                   `FST(c':(B->bool)#(B->real^N))`; `SND(c':(B->bool)#(B->real^N))`;
                   `(f:A->B) x`] CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^N^N. (K:real^N^N) ** (T0:real^N^N) ** X = X` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `!X:real^N^N. transp (T0:real^N^N) ** transp (K:real^N^N) ** X = X`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MATRIX_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL; TRANSP_MAT;
                    MATRIX_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[metric_local; mpullback] THEN ASM_SIMP_TAC[o_THM] THEN
  SUBGOAL_THEN
   `(g:A->real^N^N) x = transp (D:real^N^N) ** (g':B->real^N^N)((f:A->B) x) ** D`
  SUBST1_TAC THENL [EXPAND_TAC "D" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Helpers for Cartan's lemma: polarization, congruence of                   *)
(* local isometries, linearity of differentials, the Euclidean atlas, and   *)
(* the differential of a parametrization is onto.                            *)
(* ========================================================================= *)

(* Symmetric bilinear forms are determined by their quadratic forms. *)

let GEOI_QUAD_EQ = prove
 (`!(A:real^N^N) B.
        (!u v. u dot (A ** v) = v dot (A ** u)) /\
        (!u v. u dot (B ** v) = v dot (B ** u)) /\
        (!u. u dot (A ** u) = u dot (B ** u))
        ==> A = B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_EQ] THEN X_GEN_TAC `v:real^N` THEN
  REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `u:real^N` THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `u + v:real^N` th) THEN
                          MP_TAC(SPEC `u:real^N` th) THEN MP_TAC(SPEC `v:real^N` th)) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; DOT_LADD; DOT_RADD] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[SPECL [`v:real^N`; `u:real^N`] th]) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[SPECL [`v:real^N`; `u:real^N`] th]) THEN
  REAL_ARITH_TAC);;

(* Local isometries only depend on the map on W. *)

let GEOI_LISOM_EQ = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) W f1 f2.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_local_isometry (top,atlas) g (top',atlas') g' W f1 /\
        (!x. x IN W ==> f1 x = f2 x)
        ==> mfd_local_isometry (top,atlas) g (top',atlas') g' W f2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_local_isometry] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "met")))) ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f1:A->B` THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
    MATCH_MP_TAC MFDD_SMOOTH_MAP_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `f1:A->B`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN FST (c:(A->bool)#(A->real^N)) INTER W /\
         (f2:A->B) x IN FST (c':(B->bool)#(B->real^N))} =
    {x | x IN FST c INTER W /\ (f1:A->B) x IN FST c'}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    can (term_match [] `{x | x IN FST (c:(A->bool)#(A->real^N)) INTER W /\
                             (f2:A->B) x IN FST (c':(B->bool)#(B->real^N))} = s`) (concl th))) THEN
  USE_THEN "met" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                                  `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(B->bool)#(B->real^N)`;
                 `W:A->bool`; `f1:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (SND (c:(A->bool)#(A->real^N)))
                   {x | x IN FST c INTER W /\ (f1:A->B) x IN FST (c':(B->bool)#(B->real^N))}
        ==> (SND c' o f1 o chart_inv c) z = (SND c' o (f2:A->B) o chart_inv c) z`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN
   `frechet_derivative (SND (c':(B->bool)#(B->real^N)) o (f1:A->B) o
                        chart_inv (c:(A->bool)#(A->real^N))) (at y) =
    frechet_derivative (SND c' o (f2:A->B) o chart_inv c) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                  {x | x IN FST c INTER W /\ (f1:A->B) x IN FST (c':(B->bool)#(B->real^N))}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* Differentials of smooth maps are linear. *)

let GEOI_DIFF_LINEAR = prove
 (`!top atlas top' atlas' W (f:A->B) x.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^M))->bool) /\
        open_in top W /\ continuous_map (subtopology top W,top') f /\
        mfd_smooth_map atlas atlas' W f /\ x IN W
        ==> linear(mfd_differential atlas atlas' f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top /\ (f:A->B) x IN topspace top'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
      UNDISCH_TAC `continuous_map (subtopology top W,top') (f:A->B)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`; `(f:A->B) x`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^M))->bool`;
                 `W:A->bool`; `f:A->B`; `chart_at (atlas:((A->bool)#(A->real^N))->bool) x`;
                 `chart_at (atlas':((B->bool)#(B->real^M))->bool) ((f:A->B) x)`; `x:A`]
    GEOI_SMOOTH_REP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  REWRITE_TAC[mfd_differential; has_derivative] THEN
  SUBGOAL_THEN
   `(\y. SND (chart_at (atlas':((B->bool)#(B->real^M))->bool) ((f:A->B) x))
           (f (chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) y))) =
    SND (chart_at atlas' (f x)) o f o chart_inv (chart_at atlas x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; SIMP_TAC[]]);;

(* The Euclidean atlas. *)

let GEOI_EUCLIDEAN_ATLAS = prove
 (`smooth_manifold_atlas euclidean (open_set_atlas (:real^N))`,
  MP_TAC(ISPEC `(:real^N)` OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV]);;

let GEOI_LINEAR_SMOOTH = prove
 (`!(L:real^N^N) W.
        open W
        ==> mfd_smooth_map (open_set_atlas (:real^N)) (open_set_atlas (:real^N)) W
                           (\v. L ** v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MFD_SMOOTH_MAP_OPEN_SET_ATLAS] THEN
  REWRITE_TAC[IN_UNIV; INTER_UNIV; SET_RULE `{x:real^N | x IN s} = s`] THEN
  SUBGOAL_THEN `(\v:real^N. (L:real^N^N) ** v) = (\v. L ** v) o (\x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; SMOOTH_MAP_ON_ID]);;

let GEOI_DIFF_LINEAR_MAP = prove
 (`!(L:real^N^N) v.
        mfd_differential (open_set_atlas (:real^N)) (open_set_atlas (:real^N))
                         (\v. L ** v) v = (\h. L ** h)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
  SIMP_TAC[MFDD_OPEN_SET_CHART_AT; IN_UNIV] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

(* ========================================================================= *)
(* Cartan's lemma for curvature 1 (MFD_CARTAN_CONST1): the map               *)
(* exp'_p' o L o exp_p^-1 is a local isometry, since by                      *)
(* MFD_EXP_DIFFERENTIAL_CONST1 the length of d(exp)(v) w only depends on    *)
(* the lengths of v, w and their inner product, which L preserves.           *)
(* ========================================================================= *)

(* The differential of a parametrization is onto. *)

let GEOI_PARAM_DIFF_SURJ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (e:real^N->A) e' W v.
        smooth_manifold_atlas top atlas /\
        mfd_diffeo euclidean (open_set_atlas (:real^N)) W top atlas (IMAGE e W) e e' /\
        v IN W
        ==> !y. ?w. mfd_differential (open_set_atlas (:real^N)) atlas e v w = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                              TOPSPACE_EUCLIDEAN; INTER_UNIV; GSYM OPEN_IN]) THEN
  SUBGOAL_THEN `IMAGE (e:real^N->A) W SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `W:real^N->bool`; `IMAGE (e:real^N->A) W`; `e:real^N->A`;
                 `e':A->real^N`; `v:real^N`] GEOI_DIFF_COMPOSE) THEN
  ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas (:real^N)) (open_set_atlas (:real^N))
      ((e':A->real^N) o (e:real^N->A)) v = (\h. h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN
    SIMP_TAC[MFDD_OPEN_SET_CHART_AT; IN_UNIV] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `frechet_derivative (\y:real^N. y) (at v)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GEOI_FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_SIMP_TAC[o_THM];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE THEN
  REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `top:A topology`;
                          `W:real^N->bool`] THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w1:real^N`; `w2:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(AP_THM th `w1:real^N`) THEN
                          MP_TAC(AP_THM th `w2:real^N`)) THEN
  ASM_REWRITE_TAC[o_THM] THEN MESON_TAC[]);;

let MFD_CARTAN_CONST1 = prove
 (`!top atlas (g:A->real^N^N) top' atlas' (g':B->real^N^N) p p' (L:real^N^N) W.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g x u v = &1) /\
        hausdorff_space top' /\ smooth_manifold_atlas top' atlas' /\
        riemannian_metric atlas' g' /\
        (!x u v. x IN topspace top' /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas' g' x u v = &1) /\
        p IN topspace top /\ p' IN topspace top' /\
        transp L ** g' p' ** L = g p /\
        W SUBSET mfd_exp_dom (top,atlas) g p /\
        IMAGE (\v. L ** v) W SUBSET mfd_exp_dom (top',atlas') g' p' /\
        mfd_param top atlas W (mfd_exp (top,atlas) g p)
        ==> mfd_local_isometry (top,atlas) g (top',atlas') g'
              (IMAGE (mfd_exp (top,atlas) g p) W)
              (\y. mfd_exp (top',atlas') g' p'
                     (L ** (@v. v IN W /\ mfd_exp (top,atlas) g p v = y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `mfd_param top (atlas:((A->bool)#(A->real^N))->bool) W
                   (mfd_exp (top,atlas) (g:A->real^N^N) p)`) THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^N`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOF_EXP_ALL) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `p':B`] GEOF_EXP_ALL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) p` THEN
  ABBREV_TAC `E' = mfd_exp (top',atlas') (g':B->real^N^N) p'` THEN
  ABBREV_TAC `D = mfd_exp_dom (top,atlas) (g:A->real^N^N) p` THEN
  ABBREV_TAC `D' = mfd_exp_dom (top',atlas') (g':B->real^N^N) p'` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ASSUME `mfd_diffeo euclidean (open_set_atlas (:real^N)) W top
                   (atlas:((A->bool)#(A->real^N))->bool) (IMAGE (E:real^N->A) W) E e'`) THEN
  REWRITE_TAC[mfd_diffeo; homeomorphic_maps] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                              TOPSPACE_EUCLIDEAN; INTER_UNIV; GSYM OPEN_IN;
                              SUBSET_REFL]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ABBREV_TAC `U = IMAGE (E:real^N->A) W` THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN U ==> (e':A->real^N) y IN W /\ (E:real^N->A)(e' y) = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. v IN W ==> (e':A->real^N)((E:real^N->A) v) = v` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the map is F2 = E' o L o e' on U *)
  MATCH_MP_TAC GEOI_LISOM_EQ THEN
  EXISTS_TAC `\y. (E':real^N->B) ((L:real^N^N) ** (e':A->real^N) y)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `v:real^N` THEN REWRITE_TAC[] THEN
    EQ_TAC THENL
     [STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]]] THEN
  (* continuity and smoothness of F2 *)
  SUBGOAL_THEN `!v. v IN W ==> (L:real^N^N) ** v IN D'` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (\v. (L:real^N^N) ** v) W SUBSET D'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top U,euclidean)
      (\y. (L:real^N^N) ** (e':A->real^N) y) /\
    IMAGE (\y. L ** e' y) (topspace top INTER U) SUBSET D'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(\y. (L:real^N^N) ** (e':A->real^N) y) = (\v. L ** v) o e'`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top U,top') (\y. (E':real^N->B) ((L:real^N^N) ** (e':A->real^N) y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (E':real^N->B) ((L:real^N^N) ** (e':A->real^N) y)) =
                  E' o (\y. L ** e' y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (D':real^N->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool) (open_set_atlas (:real^N)) U
      (\y. (L:real^N^N) ** (e':A->real^N) y)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (L:real^N^N) ** (e':A->real^N) y) = (\v. L ** v) o e'`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_SMOOTH_MAP_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `euclidean:(real^N)topology`;
                          `open_set_atlas (:real^N)`;
                          `euclidean:(real^N)topology`; `(:real^N)`] THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN; OPEN_UNIV; SUBSET_UNIV;
                    SUBTOPOLOGY_UNIV] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      MATCH_MP_TAC GEOI_LINEAR_SMOOTH THEN REWRITE_TAC[OPEN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool) (atlas':((B->bool)#(B->real^N))->bool) U
      (\y. (E':real^N->B) ((L:real^N^N) ** (e':A->real^N) y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (E':real^N->B) ((L:real^N^N) ** (e':A->real^N) y)) =
                  E' o (\y. L ** e' y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC MFD_SMOOTH_MAP_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `euclidean:(real^N)topology`;
                          `open_set_atlas (:real^N)`;
                          `top':B topology`; `D':real^N->bool`] THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* the differential condition *)
  MATCH_MP_TAC GEOI_LISOM_FROM_DIFF THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ABBREV_TAC `v = (e':A->real^N) x` THEN
  SUBGOAL_THEN `(v:real^N) IN W /\ (E:real^N->A) v = x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `F2 = \y. (E':real^N->B) ((L:real^N^N) ** (e':A->real^N) y)` THEN
  ABBREV_TAC `Df = mfd_differential (atlas:((A->bool)#(A->real^N))->bool)
                     (atlas':((B->bool)#(B->real^N))->bool) (F2:A->B) x` THEN
  (* Df o d exp_p(v) = d exp_p'(L v) o L *)
  SUBGOAL_THEN
   `!w. (Df:real^N->real^N)
          (mfd_differential (open_set_atlas (:real^N)) atlas (E:real^N->A) v w) =
        mfd_differential (open_set_atlas (:real^N)) (atlas':((B->bool)#(B->real^N))->bool)
          (E':real^N->B) ((L:real^N^N) ** v) (L ** w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN
    MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `W:real^N->bool`; `U:A->bool`; `E:real^N->A`; `F2:A->B`; `v:real^N`]
      GEOI_DIFF_COMPOSE) THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN
    DISCH_THEN(MP_TAC o C AP_THM `w:real^N`) THEN REWRITE_TAC[o_THM] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `mfd_differential (open_set_atlas (:real^N))
                  (atlas':((B->bool)#(B->real^N))->bool)
                  ((E':real^N->B) o (\v. (L:real^N^N) ** v)) v w` THEN
    CONJ_TAC THENL
     [AP_THM_TAC THEN MATCH_MP_TAC GEOI_DIFFERENTIAL_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`euclidean:(real^N)topology`; `W:real^N->bool`] THEN
      ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "F2" THEN
      ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                   `euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                   `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `W:real^N->bool`; `D':real^N->bool`; `\v. (L:real^N^N) ** v`;
                   `E':real^N->B`; `v:real^N`] GEOI_DIFF_COMPOSE) THEN
    ASM_REWRITE_TAC[GEOI_EUCLIDEAN_ATLAS; GSYM OPEN_IN] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[GEOI_LINEAR_SMOOTH] THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM; GEOI_DIFF_LINEAR_MAP]];
    ALL_TAC] THEN
  (* the two exponential maps have isometric differentials *)
  SUBGOAL_THEN
   `!a b. ((L:real^N^N) ** a) dot ((g':B->real^N^N) p' ** (L ** b)) =
          a dot ((g:A->real^N^N) p ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. (L:real^N^N) ** a = vec 0 <=> a = vec 0` ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[MATRIX_VECTOR_MUL_RZERO]] THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`] GEOD_G_POS_DEF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(SPECL [`a:real^N`; `a:real^N`] th)]) THEN
    REWRITE_TAC[ASSUME `(L:real^N^N) ** a = vec 0`; DOT_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. mfd_tnorm (g':B->real^N^N) ((E':real^N->B) ((L:real^N^N) ** v))
          (mfd_differential (open_set_atlas (:real^N)) atlas' E' (L ** v) (L ** w)) pow 2 =
        mfd_tnorm (g:A->real^N^N) ((E:real^N->A) v)
          (mfd_differential (open_set_atlas (:real^N)) atlas E v w) pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `g':B->real^N^N`; `p':B`; `(L:real^N^N) ** v`; `(L:real^N^N) ** w`]
      MFD_EXP_DIFFERENTIAL_CONST1) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `v:real^N`; `w:real^N`]
      MFD_EXP_DIFFERENTIAL_CONST1) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[mfd_tnorm];
    ALL_TAC] THEN
  (* hence Df preserves the quadratic forms, and by polarization the metric *)
  SUBGOAL_THEN `(x:A) IN topspace top /\ (F2:A->B) x IN topspace top'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `continuous_map (subtopology top U,top') (F2:A->B)` THEN
    REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(F2:A->B) x = (E':real^N->B) ((L:real^N^N) ** v)` ASSUME_TAC THENL
   [EXPAND_TAC "F2" THEN EXPAND_TAC "v" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(Df:real^N->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "Df" THEN MATCH_MP_TAC GEOI_DIFF_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `top':B topology`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOI_QUAD_EQ THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                   `g':B->real^N^N`; `(F2:A->B) x`] GEOG_G_SYM_POS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^N` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `E:real^N->A`; `e':A->real^N`; `W:real^N->bool`; `v:real^N`]
    GEOI_PARAM_DIFF_SURJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `w:real^N` o SPEC `u:real^N`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `g':B->real^N^N`; `(F2:A->B) x`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 2 (CONJUNCTS th))]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(el 2 (CONJUNCTS th))]) THEN
  ASM_REWRITE_TAC[]);;

