(* ========================================================================= *)
(* Unit pc_geo_jvar (geodesics layer): the variation field of a smooth       *)
(* family of geodesics is a Jacobi field (MFD_GEODESIC_VARIATION_JACOBI, MT  *)
(* p. 12), and the differential of the exponential map at v is evaluation   *)
(* at time 1 of the Jacobi field along t -> exp(t v) with initial value 0   *)
(* and initial covariant derivative w (MFD_EXP_DIFFERENTIAL_JACOBI, MT      *)
(* p. 14-15).  Built on the two-parameter-family layer of pc_cmp_var        *)
(* (cmp_family, cmp_ffield), the exponential family exp(t(v + s w)) of       *)
(* pc_geo_gauss and the uniqueness of Jacobi fields (pc_geo_jacobi).        *)
(* ========================================================================= *)

needs "src/pc_geo_jacobi.ml";;
needs "src/pc_cmp_var.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Variations through geodesics give Jacobi fields                           *)
(* (MFD_GEODESIC_VARIATION_JACOBI).  With V = d_s f and T = d_t f:          *)
(* D_t V = D_s T (MFD_COVD_SYMMETRY), and D_t D_s T = D_s D_t T - R(V,T)T    *)
(* (MFD_COVD_COMMUTATOR) with D_t T = 0 for every s.                         *)
(* ========================================================================= *)

let MFD_GEODESIC_VARIATION_JACOBI = prove
 (`!top atlas (g:A->real^N^N) (f:real->real->A) S0 J.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        real_open S0 /\ is_realinterval S0 /\ &0 IN S0 /\
        real_open J /\ is_realinterval J /\
        continuous_map
          (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
          (\z. f (drop(fstcart z)) (drop(sndcart z))) /\
        (!c. c IN atlas
             ==> smooth_map_on
                   {pastecart (lift s) (lift t) | s IN S0 /\ t IN J /\ f s t IN FST c}
                   (\z. SND c (f (drop(fstcart z)) (drop(sndcart z))))) /\
        (!s. s IN S0 ==> mfd_geodesic (top,atlas) g (f s) J)
        ==> mfd_jacobi atlas g (f (&0)) J
              (\t. vector_derivative
                     (\s. SND(chart_at atlas (f (&0) t)) (f (drop s) t)) (at (vec 0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cmp_family (top,atlas:((A->bool)#(A->real^N))->bool) (f:real->real->A) S0 J`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[cmp_family]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. vector_derivative
          (\s. SND(chart_at atlas ((f:real->real->A) (&0) t)) (f (drop s) t)) (at (vec 0))) =
    (\t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (\s'. f s' t) (&0))`
  SUBST1_TAC THENL [REWRITE_TAC[mfd_vel; LIFT_NUM]; ALL_TAC] THEN
  (* the velocity fields and D_s T are smooth fields along the family *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`] CMPV_VEL_FIELDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fV") (LABEL_TAC "fT")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                                ((f:real->real->A) s) t`]
    CMPV_COVD_S_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "fW") THEN
  (* the lines s = 0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                                (\s'. (f:real->real->A) s' t) s`]
    CMPV_FAMILY_LINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t. mfd_covd (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                          (\s'. (f:real->real->A) s' t) (\s'. mfd_vel atlas (f s') t) s`]
    CMPV_FAMILY_LINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&0` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the s-lines *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `f:real->real->A`; `S0:real->bool`; `J:real->bool`;
                 `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                                ((f:real->real->A) s) t`]
    CMPV_FAMILY_LINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "slines" o CONJUNCT2) THEN
  (* symmetry *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) (&0))
              (\t'. mfd_vel atlas (\s'. f s' t') (&0)) t =
            mfd_covd atlas g (\s'. f s' t) (\s'. mfd_vel atlas (f s') t) (&0)`
  (LABEL_TAC "sym") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MFD_COVD_SYMMETRY THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `S0:real->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_jacobi] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN
    EXISTS_TAC `\t. mfd_covd atlas (g:A->real^N^N) (\s'. (f:real->real->A) s' t)
                      (\s'. mfd_vel atlas (f s') t) (&0)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "sym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  (* D_t D_t V = D_t D_s T near t *)
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) ((f:real->real->A) (&0))
      (mfd_covd atlas g (f (&0)) (\t'. mfd_vel atlas (\s'. f s' t') (&0))) t =
    mfd_covd atlas g (f (&0))
      (\t'. mfd_covd atlas g (\s'. f s' t') (\s'. mfd_vel atlas (f s') t') (&0)) t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPG_COVD_LOCAL THEN
    UNDISCH_TAC `real_open J` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    USE_THEN "sym" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the commutator with Z = T *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `f:real->real->A`;
                 `\s t. mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                                ((f:real->real->A) s) t`;
                 `S0:real->bool`; `J:real->bool`; `&0`; `t:real`]
    MFD_COVD_COMMUTATOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    USE_THEN "fT" (fun th -> MP_TAC(REWRITE_RULE[cmp_ffield] th)) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN
  (* D_s D_t T = 0 *)
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (\s'. (f:real->real->A) s' t)
      (\s'. mfd_covd atlas g (f s') (mfd_vel atlas (f s')) t) (&0) = vec 0`
  SUBST1_TAC THENL
   [USE_THEN "slines" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(t:real) IN J`))) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC CMPV_COVD_VANISHING THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `S0:real->bool`;
      `\s'. mfd_vel (atlas:((A->bool)#(A->real^N))->bool) ((f:real->real->A) s') t`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(f:real->real->A) s`; `J:real->bool`]
      MFD_GEODESIC_VEL_PARALLEL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[mfd_parallel]] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Covariant derivatives along a constant curve; Jacobi fields               *)
(* only depend on the curve on the (open) parameter interval (velocities:   *)
(* GEOM_VEL_LOCAL of pc_geo_max).                                            *)
(* ========================================================================= *)

(* Along a constant curve the covariant derivative is the derivative. *)

let GEOJV_COVD_CONST_CURVE = prove
 (`!top atlas (g:A->real^N^N) (x:A) (Z:real->real^N) z' t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\
        ((\s. Z(drop s)) has_vector_derivative z') (at (lift t))
        ==> mfd_covd atlas g (\s. x) Z t = z'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_covd; mfd_field_rep] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))`;
                 `x:A`] CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_GEODESIC_CONST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool)
                               (chart_at atlas (x:A)) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
    CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_LZERO th]) THEN
  REWRITE_TAC[VECTOR_ADD_RID] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  ASM_REWRITE_TAC[]);;

(* Differentiability of fields only depends on the curve on J. *)

let GEOJV_FIELD_DIFF_CURVE_LOCAL = prove
 (`!atlas (gamma1:real->A) gamma2 J (Y:real->real^N).
        real_open J /\ (!t. t IN J ==> gamma1 t = gamma2 t) /\
        mfd_field_diff atlas gamma1 Y J
        ==> mfd_field_diff atlas gamma2 Y J`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_field_diff] THEN STRIP_TAC THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> can (term_match []
    `!t. t IN J ==> (\s. mfd_field_rep atlas (gamma1:real->A) (Y:real->real^N)
                           (chart_at atlas (gamma1 t)) (drop s)) differentiable at (lift t)`)
    (concl th))) THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFFERENTIABLE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. mfd_field_rep atlas (gamma1:real->A) (Y:real->real^N)
                    (chart_at atlas ((gamma2:real->A) t)) (drop s)` THEN
  UNDISCH_TAC `real_open J` THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[mfd_field_rep] THEN
  SUBGOAL_THEN `(gamma1:real->A)(drop s) = gamma2(drop s)` (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
    `!t. t IN J ==> (gamma1:real->A) t = gamma2 t`) (concl th))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
  REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP]);;

(* Jacobi fields only depend on the curve on J. *)

let GEOJV_JACOBI_CURVE_LOCAL = prove
 (`!atlas (g:A->real^N^N) (gamma1:real->A) gamma2 J (Y:real->real^N).
        real_open J /\ (!t. t IN J ==> gamma1 t = gamma2 t) /\
        mfd_jacobi atlas g gamma1 J Y
        ==> mfd_jacobi atlas g gamma2 J Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_jacobi] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN J ==> ?d. &0 < d /\ !s. abs(s - t) < d ==> s IN J`
  (LABEL_TAC "nbhd") THENL
   [MP_TAC(ASSUME `real_open (J:real->bool)`) THEN REWRITE_TAC[real_open] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z t. t IN J
          ==> mfd_covd atlas (g:A->real^N^N) (gamma2:real->A) (Z:real->real^N) t =
              mfd_covd atlas g (gamma1:real->A) Z t`
  (LABEL_TAC "cv") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "nbhd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(t:real) IN J`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC CMPV_COVD_CURVE_LOCAL THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t. t IN J ==> (gamma1:real->A) t = gamma2 t`) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN J ==> mfd_covd atlas (g:A->real^N^N) (gamma2:real->A) (Y:real->real^N) t =
                   mfd_covd atlas g (gamma1:real->A) Y t`
  (LABEL_TAC "cY") THENL [USE_THEN "cv" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GEOJV_FIELD_DIFF_CURVE_LOCAL THEN
    EXISTS_TAC `gamma1:real->A` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN
    EXISTS_TAC `mfd_covd atlas (g:A->real^N^N) (gamma1:real->A) (Y:real->real^N)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "cY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC GEOJV_FIELD_DIFF_CURVE_LOCAL THEN
      EXISTS_TAC `gamma1:real->A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  USE_THEN "nbhd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(t:real) IN J`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(gamma2:real->A) t = gamma1 t` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t. t IN J ==> (gamma1:real->A) t = gamma2 t`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma2:real->A) t =
                mfd_vel atlas gamma1 t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC GEOM_VEL_LOCAL THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!t. t IN J ==> (gamma1:real->A) t = gamma2 t`) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "cv" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real) IN J`)]) THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma1:real->A)
      (mfd_covd atlas g (gamma2:real->A) (Y:real->real^N)) t =
    mfd_covd atlas g gamma1 (mfd_covd atlas g gamma1 Y) t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "cY" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* The differential of the exponential map by Jacobi fields                  *)
(* (MFD_EXP_DIFFERENTIAL_JACOBI_RAY, MFD_EXP_DIFFERENTIAL_JACOBI).  The      *)
(* family f(s,r) = exp_x(r(v + s w)) on (-d,d) x J, J an open interval       *)
(* containing 0 and t, is a variation through geodesics; its variation field *)
(* V has V(0) = 0 and D_r V(0) = D_s T(0,0) = w, so V agrees with Y; and      *)
(* V(t) = d/ds exp_x(t v + s t w) at s = 0 (GEOG_DEXP_CURVE).                *)
(* ========================================================================= *)

(* Jacobi fields restrict to subintervals. *)

let GEOJV_JACOBI_SUBSET = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J J' (Y:real->real^N).
        J' SUBSET J /\ mfd_jacobi atlas g gamma J Y ==> mfd_jacobi atlas g gamma J' Y`,
  REWRITE_TAC[mfd_jacobi; mfd_field_diff; SUBSET] THEN MESON_TAC[]);;

(* The exponential family on a general product of open sets (the case       *)
(* (-d,d) x (-e,1+e) is GEOG_EXP_FAMILY_CHARTS).                             *)

let GEOJV_EXP_FAMILY_CHARTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w S0 J.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        real_open S0 /\ real_open J /\
        (!s t. s IN S0 /\ t IN J ==> t % (v + s % w) IN mfd_exp_dom (top,atlas) g x)
        ==> continuous_map
              (subtopology euclidean {pastecart (lift s) (lift t) | s IN S0 /\ t IN J},top)
              (\z. mfd_exp (top,atlas) g x (drop(sndcart z) % (v + drop(fstcart z) % w))) /\
            (!c. c IN atlas
                 ==> smooth_map_on
                       {pastecart (lift s) (lift t) |
                        s IN S0 /\ t IN J /\
                        mfd_exp (top,atlas) g x (t % (v + s % w)) IN FST c}
                       (\z. SND c (mfd_exp (top,atlas) g x
                                     (drop(sndcart z) % (v + drop(fstcart z) % w)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM(LABEL_TAC "fam") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN
  ABBREV_TAC `E = mfd_exp (top,atlas) (g:A->real^N^N) x` THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D2 = {pastecart (lift s) (lift t) | s IN S0 /\ t IN J}` THEN
  ABBREV_TAC `Phi = \z:real^(1,1)finite_sum.
                      drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)` THEN
  SUBGOAL_THEN `IMAGE (Phi:real^(1,1)finite_sum->real^N) D2 SUBSET D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Phi"; "D2"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN USE_THEN "fam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w))) =
                E o (Phi:real^(1,1)finite_sum->real^N)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Phi" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean D2,top)
      (\z. (E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (D:real^N->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(1,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    EXPAND_TAC "Phi" THEN MATCH_MP_TAC GEOG_PHI_SMOOTH THEN REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `\s t. (E:real^N->A) (t % ((v:real^N) + s % w))`;
                 `S0:real->bool`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`] GEOC_PAIR_CHART_OPEN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC
       `continuous_map (subtopology euclidean D2,top)
          (\z. (E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)))` THEN
      EXPAND_TAC "D2" THEN REWRITE_TAC[];
      ASM_MESON_TAC[MFDM_CHART]];
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `E:real^N->A`; `D:real^N->bool`; `c:(A->bool)#(A->real^N)`]
    GEOP_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. SND (c:(A->bool)#(A->real^N))
          ((E:real^N->A) (drop(sndcart z) % ((v:real^N) + drop(fstcart z) % w)))) =
    (\u. SND c (E u)) o (Phi:real^(1,1)finite_sum->real^N)`
  SUBST1_TAC THENL [EXPAND_TAC "Phi" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{u | u IN D /\ (E:real^N->A) u IN FST (c:(A->bool)#(A->real^N))}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Phi"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN USE_THEN "fam" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    EXPAND_TAC "Phi" THEN MATCH_MP_TAC GEOG_PHI_SMOOTH THEN ASM_REWRITE_TAC[]]);;

(* Radial curves t -> exp(t u) on an open interval J of the domain are      *)
(* geodesics (the case (-e,1+e) is GEOG_EXP_FAMILY_GEO).                     *)

let GEOJV_EXP_FAMILY_GEO = prove
 (`!top atlas (g:A->real^N^N) (x:A) (u:real^N) J.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        real_open J /\ is_realinterval J /\
        (!t. t IN J ==> t % u IN mfd_exp_dom (top,atlas) g x)
        ==> mfd_geodesic (top,atlas) g (\t. mfd_exp (top,atlas) g x (t % u)) J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x u` THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x u` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN J ==> t IN M /\ mfd_exp (top,atlas) (g:A->real^N^N) x (t % u) = gam t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g:A->real^N^N) gam J` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `M:real->bool` THEN
    ASM_REWRITE_TAC[SUBSET] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `{J:real->bool}`; `\K:real->bool. (gam:real->A)`;
                 `\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % u)`]
    GEOM_GEODESIC_GLUE) THEN
  REWRITE_TAC[UNIONS_1; IN_SING; FORALL_UNWIND_THM2] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  ASM_SIMP_TAC[]);;

(* The core argument on a general interval J containing 0 and t0. *)

let GEOJV_EXP_DIFF_FAMILY = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w Y d J t0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 < d /\
        real_open J /\ is_realinterval J /\ &0 IN J /\ t0 IN J /\
        (!s t. abs s < d /\ t IN J ==> t % (v + s % w) IN mfd_exp_dom (top,atlas) g x) /\
        mfd_jacobi atlas g (mfd_geo (top,atlas) g x v)
                   (mfd_geo_maxint (top,atlas) g x v) Y /\
        Y(&0) = vec 0 /\ mfd_covd atlas g (mfd_geo (top,atlas) g x v) Y (&0) = w
        ==> mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) (t0 % v) (t0 % w) = Y t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "fam" o check (fun th -> can (term_match []
    `!s t. abs s < d /\ t IN J
           ==> t % ((v:real^N) + s % w) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`)
    (concl th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `real_open(real_interval(--d,d)) /\ is_realinterval(real_interval(--d,d)) /\
    &0 IN real_interval(--d,d)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ASSUME `real_open (J:real->bool)`) THEN REWRITE_TAC[real_open] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eJ"))) THEN
  (* the family is continuous and smooth in charts, and consists of geodesics *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w:real^N`;
                 `real_interval(--d,d)`; `J:real->bool`] GEOJV_EXP_FAMILY_CHARTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "fam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval(--d,d)
        ==> mfd_geodesic (top,atlas) (g:A->real^N^N)
              (\t. mfd_exp (top,atlas) g x (t % (v + s % w))) J`
  (LABEL_TAC "geos") THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
    MATCH_MP_TAC GEOJV_EXP_FAMILY_GEO THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "fam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_geodesic (top,atlas) (g:A->real^N^N) (\t. mfd_exp (top,atlas) g x (t % v)) J`
  ASSUME_TAC THENL
   [USE_THEN "geos" (MP_TAC o C MATCH_MP (ASSUME `&0 IN real_interval(--d,d)`)) THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  (* the variation field V is a Jacobi field along t -> exp(t v) *)
  SUBGOAL_THEN
   `mfd_jacobi atlas (g:A->real^N^N) (\t. mfd_exp (top,atlas) g x (t % v)) J
      (\t. mfd_vel atlas (\s. mfd_exp (top,atlas) g x (t % (v + s % w))) (&0))`
  (LABEL_TAC "jV") THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `\s t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s % w))`;
                   `real_interval(--d,d)`; `J:real->bool`]
      MFD_GEODESIC_VARIATION_JACOBI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; mfd_vel; LIFT_NUM; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  (* the radial geodesic is mfd_geo x v on J *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> t IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v /\
            mfd_exp (top,atlas) g x (t % v) = mfd_geo (top,atlas) g x v t`
  (LABEL_TAC "geo") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t % (v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
    (fun th -> REWRITE_TAC[th]) THENL
     [USE_THEN "fam" (MP_TAC o SPECL [`&0`; `t:real`]) THEN
      REWRITE_TAC[REAL_ABS_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* Y is a Jacobi field along t -> exp(t v) with the same initial data *)
  SUBGOAL_THEN
   `mfd_jacobi atlas (g:A->real^N^N) (\t. mfd_exp (top,atlas) g x (t % v)) J
      (Y:real->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOJV_JACOBI_CURVE_LOCAL THEN
    EXISTS_TAC `mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "geo" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(t:real) IN J`))) THEN
      SIMP_TAC[];
      MATCH_MP_TAC GEOJV_JACOBI_SUBSET THEN
      EXISTS_TAC `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
      ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "geo" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(t:real) IN J`))) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (\t. mfd_exp (top,atlas) g x (t % v)) (Y:real->real^N)
      (&0) = w`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_covd atlas (g:A->real^N^N) (mfd_geo (top,atlas) g x v)
                   (Y:real->real^N) (&0) = w` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC CMPV_COVD_CURVE_LOCAL THEN EXISTS_TAC `e:real` THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "geo" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [USE_THEN "eJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the initial value and covariant derivative of V *)
  SUBGOAL_THEN
   `mfd_vel atlas (\s. mfd_exp (top,atlas) (g:A->real^N^N) x (&0 % (v + s % w))) (&0) =
    vec 0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_GEODESIC_CONST) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (\t. mfd_exp (top,atlas) g x (t % v))
      (\t. mfd_vel atlas (\s. mfd_exp (top,atlas) g x (t % (v + s % w))) (&0)) (&0) = w`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `\s t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s % w))`;
                   `real_interval(--d,d)`; `J:real->bool`; `&0`; `&0`]
      MFD_COVD_SYMMETRY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `mfd_covd atlas (g:A->real^N^N) (\s:real. x)
        (\s'. mfd_vel atlas (\t. mfd_exp (top,atlas) g x (t % (v + s' % w))) (&0)) (&0) =
      mfd_covd atlas g (\s:real. x) (\s'. (v:real^N) + s' % w) (&0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CMPG_COVD_LOCAL THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `(v:real^N) + r % w`; `e:real`]
        CMPV_RADIAL_GEODESIC) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real` THEN DISCH_TAC THEN
        USE_THEN "fam" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "eJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC GEOJV_COVD_CONST_CURVE THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[GEOG_AFFINE_VD];
    ALL_TAC] THEN
  (* uniqueness of Jacobi fields *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `\t. mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)`;
                 `J:real->bool`; `&0`; `vec 0:real^N`; `w:real^N`]
    MFD_JACOBI_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y0:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "u0"))))) THEN
  SUBGOAL_THEN `(Y:real->real^N) t0 = Y0 t0` SUBST1_TAC THENL
   [USE_THEN "u0" (MP_TAC o SPEC `Y:real->real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_vel atlas (\s. mfd_exp (top,atlas) (g:A->real^N^N) x (t0 % (v + s % w))) (&0) =
    (Y0:real->real^N) t0`
  (SUBST1_TAC o SYM) THENL
   [USE_THEN "u0" (MP_TAC o SPEC
      `\t. mfd_vel atlas (\s. mfd_exp (top,atlas) (g:A->real^N^N) x (t % (v + s % w)))
                   (&0)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t0:real`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* V(t0) is the differential along the curve s -> t0 v + s (t0 w) *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `\s:real. t0 % ((v:real^N) + s % w)`;
                 `t0 % (w:real^N)`; `&0`]
    GEOG_DEXP_CURVE) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  SUBGOAL_THEN
   `(\r:real^1. t0 % ((v:real^N) + drop r % w)) = (\r. t0 % v + drop r % (t0 % w))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GEOG_AFFINE_VD] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "fam" (MP_TAC o SPECL [`&0`; `t0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_0]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* An open interval containing 0 and t on which r / t stays in (-e,1+e). *)

let GEOJV_SCALED_INTERVAL = prove
 (`!e t. &0 < e /\ ~(t = &0)
         ==> ?J. real_open J /\ is_realinterval J /\ &0 IN J /\ t IN J /\
                 !r. r IN J ==> --e < r / t /\ r / t < &1 + e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t \/ &0 < --t` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `real_interval(--(e * t),(&1 + e) * t)`;
    EXISTS_TAC `real_interval((&1 + e) * t,--(e * t))`] THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THENL
   [SUBGOAL_THEN `&0 < e * t` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 < e * --t` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `!r. r / t = --r / --t` (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MFD_EXP_DIFFERENTIAL_JACOBI_RAY = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w Y t.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        t % v IN mfd_exp_dom (top,atlas) g x /\
        mfd_jacobi atlas g (mfd_geo (top,atlas) g x v)
                   (mfd_geo_maxint (top,atlas) g x v) Y /\
        Y(&0) = vec 0 /\ mfd_covd atlas g (mfd_geo (top,atlas) g x v) Y (&0) = w
        ==> mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) (t % v) (t % w) = Y t`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfd_exp_dom (top,atlas) (g:A->real^N^N) x`; `t % (v:real^N)`;
                 `t % (w:real^N)`] GEOG_FAMILY_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `e:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fam")))))) THEN
  MP_TAC(ISPECL [`e:real`; `t:real`] GEOJV_SCALED_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC GEOJV_EXP_DIFF_FAMILY THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `J:real->bool`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `r:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r % ((v:real^N) + s % w) = (r / t) % (t % v + s % (t % w))`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(t = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  USE_THEN "fam" MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let MFD_EXP_DIFFERENTIAL_JACOBI = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w Y.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        v IN mfd_exp_dom (top,atlas) g x /\
        mfd_jacobi atlas g (mfd_geo (top,atlas) g x v)
                   (mfd_geo_maxint (top,atlas) g x v) Y /\
        Y(&0) = vec 0 /\ mfd_covd atlas g (mfd_geo (top,atlas) g x v) Y (&0) = w
        ==> mfd_differential (open_set_atlas (:real^N)) atlas
              (mfd_exp (top,atlas) g x) v w = Y(&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w:real^N`; `Y:real->real^N`; `&1`]
    MFD_EXP_DIFFERENTIAL_JACOBI_RAY) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID]);;

