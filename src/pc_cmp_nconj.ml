(* ========================================================================= *)
(* Unit pc_cmp_nconj (comparison-geometry layer CMP, used by the barriers of *)
(* pc_cmp_hess): along a unit-speed minimizing geodesic gamma on [0,d], no   *)
(* point gamma(s1), delta < s1 <= d, is conjugate to an interior point       *)
(* gamma(delta), 0 < delta < d (the step that Calabi's barrier for S7        *)
(* needs).  Shift invariance of velocities, covariant derivatives, Jacobi    *)
(* fields and smooth fields; then the index argument of CMPS_NO_CONJUGATE    *)
(* with the corner moved inside.                                             *)
(* ========================================================================= *)

needs "src/pc_cmp_mgeo.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Shift invariance (t -> t + c) of the velocity, covariant                  *)
(* derivative, Jacobi fields, smooth fields and the index density.           *)
(* ========================================================================= *)

let CMPN_HAS_VD_SHIFT = prove
 (`!(f:real^1->real^N) f' t c.
        ((\s. f(s + lift c)) has_vector_derivative f') (at t) <=>
        (f has_vector_derivative f') (at (t + lift c))`,
  SUBGOAL_THEN
   `!(f:real^1->real^N) f' t c.
        (f has_vector_derivative f') (at (t + lift c))
        ==> ((\s. f(s + lift c)) has_vector_derivative f') (at t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\s. (f:real^1->real^N)(s + lift c)) = f o (\s. s + lift c)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `f' = drop(vec 1) % (f':real^N)` SUBST1_TAC THENL
     [REWRITE_TAC[DROP_VEC; VECTOR_MUL_LID]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\s:real^1. s`; `vec 1:real^1`; `\s:real^1. lift c`; `vec 0:real^1`;
                   `at (t:real^1)`] HAS_VECTOR_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID; HAS_VECTOR_DERIVATIVE_CONST; VECTOR_ADD_RID];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\s. (f:real^1->real^N)(s + lift c)`; `f':real^N`;
                                `t + lift c`; `--c`]) THEN
  REWRITE_TAC[LIFT_NEG; VECTOR_ARITH `(t + c) + --c:real^1 = t`;
              VECTOR_ARITH `(s + --c) + c:real^1 = s`; ETA_AX] THEN
  ASM_REWRITE_TAC[]);;

let CMPN_VD_SHIFT = prove
 (`!(f:real^1->real^N) t c.
        vector_derivative (\s. f(s + lift c)) (at t) =
        vector_derivative f (at (t + lift c))`,
  REWRITE_TAC[vector_derivative; CMPN_HAS_VD_SHIFT]);;

let CMPN_DIFFERENTIABLE_SHIFT = prove
 (`!(f:real^1->real^N) t c.
        f differentiable at (t + lift c)
        ==> (\s. f(s + lift c)) differentiable at t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[CMPN_VD_SHIFT; CMPN_HAS_VD_SHIFT]);;

let CMPN_VEL_SHIFT = prove
 (`!atlas (gamma:real->A) c t.
        mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (\s. gamma(s + c)) t =
        mfd_vel atlas gamma (t + c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_vel] THEN
  MP_TAC(ISPECL [`\s:real^1. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                  ((gamma:real->A)(t + c))) (gamma(drop s))`;
                 `lift t`; `c:real`] CMPN_VD_SHIFT) THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP; GSYM LIFT_ADD]);;

let CMPN_COVD_SHIFT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) c t.
        mfd_covd atlas g (\s. gamma(s + c)) (\s. Y(s + c)) t =
        mfd_covd atlas g gamma Y (t + c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_covd; CMPN_VEL_SHIFT; mfd_field_rep] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                  ((gamma:real->A)(drop s)))
                                (chart_at atlas (gamma(t + c))) (gamma(drop s))
                                ((Y:real->real^N)(drop s))`;
                 `lift t`; `c:real`] CMPN_VD_SHIFT) THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP; GSYM LIFT_ADD]);;

let CMPN_IDENS_SHIFT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) (X:real->real^N) c t.
        cmp_idens atlas g (\s. gamma(s + c)) (\s. X(s + c)) t =
        cmp_idens atlas g gamma X (t + c)`,
  REWRITE_TAC[cmp_idens; CMPN_COVD_SHIFT; CMPN_VEL_SHIFT]);;

let CMPN_FIELD_DIFF_SHIFT = prove
 (`!atlas (gamma:real->A) (Y:real->real^N) J c.
        mfd_field_diff atlas gamma Y J
        ==> mfd_field_diff atlas (\s. gamma(s + c)) (\s. Y(s + c)) {t | t + c IN J}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_field_diff; mfd_field_rep; IN_ELIM_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t + c`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                  ((gamma:real->A)(drop s)))
                                (chart_at atlas (gamma(t + c))) (gamma(drop s))
                                ((Y:real->real^N)(drop s))`;
                 `lift t`; `c:real`] CMPN_DIFFERENTIABLE_SHIFT) THEN
  ASM_REWRITE_TAC[GSYM LIFT_ADD; DROP_ADD; LIFT_DROP]);;

let CMPN_JACOBI_SHIFT = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) c.
        mfd_jacobi atlas g gamma J Y
        ==> mfd_jacobi atlas g (\s. gamma(s + c)) {t | t + c IN J} (\s. Y(s + c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_jacobi] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (\s. (gamma:real->A)(s + c)) (\s. (Y:real->real^N)(s + c)) =
    (\s. mfd_covd atlas g gamma Y (s + c))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; CMPN_COVD_SHIFT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPN_FIELD_DIFF_SHIFT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`;
                   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N)`;
                   `J:real->bool`; `c:real`] CMPN_FIELD_DIFF_SHIFT) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`;
                   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N)`;
                   `c:real`; `t:real`] CMPN_COVD_SHIFT) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CMPN_VEL_SHIFT] THEN ASM_SIMP_TAC[]]);;

let CMPN_SFIELD_SHIFT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (X:real->real^N) c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ cmp_sfield atlas gamma J X
        ==> cmp_sfield atlas (\s. gamma(s + c)) {t | t + c IN J} (\s. X(s + c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cmp_sfield atlas (gamma:real->A) J (X:real->real^N)` THEN
  REWRITE_TAC[cmp_sfield; IN_ELIM_THM; mfd_field_rep] THEN DISCH_TAC THEN
  X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `cc:(A->bool)#(A->real^N)`] MFD_GEODESIC_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on {lift t | t IN J /\ (gamma:real->A) t IN FST (cc:(A->bool)#(A->real^N))}
      (\s. chart_jac (chart_at atlas (gamma (drop s))) cc (gamma (drop s))
             ((X:real->real^N) (drop s)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `S = {lift t | t IN J /\ (gamma:real->A) t IN FST (cc:(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN
   `{lift t | t + c IN J /\ (gamma:real->A) (t + c) IN FST (cc:(A->bool)#(A->real^N))} =
    {y | y + lift c IN S}`
  SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^1` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t + c` THEN ASM_REWRITE_TAC[LIFT_ADD];
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t - c` THEN ASM_REWRITE_TAC[REAL_SUB_ADD] THEN
      UNDISCH_TAC `y + lift c = lift t` THEN REWRITE_TAC[LIFT_SUB] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {y | y + lift c IN S}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `(\s. chart_jac (chart_at atlas ((gamma:real->A) (drop s)))
                   (cc:(A->bool)#(A->real^N)) (gamma (drop s))
                   ((X:real->real^N) (drop s))) o (\y:real^1. y + lift c)` THEN
  CONJ_TAC THENL [REWRITE_TAC[o_THM; DROP_ADD; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `S:real^1->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]]);;

(* ========================================================================= *)
(* The second variation integral of Y + e W on [a,b] for a                   *)
(* Jacobi field Y vanishing at both ends (CMPS_FIRST_PIECE on a general      *)
(* interval).                                                                *)
(* ========================================================================= *)

let CMPN_PIECE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (Y:real->real^N) W a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ mfd_jacobi atlas g gamma J Y /\
        mfd_field_diff atlas gamma W J /\ a <= b /\ real_interval[a,b] SUBSET J /\
        Y a = vec 0 /\ Y b = vec 0 /\
        (\r. cmp_idens atlas g gamma W r) real_integrable_on real_interval[a,b]
        ==> !e. ((\r. &2 * cmp_idens atlas g gamma (\s. Y s + e % W s) r)
                 has_real_integral
                 (&4 * e * (mfd_covd atlas g gamma Y b dot (g(gamma b) ** W b) -
                            mfd_covd atlas g gamma Y a dot (g(gamma a) ** W a)) +
                  e pow 2 * (&2 * real_integral (real_interval[a,b])
                                    (\r. cmp_idens atlas g gamma W r))))
                (real_interval[a,b])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN
  SUBGOAL_THEN `mfd_field_diff atlas (gamma:real->A) (Y:real->real^N) J` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_jacobi]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `Y:real->real^N`; `a:real`; `b:real`] CMPS_JACOBI_PAIR_FTC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_SUB_REFL] THEN
  DISCH_THEN(LABEL_TAC "iy") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                 `W:real->real^N`; `a:real`; `b:real`] CMPS_JACOBI_PAIR_FTC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "iw") THEN
  FIRST_X_ASSUM(LABEL_TAC "ii" o MATCH_MP REAL_INTEGRABLE_INTEGRAL o check (fun th ->
    can (find_term ((=) `real_integrable_on`)) (concl th))) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC
   `\r. (&2 * (mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) r dot
               (g(gamma r) ** mfd_covd atlas g gamma Y r) -
               Y r dot (g(gamma r) **
                        mfd_riemann atlas g (gamma r) (Y r)
                          (mfd_vel atlas gamma r) (mfd_vel atlas gamma r))) +
         (&4 * e) * (mfd_covd atlas g gamma Y r dot
                     (g(gamma r) ** mfd_covd atlas g gamma (W:real->real^N) r) -
                     W r dot (g(gamma r) **
                              mfd_riemann atlas g (gamma r) (Y r)
                                (mfd_vel atlas gamma r) (mfd_vel atlas gamma r)))) +
        e pow 2 * (&2 * cmp_idens atlas g gamma W r)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`; `Y:real->real^N`;
                   `W:real->real^N`; `e:real`; `r:real`] CMPS_IDENS_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[cmp_idens] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 * e * (mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) b dot
              (g(gamma b) ** (W:real->real^N) b) -
              mfd_covd atlas g gamma Y a dot (g(gamma a) ** W a)) +
    e pow 2 * (&2 * real_integral (real_interval[a,b])
                      (\r. cmp_idens atlas g gamma W r)) =
    (&2 * &0 + (&4 * e) * (mfd_covd atlas g gamma Y b dot (g(gamma b) ** W b) -
                           mfd_covd atlas g gamma Y a dot (g(gamma a) ** W a))) +
    e pow 2 * (&2 * real_integral (real_interval[a,b])
                      (\r. cmp_idens atlas g gamma W r))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
    USE_THEN "ii" (ACCEPT_TAC o BETA_RULE)]);;

(* ========================================================================= *)
(* The geodesic from an interior point of a ray, and transport               *)
(* of Jacobi fields based there back to the ray's parametrization.           *)
(* ========================================================================= *)

let CMPN_SHIFT_SETUP = prove
 (`!top atlas (g:A->real^N^N) (x:A) u delta.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        delta IN mfd_geo_maxint (top,atlas) g x u
        ==> mfd_geo (top,atlas) g x u delta IN topspace top /\
            mfd_tnorm g (mfd_geo (top,atlas) g x u delta)
              (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta) = mfd_tnorm g x u /\
            !t. t + delta IN mfd_geo_maxint (top,atlas) g x u
                ==> t IN mfd_geo_maxint (top,atlas) g (mfd_geo (top,atlas) g x u delta)
                           (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta) /\
                    mfd_geo (top,atlas) g (mfd_geo (top,atlas) g x u delta)
                      (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta) t =
                    mfd_geo (top,atlas) g x u (t + delta)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `delta:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) u`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u`; `delta:real`;
                   `&0`] MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sh" (MP_TAC o SPEC `t:real`) THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_SIMP_TAC[]]);;

let CMPN_JACOBI_TRANSPORT = prove
 (`!top atlas (g:A->real^N^N) (x:A) u delta (Yq:real->real^N) J1.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        delta IN mfd_geo_maxint (top,atlas) g x u /\
        mfd_jacobi atlas g
          (mfd_geo (top,atlas) g (mfd_geo (top,atlas) g x u delta)
                   (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta))
          (mfd_geo_maxint (top,atlas) g (mfd_geo (top,atlas) g x u delta)
                          (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta)) Yq /\
        real_open J1 /\ is_realinterval J1 /\
        J1 SUBSET mfd_geo_maxint (top,atlas) g (mfd_geo (top,atlas) g x u delta)
                                 (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta) /\
        cmp_sfield atlas
          (mfd_geo (top,atlas) g (mfd_geo (top,atlas) g x u delta)
                   (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta)) J1 Yq
        ==> mfd_jacobi atlas g (mfd_geo (top,atlas) g x u)
              (mfd_geo_maxint (top,atlas) g x u) (\t. Yq(t + --delta)) /\
            cmp_sfield atlas (mfd_geo (top,atlas) g x u)
              (mfd_geo_maxint (top,atlas) g x u INTER {t | t + --delta IN J1})
              (\t. Yq(t + --delta)) /\
            mfd_covd atlas g (mfd_geo (top,atlas) g x u) (\t. Yq(t + --delta)) delta =
            mfd_covd atlas g
              (mfd_geo (top,atlas) g (mfd_geo (top,atlas) g x u delta)
                       (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta)) Yq (&0)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `gq = mfd_geo (top,atlas) (g:A->real^N^N)
                     (mfd_geo (top,atlas) g (x:A) u delta)
                     (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta)` THEN
  ABBREV_TAC `Gq = mfd_geo_maxint (top,atlas) (g:A->real^N^N)
                     (mfd_geo (top,atlas) g (x:A) u delta)
                     (mfd_vel atlas (mfd_geo (top,atlas) g x u) delta)` THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) (x:A) u` THEN
  ABBREV_TAC `G = mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `delta:real`] CMPN_SHIFT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh"))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN G ==> t + --delta IN Gq /\
                               (gq:real->A) (t + --delta) = gamma t`
  (LABEL_TAC "sh2") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "sh" (MP_TAC o SPEC `t + --delta`) THEN
    REWRITE_TAC[REAL_ARITH `(t + --d) + d = t`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_jacobi atlas (g:A->real^N^N) (\t. (gq:real->A)(t + --delta)) {t | t + --delta IN Gq}
      (\t. (Yq:real->real^N)(t + --delta))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPN_JACOBI_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC GEOJV_JACOBI_CURVE_LOCAL THEN
    EXISTS_TAC `\t. (gq:real->A)(t + --delta)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC GEOJV_JACOBI_SUBSET THEN EXISTS_TAC `{t | t + --delta IN Gq}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CMPS_SFIELD_CONG THEN
    MAP_EVERY EXISTS_TAC [`\t. (gq:real->A)(t + --delta)`;
                          `\t. (Yq:real->real^N)(t + --delta)`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CMPS_SFIELD_SUBSET THEN EXISTS_TAC `{t | t + --delta IN J1}` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC CMPN_SFIELD_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `Gq:real->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) (x:A) u delta`;
                   `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N) (x:A) u) delta`]
      MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gq:real->A`; `Yq:real->real^N`; `--delta`; `delta:real`]
      CMPN_COVD_SHIFT) THEN
    REWRITE_TAC[REAL_ADD_RINV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CMPV_COVD_CURVE_LOCAL THEN
    UNDISCH_TAC `real_open (G:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `delta:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "sh2" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* A two-sided family domain for the exp variation family                    *)
(* r (u + s w) around a segment [a,b] u through 0.                           *)
(* ========================================================================= *)

let CMPN_FAMILY_TWO_SIDED = prove
 (`!D (u:real^N) w a b.
        open D /\ (!v t. v IN D /\ &0 <= t /\ t <= &1 ==> t % v IN D) /\
        a % u IN D /\ b % u IN D /\ a < &0 /\ &0 < b
        ==> ?d0 J1. &0 < d0 /\ real_open J1 /\ is_realinterval J1 /\
                    real_interval[a,b] SUBSET J1 /\
                    !s r. abs s < d0 /\ r IN J1 ==> r % (u + s % w) IN D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`D:real^N->bool`; `b % (u:real^N)`; `b % (w:real^N)`]
    GEOG_FAMILY_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`D:real^N->bool`; `a % (u:real^N)`; `a % (w:real^N)`]
    GEOG_FAMILY_DOMAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `min d1 d2` THEN
  EXISTS_TAC `real_interval((&1 + e2) * a,(&1 + e1) * b)` THEN
  REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IS_REALINTERVAL_INTERVAL] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < e2 * --a /\ &0 < e1 * b` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `r:real`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= r` THENL
   [SUBGOAL_THEN `r % ((u:real^N) + s % w) = (r / b) % (b % u + s % (b % w))`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `&0 < b` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `e1:real`)) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 < e1 * b` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `r % ((u:real^N) + s % w) = (r / a) % (a % u + s % (a % w))`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `a < &0` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `e2:real`)) (concl th))) THEN
    SUBGOAL_THEN `r / a = --r / --a` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < --a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
    SUBGOAL_THEN `&0 < e2 * --a` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

let CMPN_TRANSLATE_INTERVAL = prove
 (`!J c. real_open J /\ is_realinterval J
         ==> real_open {t | t + c IN J} /\ is_realinterval {t | t + c IN J}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_open; is_realinterval; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "op") (LABEL_TAC "iv")) THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "op" (fun th -> MP_TAC(MATCH_MP th (ASSUME `t + c IN (J:real->bool)`))) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `z:real`] THEN STRIP_TAC THEN
    USE_THEN "iv" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a + c`; `b + c`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* No conjugate points from an interior point.  Along the                    *)
(* unit-speed ray gamma = geo x u, minimizing on [0,d], for 0 < delta and    *)
(* 0 < s with delta + s <= d, d exp at gamma(delta) is injective at          *)
(* s gamma'(delta).  A kernel vector gives a Jacobi field Y along gamma with *)
(* Y(delta) = Y(delta + s) = 0, DY(delta) != 0; the broken field e W1 on     *)
(* [0,delta], Y + e W2 on [delta,delta + s] has negative second variation.  *)
(* ========================================================================= *)

let CMPN_NO_CONJ = prove
 (`!top atlas (g:A->real^N^N) (x:A) u d delta s h.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ mfd_tnorm g x u = &1 /\
        real_interval[&0,d] SUBSET mfd_geo_maxint (top,atlas) g x u /\
        mfd_dist (top,atlas) g x (mfd_geo (top,atlas) g x u d) = d /\
        &0 < delta /\ &0 < s /\ delta + s <= d /\
        mfd_differential (open_set_atlas (:real^N)) atlas
          (mfd_exp (top,atlas) g (mfd_geo (top,atlas) g x u delta))
          (s % mfd_vel atlas (mfd_geo (top,atlas) g x u) delta) h = vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p. &0 <= p /\ p <= d
                    ==> (p:real) IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u`
  (LABEL_TAC "inG") THENL
   [UNDISCH_TAC `real_interval[&0,d] SUBSET
                 mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta IN mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u /\
                delta + s IN mfd_geo_maxint (top,atlas) g x u`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `delta:real`] CMPN_SHIFT_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh"))) THEN
  ABBREV_TAC `gamma = mfd_geo (top,atlas) (g:A->real^N^N) (x:A) u` THEN
  ABBREV_TAC `G = mfd_geo_maxint (top,atlas) (g:A->real^N^N) (x:A) u` THEN
  ABBREV_TAC `q = (gamma:real->A) delta` THEN
  ABBREV_TAC `uq = mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) delta` THEN
  ABBREV_TAC `gq = mfd_geo (top,atlas) (g:A->real^N^N) (q:A) uq` THEN
  ABBREV_TAC `Gq = mfd_geo_maxint (top,atlas) (g:A->real^N^N) (q:A) uq` THEN
  SUBGOAL_THEN `!t. t IN G ==> mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                                   (gamma:real->A) t dot
                                 ((g:A->real^N^N) (gamma t) ** mfd_vel atlas gamma t) = &1`
  (LABEL_TAC "gunit") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `G:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `(gamma:real->A) t`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) t` o
               CONJUNCT1 o CONJUNCT2 o
               CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`; `t:real`; `&0`]
      MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r + delta IN G ==> r % (uq:real^N) IN mfd_exp_dom (top,atlas)
                                          (g:A->real^N^N) (q:A)`
  (LABEL_TAC "rdom") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    USE_THEN "sh" (MP_TAC o SPEC `r:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `uq:real^N`; `r:real`] MFD_EXP_RADIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `w = inv s % (h:real^N)` THEN
  SUBGOAL_THEN `~(w:real^N = vec 0) /\ s % w = h` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC;
                 REAL_MUL_RINV; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 IN Gq` ASSUME_TAC THENL
   [USE_THEN "sh" (MP_TAC o SPEC `&0`) THEN REWRITE_TAC[REAL_ADD_LID] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gq:real->A`; `Gq:real->bool`; `&0`;
                 `vec 0:real^N`; `w:real^N`] MFD_JACOBI_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Yq:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  SUBGOAL_THEN `(Yq:real->real^N) s = vec 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `uq:real^N`; `w:real^N`; `Yq:real->real^N`;
                   `s:real`] MFD_EXP_DIFFERENTIAL_JACOBI_RAY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [USE_THEN "rdom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `--delta % (uq:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) (q:A) /\
                s % uq IN mfd_exp_dom (top,atlas) g q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "rdom" MATCH_MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_ADD_LINV];
      ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`mfd_exp_dom (top,atlas) (g:A->real^N^N) (q:A)`; `uq:real^N`; `w:real^N`;
                 `--delta`; `s:real`] CMPN_FAMILY_TWO_SIDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d0:real` (X_CHOOSE_THEN `J1:real->bool` STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `(J1:real->bool) SUBSET Gq` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `uq:real^N`; `r:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `r:real`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_ABS_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 IN (J1:real->bool) /\ s IN J1 /\ --delta IN J1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `real_interval[--delta,s] SUBSET (J1:real->bool)` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `q:A`; `uq:real^N`; `w:real^N`; `Yq:real->real^N`;
                 `d0:real`; `J1:real->bool`] CMPS_JACOBI_SFIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`; `delta:real`; `Yq:real->real^N`;
                 `J1:real->bool`] CMPN_JACOBI_TRANSPORT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Y = \t. (Yq:real->real^N) (t + --delta)` THEN
  SUBGOAL_THEN `(Y:real->real^N) delta = vec 0 /\ Y (delta + s) = vec 0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN
    ASM_REWRITE_TAC[REAL_ADD_RINV; REAL_ARITH `(d + s) + --d = s`];
    ALL_TAC] THEN
  ABBREV_TAC `JJ = (G:real->bool) INTER {t | t + --delta IN J1}` THEN
  SUBGOAL_THEN `real_open JJ /\ is_realinterval JJ /\ JJ SUBSET G /\
                real_interval[&0,delta + s] SUBSET JJ`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`J1:real->bool`; `--delta`] CMPN_TRANSLATE_INTERVAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXPAND_TAC "JJ" THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC IS_REALINTERVAL_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `real_interval[--delta,s] SUBSET (J1:real->bool)` THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_geodesic (top,atlas) (g:A->real^N^N) (gamma:real->A) JJ` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_GEODESIC_SUBINTERVAL THEN EXISTS_TAC `G:real->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_jacobi atlas (g:A->real^N^N) (gamma:real->A) JJ (Y:real->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOJV_JACOBI_SUBSET THEN EXISTS_TAC `G:real->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `u:real^N`] CMPI_FRAME_UNIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?j. 1 <= j /\ j <= dimindex(:N) /\
        ~((Fr:num->real->real^N) j delta dot ((g:A->real^N^N) (q:A) ** (w:real^N)) = &0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[TAUT `a /\ b /\ ~c <=> ~(a /\ b ==> c)`; GSYM NOT_FORALL_THM] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(w:real^N = vec 0)` THEN REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
                             (Y:real->real^N) delta = w`)) THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `gamma:real->A`; `G:real->bool`; `Fr:num->real->real^N`;
                   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N)`;
                   `delta:real`] CMPF_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `cmp_fcoord (g:A->real^N^N) (gamma:real->A) (Fr:num->real->real^N)
        (mfd_covd atlas g gamma (Y:real->real^N)) delta = vec 0`
    SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[CMPF_FCOORD_COMPONENT];
      REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  ABBREV_TAC
   `cj = (Fr:num->real->real^N) j delta dot ((g:A->real^N^N) (q:A) ** (w:real^N))` THEN
  SUBGOAL_THEN `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) G
                  ((Fr:num->real->real^N) j)` ASSUME_TAC THENL
   [UNDISCH_TAC `cmp_pframe atlas (g:A->real^N^N) (gamma:real->A) G
                   (Fr:num->real->real^N)` THEN
    REWRITE_TAC[cmp_pframe] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_sfield atlas (gamma:real->A) G ((Fr:num->real->real^N) j)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPI_PARALLEL_SFIELD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. cmp_sfield atlas (gamma:real->A) JJ
                        (\r. (a + b * r) % (Fr:num->real->real^N) j r)`
  (LABEL_TAC "aff") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC CMPS_SFIELD_SUBSET THEN
    EXISTS_TAC `G:real->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CMPI_SFIELD_AFFINE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. mfd_field_diff atlas (gamma:real->A)
                        (\r. (a + b * r) % (Fr:num->real->real^N) j r) JJ`
  (LABEL_TAC "affd") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `JJ:real->bool`] CMPS_GEODESIC_CURVES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPG_FIELD_DIFF_SCALAR THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_parallel atlas (g:A->real^N^N) (gamma:real->A) G
                     ((Fr:num->real->real^N) j)` THEN
      REWRITE_TAC[mfd_parallel; mfd_field_diff] THEN
      DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT1 th)) THEN
      ASM SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_DIFFERENTIABLE_ADD THEN
      REWRITE_TAC[REAL_DIFFERENTIABLE_CONST] THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_MUL_ATREAL THEN
      REWRITE_TAC[REAL_DIFFERENTIABLE_CONST; REAL_DIFFERENTIABLE_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r <= delta + s ==> (r:real) IN JJ` (LABEL_TAC "inJJ") THENL
   [UNDISCH_TAC `real_interval[&0,delta + s] SUBSET JJ` THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(delta = &0) /\ ~(s = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `b1 = cj / delta` THEN
  ABBREV_TAC `a2 = cj * (delta + s) / s` THEN
  ABBREV_TAC `b2 = --cj / s` THEN
  SUBGOAL_THEN
   `!r. r IN real_interval[delta,delta + s]
        ==> cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
              (\r. (a2 + b2 * r) % (Fr:num->real->real^N) j r) r =
            b2 pow 2 - (a2 + b2 * r) pow 2 * cmp_rmat atlas g gamma Fr r$j$j`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMPI_IDENS_FRAME THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `G:real->bool`] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r. cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
           (\r. (a2 + b2 * r) % (Fr:num->real->real^N) j r) r)
    real_integrable_on real_interval[delta,delta + s]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC `\r. b2 pow 2 - (a2 + b2 * r) pow 2 *
                    cmp_rmat atlas (g:A->real^N^N) (gamma:real->A)
                      (Fr:num->real->real^N) r$j$j` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`;
                   `Fr:num->real->real^N`; `j:num`; `a2:real`; `b2:real`; `delta:real`;
                   `delta + s`] CMPI_PIECE_INTEGRAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `&0 < s ==> d <= d + s`] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `JJ:real->bool`; `Y:real->real^N`;
                 `\r. (a2 + b2 * r) % (Fr:num->real->real^N) j r`; `delta:real`;
                 `delta + s`] CMPN_PIECE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `&0 < s ==> d <= d + s`] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inJJ" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "p2" o BETA_RULE)] THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) (delta + s) dot
    (g (gamma (delta + s)) **
     (a2 + b2 * (delta + s)) % (Fr:num->real->real^N) j (delta + s)) -
    mfd_covd atlas g gamma Y delta dot
    (g (gamma delta) ** (a2 + b2 * delta) % Fr j delta) = --(cj * cj)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `a2 + b2 * (delta + s) = &0 /\ a2 + b2 * delta = cj`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY EXPAND_TAC ["a2"; "b2"] THEN UNDISCH_TAC `~(s = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO;
                MATRIX_VECTOR_MUL_RMUL; DOT_RMUL; REAL_SUB_LZERO] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `q:A`; `w:real^N`;
                   `(Fr:num->real->real^N) j delta`] CMPS_G_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`--(cj * cj)`;
    `real_integral (real_interval[&0,delta])
       (\t. &2 * cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
                   (\t. (&0 + b1 * t) % (Fr:num->real->real^N) j t) t) +
     &2 * real_integral (real_interval[delta,delta + s])
            (\t. cmp_idens atlas g gamma (\r. (a2 + b2 * r) % Fr j r) t)`]
    CMPS_QUAD_NEG) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x < &0`) THEN ASM_REWRITE_TAC[REAL_LT_SQUARE];
    DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) ((gamma:real->A) (&0))
                  (gamma (delta + s)) = delta + s`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < d /\ d IN G /\ delta + s IN G` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `d:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `u:real^N`; `delta + s`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `d % (u:real^N)`; `(delta + s) / d`]
      CMPS_RAY_DIST0) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_MUL_RID; REAL_LE_DIV;
                 REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                 REAL_ARITH `&0 < delta /\ &0 < s ==> &0 <= delta + s`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `gamma:real->A`; `JJ:real->bool`; `delta + s`; `2`;
    `\i. if i = 0 then &0 else if i = 1 then delta else delta + s`;
    `\i. if i = 1 then (\r. (eps * &0 + eps * b1 * r) % (Fr:num->real->real^N) j r)
         else (\r. (Y:real->real^N) r + eps % ((a2 + b2 * r) % Fr j r))`]
    CMPI_SECVAR_NONNEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN USE_THEN "gunit" MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[cmp_pwfield] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1 \/ i = 2` MP_TAC THENL
       [ASM_ARITH_TAC; DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC CMPS_SFIELD_CONG THEN
        MAP_EVERY EXISTS_TAC
         [`gamma:real->A`;
          `\t. &1 % (Y:real->real^N) t +
               eps % (\r. (a2 + b2 * r) % (Fr:num->real->real^N) j r) t`] THEN
        CONJ_TAC THENL [REWRITE_TAC[VECTOR_MUL_LID]; ALL_TAC] THEN
        MATCH_MP_TAC CMPS_SFIELD_LIN THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`] THEN
        ASM_REWRITE_TAC[]];
      GEN_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `i = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      MAP_EVERY EXPAND_TAC ["b1"; "a2"; "b2"] THEN
      MAP_EVERY UNDISCH_TAC [`~(delta = &0)`; `~(s = &0)`] THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; VECTOR_MUL_LZERO];
      SUBGOAL_THEN `a2 + b2 * (delta + s) = &0` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["a2"; "b2"] THEN UNDISCH_TAC `~(s = &0)` THEN
        CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID]]];
    ALL_TAC] THEN
  REWRITE_TAC[cmp_secvar; CMPS_SUM_TWO] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  USE_THEN "p2" (fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL_UNIQUE (SPEC `eps:real` th)]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `G:real->bool`;
                 `Fr:num->real->real^N`; `j:num`; `&0`; `b1:real`; `&0`;
                 `delta:real`; `eps:real`] CMPS_SECOND_PIECE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    USE_THEN "inG" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `&4 * eps * --(cj * cj) +
    eps pow 2 *
    (real_integral (real_interval[&0,delta])
       (\t. &2 * cmp_idens atlas (g:A->real^N^N) (gamma:real->A)
                   (\t. (&0 + b1 * t) % (Fr:num->real->real^N) j t) t) +
     &2 * real_integral (real_interval[delta,delta + s])
            (\t. cmp_idens atlas g gamma (\r. (a2 + b2 * r) % Fr j r) t)) < &0` THEN
  REAL_ARITH_TAC);;

