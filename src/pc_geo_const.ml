(* ========================================================================= *)
(* Unit pc_geo_const (geodesics layer): constant curvature.  The             *)
(* curvature tensor of constant sectional curvature k                         *)
(* (MFD_SECTIONAL_CONST_RIEMANN, from APX_CONST_CURV_RIEMANN of              *)
(* pc_lrg_constcurv), the normal Jacobi fields (a sin(Lt) + b cos(Lt)) E     *)
(* along geodesics of curvature 1 (MFD_JACOBI_CONST1) and the resulting      *)
(* length of d(exp) (MFD_EXP_DIFFERENTIAL_CONST1, MT p. 14-15).               *)
(* ========================================================================= *)

needs "src/pc_geo_jvar.ml";;
needs "src/pc_lrg_constcurv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The curvature tensor of constant sectional curvature, and                 *)
(* the normal Jacobi fields of curvature 1.                                  *)
(* ========================================================================= *)

let MFD_SECTIONAL_CONST_RIEMANN = prove
 (`!top atlas (g:A->real^N^N) (x:A) k.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\
        (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g x u v = k)
        ==> !u v w. mfd_riemann atlas g x u v w =
                    k % ((v dot (g x ** w)) % u - (u dot (g x ** w)) % v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] CMPF_LOCAL_METRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local (atlas:((A->bool)#(A->real^N))->bool)
                               (chart_at atlas (x:A)) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`;
                 `k:real`] APX_CONST_CURV_RIEMANN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM mfd_sectional] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_riemann]);;

(* Derivatives of a sin(L(t - t0)) + b cos(L(t - t0)). *)

let GEOK_SINCOS_DERIV = prove
 (`!a b L t0 t.
        ((\t. a * sin(L * (t - t0)) + b * cos(L * (t - t0))) has_real_derivative
         (L * (a * cos(L * (t - t0)) - b * sin(L * (t - t0))))) (atreal t) /\
        ((\t. L * (a * cos(L * (t - t0)) - b * sin(L * (t - t0)))) has_real_derivative
         (--(L pow 2) * (a * sin(L * (t - t0)) + b * cos(L * (t - t0))))) (atreal t)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REAL_DIFF_TAC THEN CONV_TAC REAL_RING);;

(* Normal Jacobi fields when the sectional curvature is identically 1. *)

let MFD_JACOBI_CONST1 = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J E t0 a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g x u v = &1) /\
        mfd_geodesic (top,atlas) g gamma J /\ t0 IN J /\
        mfd_parallel atlas g gamma J E /\
        E t0 dot (g(gamma t0) ** mfd_vel atlas gamma t0) = &0
        ==> mfd_jacobi atlas g gamma J
              (\t. (a * sin(mfd_tnorm g (gamma t0) (mfd_vel atlas gamma t0) * (t - t0)) +
                    b * cos(mfd_tnorm g (gamma t0) (mfd_vel atlas gamma t0) * (t - t0))) %
                   E t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) ((gamma:real->A) t0)
                            (mfd_vel atlas gamma t0)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    MFD_GEODESIC_VEL_PARALLEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!t. t IN J ==> (gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* inner products along gamma *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> (E:real->real^N) t dot ((g:A->real^N^N)((gamma:real->A) t) **
                                    mfd_vel atlas gamma t) = &0 /\
            mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) = L pow 2`
  (LABEL_TAC "inner") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
        `(E:real->real^N) t0 dot ((g:A->real^N^N)((gamma:real->A) t0) **
                                    mfd_vel atlas gamma t0) = &0`)
        (concl th))) THEN
      MATCH_MP_TAC MFD_PARALLEL_INNER THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `J:real->bool`] THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "L" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `(gamma:real->A) t0`] GEOD_TNORM_BASIC) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC MFD_PARALLEL_INNER THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `J:real->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the scalar functions *)
  ABBREV_TAC `f = \t. a * sin(L * (t - t0)) + b * cos(L * (t - t0))` THEN
  ABBREV_TAC `f' = \t. L * (a * cos(L * (t - t0)) - b * sin(L * (t - t0)))` THEN
  SUBGOAL_THEN
   `!t. (f has_real_derivative f' t) (atreal t) /\
        (f' has_real_derivative --(L pow 2) * f t) (atreal t)`
  (LABEL_TAC "der") THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["f"; "f'"] THEN REWRITE_TAC[GEOK_SINCOS_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. (a * sin(L * (t - t0)) + b * cos(L * (t - t0))) % (E:real->real^N) t) =
    (\t. f t % E t)`
  SUBST1_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ASSUME `mfd_parallel (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                              (gamma:real->A) J (E:real->real^N)`) THEN
  REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\t. f t % (E:real->real^N) t) t =
            f' t % E t`
  (LABEL_TAC "c1") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `E:real->real^N`; `f:real->real`; `(f':real->real) t`; `t:real`]
      CMPG_COVD_SCALAR) THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\t. f' t % (E:real->real^N) t) t =
            (--(L pow 2) * f t) % E t`
  (LABEL_TAC "c2") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `E:real->real^N`; `f':real->real`; `--(L pow 2) * (f:real->real) t`;
                   `t:real`] CMPG_COVD_SCALAR) THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real->real. (!t. t IN J ==> h real_differentiable atreal t) ==>
                   mfd_field_diff atlas (gamma:real->A) (\t. h t % (E:real->real^N) t) J`
  (LABEL_TAC "fd") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPG_FIELD_DIFF_SCALAR THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_jacobi] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "fd" MATCH_MP_TAC THEN REWRITE_TAC[real_differentiable] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXISTS_TAC `(f':real->real) t` THEN
    USE_THEN "der" (fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN
    EXISTS_TAC `\t. (f':real->real) t % (E:real->real^N) t` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "fd" MATCH_MP_TAC THEN REWRITE_TAC[real_differentiable] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      EXISTS_TAC `--(L pow 2) * (f:real->real) t` THEN
      USE_THEN "der" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
      (mfd_covd atlas g gamma (\t. f t % (E:real->real^N) t)) t =
    mfd_covd atlas g gamma (\t. f' t % E t) t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPG_COVD_LOCAL THEN
    MP_TAC(ASSUME `real_open (J:real->bool)`) THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "c1" MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "c2" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(t:real) IN J`)]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`; `&1`]
    MFD_SECTIONAL_CONST_RIEMANN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "inner" (MP_TAC o C MATCH_MP (ASSUME `(t:real) IN J`)) THEN
  REWRITE_TAC[DOT_LMUL] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO; VECTOR_MUL_LID] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `--(L pow 2) * x + L pow 2 * x = &0`; VECTOR_MUL_LZERO]);;

(* ========================================================================= *)
(* The length of d(exp) when the sectional curvature is 1                    *)
(* (MFD_EXP_DIFFERENTIAL_CONST1).  For v <> 0 write w = c v + w0 with       *)
(* w0 orthogonal to v; the Jacobi field c t T(t) + (sin(L t)/L) E(t), E the  *)
(* parallel field with E(0) = w0, has value 0 and covariant derivative w at  *)
(* 0, so d exp_x(v) w is its value at 1 (MFD_EXP_DIFFERENTIAL_JACOBI).        *)
(* ========================================================================= *)

let GEOK_QUAD_EXPAND = prove
 (`!(G:real^N^N) (X:real^N) Z a b.
        (!u v. u dot (G ** v) = v dot (G ** u))
        ==> (a % X + b % Z) dot (G ** (a % X + b % Z)) =
            a pow 2 * (X dot (G ** X)) + &2 * a * b * (X dot (G ** Z)) +
            b pow 2 * (Z dot (G ** Z))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `(Z:real^N) dot ((G:real^N^N) ** X) = X dot (G ** Z)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; CONV_TAC REAL_RING]);;

let MFD_EXP_DIFFERENTIAL_CONST1 = prove
 (`!top atlas (g:A->real^N^N) (x:A) v w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g x u v = &1) /\
        x IN topspace top /\ v IN mfd_exp_dom (top,atlas) g x
        ==> mfd_tnorm g (mfd_exp (top,atlas) g x v)
              (mfd_differential (open_set_atlas (:real^N)) atlas
                 (mfd_exp (top,atlas) g x) v w) pow 2 =
            (if v = vec 0 then mfd_tnorm g x w pow 2
             else ((v dot (g x ** w)) / mfd_tnorm g x v) pow 2 +
                  (sin(mfd_tnorm g x v) / mfd_tnorm g x v) pow 2 *
                  (mfd_tnorm g x w pow 2 -
                   ((v dot (g x ** w)) / mfd_tnorm g x v) pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_DOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] MFD_EXP_DIFFERENTIAL_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `L = mfd_tnorm (g:A->real^N^N) x v` THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC SQRT_POS_LT THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_G_POS_DEF) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(L = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) dot ((g:A->real^N^N) x ** v) = L pow 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N` o el 2 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) dot ((g:A->real^N^N) x ** v) = v dot (g x ** w)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOG_G_SYM_POS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p = (v:real^N) dot ((g:A->real^N^N) x ** w)` THEN
  ABBREV_TAC `c = p / L pow 2` THEN
  ABBREV_TAC `w0 = (w:real^N) - c % v` THEN
  SUBGOAL_THEN `(w0:real^N) dot ((g:A->real^N^N) x ** v) = &0 /\
                (v:real^N) dot ((g:A->real^N^N) x ** w0) = &0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN
    REWRITE_TAC[DOT_LSUB; DOT_LMUL; MATRIX_VECTOR_MUL_SUB_LDISTRIB;
                MATRIX_VECTOR_MUL_RMUL; DOT_RSUB; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN
    UNDISCH_TAC `~(L = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w0:real^N) dot ((g:A->real^N^N) x ** w0) =
    w dot (g x ** w) - &2 * c * p + c pow 2 * L pow 2`
  ASSUME_TAC THENL
   [EXPAND_TAC "w0" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
                DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  (* the geodesic gam = mfd_geo x v on I0 *)
  REWRITE_TAC[mfd_exp] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^N^N) x v` THEN
  ABBREV_TAC `I0 = mfd_geo_maxint (top,atlas) (g:A->real^N^N) x v` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 IN (I0:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "I0" THEN
    MP_TAC(ASSUME `(v:real^N) IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`) THEN
    REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`]
    MFD_GEODESIC_VEL_PARALLEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the parallel field E with E(0) = w0 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`; `&0`; `w0:real^N`]
    MFD_PARALLEL_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  (* the Jacobi field *)
  SUBGOAL_THEN
   `mfd_jacobi atlas (g:A->real^N^N) (gam:real->A) I0
      (\t. (&0 + c * t) % mfd_vel atlas gam t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JACOBI_TANGENTIAL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_jacobi atlas (g:A->real^N^N) (gam:real->A) I0
      (\t. (inv L * sin(L * (t - &0)) + &0 * cos(L * (t - &0))) % (E:real->real^N) t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`; `E:real->real^N`;
                   `&0`; `inv L`; `&0`] MFD_JACOBI_CONST1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_jacobi atlas (g:A->real^N^N) (gam:real->A) I0
      (\t. (c * t) % mfd_vel atlas gam t + (inv L * sin(L * t)) % (E:real->real^N) t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`;
                   `\t. (&0 + c * t) % mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) t`;
                   `\t. (inv L * sin(L * (t - &0)) + &0 * cos(L * (t - &0))) %
                        (E:real->real^N) t`;
                   `&1`; `&1`] MFD_JACOBI_LINEAR) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
    REWRITE_TAC[VECTOR_MUL_LID; REAL_ADD_LID; REAL_SUB_RZERO; REAL_MUL_LZERO;
                REAL_ADD_RID];
    ALL_TAC] THEN
  (* its covariant derivative at 0 *)
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gam:real->A)
      (\t. (c * t) % mfd_vel atlas gam t + (inv L * sin(L * t)) % (E:real->real^N) t)
      (&0) = w`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `mfd_parallel atlas (g:A->real^N^N) (gam:real->A) I0
                     (mfd_vel atlas gam)`) THEN
    MP_TAC(ASSUME `mfd_parallel atlas (g:A->real^N^N) (gam:real->A) I0
                     (E:real->real^N)`) THEN
    REWRITE_TAC[mfd_parallel] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cE")) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cT")) THEN
    SUBGOAL_THEN
     `((\t. c * t) has_real_derivative c) (atreal (&0)) /\
      ((\t. inv L * sin(L * t)) has_real_derivative &1) (atreal (&0)) /\
      (!t. (\t. c * t) real_differentiable atreal t) /\
      (!t. (\t. inv L * sin(L * t)) real_differentiable atreal t)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        REAL_DIFF_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; COS_0] THEN
        UNDISCH_TAC `~(L = &0)` THEN CONV_TAC REAL_FIELD;
        GEN_TAC THEN REAL_DIFFERENTIABLE_TAC;
        GEN_TAC THEN REAL_DIFFERENTIABLE_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `mfd_field_diff atlas (gam:real->A) (\t. (c * t) % mfd_vel atlas gam t) I0 /\
      mfd_field_diff atlas gam (\t. (inv L * sin(L * t)) % (E:real->real^N) t) I0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CMPG_FIELD_DIFF_SCALAR THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`;
                   `\t. (c * t) % mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) t`;
                   `\t. (inv L * sin(L * t)) % (E:real->real^N) t`;
                   `&1`; `&1`; `&0`] CMPG_COVD_LIN) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`;
                   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A)`; `\t:real. c * t`; `c:real`; `&0`]
      CMPG_COVD_SCALAR) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gam:real->A`; `I0:real->bool`;
                   `E:real->real^N`; `\t. inv L * sin(L * t)`; `&1`; `&0`]
      CMPG_COVD_SCALAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "cE" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&0 IN I0`)]) THEN
    USE_THEN "cT" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `&0 IN I0`)]) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; SIN_0; VECTOR_MUL_RZERO; VECTOR_MUL_LZERO;
                    VECTOR_ADD_RID; VECTOR_MUL_LID] THEN
    MP_TAC(ASSUME `(w:real^N) - c % v = w0`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  (* d exp is the value at 1 *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `v:real^N`; `w:real^N`;
                 `\t. (c * t) % mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) t +
                      (inv L * sin(L * t)) % (E:real->real^N) t`]
    MFD_EXP_DIFFERENTIAL_JACOBI) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; SIN_0; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
  (* the metric at gam 1 *)
  SUBGOAL_THEN `(gam:real->A) (&1) IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `I0:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gam:real->A) (&1)`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[el 2 (CONJUNCTS th)]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gam:real->A) (&1)`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP GEOK_QUAD_EXPAND th]) THEN
  (* inner products are transported from 0 *)
  SUBGOAL_THEN
   `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&1) dot ((g:A->real^N^N)(gam (&1)) **
                                          mfd_vel atlas gam (&1)) = L pow 2 /\
    mfd_vel atlas gam (&1) dot (g(gam (&1)) ** (E:real->real^N) (&1)) = &0 /\
    E (&1) dot (g(gam (&1)) ** E (&1)) = w0 dot (g x ** w0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS
       `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&0) dot ((g:A->real^N^N)(gam (&0)) **
                                              mfd_vel atlas gam (&0))`;
      TRANS_TAC EQ_TRANS
       `mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gam:real->A) (&0) dot ((g:A->real^N^N)(gam (&0)) **
                                              (E:real->real^N) (&0))`;
      TRANS_TAC EQ_TRANS
       `(E:real->real^N) (&0) dot ((g:A->real^N^N)((gam:real->A) (&0)) ** E (&0))`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC MFD_PARALLEL_INNER THEN
       MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                             `I0:real->bool`] THEN
       ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[el 2 (CONJUNCTS th)]) THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[real_div] THEN
  UNDISCH_TAC `~(L = &0)` THEN CONV_TAC REAL_FIELD);;

