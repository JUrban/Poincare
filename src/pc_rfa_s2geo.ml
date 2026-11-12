(* ========================================================================= *)
(* Unit pc_rfa_s2geo: for the 2-dimensional case of                          *)
(* P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT, the radial structure of             *)
(* a compact 2-d gradient shrinker with R = C exp f about a maximum point p  *)
(* of f.  Along every geodesic (f o gamma)'' = (1/2 - (C/2) e^f) |gamma'|^2  *)
(* (RFA_S2_GEO_F2); for unit v at p the radial function F_v(r) =            *)
(* f(exp_p(r v)) solves F'' = 1/2 - (C/2) e^F with F(0) = f(p), F'(0) = 0,   *)
(* F <= f(p) (RFA_S2_RADIAL_ODE, RFA_S2_RADIAL_MAX) and does not depend on v *)
(* (RFA_S2_RADIAL_UNIQ); if (C/2) e^f(p) <= 1/2 then f is constant and the  *)
(* metric is round (RFA_S2_ODE_FLAT, RFA_S2_POLAR, RFA_S2_FLAT_ROUND).       *)
(* Otherwise d exp_p(r u)(r n) = j(r) E(r) with j = -F'/beta and E the       *)
(* parallel normal (RFA_S2_JACOBI_SCALAR, RFA_S2_DEXP_JACOBI), all geodesics *)
(* from p meet at q = exp_p(A e1) (RFA_S2_ANTIPODE), and the arrival map at q *)
(* has speed alpha/beta < 1, against the circle lemma (RFA_S2_CIRCLE_D):      *)
(* the steep case is impossible (RFA_S2_NOT_STEEP).                           *)
(* ========================================================================= *)

needs "src/pc_rfa_s2loc.ml";;
needs "src/pc_rfa_s2ode.ml";;
needs "src/pc_geo_const.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The radial ODE.  Second derivative of f along                             *)
(* geodesics (RFA_S2_GEO_F2), the radial ODE and its initial data at a      *)
(* maximum point (RFA_S2_RADIAL_ODE, RFA_S2_RADIAL_MAX), a Lipschitz bound  *)
(* for exp (RFA_S2_EXP_LIP), independence of the direction                  *)
(* (RFA_S2_RADIAL_UNIQ), the flat case of the ODE (RFA_S2_ODE_FLAT), polar   *)
(* representation of points (RFA_S2_UNIT_SCALE, RFA_S2_POLAR) and the round  *)
(* conclusion when (C/2) e^f(p) <= 1/2 (RFA_S2_FLAT_ROUND).                  *)
(* ========================================================================= *)

let RFA_S2_GEO_F2 = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C
    (gamma:real->A) J t.
     p2b_shrinker (top,atlas) g f /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     mfd_geodesic (top,atlas) g gamma J /\ t IN J
     ==> (\s. f(gamma s)) real_differentiable atreal t /\
         (real_derivative (\s. f(gamma s)) has_real_derivative
            ((inv(&2) - C / &2 * exp(f(gamma t))) *
             (mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t)))) (atreal t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `(gamma:real->A) t`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U phi. chart_at atlas ((gamma:real->A) t) = (U:A->bool,phi:A->real^2)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `(U:A->bool,phi:A->real^2)`] RFA_SH_CHART_DATA) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `U:A->bool`; `phi:A->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `U:A->bool`; `phi:A->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `gamma:real->A`; `J:real->bool`; `(U:A->bool,phi:A->real^2)`]
                GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^2` (LABEL_TAC "vv")) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`; `U:A->bool`; `t:real`]
                GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[GEOL_GEODESIC_BASIC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  SUBGOAL_THEN
   `!s. abs(s - t) < d
        ==> (f:A->real)((gamma:real->A) s) =
            f(chart_inv (U,phi) ((phi:A->real^2)(gamma s)))`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "near" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - t) < d
        ==> ((\s. (f:A->real)((gamma:real->A) s)) has_real_derivative
             drop(frechet_derivative (\y. lift(f(chart_inv (U,phi) y)))
                    (at ((phi:A->real^2)(gamma s))) ((v:real->real^2) s))) (atreal s)`
  (LABEL_TAC "d1") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "near" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `abs(s - t) < d`))) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\r. (f:A->real)(chart_inv (U,phi) ((phi:A->real^2)((gamma:real->A) r)))` THEN
    EXISTS_TAC `d - abs(s - t)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "loc" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^2) U`;
                   `\y. (f:A->real)(chart_inv (U:A->bool,phi:A->real^2) y)`;
                   `\r. (phi:A->real^2)((gamma:real->A)(drop r))`; `(v:real->real^2) s`;
                   `lift s`] RFA_S2_CURVE_D1) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(s:real) IN J`)
                                                        (ASSUME `(gamma:real->A) s IN U`)))) THEN
      SIMP_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U,phi) y)))
              (at ((phi:A->real^2)((gamma:real->A) s))) ((v:real->real^2) s)))
     has_real_derivative
     lnabla 1 (metric_local atlas (U,phi) (g:A->real^2^2))
       (rfa_sh_df (\y. f(chart_inv (U,phi) y))) (phi(gamma t)) (\m. v t)) (atreal t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    MP_TAC(ISPECL [`IMAGE (phi:A->real^2) U`; `metric_local atlas (U,phi) (g:A->real^2^2)`;
                   `\y. (f:A->real)(chart_inv (U:A->bool,phi:A->real^2) y)`;
                   `\r. (phi:A->real^2)((gamma:real->A)(drop r))`;
                   `\r. (v:real->real^2)(drop r)`; `lift t`] RFA_S2_CURVE_HESS) THEN
    REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(t:real) IN J`)
                                                        (ASSUME `(gamma:real->A) t IN U`)))) THEN
      SIMP_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnabla 1 (metric_local atlas (U,phi) (g:A->real^2^2))
      (rfa_sh_df (\y. (f:A->real)(chart_inv (U,phi) y))) ((phi:A->real^2)((gamma:real->A) t))
      (\m. (v:real->real^2) t) =
    (inv(&2) - C / &2 * exp(f(gamma t))) *
    (mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t))`
  SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi:A->real^2) U`; `metric_local atlas (U,phi) (g:A->real^2^2)`;
                   `\y. (f:A->real)(chart_inv (U:A->bool,phi:A->real^2) y)`;
                   `(phi:A->real^2)((gamma:real->A) t)`; `\m:num. (v:real->real^2) t`]
                  RFA_S2_HESS_CONF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `(U:A->bool,phi:A->real^2)`; `(gamma:real->A) t`] RFA_SH_QR_CHART) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `gamma:real->A`; `J:real->bool`; `(U:A->bool,phi:A->real^2)`;
                   `(v:real->real^2) t`; `t:real`] GEOL_ENERGY_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FST; SND] THEN
      USE_THEN "vv" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `(t:real) IN J`)
                                                        (ASSUME `(gamma:real->A) t IN U`)))) THEN
      SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[lmetric2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_differentiable] THEN
    EXISTS_TAC `drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U,phi) y)))
                   (at ((phi:A->real^2)((gamma:real->A) t))) ((v:real->real^2) t))` THEN
    USE_THEN "d1" MATCH_MP_TAC THEN REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. drop(frechet_derivative (\y. lift((f:A->real)(chart_inv (U,phi) y)))
                    (at ((phi:A->real^2)((gamma:real->A) s))) ((v:real->real^2) s))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  USE_THEN "d1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_S2_RADIAL_ODE = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p v.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ v dot (g p ** v) = &1
     ==> !r. ((\r. f(mfd_geo (top,atlas) g p v r)) has_real_derivative
              real_derivative (\r. f(mfd_geo (top,atlas) g p v r)) r) (atreal r) /\
             (real_derivative (\r. f(mfd_geo (top,atlas) g p v r)) has_real_derivative
              (inv(&2) - C / &2 * exp(f(mfd_geo (top,atlas) g p v r)))) (atreal r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `v:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `v:real^2`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `r:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `mfd_geo (top,atlas) (g:A->real^2^2) p v`;
                 `(:real)`; `r:real`] RFA_S2_GEO_F2) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  SUBGOAL_THEN
   `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p v) r dot
    (g(mfd_geo (top,atlas) g p v r) ** mfd_vel atlas (mfd_geo (top,atlas) g p v) r) = &1`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `mfd_geo (top,atlas) (g:A->real^2^2) p v`; `(:real)`; `r:real`; `&0`]
                  MFD_GEODESIC_SPEED) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^2^2) p v r IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `mfd_geo (top,atlas) (g:A->real^2^2) p v`; `(:real)`; `r:real`]
                    GEOL_GEODESIC_IN_TOPSPACE) THEN
      ASM_REWRITE_TAC[IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `mfd_geo (top,atlas) (g:A->real^2^2) p v r`] GEOD_TNORM_BASIC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `v:real^2` (CONJUNCT1(CONJUNCT2(CONJUNCT2 th))))) THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
                         MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID; HAS_REAL_DERIVATIVE_DIFFERENTIABLE] THEN SIMP_TAC[]);;

let RFA_S2_RADIAL_MAX = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p v.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\ v dot (g p ** v) = &1
     ==> (!r. mfd_geo (top,atlas) g p v r IN topspace top) /\
         (!r. f(mfd_geo (top,atlas) g p v r) <= f p) /\
         f(mfd_geo (top,atlas) g p v (&0)) = f p /\
         real_derivative (\r. f(mfd_geo (top,atlas) g p v r)) (&0) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `v:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `v:real^2`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. mfd_geo (top,atlas) (g:A->real^2^2) p v r IN topspace top` ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `mfd_geo (top,atlas) (g:A->real^2^2) p v`; `(:real)`; `r:real`]
                  GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `v:real^2`] RFA_S2_RADIAL_ODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `&0`) THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_DERIVATIVE_ZERO_MAXMIN THEN
  MAP_EVERY EXISTS_TAC [`\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p v r)`;
                        `&0`; `(:real)`] THEN
  ASM_REWRITE_TAC[IN_UNIV; REAL_OPEN_UNIV] THEN DISJ1_TAC THEN ASM_SIMP_TAC[]);;

let RFA_S2_EXP_LIP = prove
 (`!a b m. a <= m /\ b <= m ==> abs(exp a - exp b) <= exp m * abs(a - b)`,
  SUBGOAL_THEN `!a b m. a <= b /\ b <= m ==> abs(exp a - exp b) <= exp m * abs(a - b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `exp a = exp b * exp(a - b)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `a - b:real` REAL_EXP_LE_X) THEN
    SUBGOAL_THEN `exp(a - b) <= &1` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp b <= exp m` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_EXP_MONO_LE]; ALL_TAC] THEN
    MP_TAC(SPEC `b:real` REAL_EXP_POS_LT) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs(exp b * exp(a - b) - exp b) = exp b * (&1 - exp(a - b))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y - x = --(x * (&1 - y))`; REAL_ABS_NEG] THEN
      REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp b * abs(a - b)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a:real <= b` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RFA_S2_RADIAL_UNIQ = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p v w.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\
     v dot (g p ** v) = &1 /\ w dot (g p ** w) = &1
     ==> !r. &0 <= r
             ==> f(mfd_geo (top,atlas) g p v r) = f(mfd_geo (top,atlas) g p w r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `v:real^2`] RFA_S2_RADIAL_ODE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `w:real^2`] RFA_S2_RADIAL_ODE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `v:real^2`] RFA_S2_RADIAL_MAX) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `w:real^2`] RFA_S2_RADIAL_MAX) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[FORALL_AND_THM])) THEN
  MP_TAC(ISPECL [`\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p v r)`;
                 `real_derivative (\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p v r))`;
                 `\r. inv(&2) - C / &2 * exp((f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p v r))`;
                 `\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p w r)`;
                 `real_derivative (\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p w r))`;
                 `\r. inv(&2) - C / &2 * exp((f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p w r))`;
                 `C / &2 * exp((f:A->real) p)`; `r + &1`] RFA_S2_ODE2_UNIQ) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `(i - c * x) - (i - c * y) = c * (y - x)`] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(C / &2) = C / &2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ABS_SUB] THEN MATCH_MP_TAC RFA_S2_EXP_LIP THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

let RFA_S2_ODE_FLAT = prove
 (`!(y:real->real) y' C m.
     &0 < C /\ C * exp m <= &1 / &2 /\
     (!r. (y has_real_derivative y' r) (atreal r)) /\
     (!r. (y' has_real_derivative (&1 / &2 - C * exp(y r))) (atreal r)) /\
     y(&0) = m /\ y'(&0) = &0 /\ (!r. y r <= m)
     ==> C * exp m = &1 / &2 /\ !r. y r = m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:real->real`; `y':real->real`; `C:real`; `m:real`] RFA_S2_ENERGY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!r. (y':real->real) r = &0` ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN
    ABBREV_TAC `s = (y:real->real) r - m` THEN
    SUBGOAL_THEN `(y:real->real) r = m + s` SUBST1_TAC THENL
     [EXPAND_TAC "s" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s <= &0` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN ASM_SIMP_TAC[REAL_ARITH `y <= m ==> y - m <= &0`]; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_ADD] THEN
    MP_TAC(SPEC `s:real` REAL_EXP_LE_X) THEN
    MP_TAC(SPEC `m:real` REAL_EXP_POS_LT) THEN
    SUBGOAL_THEN `&0 <= (--s) * (&1 - &2 * C * exp m)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= C * exp m * (exp s - (&1 + s))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN MP_TAC(SPEC `s:real` REAL_EXP_LE_X) THEN
      MP_TAC(SPEC `m:real` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `(y':real->real) r` REAL_LE_SQUARE) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(y':real->real) r * y' r = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ENTIRE] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. (y:real->real) r = m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real->real`; `(:real)`; `m:real`; `&0`] HAS_REAL_DERIVATIVE_ZERO_UNIQUE) THEN
    ASM_REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real` THEN
      MP_TAC(SPEC `x:real` (ASSUME `!r. ((y:real->real) has_real_derivative y' r) (atreal r)`)) THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        can (term_match [] `!r. (y':real->real) r = &0`) (concl th)));
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y':real->real) = \r. &0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\r:real. &0`; `&0`; `&0`; `&1 / &2 - C * exp m`]
                REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN ANTS_TAC THENL
   [UNDISCH_TAC `!r. ((y':real->real) has_real_derivative (&1 / &2 - C * exp((y:real->real) r)))
                     (atreal r)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let RFA_S2_UNIT_SCALE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p v.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ p IN topspace top /\
     ~(v = vec 0)
     ==> &0 < mfd_tnorm g p v /\
         (inv(mfd_tnorm g p v) % v) dot (g p ** (inv(mfd_tnorm g p v) % v)) = &1 /\
         v = mfd_tnorm g p v % (inv(mfd_tnorm g p v) % v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `v:real^N`] GEOD_TNORM_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < mfd_tnorm (g:A->real^N^N) p v` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
      can (term_match [] `!v. mfd_tnorm (g:A->real^N^N) p v pow 2 = v dot (g p ** v)`)
          (concl th))) THEN
    UNDISCH_TAC `&0 < mfd_tnorm (g:A->real^N^N) p v` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `mfd_tnorm (g:A->real^N^N) p v * inv(mfd_tnorm g p v) = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_MUL_LID]]]);;

let RFA_S2_POLAR = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) p x.
     hausdorff_space top /\ compact_space top /\ connected_space top /\
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p IN topspace top /\ x IN topspace top
     ==> ?u r. &0 <= r /\ u dot (g p ** u) = &1 /\ x = mfd_geo (top,atlas) g p u r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_complete (top,atlas) (g:A->real^N^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`]
                  MFD_HOPF_RINOW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_MESON_TAC[MFD_COMPACT_GEO_COMPLETE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`] MFD_COMPLETE_EXP_ONTO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:A` o REWRITE_RULE[EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` SUBST1_TAC) THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o last o CONJUNCTS) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `basis 1:real^N`] RFA_S2_UNIT_SCALE) THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`inv(mfd_tnorm (g:A->real^N^N) p (basis 1)) % basis 1:real^N`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `p:A`; `inv(mfd_tnorm (g:A->real^N^N) p (basis 1)) % basis 1:real^N`]
                  MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `w:real^N`] RFA_S2_UNIT_SCALE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`inv(mfd_tnorm (g:A->real^N^N) p w) % w`; `mfd_tnorm (g:A->real^N^N) p w`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o check (fun th ->
    can (term_match [] `w = mfd_tnorm (g:A->real^N^N) p w % (inv(mfd_tnorm g p w) % w)`)
        (concl th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `inv(mfd_tnorm (g:A->real^N^N) p w) % w`;
                 `mfd_tnorm (g:A->real^N^N) p w`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `inv(mfd_tnorm (g:A->real^N^N) p w) % w`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_SIMP_TAC[IN_UNIV]);;

let RFA_S2_FLAT_ROUND = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p.
     hausdorff_space top /\ compact_space top /\ connected_space top /\
     p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\
     C / &2 * exp(f p) <= &1 / &2
     ==> p2b_round (top,atlas) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> (f:A->real) x = f p` (LABEL_TAC "fc") THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `x:A`] RFA_S2_POLAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `f:A->real`; `C:real`; `p:A`; `u:real^2`] RFA_S2_RADIAL_ODE) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `f:A->real`; `C:real`; `p:A`; `u:real^2`] RFA_S2_RADIAL_MAX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[FORALL_AND_THM; REAL_ARITH `inv(&2) = &1 / &2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p u r)`;
                   `real_derivative (\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p u r))`;
                   `C / &2`; `(f:A->real) p`] RFA_S2_ODE_FLAT) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2b_round] THEN EXISTS_TAC `C / &2 * exp((f:A->real) p)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `x:A`; `u:real^2`; `v:real^2`] RFA_S2_MFD_SEC_SCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^2^2) x = C * exp((f:A->real) p)` SUBST1_TAC THENL
   [REMOVE_THEN "fc" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(x:A) IN topspace top`))]) THEN
    ASM_SIMP_TAC[];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Jacobi fields.  With a variable sectional curvature                       *)
(* k(t) along a geodesic, j E is a Jacobi field when E is a parallel normal  *)
(* and j'' = -k L^2 j (RFA_S2_JACOBI_SCALAR, after MFD_JACOBI_CONST1); the    *)
(* scalar function j = -F'/beta (RFA_S2_JFUN); in the steep case             *)
(* (C/2) e^f(p) > 1/2, d exp_p(r u)(r n) = j(r) E(r) for the parallel field  *)
(* E with E(0) = n (RFA_S2_DEXP_JACOBI, MFD_EXP_DIFFERENTIAL_JACOBI_RAY).     *)
(* ========================================================================= *)

let RFA_S2_JACOBI_SCALAR = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J (E:real->real^N) t0 (k:real->real)
    (j:real->real) j' L.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ t0 IN J /\
        mfd_parallel atlas g gamma J E /\
        E t0 dot (g(gamma t0) ** mfd_vel atlas gamma t0) = &0 /\
        mfd_tnorm g (gamma t0) (mfd_vel atlas gamma t0) = L /\
        (!t u v. t IN J /\ ~collinear {vec 0,u,v}
                 ==> mfd_sectional atlas g (gamma t) u v = k t) /\
        (!t. (j has_real_derivative j' t) (atreal t)) /\
        (!t. (j' has_real_derivative (--(k t * L pow 2) * j t)) (atreal t))
        ==> mfd_jacobi atlas g gamma J (\t. j t % E t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  MP_TAC(ASSUME `mfd_parallel (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                              (gamma:real->A) J (E:real->real^N)`) THEN
  REWRITE_TAC[mfd_parallel] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\t. j t % (E:real->real^N) t) t =
            j' t % E t`
  (LABEL_TAC "c1") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `E:real->real^N`; `j:real->real`; `(j':real->real) t`; `t:real`]
      CMPG_COVD_SCALAR) THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> mfd_covd atlas (g:A->real^N^N) (gamma:real->A) (\t. j' t % (E:real->real^N) t) t =
            (--(k t * L pow 2) * j t) % E t`
  (LABEL_TAC "c2") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `E:real->real^N`; `j':real->real`; `--((k:real->real) t * L pow 2) * j t`;
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
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXISTS_TAC `(j':real->real) t` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CMPG_FIELD_DIFF_LOCAL THEN
    EXISTS_TAC `\t. (j':real->real) t % (E:real->real^N) t` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      USE_THEN "c1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "fd" MATCH_MP_TAC THEN REWRITE_TAC[real_differentiable] THEN
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      EXISTS_TAC `--((k:real->real) t * L pow 2) * (j:real->real) t` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_covd atlas (g:A->real^N^N) (gamma:real->A)
      (mfd_covd atlas g gamma (\t. j t % (E:real->real^N) t)) t =
    mfd_covd atlas g gamma (\t. j' t % E t) t`
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
                 `g:A->real^N^N`; `(gamma:real->A) t`; `(k:real->real) t`]
    MFD_SECTIONAL_CONST_RIEMANN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "inner" (MP_TAC o C MATCH_MP (ASSUME `(t:real) IN J`)) THEN
  REWRITE_TAC[DOT_LMUL] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `--(a * b) * c + (a * b) * c = &0`; VECTOR_MUL_LZERO]);;

let RFA_S2_JFUN = prove
 (`!(y:real->real) y1 c beta.
     (!r. (y has_real_derivative y1 r) (atreal r)) /\
     (!r. (y1 has_real_derivative (inv(&2) - c * exp(y r))) (atreal r)) /\ ~(beta = &0)
     ==> (!r. ((\r. --(y1 r) / beta) has_real_derivative
               (--(inv(&2) - c * exp(y r)) / beta)) (atreal r)) /\
         (!r. ((\r. --(inv(&2) - c * exp(y r)) / beta) has_real_derivative
               (--((c * exp(y r)) * &1 pow 2) * (--(y1 r) / beta))) (atreal r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `r:real` THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\r. exp((y:real->real) r)) has_real_derivative y1 r * exp(y r)) (atreal r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SPEC `r:real` (CONJUNCT2 (MATCH_MP
      (ISPECL [`y:real->real`; `exp`] HAS_REAL_DERIVATIVE_CHAIN_UNIV) HAS_REAL_DERIVATIVE_EXP))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--((c * exp((y:real->real) r)) * &1 pow 2) * (--(y1 r) / beta) =
    --(&0 - c * (y1 r * exp(y r))) * inv beta`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_REWRITE_TAC[]);;

let RFA_S2_DEXP_JACOBI = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p u nn.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\
     &1 / &2 < C / &2 * exp(f p) /\
     u dot (g p ** u) = &1 /\ nn dot (g p ** nn) = &1 /\ nn dot (g p ** u) = &0
     ==> ?E. mfd_parallel atlas g (mfd_geo (top,atlas) g p u) (:real) E /\ E(&0) = nn /\
             (!r. E r dot (g(mfd_geo (top,atlas) g p u r) ** E r) = &1) /\
             (!r. mfd_differential (open_set_atlas (:real^2)) atlas (mfd_exp (top,atlas) g p)
                    (r % u) (r % nn) =
                  (--(real_derivative (\r. f(mfd_geo (top,atlas) g p u r)) r) /
                   (C / &2 * exp(f p) - &1 / &2)) % E r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `u:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `u:real^2`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`] RFA_S2_RADIAL_ODE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`] RFA_S2_RADIAL_MAX) THEN
  ASM_REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^2^2) p u` THEN
  ABBREV_TAC `beta = C / &2 * exp((f:A->real) p) - &1 / &2` THEN
  SUBGOAL_THEN `&0 < beta` ASSUME_TAC THENL [EXPAND_TAC "beta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `g:A->real^2^2`; `gam:real->A`; `(:real)`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `g:A->real^2^2`; `gam:real->A`; `(:real)`; `&0`; `nn:real^2`]
                MFD_PARALLEL_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[REAL_OPEN_UNIV; IS_REALINTERVAL_UNIV; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real->real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `E:real->real^2` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `g:A->real^2^2`; `gam:real->A`; `(:real)`; `E:real->real^2`;
                   `E:real->real^2`; `r:real`; `&0`] MFD_PARALLEL_INNER) THEN
    ASM_REWRITE_TAC[REAL_OPEN_UNIV; IS_REALINTERVAL_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r. (f:A->real)((gam:real->A) r)`;
                 `real_derivative (\r. (f:A->real)((gam:real->A) r))`;
                 `C / &2`; `beta:real`] RFA_S2_JFUN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN(STRIP_ASSUME_TAC o BETA_RULE)] THEN
  MP_TAC(ASSUME `mfd_parallel atlas (g:A->real^2^2) (gam:real->A) (:real) (E:real->real^2)`) THEN
  REWRITE_TAC[mfd_parallel; IN_UNIV] THEN STRIP_TAC THEN
  X_GEN_TAC `r:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `u:real^2`; `nn:real^2`;
                 `\t. (--(real_derivative (\r. (f:A->real)((gam:real->A) r)) t) / beta) %
                      (E:real->real^2) t`; `r:real`] MFD_EXP_DIFFERENTIAL_JACOBI_RAY) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `!t a b. ~collinear {vec 0,a,b}
                ==> mfd_sectional atlas (g:A->real^2^2) ((gam:real->A) t) a b =
                    C / &2 * exp((f:A->real)(gam t))`
      ASSUME_TAC THENL
       [MAP_EVERY X_GEN_TAC [`t:real`; `a:real^2`; `b:real^2`] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                       `(gam:real->A) t`; `a:real^2`; `b:real^2`] RFA_S2_MFD_SEC_SCAL) THEN
        ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC RFA_S2_JACOBI_SCALAR THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `&0`; `\t. C / &2 * exp((f:A->real)((gam:real->A) t))`;
        `\t. --(inv(&2) - C / &2 * exp((f:A->real)((gam:real->A) t))) / beta`; `&1`] THEN
      BETA_TAC THEN ASM_REWRITE_TAC[IN_UNIV; mfd_tnorm; SQRT_1];
      BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_NEG_0; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                     `g:A->real^2^2`; `gam:real->A`; `(:real)`; `E:real->real^2`;
                     `\t. --(real_derivative (\r. (f:A->real)((gam:real->A) r)) t) / beta`;
                     `--(inv(&2) - C / &2 * exp((f:A->real)((gam:real->A) (&0)))) / beta`;
                     `&0`] CMPG_COVD_SCALAR) THEN
      ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN BETA_TAC THEN
      ASM_REWRITE_TAC[REAL_NEG_0; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO;
                      VECTOR_ADD_RID] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `--(inv(&2) - (C * inv(&2)) * exp((f:A->real) p)) * inv beta = &1`
      SUBST1_TAC THENL
       [UNDISCH_TAC `C / &2 * exp ((f:A->real) p) - &1 / &2 = beta` THEN
        UNDISCH_TAC `&0 < beta` THEN CONV_TAC REAL_FIELD;
        REWRITE_TAC[VECTOR_MUL_LID]]];
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The antipodal point.  An orthonormal pair at a point                      *)
(* (RFA_S2_ONB2), the unit circle v(s) = cos s e1 + sin s e2 and its normal *)
(* (RFA_S2_CIRC_FRAME, RFA_S2_VD_SCALAR_VEC, RFA_S2_CIRC_VD), equality of   *)
(* the radial derivatives (RFA_S2_RADIAL_RD), the first zero A of F' in the  *)
(* steep case (RFA_S2_STEEP_A, from RFA_S2_FIRST_ZERO), and exp_p(A v(s))    *)
(* independent of s (RFA_S2_ANTIPODE: d exp kills the angular direction at   *)
(* A, so the chart curves have zero derivative; LOCALLY_CONSTANT_IMP_CONSTANT).*)
(* ========================================================================= *)

let RFA_S2_ONB2 = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> ?e1 e2. e1 dot (g x ** e1) = &1 /\ e2 dot (g x ** e2) = &1 /\
                 e1 dot (g x ** e2) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^2^2`) THEN
  MAP_EVERY EXISTS_TAC [`(E:real^2^2) ** basis 1`; `(E:real^2^2) ** basis 2`] THEN
  SUBGOAL_THEN `!a b. ((E:real^2^2) ** a) dot ((g:A->real^2^2) x ** (E ** b)) = a dot b`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_VECTOR_MUL_LID];
    SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_2; ARITH]]);;

let RFA_S2_CIRC_FRAME = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) p e1 e2 s.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ p IN topspace top /\
     e1 dot (g p ** e1) = &1 /\ e2 dot (g p ** e2) = &1 /\ e1 dot (g p ** e2) = &0
     ==> (cos s % e1 + sin s % e2) dot (g p ** (cos s % e1 + sin s % e2)) = &1 /\
         (--(sin s) % e1 + cos s % e2) dot (g p ** (--(sin s) % e1 + cos s % e2)) = &1 /\
         (--(sin s) % e1 + cos s % e2) dot (g p ** (cos s % e1 + sin s % e2)) = &0 /\
         (cos s % e1 + sin s % e2) dot (g p ** (--(sin s) % e1 + cos s % e2)) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`] GEOG_G_SYM_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e2:real^2) dot ((g:A->real^2^2) p ** e1) = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
              DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `s:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

let RFA_S2_VD_SCALAR_VEC = prove
 (`!(c:real->real) c' (e:real^N) s.
     (c has_real_derivative c') (atreal s)
     ==> ((\t. c(drop t) % e) has_vector_derivative (c' % e)) (at (lift s))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_VECTOR_DERIVATIVE_AT]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\(u:real^1) (v:real^N). drop u % v`; `lift o (c:real->real) o drop`;
                 `\t:real^1. (e:real^N)`; `lift(c':real)`; `vec 0:real^N`; `lift s`]
                HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN ANTS_TAC THENL
   [REWRITE_TAC[bilinear; linear; DROP_ADD; DROP_CMUL] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[o_THM; LIFT_DROP; VECTOR_MUL_RZERO; VECTOR_ADD_LID]]);;

let RFA_S2_CIRC_VD = prove
 (`!(a:real) (e1:real^N) e2 s.
     ((\t. a % (cos(drop t) % e1 + sin(drop t) % e2)) has_vector_derivative
      (a % (--(sin s) % e1 + cos s % e2))) (at (lift s))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC RFA_S2_VD_SCALAR_VEC THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_SIN; HAS_REAL_DERIVATIVE_COS]);;

let RFA_S2_RADIAL_RD = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p v w r.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\
     v dot (g p ** v) = &1 /\ w dot (g p ** w) = &1 /\ &0 < r
     ==> real_derivative (\r. f(mfd_geo (top,atlas) g p v r)) r =
         real_derivative (\r. f(mfd_geo (top,atlas) g p w r)) r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `w:real^2`] RFA_S2_RADIAL_ODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `r:real`) THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_DERIVATIVE THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p w r)`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `v:real^2`; `w:real^2`] RFA_S2_RADIAL_UNIQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let RFA_S2_STEEP_A = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p u.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\
     &1 / &2 < C / &2 * exp(f p) /\ u dot (g p ** u) = &1
     ==> ?A. &0 < A /\ real_derivative (\r. f(mfd_geo (top,atlas) g p u r)) A = &0 /\
             (!r. &0 < r /\ r < A ==> real_derivative (\r. f(mfd_geo (top,atlas) g p u r)) r < &0) /\
             &0 < &1 / &2 - C / &2 * exp(f(mfd_geo (top,atlas) g p u A)) /\
             &1 / &2 - C / &2 * exp(f(mfd_geo (top,atlas) g p u A)) <
             C / &2 * exp(f p) - &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`] RFA_S2_RADIAL_ODE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`] RFA_S2_RADIAL_MAX) THEN
  ASM_REWRITE_TAC[FORALL_AND_THM; REAL_ARITH `inv(&2) = &1 / &2`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p u r)`;
                 `real_derivative (\r. (f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p u r))`;
                 `C / &2`; `(f:A->real) p`] RFA_S2_FIRST_ZERO) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let RFA_S2_ANTIPODE = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p e1 e2 A.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\
     &1 / &2 < C / &2 * exp(f p) /\
     e1 dot (g p ** e1) = &1 /\ e2 dot (g p ** e2) = &1 /\ e1 dot (g p ** e2) = &0 /\
     &0 < A /\ real_derivative (\r. f(mfd_geo (top,atlas) g p e1 r)) A = &0
     ==> !s. mfd_exp (top,atlas) g p (A % (cos s % e1 + sin s % e2)) =
             mfd_exp (top,atlas) g p (A % e1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `e1:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. mfd_differential (open_set_atlas (:real^2)) (atlas:((A->bool)#(A->real^2))->bool)
          (mfd_exp (top,atlas) (g:A->real^2^2) (p:A))
          (A % (cos s % e1 + sin s % e2)) (A % (--(sin s) % e1 + cos s % (e2:real^2))) = vec 0`
  (LABEL_TAC "zd") THENL
   [X_GEN_TAC `s:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `e1:real^2`; `e2:real^2`; `s:real`] RFA_S2_CIRC_FRAME) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `f:A->real`; `C:real`; `p:A`; `cos s % e1 + sin s % e2:real^2`;
                   `--(sin s) % e1 + cos s % e2:real^2`] RFA_S2_DEXP_JACOBI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `E:real->real^2` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `f:A->real`; `C:real`; `p:A`; `cos s % e1 + sin s % e2:real^2`;
                   `e1:real^2`; `A:real`] RFA_S2_RADIAL_RD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REAL_NEG_0; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (euclidean,top)
      (\t:real^1. mfd_exp (top,atlas) (g:A->real^2^2) p
                    (A % (cos(drop t) % e1 + sin(drop t) % e2)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\t:real^1. mfd_exp (top,atlas) (g:A->real^2^2) p
                    (A % (cos(drop t) % e1 + sin(drop t) % e2))) =
      mfd_exp (top,atlas) g p o (\t. A % (cos(drop t) % e1 + sin(drop t) % e2))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `euclidean:(real^2)topology` THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2; SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    MP_TAC(ISPECL [`A:real`; `e1:real^2`; `e2:real^2`; `drop t`] RFA_S2_CIRC_VD) THEN
    REWRITE_TAC[LIFT_DROP] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. mfd_exp (top,atlas) (g:A->real^2^2) p
                               (A % (cos(drop t) % e1 + sin(drop t) % e2))`;
                 `(:real^1)`] LOCALLY_CONSTANT_IMP_CONSTANT) THEN
  REWRITE_TAC[CONNECTED_UNIV; IN_UNIV; SUBTOPOLOGY_UNIV; OPEN_IN_EUCLIDEAN] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t0:real^1` THEN
    ABBREV_TAC `y0 = mfd_exp (top,atlas) (g:A->real^2^2) p
                       (A % (cos(drop t0) % e1 + sin(drop t0) % e2))` THEN
    SUBGOAL_THEN `(y0:A) IN topspace top` ASSUME_TAC THENL
     [EXPAND_TAC "y0" THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map] o
        check (fun th -> can (term_match []
          `continuous_map (euclidean,top) (mfd_exp (top,atlas) (g:A->real^2^2) p)`) (concl th))) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `y0:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?U psi. chart_at atlas (y0:A) = (U:A->bool,psi:A->real^2)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `U:A->bool`; `psi:A->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `U:A->bool`; `psi:A->real^2`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\t:real^1. mfd_exp (top,atlas) (g:A->real^2^2) p
                                 (A % (cos(drop t) % e1 + sin(drop t) % e2))`;
                   `euclidean:(real^1)topology`; `top:A topology`; `U:A->bool`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; OPEN_IN_EUCLIDEAN] THEN
    DISCH_THEN(MP_TAC o SPEC `t0:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `ball(t0:real^1,d)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    SUBGOAL_THEN
     `!t. t IN ball(t0:real^1,d)
          ==> mfd_exp (top,atlas) (g:A->real^2^2) p
                (A % (cos(drop t) % e1 + sin(drop t) % e2)) IN U`
    (LABEL_TAC "inU") THENL
     [UNDISCH_TAC `ball(t0:real^1,d) SUBSET
                   {x | mfd_exp (top,atlas) (g:A->real^2^2) p
                          (A % (cos(drop x) % e1 + sin(drop x) % e2)) IN U}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\t:real^1. (psi:A->real^2)(mfd_exp (top,atlas) (g:A->real^2^2) p
                                 (A % (cos(drop t) % e1 + sin(drop t) % e2)))`;
                   `ball(t0:real^1,d)`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
     [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN `(\h:real^1. vec 0:real^2) = (\h. drop h % vec 0)` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
      REWRITE_TAC[GSYM has_vector_derivative] THEN
      USE_THEN "inU" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(t:real^1) IN ball(t0,d)`))) THEN
      MP_TAC(ISPECL [`\t:real^1. A % (cos(drop t) % e1 + sin(drop t) % (e2:real^2))`;
                     `\y:real^2. (psi:A->real^2)(mfd_exp (top,atlas) (g:A->real^2^2) p y)`;
                     `A % (--(sin(drop t)) % e1 + cos(drop t) % (e2:real^2))`;
                     `\h. chart_jac (chart_at atlas (mfd_exp (top,atlas) (g:A->real^2^2) p
                                      (A % (cos(drop t) % e1 + sin(drop t) % e2))))
                            (U:A->bool,psi:A->real^2)
                            (mfd_exp (top,atlas) g p (A % (cos(drop t) % e1 + sin(drop t) % e2)))
                            (mfd_differential (open_set_atlas (:real^2)) atlas
                               (mfd_exp (top,atlas) g p)
                               (A % (cos(drop t) % e1 + sin(drop t) % e2)) h)`;
                     `t:real^1`] ODE_HAS_VECTOR_DERIVATIVE_CHAIN) THEN
      BETA_TAC THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`A:real`; `e1:real^2`; `e2:real^2`; `drop t`] RFA_S2_CIRC_VD) THEN
          REWRITE_TAC[LIFT_DROP];
          MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                         `g:A->real^2^2`; `p:A`;
                         `A % (cos(drop t) % e1 + sin(drop t) % (e2:real^2))`;
                         `(U:A->bool,psi:A->real^2)`] CMPP_EXP_CHART_DERIV) THEN
          ASM_REWRITE_TAC[IN_UNIV; FST; SND]];
        ALL_TAC] THEN
      USE_THEN "zd" (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                     `(U:A->bool,psi:A->real^2)`;
                     `mfd_exp (top,atlas) (g:A->real^2^2) p
                        (A % (cos(drop t) % e1 + sin(drop t) % e2))`] CMPI_CHART_JAC_LINEAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[FST] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:real^2` (LABEL_TAC "cst")) THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "inU" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `(t:real^1) IN ball(t0,d)`))) THEN
    SUBGOAL_THEN `(t0:real^1) IN ball(t0,d)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    USE_THEN "cst" (fun th -> MP_TAC(BETA_RULE(MATCH_MP th (ASSUME `(t:real^1) IN ball(t0,d)`))) THEN
                              MP_TAC(BETA_RULE(MATCH_MP th (ASSUME `(t0:real^1) IN ball(t0,d)`)))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `chart_inv (U:A->bool,psi:A->real^2)
        (psi(mfd_exp (top,atlas) (g:A->real^2^2) p (A % (cos(drop t) % e1 + sin(drop t) % e2)))) =
      chart_inv (U,psi) (psi y0)`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:A` (LABEL_TAC "q")) THEN X_GEN_TAC `s:real` THEN
  USE_THEN "q" (fun th -> MP_TAC(BETA_RULE(SPEC `lift s` th)) THEN
                          MP_TAC(BETA_RULE(SPEC `lift(&0)` th))) THEN
  REWRITE_TAC[LIFT_DROP; COS_0; SIN_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID] THEN
  MESON_TAC[]);;

(* ========================================================================= *)
(* The circle lemma without continuity of the derivative                     *)
(* (RFA_S2_CIRCLE_D).  For a curve (x,y) on the unit circle with speed c,   *)
(* (x',y') = lam (-y,x) with lam = x y' - y x' = +/- c; by Darboux          *)
(* (REAL_DERIVATIVE_IVT_INCREASING/DECREASING, RFA_S2_DERIV_NOZERO_SIGN)     *)
(* lam is locally constant (RFA_S2_SAME_SIGN, RFA_S2_LAM_CONST), so x', y'   *)
(* are continuous and RFA_S2_CIRCLE applies.                                 *)
(* ========================================================================= *)

let RFA_S2_DERIV_NOZERO_SIGN = prove
 (`!(f:real->real) f' a b.
     a <= b /\ (!t. (f has_real_derivative f' t) (atreal t)) /\
     (!t. a <= t /\ t <= b ==> ~(f' t = &0))
     ==> &0 < f' a * f' b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((f':real->real) a = &0) /\ ~(f' b = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x. x IN real_interval[a,b] /\ (f':real->real) x = &0` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(f':real->real) a < &0` THENL
     [MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`]
                    REAL_DERIVATIVE_IVT_INCREASING) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_CASES_TAC `&0 <= (f':real->real) b` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(f':real->real) a * f' b <= &0` THEN
      MP_TAC(SPECL [`--((f':real->real) a)`; `--((f':real->real) b)`] REAL_LT_MUL) THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`]
                    REAL_DERIVATIVE_IVT_DECREASING) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      ASM_CASES_TAC `(f':real->real) b <= &0` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(f':real->real) a * f' b <= &0` THEN
      MP_TAC(SPECL [`(f':real->real) a`; `(f':real->real) b`] REAL_LT_MUL) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real) IN real_interval[a,b]` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  STRIP_TAC THEN ASM_MESON_TAC[]);;

let RFA_S2_SAME_SIGN = prove
 (`!a b. abs(a - b) < abs b ==> &0 < a * b`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < b` THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`--a:real`; `--b:real`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

let RFA_S2_LAM_CONST = prove
 (`!(f:real->real) f' (w:real->real) lam c t0.
     &0 < c /\ (!t. (f has_real_derivative f' t) (atreal t)) /\
     w real_continuous atreal t0 /\ ~(w t0 = &0) /\
     (!t. f' t = lam t * w t) /\ (!t. lam t pow 2 = c pow 2)
     ==> ?d. &0 < d /\ !t. abs(t - t0) < d ==> lam t = lam t0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `abs((w:real->real) t0)` o
    GEN_REWRITE_RULE I [real_continuous_atreal] o check (fun th ->
      can (term_match [] `(w:real->real) real_continuous atreal t0`) (concl th))) THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wc"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s. abs(s - t0) < d ==> &0 < (w:real->real) s * w t0` (LABEL_TAC "ws") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_S2_SAME_SIGN THEN
    USE_THEN "wc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. ~((lam:real->real) s = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `s:real` (ASSUME `!t. (lam:real->real) t pow 2 = c pow 2`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `(lam:real->real) s = &0`)) THEN
    MP_TAC(SPECL [`c:real`; `2`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (f':real->real) (min t t0) * f' (max t t0)` MP_TAC THENL
   [MATCH_MP_TAC RFA_S2_DERIV_NOZERO_SIGN THEN EXISTS_TAC `f:real->real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
    USE_THEN "ws" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(w:real->real) s = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f':real->real) (min t t0) * f' (max t t0) = ((lam:real->real) t * lam t0) * (w t * w t0)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t <= t0` THENL
     [ASM_SIMP_TAC[REAL_ARITH `t <= t0 ==> min t t0 = t /\ max t t0 = t0`] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH `~(t <= t0) ==> min t t0 = t0 /\ max t t0 = t`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "ws" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `abs(t - t0) < d`))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (lam:real->real) t * lam t0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`--((lam:real->real) t * lam t0)`; `(w:real->real) t * w t0`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((lam:real->real) t - lam t0) * (lam t + lam t0) = &0` MP_TAC THENL
   [MP_TAC(SPEC `t:real` (ASSUME `!t. (lam:real->real) t pow 2 = c pow 2`)) THEN
    MP_TAC(SPEC `t0:real` (ASSUME `!t. (lam:real->real) t pow 2 = c pow 2`)) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(lam:real->real) t = --(lam t0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < (lam:real->real) t * lam t0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `(lam:real->real) t0` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

let RFA_S2_CIRCLE_D = prove
 (`!(x:real->real) y x' y' c.
     &0 < c /\
     (!t. (x has_real_derivative x' t) (atreal t)) /\
     (!t. (y has_real_derivative y' t) (atreal t)) /\
     (!t. x t pow 2 + y t pow 2 = &1) /\
     (!t. x' t pow 2 + y' t pow 2 = c pow 2) /\
     x(&2 * pi) = x(&0) /\ y(&2 * pi) = y(&0) /\
     (!t. &0 < t /\ t < &2 * pi ==> ~(x t = x(&0) /\ y t = y(&0)))
     ==> c = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. (x:real->real) t * x' t + y t * y' t = &0` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN
    MP_TAC(ISPECL [`\t. (x:real->real) t * x t + y t * y t`; `t:real`;
                   `((x:real->real) t * x' t + x' t * x t) + (y t * y' t + y' t * y t)`; `&0`]
                  REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(\t. (x:real->real) t * x t + y t * y t) = (\t. &1)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:real` THEN
          MP_TAC(SPEC `s:real` (ASSUME `!t. (x:real->real) t pow 2 + y t pow 2 = &1`)) THEN
          REWRITE_TAC[REAL_POW_2];
          REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (x':real->real) t + ((x:real->real) t * y' t - y t * x' t) * y t = &0 /\
        y' t - (x t * y' t - y t * x' t) * x t = &0`
  (LABEL_TAC "k2") THENL
   [X_GEN_TAC `t:real` THEN
    MP_TAC(SPEC `t:real` (ASSUME `!t. (x:real->real) t pow 2 + y t pow 2 = &1`)) THEN
    MP_TAC(SPEC `t:real` (ASSUME `!t. (x:real->real) t * x' t + y t * y' t = &0`)) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ((x:real->real) t * y' t - y t * x' t) pow 2 = c pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN
    MP_TAC(SPEC `t:real` (ASSUME `!t. (x:real->real) t pow 2 + y t pow 2 = &1`)) THEN
    MP_TAC(SPEC `t:real` (ASSUME `!t. (x':real->real) t pow 2 + y' t pow 2 = c pow 2`)) THEN
    USE_THEN "k2" (MP_TAC o SPEC `t:real`) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t0. ?d. &0 < d /\
             !t. abs(t - t0) < d
                 ==> (x:real->real) t * y' t - y t * x' t = x t0 * y' t0 - y t0 * x' t0`
  (LABEL_TAC "lc") THENL
   [X_GEN_TAC `t0:real` THEN ASM_CASES_TAC `(y:real->real) t0 = &0` THENL
     [MP_TAC(ISPECL [`y:real->real`; `y':real->real`; `x:real->real`;
                     `\t. (x:real->real) t * y' t - y t * x' t`; `c:real`; `t0:real`]
                    RFA_S2_LAM_CONST) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL];
        DISCH_TAC THEN
        MP_TAC(SPEC `t0:real` (ASSUME `!t. (x:real->real) t pow 2 + y t pow 2 = &1`)) THEN
        REWRITE_TAC[ASSUME `(x:real->real) t0 = &0`; ASSUME `(y:real->real) t0 = &0`] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        X_GEN_TAC `t:real` THEN USE_THEN "k2" (MP_TAC o CONJUNCT2 o SPEC `t:real`) THEN
        REAL_ARITH_TAC];
      MP_TAC(ISPECL [`x:real->real`; `x':real->real`; `y:real->real`;
                     `\t. --((x:real->real) t * y' t - y t * x' t)`; `c:real`; `t0:real`]
                    RFA_S2_LAM_CONST) THEN
      BETA_TAC THEN REWRITE_TAC[REAL_EQ_NEG2] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL];
        X_GEN_TAC `t:real` THEN USE_THEN "k2" (MP_TAC o CONJUNCT1 o SPEC `t:real`) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_S2_CIRCLE THEN
  MAP_EVERY EXISTS_TAC [`x:real->real`; `y:real->real`; `x':real->real`; `y':real->real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `t0:real` THEN
  USE_THEN "lc" (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o SPEC `t0:real`) THEN
  MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_ATREAL THENL
   [EXISTS_TAC `\t. --((x:real->real) t0 * y' t0 - y t0 * x' t0) * y t`;
    EXISTS_TAC `\t. ((x:real->real) t0 * y' t0 - y t0 * x' t0) * x t`] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
     FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `abs(t - t0) < d`) o check (fun th ->
       is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th))) THEN
     USE_THEN "k2" (MP_TAC o SPEC `t:real`) THEN CONV_TAC REAL_RING;
     MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
     ASM_MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL]]));;

(* ========================================================================= *)
(* The arrival velocities at q.  The velocity of a radial                    *)
(* geodesic is d exp applied to its direction (RFA_S2_EXP_VEL); chart        *)
(* compositions with exp are smooth on open sets (RFA_S2_CHART_INV_ID,       *)
(* RFA_S2_EXPCHART_SMOOTH); field representations of d exp are derivatives   *)
(* of chart compositions (RFA_S2_FIELDREP_DEXP); a field vanishing at t has  *)
(* plain-derivative covariant derivative there (RFA_S2_COVD_AT_ZERO); the     *)
(* arrival map s |-> w(s) at q has derivative of g(q)-length alpha/beta      *)
(* (RFA_S2_VD_DROP_MUL, RFA_S2_ARRIVAL: GEOL_FRECHET_ALONG twice, symmetry of *)
(* second derivatives LRG_SECOND_DERIVATIVE_SYM, the Jacobi field j E).       *)
(* ========================================================================= *)

let RFA_S2_EXP_VEL = prove
 (`!top atlas (g:A->real^N^N) (x:A) v t.
     hausdorff_space top /\ compact_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top
     ==> mfd_vel atlas (mfd_geo (top,atlas) g x v) t =
         mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g x) (t % v) v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `v:real^N`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. mfd_geo (top,atlas) (g:A->real^N^N) x v r = mfd_exp (top,atlas) g x (r % v)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x:A`; `v:real^N`; `r:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_vel] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MP_TAC(ISPECL [`\s:real^1. drop s % (v:real^N)`;
                 `\y. SND(chart_at atlas (mfd_exp (top,atlas) (g:A->real^N^N) x (t % v)))
                         (mfd_exp (top,atlas) g x y)`;
                 `v:real^N`;
                 `mfd_differential (open_set_atlas (:real^N)) atlas
                    (mfd_exp (top,atlas) (g:A->real^N^N) x) (t % v)`;
                 `lift t`] ODE_HAS_VECTOR_DERIVATIVE_CHAIN) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\r:real. r`; `&1`; `v:real^N`; `t:real`] RFA_S2_VD_SCALAR_VEC) THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; VECTOR_MUL_LID];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `x:A`; `t % v:real^N`] CMPP_EXP_DIFF) THEN
      ASM_SIMP_TAC[IN_UNIV]];
    REWRITE_TAC[]]);;

let RFA_S2_CHART_INV_ID = prove
 (`chart_inv ((:real^N),(\x:real^N. x)) = (\y. y)`,
  REWRITE_TAC[FUN_EQ_THM; chart_inv; IN_UNIV] THEN MESON_TAC[]);;

let RFA_S2_EXPCHART_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (x:A) c.
     hausdorff_space top /\ compact_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\ c IN atlas
     ==> open {y | mfd_exp (top,atlas) g x y IN FST c} /\
         smooth_map_on {y | mfd_exp (top,atlas) g x y IN FST c}
                       (\y. SND c (mfd_exp (top,atlas) g x y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `vec 0:real^N`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?U phi. c = (U:A->bool,phi:A->real^N)` STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`mfd_exp (top,atlas) (g:A->real^N^N) x`; `euclidean:(real^N)topology`;
                   `top:A topology`; `U:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV; OPEN_IN_EUCLIDEAN];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`((:real^N),(\x:real^N. x))`; `(U:A->bool,phi:A->real^N)`] o
    GEN_REWRITE_RULE I [mfd_smooth_map] o check (fun th -> can (term_match []
      `mfd_smooth_map (open_set_atlas (:real^N)) (atlas:((A->bool)#(A->real^N))->bool) (:real^N)
                      (mfd_exp (top,atlas) (g:A->real^N^N) x)`) (concl th))) THEN
  ASM_REWRITE_TAC[open_set_atlas; IN_SING; FST; SND; INTER_UNIV; IN_UNIV; IMAGE_ID;
                  RFA_S2_CHART_INV_ID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM]);;

let RFA_S2_FIELDREP_DEXP = prove
 (`!top atlas (g:A->real^N^N) (x:A) y c h.
     hausdorff_space top /\ compact_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ x IN topspace top /\ c IN atlas /\
     mfd_exp (top,atlas) g x y IN FST c
     ==> chart_jac (chart_at atlas (mfd_exp (top,atlas) g x y)) c (mfd_exp (top,atlas) g x y)
           (mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g x) y h) =
         frechet_derivative (\y. SND c (mfd_exp (top,atlas) g x y)) (at y) h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `vec 0:real^N`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`; `y:real^N`; `c:(A->bool)#(A->real^N)`] CMPP_EXP_CHART_DERIV) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REWRITE_TAC[]);;

let RFA_S2_COVD_AT_ZERO = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) (Y:real->real^N) t.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     gamma t IN topspace top /\ Y t = vec 0
     ==> mfd_covd atlas g gamma Y t =
         vector_derivative
           (\s. mfd_field_rep atlas gamma Y (chart_at atlas (gamma t)) (drop s)) (at (lift t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_covd] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `(gamma:real->A) t`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)))
                        (FST(chart_at atlas (gamma t)))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                        ((gamma:real->A) t)) (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t))
                     (gamma t)`] CHRISTOFFEL_BILINEAR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP BILINEAR_RZERO th; VECTOR_ADD_RID])]);;

let RFA_S2_VD_DROP_MUL = prove
 (`!(v:real^N) a. ((\t. drop t % v) has_vector_derivative v) (at a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let RFA_S2_ARRIVAL = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p e1 e2 A s.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p) /\
     &1 / &2 < C / &2 * exp(f p) /\
     e1 dot (g p ** e1) = &1 /\ e2 dot (g p ** e2) = &1 /\ e1 dot (g p ** e2) = &0 /\
     &0 < A /\ real_derivative (\r. f(mfd_geo (top,atlas) g p e1 r)) A = &0 /\
     (!s. mfd_exp (top,atlas) g p (A % (cos s % e1 + sin s % e2)) =
          mfd_exp (top,atlas) g p (A % e1))
     ==> ?W. ((\t. mfd_vel atlas (mfd_geo (top,atlas) g p (cos(drop t) % e1 + sin(drop t) % e2)) A)
              has_vector_derivative W) (at (lift s)) /\
             W dot (g(mfd_exp (top,atlas) g p (A % e1)) ** W) =
             ((&1 / &2 - C / &2 * exp(f(mfd_geo (top,atlas) g p e1 A))) /
              (C / &2 * exp(f p) - &1 / &2)) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  ABBREV_TAC `q = mfd_exp (top,atlas) (g:A->real^2^2) p (A % e1)` THEN
  ABBREV_TAC `beta = C / &2 * exp((f:A->real) p) - &1 / &2` THEN
  SUBGOAL_THEN `&0 < beta` ASSUME_TAC THENL [EXPAND_TAC "beta" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `e1:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map] o
      check (fun th -> can (term_match []
        `continuous_map (euclidean,top) (mfd_exp (top,atlas) (g:A->real^2^2) p)`) (concl th))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `q:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U psi. chart_at atlas (q:A) = (U:A->bool,psi:A->real^2)`
  STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR_SURJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `(U:A->bool,psi:A->real^2)`] RFA_S2_EXPCHART_SMOOTH) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  ABBREV_TAC `h = \y. (psi:A->real^2)(mfd_exp (top,atlas) (g:A->real^2^2) p y)` THEN
  ABBREV_TAC `W0 = {y | mfd_exp (top,atlas) (g:A->real^2^2) p y IN U}` THEN
  SUBGOAL_THEN `!t. A % (cos t % e1 + sin t % e2) IN (W0:real^2->bool)` ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN EXPAND_TAC "W0" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  (* the arrival velocities in the chart at q *)
  SUBGOAL_THEN
   `!t. mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p (cos t % e1 + sin t % e2)) A =
        frechet_derivative (h:real^2->real^2) (at (A % (cos t % e1 + sin t % e2)))
                           (cos t % e1 + sin t % e2)`
  (LABEL_TAC "wv") THENL
   [X_GEN_TAC `t:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `cos t % e1 + sin t % e2:real^2`; `A:real`] RFA_S2_EXP_VEL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MFD_DIFFERENTIAL_OPEN_SET_ATLAS] THEN ASM_REWRITE_TAC[SND] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W0:real^2->bool`; `h:real^2->real^2`;
                 `\t:real^1. A % (cos(drop t) % e1 + sin(drop t) % (e2:real^2))`;
                 `\t:real^1. cos(drop t) % e1 + sin(drop t) % (e2:real^2)`;
                 `A % (--(sin s) % e1 + cos s % (e2:real^2))`;
                 `--(sin s) % e1 + cos s % (e2:real^2)`; `lift s`] GEOL_FRECHET_ALONG) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[RFA_S2_CIRC_VD] THEN
    MP_TAC(ISPECL [`&1`; `e1:real^2`; `e2:real^2`; `s:real`] RFA_S2_CIRC_VD) THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    DISCH_TAC] THEN
  EXISTS_TAC
   `frechet_derivative (\z. frechet_derivative (h:real^2->real^2) (at z) (cos s % e1 + sin s % e2))
      (at (A % (cos s % e1 + sin s % e2))) (A % (--(sin s) % e1 + cos s % (e2:real^2))) +
    frechet_derivative h (at (A % (cos s % e1 + sin s % e2))) (--(sin s) % e1 + cos s % e2)` THEN
  CONJ_TAC THENL
   [USE_THEN "wv" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u:real^2 = cos s % e1 + sin s % e2` THEN
  ABBREV_TAC `nn:real^2 = --(sin s) % e1 + cos s % e2` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `e1:real^2`; `e2:real^2`; `s:real`] RFA_S2_CIRC_FRAME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`; `nn:real^2`] RFA_S2_DEXP_JACOBI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `u:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `u:real^2`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. mfd_exp (top,atlas) (g:A->real^2^2) p (r % u) = mfd_geo (top,atlas) g p u r`
  (LABEL_TAC "rad") THENL
   [X_GEN_TAC `r:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `u:real^2`; `r:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `gam = mfd_geo (top,atlas) (g:A->real^2^2) p u` THEN
  SUBGOAL_THEN `(gam:real->A) A = q` ASSUME_TAC THENL
   [USE_THEN "rad" (fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBST1_TAC(SYM(ASSUME `cos s % e1 + sin s % e2 = (u:real^2)`)) THEN
    FIRST_ASSUM(ACCEPT_TAC o SPEC `s:real` o check (fun th -> can (term_match []
      `!s. mfd_exp (top,atlas) (g:A->real^2^2) p (A % (cos s % e1 + sin s % e2)) = q`)
      (concl th)));
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`] RFA_S2_RADIAL_ODE) THEN
  ASM_REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`; `e1:real^2`; `A:real`]
                RFA_S2_RADIAL_RD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `u:real^2`; `e1:real^2`] RFA_S2_RADIAL_UNIQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `A:real`) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r. (f:A->real)((gam:real->A) r)`;
                 `real_derivative (\r. (f:A->real)((gam:real->A) r))`;
                 `C / &2`; `beta:real`] RFA_S2_JFUN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `A:real` o CONJUNCT1) THEN BETA_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `jj = \r. --(real_derivative (\r. (f:A->real)((gam:real->A) r)) r) / beta` THEN
  SUBGOAL_THEN `(jj:real->real) A = &0` ASSUME_TAC THENL
   [EXPAND_TAC "jj" THEN ASM_REWRITE_TAC[REAL_NEG_0; real_div; REAL_MUL_LZERO]; ALL_TAC] THEN
  MP_TAC(ASSUME `mfd_parallel atlas (g:A->real^2^2) (gam:real->A) (:real) (E:real->real^2)`) THEN
  REWRITE_TAC[mfd_parallel; IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `g:A->real^2^2`; `gam:real->A`; `(:real)`] CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `g:A->real^2^2`; `gam:real->A`; `(:real)`; `E:real->real^2`;
                 `jj:real->real`;
                 `--(inv(&2) - C / &2 * exp((f:A->real)((gam:real->A) A))) / beta`; `A:real`]
                CMPG_COVD_SCALAR) THEN
  ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  DISCH_THEN(LABEL_TAC "cov") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `gam:real->A`; `\s. (jj:real->real) s % (E:real->real^2) s`; `A:real`]
                RFA_S2_COVD_AT_ZERO) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN DISCH_THEN(LABEL_TAC "cz") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `U:A->bool`; `psi:A->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gam:real->A`; `(:real)`; `U:A->bool`; `A:real`]
                GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_OPEN_UNIV; IN_UNIV] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `gam:real->A`; `(:real)`] GEOL_GEODESIC_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  SUBGOAL_THEN
   `!r. abs(r - A) < d
        ==> mfd_field_rep atlas (gam:real->A) (\s. (jj:real->real) s % (E:real->real^2) s)
              (U:A->bool,psi:A->real^2) r =
            frechet_derivative (h:real^2->real^2) (at (r % u)) (r % nn)`
  (LABEL_TAC "fr") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    USE_THEN "near" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `abs(r - A) < d`))) THEN
    REWRITE_TAC[mfd_field_rep] THEN BETA_TAC THEN
    SUBGOAL_THEN
     `(jj:real->real) r % (E:real->real^2) r =
      mfd_differential (open_set_atlas (:real^2)) atlas
        (mfd_exp (top,atlas) (g:A->real^2^2) p) (r % u) (r % nn)`
    SUBST1_TAC THENL
     [EXPAND_TAC "jj" THEN BETA_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `r % u:real^2`; `(U:A->bool,psi:A->real^2)`; `r % nn:real^2`]
                  RFA_S2_FIELDREP_DEXP) THEN
    ASM_REWRITE_TAC[FST; SND] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `A % (u:real^2) IN W0` ASSUME_TAC THENL
   [MP_TAC(SPEC `s:real` (ASSUME `!t. A % (cos t % e1 + sin t % e2) IN (W0:real^2->bool)`)) THEN
    REWRITE_TAC[ASSUME `cos s % e1 + sin s % e2 = (u:real^2)`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W0:real^2->bool`; `h:real^2->real^2`; `\t:real^1. drop t % (u:real^2)`;
                 `\t:real^1. drop t % (nn:real^2)`; `u:real^2`; `nn:real^2`; `lift A`]
                GEOL_FRECHET_ALONG) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[RFA_S2_VD_DROP_MUL];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\s. mfd_field_rep atlas (gam:real->A) (\s. (jj:real->real) s % (E:real->real^2) s)
             (U:A->bool,psi:A->real^2) (drop s)) (at (lift A)) =
    frechet_derivative (\z. frechet_derivative (h:real^2->real^2) (at z) (A % nn))
      (at (A % u)) u + frechet_derivative h (at (A % u)) nn`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\r:real^1. frechet_derivative (h:real^2->real^2) (at (drop r % u)) (drop r % nn)` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "fr" MATCH_MP_TAC THEN
    UNDISCH_TAC `dist(t:real^1,lift A) < d` THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W0:real^2->bool`; `h:real^2->real^2`; `A % (u:real^2)`; `A % (nn:real^2)`;
                 `u:real^2`] LRG_SECOND_DERIVATIVE_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    can (term_match [] `vector_derivative (X:real^1->real^2) (at (lift A)) = Y`) (concl th))) THEN
  USE_THEN "cz" (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  MP_TAC(SPEC `A:real` (ASSUME `!r. (E:real->real^2) r dot
                                   ((g:A->real^2^2)((gam:real->A) r) ** E r) = &1`)) THEN
  REWRITE_TAC[ASSUME `(gam:real->A) A = q`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ARITH `inv(&2) = &1 / &2`] THEN
  UNDISCH_TAC `&0 < beta` THEN CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* The steep case is impossible.  The metric                                 *)
(* at a point is invertible (RFA_S2_G_INVERTIBLE); coordinates in a 2-d     *)
(* orthonormal frame (RFA_S2_EXPAND2); unit speed of radial geodesics        *)
(* (RFA_S2_UNIT_SPEED); derivative of a coordinate of a vector curve         *)
(* (RFA_S2_VD_DOT); geodesics from p with the same position and velocity at  *)
(* A have the same initial direction (RFA_S2_VEL_INJ); if (C/2) e^f(p) > 1/2 *)
(* then the arrival map at q is a unit circle map of constant speed          *)
(* alpha/beta, injective on [0,2 pi), so alpha = beta by RFA_S2_CIRCLE_D,    *)
(* against alpha < beta (RFA_S2_NOT_STEEP).                                   *)
(* ========================================================================= *)

let RFA_S2_G_INVERTIBLE = prove
 (`!top atlas (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> invertible(g x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `x:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                        (FST(chart_at atlas x))`;
                 `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A))
                               (g:A->real^N^N)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]
                LRG_METRIC_INVERTIBLE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;

let RFA_S2_EXPAND2 = prove
 (`!(G0:real^2^2) d1 d2 z.
     invertible G0 /\ (!a b. a dot (G0 ** b) = b dot (G0 ** a)) /\
     d1 dot (G0 ** d1) = &1 /\ d2 dot (G0 ** d2) = &1 /\ d1 dot (G0 ** d2) = &0
     ==> z = (z dot (G0 ** d1)) % d1 + (z dot (G0 ** d2)) % d2 /\
         z dot (G0 ** z) = (z dot (G0 ** d1)) pow 2 + (z dot (G0 ** d2)) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G0:real^2^2`; `d1:real^2`; `d2:real^2`] RFA_S2_ORTHO2_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`G0:real^2^2`; `S:real^2^2`; `z:real^2`] RFA_FRAME_VEXPAND) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; VSUM_2] THEN
  SUBGOAL_THEN `(d1:real^2) dot (G0 ** z) = z dot (G0 ** d1) /\
                (d2:real^2) dot (G0 ** z) = z dot (G0 ** d2)`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RADD; DOT_RMUL] THEN
  REWRITE_TAC[REAL_POW_2]);;

let RFA_S2_UNIT_SPEED = prove
 (`!top atlas (g:A->real^N^N) p u.
     hausdorff_space top /\ compact_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ p IN topspace top /\ u dot (g p ** u) = &1
     ==> !r. mfd_vel atlas (mfd_geo (top,atlas) g p u) r dot
             (g(mfd_geo (top,atlas) g p u r) ** mfd_vel atlas (mfd_geo (top,atlas) g p u) r) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:real` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`; `r:real`; `&0`]
                MFD_GEODESIC_SPEED) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p u r IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) p u`; `(:real)`; `r:real`]
                  GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_geo (top,atlas) (g:A->real^N^N) p u r`] GEOD_TNORM_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`] GEOD_TNORM_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^N` (CONJUNCT1(CONJUNCT2(CONJUNCT2 th))))) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
                       MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[]);;

let RFA_S2_VD_DOT = prove
 (`!(f:real^1->real^N) f' c s.
     (f has_vector_derivative f') (at (lift s))
     ==> ((\t. f(lift t) dot c) has_real_derivative (f' dot c)) (atreal s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  SUBGOAL_THEN `(lift o (\t. (f:real^1->real^N)(lift t) dot c) o drop) = (\x. lift(c dot f x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^1. drop x % lift((f':real^N) dot c)) = (\t. lift(c dot (drop t % f')))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DOT_RMUL; LIFT_CMUL] THEN REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LIFT_DOT THEN ASM_REWRITE_TAC[GSYM has_vector_derivative]);;

let RFA_S2_VEL_INJ = prove
 (`!top atlas (g:A->real^N^N) p u u' A.
     hausdorff_space top /\ compact_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas g /\ p IN topspace top /\
     mfd_geo (top,atlas) g p u A = mfd_geo (top,atlas) g p u' A /\
     mfd_vel atlas (mfd_geo (top,atlas) g p u) A = mfd_vel atlas (mfd_geo (top,atlas) g p u') A
     ==> u = u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`] MFD_COMPACT_GEO_COMPLETE) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u':real^N`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`; `A:real`] MFD_GEO_SHIFT) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u':real^N`; `A:real`] MFD_GEO_SHIFT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) p u = mfd_geo (top,atlas) g p u'`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:real` THEN
    SUBGOAL_THEN `r = A + (r - A)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u:real^N`] MFD_GEO_MAXIMAL) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `p:A`; `u':real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let RFA_S2_NOT_STEEP = prove
 (`!top (atlas:((A->bool)#(A->real^2))->bool) (g:A->real^2^2) (f:A->real) C p.
     hausdorff_space top /\ compact_space top /\ p2b_shrinker (top,atlas) g f /\ &0 < C /\
     (!x. x IN topspace top ==> mfd_scalar atlas g x = C * exp(f x)) /\
     p IN topspace top /\ (!x. x IN topspace top ==> f x <= f p)
     ==> ~(&1 / &2 < C / &2 * exp(f p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2b_shrinker]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`] RFA_S2_ONB2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^2` (X_CHOOSE_THEN `e2:real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `e1:real^2`] RFA_S2_STEEP_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `f:A->real`; `C:real`; `p:A`; `e1:real^2`; `e2:real^2`; `A:real`]
                RFA_S2_ANTIPODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(GEN `s:real` (ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `g:A->real^2^2`; `f:A->real`; `C:real`; `p:A`; `e1:real^2`; `e2:real^2`;
                 `A:real`; `s:real`] RFA_S2_ARRIVAL)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `W':real->real^2` (LABEL_TAC "ar")) THEN
  ABBREV_TAC `q = mfd_exp (top,atlas) (g:A->real^2^2) p (A % e1)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `p:A`; `e1:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s. mfd_geo (top,atlas) (g:A->real^2^2) p (cos s % e1 + sin s % e2) A = q`
  (LABEL_TAC "atq") THENL
   [X_GEN_TAC `s:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `cos s % e1 + sin s % e2:real^2`] MFD_COMPACT_GEO_COMPLETE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `cos s % e1 + sin s % e2:real^2`; `A:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `e1:real^2`] MFD_GEO_MAXIMAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `e1:real^2`; `A:real`] MFD_EXP_RADIAL) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `mfd_geo (top,atlas) (g:A->real^2^2) p e1`; `(:real)`; `A:real`]
                  GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                 `q:A`] RFA_S2_ONB2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^2` (X_CHOOSE_THEN `d2:real^2` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `invertible((g:A->real^2^2) q) /\ (!a b. a dot (g q ** b) = b dot (g q ** a))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RFA_S2_G_INVERTIBLE THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`] THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `q:A`] GEOG_G_SYM_POS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p (cos s % e1 + sin s % e2)) A dot
        (g q ** mfd_vel atlas (mfd_geo (top,atlas) g p (cos s % e1 + sin s % e2)) A) = &1`
  (LABEL_TAC "unit") THENL
   [X_GEN_TAC `s:real` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `e1:real^2`; `e2:real^2`; `s:real`] RFA_S2_CIRC_FRAME) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `cos s % e1 + sin s % e2:real^2`] RFA_S2_UNIT_SPEED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `A:real`) THEN
    USE_THEN "atq" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `cos(&2 * pi) = &1 /\ sin(&2 * pi) = &0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&0` COS_PERIODIC) THEN MP_TAC(SPEC `&0` SIN_PERIODIC) THEN
    REWRITE_TAC[REAL_ADD_LID; COS_0; SIN_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p (cos t % e1 + sin t % e2)) A dot
         (g q ** (d1:real^2))`;
    `\t. mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p (cos t % e1 + sin t % e2)) A dot
         (g q ** (d2:real^2))`;
    `\t. (W':real->real^2) t dot ((g:A->real^2^2) q ** (d1:real^2))`;
    `\t. (W':real->real^2) t dot ((g:A->real^2^2) q ** (d2:real^2))`;
    `(&1 / &2 - C / &2 * exp((f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p e1 A))) /
     (C / &2 * exp(f p) - &1 / &2)`] RFA_S2_CIRCLE_D) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN
      MP_TAC(ISPECL [`\t:real^1. mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p
                                   (cos(drop t) % e1 + sin(drop t) % e2)) A`;
                     `(W':real->real^2) t`; `(g:A->real^2^2) q ** (d1:real^2)`; `t:real`]
                    RFA_S2_VD_DOT) THEN
      BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "ar" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `t:real` th)]);
      X_GEN_TAC `t:real` THEN
      MP_TAC(ISPECL [`\t:real^1. mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p
                                   (cos(drop t) % e1 + sin(drop t) % e2)) A`;
                     `(W':real->real^2) t`; `(g:A->real^2^2) q ** (d2:real^2)`; `t:real`]
                    RFA_S2_VD_DOT) THEN
      BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "ar" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `t:real` th)]);
      X_GEN_TAC `t:real` THEN
      MP_TAC(ISPECL [`(g:A->real^2^2) q`; `d1:real^2`; `d2:real^2`;
                     `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p
                        (cos t % e1 + sin t % e2)) A`] RFA_S2_EXPAND2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      USE_THEN "unit" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN
      MP_TAC(ISPECL [`(g:A->real^2^2) q`; `d1:real^2`; `d2:real^2`; `(W':real->real^2) t`]
                    RFA_S2_EXPAND2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      USE_THEN "ar" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `t:real` th)]) THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[COS_0; SIN_0];
      ASM_REWRITE_TAC[COS_0; SIN_0];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    REWRITE_TAC[COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^2^2) p e1 A = q` ASSUME_TAC THENL
     [USE_THEN "atq" (MP_TAC o SPEC `&0`) THEN
      REWRITE_TAC[COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(g:A->real^2^2) q`; `d1:real^2`; `d2:real^2`;
                   `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p
                      (cos t % e1 + sin t % e2)) A`] RFA_S2_EXPAND2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`(g:A->real^2^2) q`; `d1:real^2`; `d2:real^2`;
                   `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^2^2) p e1) A`] RFA_S2_EXPAND2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                   `p:A`; `cos t % e1 + sin t % e2:real^2`; `e1:real^2`; `A:real`]
                  RFA_S2_VEL_INJ) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "atq" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    SUBGOAL_THEN `cos t = &1` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^2. z dot ((g:A->real^2^2) p ** e1)` o check
        (fun th -> concl th = `cos t % e1 + sin t % e2 = (e1:real^2)`)) THEN
      REWRITE_TAC[DOT_LADD; DOT_LMUL] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `g:A->real^2^2`;
                     `p:A`] GEOG_G_SYM_POS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(e2:real^2) dot ((g:A->real^2^2) p ** e1) = &0` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COS_EQ_1] THEN DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * pi) * &0 < (&2 * pi) * n /\ (&2 * pi) * n < (&2 * pi) * &1` MP_TAC THENL
     [UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `t < &2 * pi` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN STRIP_TAC] THEN
    MP_TAC(SPECL [`&0`; `n:real`] REAL_LT_INTEGERS) THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&1 / &2 - C / &2 * exp((f:A->real)(mfd_geo (top,atlas) (g:A->real^2^2) p e1 A)) <
               C / &2 * exp(f p) - &1 / &2` THEN
  UNDISCH_TAC `&1 / &2 < C / &2 * exp((f:A->real) p)` THEN CONV_TAC REAL_FIELD);;

