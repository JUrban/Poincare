(* ========================================================================= *)
(* Unit pc_cmp_dens (comparison-geometry layer CMP): the volume density of   *)
(* the exp pullback metric along rays, sqrt(det G(s u)) = det A(s) / s^n for *)
(* the Jacobi matrix A of the ray, Bishop's monotonicity of det A(t) / (t    *)
(* sn_{-K}(t)^(n-1)) under Ric >= -(n-1)K and the bound by the model         *)
(* density, and the volume of images under exp_x o E by the area formula     *)
(* (GRGA_AREA_FORMULA) with integrand sqrt(det G).                           *)
(* ========================================================================= *)

needs "src/pc_cmp_hess.ml";;
needs "src/pc_cmp_rad.ml";;
needs "src/pc_grg_area.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Ray data (Jacobi matrices along the ray of w) with the Ricci lower bound  *)
(* assumed only on the ball mfd_ball x rho.                                  *)
(* ========================================================================= *)

let CMPD_RAY_DATA_RIC_BALL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < rho /\
        mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y v. y IN mfd_ball (top,atlas) g x rho
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        &0 < norm w
        ==> ?P A B R.
              orthogonal_matrix P /\ P ** basis 1 = inv(norm w) % w /\
              cmp_jsys A B R rho /\
              (!t. &0 <= t /\ t < rho
                   ==> --(&(dimindex(:N) - 1) * K) <= trace(R t)) /\
              (!s a. &0 < s /\ s < rho
                     ==> a dot (cmp_expmetric (top,atlas) g x E (s % inv(norm w) % w) ** a) =
                         ((A s ** (transp P ** a)) dot (A s ** (transp P ** a))) / s pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u:real^N = inv(norm w) % w` THEN
  SUBGOAL_THEN `norm(u:real^N) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `?P:real^N^N. orthogonal_matrix P /\ P ** basis 1 = u` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`basis 1:real^N`; `u:real^N`] ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
    ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(f:real^N->real^N)` THEN
    FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ORTHOGONAL_TRANSFORMATION]) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX];
    ALL_TAC] THEN
  EXISTS_TAC `P:real^N^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** u`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `P:real^N^N`; `u:real^N`]
    CMPP_FRAME_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fr:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                 `Fr:num->real->real^N`] CMPP_JACOBI_ALONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->real->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `u:real^N`; `rho:real`]
    CMPP_RADIAL) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(LABEL_TAC "rad") THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                ((Y:num->real->real^N) j))` THEN
  EXISTS_TAC `cmp_fmat (\j. cmp_fcoord (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)
                (mfd_covd atlas g (mfd_geo (top,atlas) g x (E ** u))
                   ((Y:num->real->real^N) j)))` THEN
  EXISTS_TAC `cmp_rmat atlas (g:A->real^N^N)
                (mfd_geo (top,atlas) g x ((E:real^N^N) ** u)) (Fr:num->real->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_FRAME_JSYS THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`;
      `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u) t IN topspace top`
    ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u) t IN
                  mfd_ball (top,atlas) g x rho`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CMPP_RAY_IN_BALL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`;
                   `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                   `Fr:num->real->real^N`; `t:real`] CMPJ_FRAME_RICCI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `--k * &1 <= r ==> --k <= r`) THEN
    SUBGOAL_THEN
     `mfd_vel atlas (mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)) t dot
      (g(mfd_geo (top,atlas) g x (E ** u) t) **
       mfd_vel atlas (mfd_geo (top,atlas) g x (E ** u)) t) = &1`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`;
                     `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u) t`]
        GEOD_TNORM_BASIC) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `mfd_vel (atlas:((A->bool)#(A->real^N))->bool)
                   (mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)) t` o
                 CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`;
                     `mfd_geo (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                     `mfd_geo_maxint (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** u)`;
                     `t:real`; `&0`] MFD_GEODESIC_SPEED) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real`; `a:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPP_RAY_IDENTITY THEN EXISTS_TAC `rho:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_EXP_DIFFERENTIAL_JACOBI_RAY THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
    USE_THEN "rad" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The density along a ray.  If the quadratic form of a symmetric G is |A    *)
(* P^T a|^2 / s^2 with P orthogonal, then sqrt(det G) = |det A| / s^n.       *)
(* ========================================================================= *)

let CMPD_RAY_DET = prove
 (`!(G:real^N^N) (P:real^N^N) (A:real^N^N) s.
        transp G = G /\ orthogonal_matrix P /\ &0 < s /\
        (!a. a dot (G ** a) =
             ((A ** (transp P ** a)) dot (A ** (transp P ** a))) / s pow 2)
        ==> sqrt(det G) = abs(det A) / s pow dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `G = inv(s pow 2) %% (transp((A:real^N^N) ** transp(P:real^N^N)) ** (A ** transp P))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CMPH_SYM_QUAD_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_TRANSP_MUL; TRANSP_TRANSP];
      GEN_TAC THEN
      REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; GSYM MATRIX_VECTOR_MUL_ASSOC;
                  DOT_MATRIX_TRANSP_RMUL] THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(inv(s pow 2) %% (transp((A:real^N^N) ** transp(P:real^N^N)) ** (A ** transp P))) =
    (det A / s pow dimindex(:N)) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[DET_CMUL; DET_MUL; DET_TRANSP] THEN
    SUBGOAL_THEN `inv(s pow 2) pow dimindex(:N) = inv(s pow dimindex(:N)) pow 2`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_INV; REAL_POW_POW] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP DET_ORTHOGONAL_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[POW_2_SQRT_ABS; REAL_ABS_DIV; REAL_ABS_POW] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`]);;

(* ========================================================================= *)
(* Bishop's monotonicity.  Under the trace bound for R and invertibility of  *)
(* A on (0,L), det A(t) / (t sn_{-K}(t)^(n-1)) is non-increasing on (0,L)    *)
(* (Jacobi's formula for det A and the trace comparison CMPJ_TRACE_UPPER).   *)
(* ========================================================================= *)

let CMPD_BISHOP_ALG = prove
 (`!tr u sn cs m.
        &0 < u /\ &0 < sn /\ (tr - inv u) * sn <= &m * cs
        ==> tr * (u * sn pow m) <= sn pow m + u * (&m * sn pow (m - 1) * cs)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `tr * u * sn - sn <= u * (&m * cs)` ASSUME_TAC THENL
   [SUBGOAL_THEN `tr * u * sn - sn = u * ((tr - inv u) * sn)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < u` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    UNDISCH_TAC `tr * u * sn - sn <= u * (&m * cs)` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `sn:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `m:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[real_pow; ARITH_RULE `SUC k - 1 = k`] THEN
  SUBGOAL_THEN `&0 <= sn pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sn pow k * (tr * u * sn - sn) <= sn pow k * (u * (&(SUC k) * cs))`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CMPD_BISHOP_MONO = prove
 (`!(A:real->real^N^N) B R L K s t.
        cmp_jsys A B R L /\
        (!t. &0 <= t /\ t < L ==> --(&(dimindex(:N) - 1) * K) <= trace(R t)) /\
        (!t. &0 < t /\ t < L ==> invertible(A t)) /\
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn (--K) t) /\
        &0 < s /\ s <= t /\ t < L
        ==> det(A t) * (s * cmp_sn (--K) s pow (dimindex(:N) - 1)) <=
            det(A s) * (t * cmp_sn (--K) t pow (dimindex(:N) - 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`; `K:real`] CMPJ_TRACE_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "tr") THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `R:real->real^N^N`;
                 `L:real`] CMPJ_DET_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "pos") THEN
  MP_TAC(ISPECL
   [`\u. det((A:real->real^N^N) u)`;
    `\u. det((A:real->real^N^N) u) * trace(matrix_inv(A u) ** (B:real->real^N^N) u)`;
    `\u. u * cmp_sn (--K) u pow (dimindex(:N) - 1)`;
    `\u. cmp_sn (--K) u pow (dimindex(:N) - 1) +
         u * (&(dimindex(:N) - 1) * cmp_sn (--K) u pow (dimindex(:N) - 1 - 1) *
              cmp_cs (--K) u)`;
    `L:real`; `s:real`; `t:real`] CMPO_RATIO_DECREASING) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CMPJ_DET_HAS_DERIV THEN EXISTS_TAC `R:real->real^N^N` THEN
    EXISTS_TAC `L:real` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM INVERTIBLE_DET_NZ];
    MP_TAC(ISPECL [`\u:real. u`; `&1`; `\u. cmp_sn (--K) u pow (dimindex(:N) - 1)`;
                   `&(dimindex(:N) - 1) * cmp_sn (--K) u pow (dimindex(:N) - 1 - 1) *
                    cmp_cs (--K) u`; `u:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`cmp_sn (--K)`; `cmp_cs (--K) u`; `u:real`; `dimindex(:N) - 1`]
        HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
      REWRITE_TAC[CMP_SN_HAS_DERIV];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CMPD_BISHOP_ALG THEN ASM_SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[TRACE_MUL_SYM] THEN USE_THEN "tr" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Volumes of images under F = exp_x o E.  The chart representation of F at  *)
(* w has derivative cmp_dexp w, the integrand of the area formula is         *)
(* sqrt(det G(w)) for the exp pullback metric G, and the area formula gives  *)
(* the volume of F(S) (equality when F is injective on S).                   *)
(* ========================================================================= *)

let CMPD_EXP_FRAME_DERIV = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        E ** w IN mfd_exp_dom (top,atlas) g x
        ==> ((\v. SND(chart_at atlas (mfd_exp (top,atlas) g x (E ** w)))
                     (mfd_exp (top,atlas) g x (E ** v))) has_derivative
             (\h. cmp_dexp (top,atlas) g x E w ** h)) (at w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`] CMPP_EXP_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\v. SND(chart_at atlas (mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)))
           (mfd_exp (top,atlas) g x (E ** v))) =
    (\y. SND(chart_at atlas (mfd_exp (top,atlas) g x (E ** w)))
           (mfd_exp (top,atlas) g x y)) o (\v. E ** v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) w ** h) =
    mfd_differential (open_set_atlas (:real^N)) atlas
      (mfd_exp (top,atlas) g x) (E ** w) o (\h. E ** h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[CMPP_DEXP_APPLY]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let CMPD_AREA_INTEGRAND = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        E ** w IN mfd_exp_dom (top,atlas) g x
        ==> abs(det(matrix(\h. cmp_dexp (top,atlas) g x E w ** h))) *
            mfd_density atlas (chart_at atlas (mfd_exp (top,atlas) g x (E ** w))) g
              (SND(chart_at atlas (mfd_exp (top,atlas) g x (E ** w)))
                  (mfd_exp (top,atlas) g x (E ** w))) =
            sqrt(det(cmp_expmetric (top,atlas) g x E w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w) IN topspace top`
  ASSUME_TAC THENL [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; mfd_density] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`]
    METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[cmp_expmetric; DET_MUL; DET_TRANSP] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`]
    GRGV_SQRT_DET_POS) THEN
  ASM_REWRITE_TAC[SQRT_POS_LT] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `a * b * a = a pow 2 * b`] THEN
  ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE; POW_2_SQRT_ABS]);;

let CMPD_IMAGE_VOLUME = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) S.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        lebesgue_measurable S /\
        (!w. w IN S ==> E ** w IN mfd_exp_dom (top,atlas) g x) /\
        (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w)))) integrable_on S
        ==> ?v. mfd_has_volume (top,atlas) g
                  (IMAGE (\w. mfd_exp (top,atlas) g x (E ** w)) S) v /\
                v <= drop(integral S (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))) /\
                ((!w w'. w IN S /\ w' IN S /\
                         mfd_exp (top,atlas) g x (E ** w) = mfd_exp (top,atlas) g x (E ** w')
                         ==> w = w')
                 ==> v = drop(integral S
                           (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!Z. Z IN S
        ==> lift(abs(det(matrix(\h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N)
                                  Z ** h))) *
                 mfd_density atlas (chart_at atlas (mfd_exp (top,atlas) g x (E ** Z))) g
                   (SND(chart_at atlas (mfd_exp (top,atlas) g x (E ** Z)))
                       (mfd_exp (top,atlas) g x (E ** Z)))) =
            lift(sqrt(det(cmp_expmetric (top,atlas) g x E Z)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_EQ] THEN
    MATCH_MP_TAC CMPD_AREA_INTEGRAND THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)`;
                 `\Z h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) Z ** h`;
                 `S:real^N->bool`] GRGA_AREA_FORMULA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN
       `(\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)) =
        mfd_exp (top,atlas) g x o (\w. E ** w)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (mfd_exp_dom (top,atlas) (g:A->real^N^N) x)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
         [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
        ASM_SIMP_TAC[]];
      X_GEN_TAC `Z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC CMPD_EXP_FRAME_DERIV THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC `\w. lift(sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N) x
                                     (E:real^N^N) w)))` THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral S (\Z. lift(abs(det(matrix(\h. cmp_dexp (top,atlas) (g:A->real^N^N) x
                                              (E:real^N^N) Z ** h))) *
                 mfd_density atlas (chart_at atlas (mfd_exp (top,atlas) g x (E ** Z))) g
                   (SND(chart_at atlas (mfd_exp (top,atlas) g x (E ** Z)))
                       (mfd_exp (top,atlas) g x (E ** Z))))) =
    integral S (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]);;

