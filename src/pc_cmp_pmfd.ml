(* ========================================================================= *)
(* Unit pc_cmp_pmfd (comparison-geometry layer CMP, the first of four units  *)
(* for the Cheeger-Gromov-Taylor injectivity radius bound CMP_T2_CGT of      *)
(* pc_cmp_cgt): the exp_x pullback as a Riemannian manifold.  On             *)
(* T = ball(0,rho) with K rho^2 <= 1 and |Rm| <= K on B(x,rho), the open-set *)
(* manifold (subtopology euclidean T, open_set_atlas T) with the metric G =  *)
(* cmp_expmetric is Riemannian and Psi = exp_x o E is a local isometry into  *)
(* M with injective differential; radial lines are G-geodesics; G-geodesics  *)
(* from small points stay in small balls (Gauss lemma G w w = w) and so are  *)
(* defined up to time 1.                                                     *)
(* ========================================================================= *)

needs "src/pc_cmp_bg.ml";;
needs "src/pc_geo_lisom.ml";;
needs "src/pc_geo_s3.ml";;
needs "src/pc_geo_normal.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The pullback manifold and the local isometry Psi.                         *)
(* ========================================================================= *)

let cmp_psi = new_definition
 `cmp_psi (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
          (x:A) (E:real^N^N) (w:real^N) =
    mfd_exp (top,atlas) g x (E ** w)`;;

let cmp_pullsetup = new_definition
 `cmp_pullsetup (top:A topology,atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
                (x:A) (E:real^N^N) (K:real) (rho:real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    riemannian_metric atlas g /\ x IN topspace top /\
    mfd_orthonormal_frame g x E /\ &0 <= K /\ &0 < rho /\ K * rho pow 2 <= &1 /\
    mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
    (!y. y IN mfd_ball (top,atlas) g x rho ==> mfd_rm_norm atlas g y <= K)`;;

let CMPW_PM_BASIC = prove
 (`!U:real^N->bool.
        open U
        ==> hausdorff_space (subtopology euclidean U) /\
            smooth_manifold_atlas (subtopology euclidean U) (open_set_atlas U) /\
            topspace (subtopology euclidean U) = U`,
  SIMP_TAC[OPEN_SET_ATLAS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN]);;

let CMPW_LINEAR_SMOOTH = prove
 (`!s (M:real^N^N). open s ==> smooth_map_on s (\z. M ** z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. x`; `\z:real^N. (M:real^N^N) ** z`]
    SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; MATRIX_VECTOR_MUL_LINEAR; o_DEF]);;

let CMPW_PM_DIFF = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (f:real^N->A) U v.
        open U /\ v IN U
        ==> mfd_differential (open_set_atlas U) atlas f v =
            frechet_derivative (\y. SND(chart_at atlas (f v)) (f y)) (at v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_differential] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT] THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[MFDM_CHART_INV_ID]);;

(* The chart derivative of Psi at w. *)

let CMPW_PSI_HAS_DERIV = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        E ** w IN mfd_exp_dom (top,atlas) g x
        ==> ((\y. SND(chart_at atlas (cmp_psi (top,atlas) g x E w))
                    (cmp_psi (top,atlas) g x E y)) has_derivative
             (\h. cmp_dexp (top,atlas) g x E w ** h)) (at w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cmp_psi] THEN
  ABBREV_TAC `p = mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)` THEN
  SUBGOAL_THEN `(p:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `p:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A)`]
    CMPP_EXP_CHART_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `chart_jac (chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))
              (chart_at atlas p) p = (\h. h)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))`;
                   `p:A`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (p:A))
           (mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** y))) =
    (\v. SND(chart_at atlas p) (mfd_exp (top,atlas) g x v)) o (\y. E ** y)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h. cmp_dexp (top,atlas) (g:A->real^N^N) x (E:real^N^N) w ** h) =
    (\v. mfd_differential (open_set_atlas (:real^N)) atlas (mfd_exp (top,atlas) g x)
           (E ** w) v) o (\h. E ** h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC CMPP_DEXP_APPLY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[ETA_AX]]);;

let CMPW_PSI_DIFF = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) U w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        open U /\ w IN U /\ E ** w IN mfd_exp_dom (top,atlas) g x
        ==> mfd_differential (open_set_atlas U) atlas (cmp_psi (top,atlas) g x E) w =
            (\h. cmp_dexp (top,atlas) g x E w ** h)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CMPW_PM_DIFF] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC CMPW_PSI_HAS_DERIV THEN ASM_REWRITE_TAC[]);;

let CMPW_PSI_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) U.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        open U /\ (!w. w IN U ==> E ** w IN mfd_exp_dom (top,atlas) g x)
        ==> continuous_map (subtopology euclidean U,top) (cmp_psi (top,atlas) g x E) /\
            mfd_smooth_map (open_set_atlas U) atlas U (cmp_psi (top,atlas) g x E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) =
                  (\w. mfd_exp (top,atlas) g x (E ** w))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; cmp_psi]; ALL_TAC] THEN
    MATCH_MP_TAC CMPQ_EXPF_CONT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES] THEN
  MAP_EVERY X_GEN_TAC [`c0:(real^N->bool)#(real^N->real^N)`;
                       `c:(A->bool)#(A->real^N)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `(\v. SND (c:(A->bool)#(A->real^N))
                 (mfd_exp (top,atlas) (g:A->real^N^N) x v)) o (\w. (E:real^N^N) ** w)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM; cmp_psi] THEN SIMP_TAC[MFDM_CHART_INV_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `c:(A->bool)#(A->real^N)`] CMPH_EXP_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open {w | w IN U /\ cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) w IN
                       FST (c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{w | w IN U /\ cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) w IN
                     FST (c:(A->bool)#(A->real^N))} =
      U INTER {w | (E ** w) IN {v | v IN mfd_exp_dom (top,atlas) g x /\
                                   mfd_exp (top,atlas) g x v IN FST c}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; cmp_psi] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{v | v IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x /\
                   mfd_exp (top,atlas) g x v IN FST (c:(A->bool)#(A->real^N))}` THEN
  ASM_SIMP_TAC[CMPW_LINEAR_SMOOTH] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; cmp_psi] THEN ASM_MESON_TAC[]);;

(* Psi is a local isometry from the pullback manifold into M. *)

let CMPW_PSI_LISOM = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) U.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        open U /\ (!w. w IN U ==> E ** w IN mfd_exp_dom (top,atlas) g x)
        ==> mfd_local_isometry (subtopology euclidean U,open_set_atlas U)
              (cmp_expmetric (top,atlas) g x E) (top,atlas) g U
              (cmp_psi (top,atlas) g x E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `U:real^N->bool`] CMPW_PSI_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_local_isometry] THEN
  ASM_SIMP_TAC[OPEN_IN_REFL; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT;
               TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT; IN_ELIM_THM] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[cmp_psi] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `y:real^N`] CMPP_EXPMETRIC_LOCAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN
   `frechet_derivative (\w. SND (c:(A->bool)#(A->real^N))
                              (mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w)))
                       (at y) =
    frechet_derivative (SND c o cmp_psi (top,atlas) g x E o chart_inv (U,(\x:real^N. x)))
                       (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID; cmp_psi];
    ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID; cmp_psi]);;

(* ========================================================================= *)
(* The setup facts (S4 unpacked, the pullback manifold is                    *)
(* Riemannian, Psi a local isometry) and radial lines as G-geodesics.        *)
(* ========================================================================= *)

let CMPW_SETUP = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho.
        cmp_pullsetup (top,atlas) g x E K rho
        ==> open(ball(vec 0:real^N,rho)) /\
            (!w. w IN ball(vec 0,rho) ==> E ** w IN mfd_exp_dom (top,atlas) g x) /\
            metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) g x E) /\
            riemannian_metric (open_set_atlas (ball(vec 0,rho)))
                              (cmp_expmetric (top,atlas) g x E) /\
            cmp_expmetric (top,atlas) g x E (vec 0) = mat 1 /\
            (!w a. norm w < rho
                   ==> inv(&2) * (a dot a) <= a dot (cmp_expmetric (top,atlas) g x E w ** a) /\
                       a dot (cmp_expmetric (top,atlas) g x E w ** a) <= &2 * (a dot a)) /\
            (!w. norm w < rho ==> cmp_expmetric (top,atlas) g x E w ** w = w) /\
            (!w a. &0 < norm w /\ norm w < rho
                   ==> (inv(norm w) - K * norm w) *
                       (a dot (cmp_expmetric (top,atlas) g x E w ** a) -
                        (w dot a) pow 2 / norm w pow 2) <=
                       cmp_lhess (cmp_expmetric (top,atlas) g x E) (\z. norm z) w a a) /\
            mfd_local_isometry (subtopology euclidean (ball(vec 0,rho)),
                                open_set_atlas (ball(vec 0,rho)))
              (cmp_expmetric (top,atlas) g x E) (top,atlas) g (ball(vec 0,rho))
              (cmp_psi (top,atlas) g x E)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_pullsetup] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:A)`; `(:N)`] CMP_EXP_PULLBACK) THEN
  REWRITE_TAC[CMP_EXP_PULLBACK_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                             `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[OPEN_BALL] THEN
  SUBGOAL_THEN `!w. w IN ball(vec 0:real^N,rho)
                    ==> (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `rho:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN; OPEN_BALL] THEN
  MATCH_MP_TAC CMPW_PSI_LISOM THEN ASM_REWRITE_TAC[OPEN_BALL]);;

(* Christoffel symbols along radial lines vanish (G z z = z). *)

let CMPW_RADIAL_CHRISTOFFEL = prove
 (`!U (G:real^N->real^N^N) u t.
        metric_field U G /\ vec 0 IN U /\ (!z. z IN U ==> G z ** z = z) /\ t % u IN U
        ==> christoffel G (t % u) u u = vec 0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC GEON_CHRISTOFFEL_ZERO THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `t % u:real^N`]
    GEON_RADIAL_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `t % u:real^N`]
    LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `christoffel (G:real^N->real^N^N) (t % u) (t % u) (t % u) =
    t % t % christoffel G (t % u) u u`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t % u:real^N`) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `u:real^N`] o MATCH_MP LINEAR_CMUL) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N`) THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real`; `u:real^N`] o MATCH_MP LINEAR_CMUL) THEN
    REWRITE_TAC[];
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0]]);;

(* Radial lines are geodesics of the pullback manifold. *)

let CMPW_RADIAL_GEODESIC = prove
 (`!U (G:real^N->real^N^N) u J.
        open U /\ metric_field U G /\ vec 0 IN U /\ (!z. z IN U ==> G z ** z = z) /\
        is_realinterval J /\ real_open J /\ (!t. t IN J ==> t % u IN U)
        ==> mfd_geodesic (subtopology euclidean U,open_set_atlas U) G (\t. t % u) J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_geodesic] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEAN; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN REWRITE_TAC[CONTINUOUS_MAP_ID];
    ALL_TAC] THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `\t:real. (u:real^N)` THEN REWRITE_TAC[FST; SND] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `christoffel (metric_local (open_set_atlas U) (U,(\x:real^N. x)) (G:real^N->real^N^N))
                (t % u) u u = vec 0`
  (fun th -> REWRITE_TAC[th; VECTOR_NEG_0; HAS_VECTOR_DERIVATIVE_CONST]) THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `christoffel (G:real^N->real^N^N) (t % u) u u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL];
    MATCH_MP_TAC CMPW_RADIAL_CHRISTOFFEL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Geodesics of an open-set manifold in the identity chart (the              *)
(* ODE y' = V, V' = -Gamma(y)(V,V)), Cauchy-Schwarz for a metric field, and  *)
(* the sharp Gauss growth bound |beta t1| <= |beta t0| + (t1 - t0) |V|_G      *)
(* when G z z = z.                                                           *)
(* ========================================================================= *)

let CMPW_GEO_ODE = prove
 (`!U (G:real^N->real^N^N) (beta:real->real^N) J.
        open U /\ metric_field U G /\
        mfd_geodesic (subtopology euclidean U,open_set_atlas U) G beta J
        ==> !t. t IN J
                ==> beta t IN U /\
                    ((\s. beta(drop s)) has_vector_derivative
                     mfd_vel (open_set_atlas U) beta t) (at (lift t)) /\
                    ((\s. mfd_vel (open_set_atlas U) beta (drop s)) has_vector_derivative
                     --(christoffel G (beta t) (mfd_vel (open_set_atlas U) beta t)
                                                (mfd_vel (open_set_atlas U) beta t)))
                    (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN J ==> (beta:real->real^N) t IN U` (LABEL_TAC "inU") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`;
                   `open_set_atlas (U:real^N->bool)`; `G:real^N->real^N^N`;
                   `beta:real->real^N`; `J:real->bool`; `t:real`]
      GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`;
                 `open_set_atlas (U:real^N->bool)`; `G:real^N->real^N^N`;
                 `beta:real->real^N`; `J:real->bool`; `(U:real^N->bool),(\x:real^N. x)`]
    GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real->real^N` (LABEL_TAC "ode")) THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> ((\s. (beta:real->real^N)(drop s)) has_vector_derivative v t) (at (lift t)) /\
            ((\s. v(drop s)) has_vector_derivative
             --(christoffel (G:real^N->real^N^N) (beta t) (v t) (v t))) (at (lift t))`
  (LABEL_TAC "ode2") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(beta:real->real^N) t IN U` ASSUME_TAC THENL
     [USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `christoffel (G:real^N->real^N^N) ((beta:real->real^N) t) (v t) (v t) =
      christoffel (metric_local (open_set_atlas U) (U,(\x:real^N. x)) G) (beta t)
                  (v t) (v t)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL];
      ALL_TAC] THEN
    USE_THEN "ode" (fun th -> MATCH_MP_TAC(SPEC `t:real` th)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> mfd_vel (open_set_atlas U) (beta:real->real^N) t = v t`
  (LABEL_TAC "vel") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(beta:real->real^N) t IN U` ASSUME_TAC THENL
     [USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_vel] THEN ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    USE_THEN "ode2" (fun th -> ACCEPT_TAC(CONJUNCT1(MATCH_MP (SPEC `t:real` th)
      (ASSUME `(t:real) IN J`))));
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(beta:real->real^N) t IN U` ASSUME_TAC THENL
   [USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "ode2" (fun th -> STRIP_ASSUME_TAC(MATCH_MP (SPEC `t:real` th)
    (ASSUME `(t:real) IN J`))) THEN
  SUBGOAL_THEN `mfd_vel (open_set_atlas U) (beta:real->real^N) t = v t` SUBST1_TAC THENL
   [USE_THEN "vel" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. (v:real->real^N)(drop s)` THEN
  SUBGOAL_THEN `real_open (J:real->bool)` MP_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_BASIC]; ALL_TAC] THEN
  REWRITE_TAC[real_open] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "vel" MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

(* Derivative of a dot product of two curves. *)

let CMPW_DOT_DERIV = prove
 (`!(a:real->real^N) b a' b' t.
        ((\s. a(drop s)) has_vector_derivative a') (at (lift t)) /\
        ((\s. b(drop s)) has_vector_derivative b') (at (lift t))
        ==> ((\s. a s dot b s) has_real_derivative (a t dot b' + a' dot b t)) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  MP_TAC(ISPECL [`\x y:real^N. lift(x dot y)`; `\s. (a:real->real^N)(drop s)`;
                 `\s. (b:real->real^N)(drop s)`; `a':real^N`; `b':real^N`; `lift t`]
    HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT; o_DEF; LIFT_DROP; LIFT_ADD]);;

(* Cauchy-Schwarz for a metric field. *)

let CMPW_GCS = prove
 (`!U (G:real^N->real^N^N) y a b.
        metric_field U G /\ y IN U
        ==> a dot (G y ** b) <= sqrt(a dot (G y ** a)) * sqrt(b dot (G y ** b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!c d:real^N. c dot ((G:real^N->real^N^N) y ** d) =
                             ((M:real^N^N) ** c) dot (M ** d)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_FRAME_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2; GSYM vector_norm] THEN
  SIMP_TAC[POW_2_SQRT; NORM_POS_LE; NORM_CAUCHY_SCHWARZ]);;

(* Nonnegativity of a metric field. *)

let CMPW_METRIC_POS_LE = prove
 (`!U (G:real^N->real^N^N) y v.
        metric_field U G /\ y IN U ==> &0 <= v dot (G y ** v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `v:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LRG_METRIC_POS THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The derivative of sqrt(|beta|^2 + e). *)

let CMPW_SQRT_DERIV = prove
 (`!(beta:real->real^N) V t e.
        ((\s. beta(drop s)) has_vector_derivative V) (at (lift t)) /\ &0 < e
        ==> ((\s. sqrt(beta s dot beta s + e)) has_real_derivative
             ((beta t dot V) / sqrt(beta t dot beta t + e))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`beta:real->real^N`; `beta:real->real^N`; `V:real^N`; `V:real^N`; `t:real`]
    CMPW_DOT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (beta:real->real^N) t dot beta t + e` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(beta:real->real^N) t` DOT_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt((beta:real->real^N) t dot beta t + e)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((beta:real->real^N) t dot V) / sqrt(beta t dot beta t + e) =
    inv(&2 * sqrt(beta t dot beta t + e)) * (beta t dot V + V dot beta t)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(V:real^N) dot (beta:real->real^N) t = beta t dot V` SUBST1_TAC THENL
     [MATCH_ACCEPT_TAC DOT_SYM; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sqrt((beta:real->real^N) t dot beta t + e)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. (beta:real->real^N) s dot beta s + e`; `sqrt`;
                 `(beta:real->real^N) t dot V + V dot beta t`;
                 `inv(&2 * sqrt((beta:real->real^N) t dot beta t + e))`; `t:real`]
    REAL_DIFF_CHAIN_ATREAL) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\s. (beta:real->real^N) s dot beta s`;
                   `(beta:real->real^N) t dot V + V dot beta t`;
                   `\s:real. (e:real)`; `&0`; `atreal t`] HAS_REAL_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_ADD_RID];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[]]);;

(* The derivative bound (Gauss lemma and Cauchy-Schwarz for G). *)

let CMPW_GAUSS_SPEED = prove
 (`!U (G:real^N->real^N^N) y V e.
        metric_field U G /\ y IN U /\ G y ** y = y /\ &0 < e
        ==> (y dot V) / sqrt(y dot y + e) <= sqrt(V dot (G y ** V))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt((y:real^N) dot y + e)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC(ISPEC `y:real^N` DOT_POS_LE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(y:real^N) dot V = y dot ((G:real^N->real^N^N) y ** V)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `y:real^N`;
                   `V:real^N`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt((y:real^N) dot ((G:real^N->real^N^N) y ** y)) *
              sqrt(V dot (G y ** V))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMPW_GCS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC CMPW_METRIC_POS_LE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Letting e -> 0. *)

let CMPW_EPS_LIMIT = prove
 (`!(a:real^N) (b:real^N) h.
        (!e. &0 < e ==> sqrt(a dot a + e) <= sqrt(b dot b + e) + h)
        ==> norm a <= norm b + h`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!b. (~(a <= b) ==> F) ==> a <= b`) THEN DISCH_TAC THEN
  ABBREV_TAC `dlt = norm(a:real^N) - (norm(b:real^N) + h)` THEN
  SUBGOAL_THEN `&0 < dlt` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(dlt / &2) pow 2`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(a:real^N) <= sqrt(a dot a + (dlt / &2) pow 2) /\
    sqrt((b:real^N) dot b + (dlt / &2) pow 2) <= norm b + dlt / &2`
  MP_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      MP_TAC(SPEC `dlt / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[GSYM NORM_POW_2] THEN
        SUBGOAL_THEN `&0 <= norm(b:real^N) * (dlt / &2)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The sharp Gauss growth bound along a geodesic of the pullback. *)

let CMPW_GROWTH = prove
 (`!U (G:real^N->real^N^N) (beta:real->real^N) J t0 t1.
        open U /\ metric_field U G /\ (!z. z IN U ==> G z ** z = z) /\
        mfd_geodesic (subtopology euclidean U,open_set_atlas U) G beta J /\
        t0 IN J /\ t1 IN J /\ t0 <= t1
        ==> norm(beta t1) <=
            norm(beta t0) +
            (t1 - t0) * mfd_tnorm G (beta t0) (mfd_vel (open_set_atlas U) beta t0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = mfd_tnorm (G:real^N->real^N^N) ((beta:real->real^N) t0)
                    (mfd_vel (open_set_atlas U) beta t0)` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`; `J:real->bool`]
    CMPW_GEO_ODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ode") THEN
  SUBGOAL_THEN `!t. t IN J ==> mfd_tnorm (G:real^N->real^N^N) ((beta:real->real^N) t)
                                 (mfd_vel (open_set_atlas U) beta t) = c`
  (LABEL_TAC "speed") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC MFD_GEODESIC_SPEED THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (U:real^N->bool)`; `J:real->bool`] THEN
    ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_RIEMANNIAN];
    ALL_TAC] THEN
  SUBGOAL_THEN `is_realinterval (J:real->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[GEOL_GEODESIC_BASIC]; ALL_TAC] THEN
  SUBGOAL_THEN `real_interval[t0,t1] SUBSET (J:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[is_realinterval]) THEN
    MAP_EVERY EXISTS_TAC [`t0:real`; `t1:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CMPW_EPS_LIMIT THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\t. sqrt((beta:real->real^N) t dot beta t + e)`;
    `\t. ((beta:real->real^N) t dot mfd_vel (open_set_atlas U) beta t) /
         sqrt(beta t dot beta t + e)`;
    `t0:real`; `t1:real`] REAL_MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC CMPW_SQRT_DERIV THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ode" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `xi:real` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  SUBGOAL_THEN `(xi:real) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((beta:real->real^N) xi dot mfd_vel (open_set_atlas U) beta xi) /
    sqrt(beta xi dot beta xi + e) <= c`
  ASSUME_TAC THENL
   [USE_THEN "speed" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
       (ASSUME `(xi:real) IN J`))]) THEN
    REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC CMPW_GAUSS_SPEED THEN
    EXISTS_TAC `U:real^N->bool` THEN
    USE_THEN "ode" (MP_TAC o SPEC `xi:real`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `!d. a - b = d * h /\ d * h <= c * h ==> a <= b + h * c`) THEN
  EXISTS_TAC `((beta:real->real^N) xi dot mfd_vel (open_set_atlas U) beta xi) /
              sqrt(beta xi dot beta xi + e)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Geodesics of the pullback from small points exist up to time              *)
(* 1 and stay in small balls (escape lemma + growth bound), and the          *)
(* exponential map of the pullback at 0 is the identity.                     *)
(* ========================================================================= *)

let CMPW_EXP_DOM = prove
 (`!U (G:real^N->real^N^N) R p v.
        open U /\ metric_field U G /\ (!z. z IN U ==> G z ** z = z) /\
        cball(vec 0,R) SUBSET U /\ p IN U /\ norm p + mfd_tnorm G p v < R
        ==> v IN mfd_exp_dom (subtopology euclidean U,open_set_atlas U) G p /\
            !t. &0 <= t /\ t <= &1
                ==> mfd_exp (subtopology euclidean U,open_set_atlas U) G p (t % v) IN U /\
                    norm(mfd_exp (subtopology euclidean U,open_set_atlas U) G p (t % v)) <=
                    norm p + t * mfd_tnorm G p v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `U:real^N->bool` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas U) (G:real^N->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= mfd_tnorm (G:real^N->real^N^N) p v` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tnorm] THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC CMPW_METRIC_POS_LE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `G:real^N->real^N^N`; `p:real^N`; `v:real^N`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = mfd_geo_maxint (subtopology euclidean U,open_set_atlas U)
                    (G:real^N->real^N^N) p v` THEN
  ABBREV_TAC `geo = mfd_geo (subtopology euclidean U,open_set_atlas U)
                      (G:real^N->real^N^N) p v` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN M /\ &0 <= t
                    ==> norm((geo:real->real^N) t) <=
                        norm(p:real^N) + t * mfd_tnorm (G:real^N->real^N^N) p v`
  (LABEL_TAC "grow") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `geo:real->real^N`;
                   `M:real->bool`; `&0`; `t:real`] CMPW_GROWTH) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN M ==> (geo:real->real^N) t IN U` (LABEL_TAC "inU") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`;
                   `open_set_atlas (U:real^N->bool)`; `G:real^N->real^N^N`;
                   `geo:real->real^N`; `M:real->bool`; `t:real`]
      GEOL_GEODESIC_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 IN M` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `!t. t IN M ==> t < &1` ASSUME_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(&1 IN M)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `is_realinterval (M:real->bool)` THEN
      REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`&0`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`;
                   `open_set_atlas (U:real^N->bool)`; `G:real^N->real^N^N`; `p:real^N`;
                   `v:real^N`; `cball(vec 0:real^N,R)`; `&1`] MFD_GEO_ESCAPE) THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `max t1 (&0) IN M` ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= t1` THENL
       [ASM_SIMP_TAC[REAL_ARITH `&0 <= t1 ==> max t1 (&0) = t1`];
        ASM_SIMP_TAC[REAL_ARITH `~(&0 <= t1) ==> max t1 (&0) = &0`]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `max t1 (&0)` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `cball(vec 0:real^N,R)`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN
    REWRITE_TAC[NOT_IMP] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(p:real^N) + max t1 (&0) * mfd_tnorm (G:real^N->real^N^N) p v` THEN
    CONJ_TAC THENL
     [USE_THEN "grow" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `max t1 (&0) < &1` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `max t1 (&0) * mfd_tnorm (G:real^N->real^N^N) p v <= mfd_tnorm G p v`
    MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[mfd_exp_dom; IN_ELIM_THM]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real) IN M` ASSUME_TAC THENL
   [UNDISCH_TAC `is_realinterval (M:real->bool)` THEN
    REWRITE_TAC[is_realinterval] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `G:real^N->real^N^N`; `p:real^N`; `v:real^N`; `t:real`] MFD_EXP_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  CONJ_TAC THENL
   [USE_THEN "inU" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "grow" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The exponential map of the pullback at 0 is the identity. *)

let CMPW_EXP_ZERO = prove
 (`!(G:real^N->real^N^N) rho v.
        metric_field (ball(vec 0,rho)) G /\
        (!z. z IN ball(vec 0,rho) ==> G z ** z = z) /\ norm v < rho
        ==> v IN mfd_exp_dom (subtopology euclidean (ball(vec 0,rho)),
                              open_set_atlas (ball(vec 0,rho))) G (vec 0) /\
            mfd_exp (subtopology euclidean (ball(vec 0,rho)),
                     open_set_atlas (ball(vec 0,rho))) G (vec 0) v = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `U = ball(vec 0:real^N,rho)` THEN
  SUBGOAL_THEN `open (U:real^N->bool) /\ vec 0 IN U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `U:real^N->bool` CMPW_PM_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `riemannian_metric (open_set_atlas U) (G:real^N->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN]; ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ (&1 + d) * norm(v:real^N) < rho` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(rho - norm(v:real^N)) / (norm v + &1)` THEN
    SUBGOAL_THEN `&0 < norm(v:real^N) + &1 /\ &0 < rho - norm v` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    SUBGOAL_THEN `(&1 + (rho - norm(v:real^N)) / (norm v + &1)) * norm v =
                  norm v + ((rho - norm v) * norm v) / (norm v + &1)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm(v:real^N) + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x < rho - n ==> n + x < rho`) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `J = real_interval(--(&1 + d),&1 + d)` THEN
  SUBGOAL_THEN `is_realinterval (J:real->bool) /\ real_open J /\ &0 IN J /\ &1 IN J`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL;
                                    IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN J ==> t % (v:real^N) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `ball(vec 0:real^N,rho) = U`)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; IN_BALL_0; NORM_MUL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(&1 + d) * norm(v:real^N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `v:real^N`; `J:real->bool`]
    CMPW_RADIAL_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_vel (open_set_atlas U) (\t. t % (v:real^N)) (&0) = v` ASSUME_TAC THENL
   [REWRITE_TAC[mfd_vel; VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_CHART_AT] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (U:real^N->bool)`; `open_set_atlas (U:real^N->bool)`;
                 `G:real^N->real^N^N`; `\t. t % (v:real^N)`; `J:real->bool`;
                 `vec 0:real^N`; `v:real^N`] MFD_GEO_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `&1` o REWRITE_RULE[SUBSET])
                             (MP_TAC o SPEC `&1`)) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[mfd_exp_dom; mfd_exp; IN_ELIM_THM]);;

(* ========================================================================= *)
(* Convexity of |beta|^2 along geodesics of the pullback.  The               *)
(* S4 Hessian lower bound gives a.(D_w G(w)) a >= -2 K |w|^2 <a,a>_G, so     *)
(* (beta . V)' = <V,V>_G + (1/2) V.(D_beta G(beta)) V >= (1 - K|beta|^2)     *)
(* <V,V>_G.                                                                  *)
(* ========================================================================= *)

(* Cauchy-Schwarz with the Gauss lemma: (w.a)^2 <= |w|^2 <a,a>_G. *)

let CMPW_GAUSS_CS = prove
 (`!U (G:real^N->real^N^N) w a.
        metric_field U G /\ w IN U /\ G w ** w = w
        ==> (w dot a) pow 2 <= (w dot w) * (a dot (G w ** a))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N) dot a = w dot ((G:real^N->real^N^N) w ** a)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `w:real^N`;
                   `a:real^N`] LRG_METRIC_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (a:real^N) dot ((G:real^N->real^N^N) w ** a)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPW_METRIC_POS_LE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `w:real^N`; `a:real^N`]
    CMPW_GCS) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `--w:real^N`; `a:real^N`]
    CMPW_GCS) THEN
  ASM_REWRITE_TAC[DOT_LNEG; MATRIX_VECTOR_MUL_RNEG; DOT_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[GSYM vector_norm] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= norm(w:real^N) * sqrt((a:real^N) dot ((G:real^N->real^N^N) w ** a))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[NORM_POS_LE; SQRT_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(w:real^N) * sqrt((a:real^N) dot ((G:real^N->real^N^N) w ** a))) pow 2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_MUL; NORM_POW_2] THEN ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]]);;

let CMPW_MDERIV_LOWER = prove
 (`!U (G:real^N->real^N^N) K w a.
        metric_field U G /\ w IN U /\ (!z. z IN U ==> G z ** z = z) /\ &0 <= K /\
        (~(w = vec 0)
         ==> (inv(norm w) - K * norm w) *
             (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2) <=
             cmp_lhess G (\z. norm z) w a a)
        ==> --(&2 * K * (w dot w)) * (a dot (G w ** a)) <= a dot (mderiv G w w ** a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[DOT_LZERO; REAL_MUL_RZERO; REAL_NEG_0; REAL_MUL_LZERO] THEN
    SUBGOAL_THEN
     `linear (\v. lift((a:real^N) dot (mderiv (G:real^N->real^N^N) (vec 0) v ** a)))`
    MP_TAC THENL
     [MATCH_MP_TAC LRG_MDERIV_DOT_LINEAR THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `vec 0:real^N`]
        LRG_METRIC_FIELD_DIFF) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(MP_TAC o MATCH_MP LINEAR_0) THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && is_neg(lhand(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `w:real^N`; `a:real^N`]
    CMPP_LHESS_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `&0 <= ((w:real^N) dot a) pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `n = norm(w:real^N)` THEN
  ABBREV_TAC `A = (a:real^N) dot ((G:real^N->real^N^N) w ** a)` THEN
  ABBREV_TAC `B = ((w:real^N) dot a) pow 2` THEN
  ABBREV_TAC `M = (a:real^N) dot (mderiv (G:real^N->real^N^N) w w ** a)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= K * B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * n) * ((inv n - K * n) * (A - B / n pow 2)) <=
                (&2 * n) * (A / n - B / n pow 3 + M / (&2 * n))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * n) * ((inv n - K * n) * (A - B / n pow 2)) =
                &2 * A - &2 * B / n pow 2 + (--(&2 * K * n pow 2) * A + &2 * K * B) /\
                (&2 * n) * (A / n - B / n pow 3 + M / (&2 * n)) =
                &2 * A - &2 * B / n pow 2 + M`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The second derivative of |beta|^2 / 2 along a geodesic of the pullback. *)

let CMPW_CONVEX_DERIV = prove
 (`!U (G:real^N->real^N^N) K (beta:real->real^N) J t.
        open U /\ metric_field U G /\ (!z. z IN U ==> G z ** z = z) /\ &0 <= K /\
        (!w a. w IN U /\ ~(w = vec 0)
               ==> (inv(norm w) - K * norm w) *
                   (a dot (G w ** a) - (w dot a) pow 2 / norm w pow 2) <=
                   cmp_lhess G (\z. norm z) w a a) /\
        mfd_geodesic (subtopology euclidean U,open_set_atlas U) G beta J /\ t IN J
        ==> ((\s. beta s dot beta s) has_real_derivative
             (&2 * (beta t dot mfd_vel (open_set_atlas U) beta t))) (atreal t) /\
            ((\s. beta s dot mfd_vel (open_set_atlas U) beta s) has_real_derivative
             (mfd_vel (open_set_atlas U) beta t dot mfd_vel (open_set_atlas U) beta t -
              beta t dot christoffel G (beta t) (mfd_vel (open_set_atlas U) beta t)
                                                (mfd_vel (open_set_atlas U) beta t)))
            (atreal t) /\
            (&1 - K * (beta t dot beta t)) *
            (mfd_vel (open_set_atlas U) beta t dot
             (G(beta t) ** mfd_vel (open_set_atlas U) beta t)) <=
            mfd_vel (open_set_atlas U) beta t dot mfd_vel (open_set_atlas U) beta t -
            beta t dot christoffel G (beta t) (mfd_vel (open_set_atlas U) beta t)
                                              (mfd_vel (open_set_atlas U) beta t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `beta:real->real^N`; `J:real->bool`]
    CMPW_GEO_ODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = mfd_vel (open_set_atlas U) (beta:real->real^N)` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`beta:real->real^N`; `beta:real->real^N`; `(V:real->real^N) t`;
                   `(V:real->real^N) t`; `t:real`] CMPW_DOT_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`beta:real->real^N`; `V:real->real^N`; `(V:real->real^N) t`;
                   `--(christoffel (G:real^N->real^N^N) ((beta:real->real^N) t)
                                   ((V:real->real^N) t) (V t))`; `t:real`]
      CMPW_DOT_DERIV) THEN
    ASM_REWRITE_TAC[DOT_RNEG] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(beta:real->real^N) t`;
                 `(V:real->real^N) t`] CMPP_CHRISTOFFEL_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `K:real`; `(beta:real->real^N) t`;
                 `(V:real->real^N) t`] CMPW_MDERIV_LOWER) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

