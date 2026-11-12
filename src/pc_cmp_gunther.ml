(* ========================================================================= *)
(* Unit pc_cmp_gunther (comparison-geometry layer CMP): S2, CMP_GUNTHER, the *)
(* Gunther-Bishop lower volume bound vol B(x,r) >= V_K(r) on an injectivity  *)
(* ball with sec <= K and sqrt K r <= pi (MT Prop 1.35).  In an orthonormal  *)
(* frame, for r' < r, exp_x o E maps B(0,r') injectively into B(x,r), the    *)
(* density sqrt(det G) is at least the model density mu_K (Gunther,          *)
(* CMPJ_GUNTHER along each ray), so vol B(x,r) >= V_K(r'); continuity of V_K *)
(* gives the bound at r.                                                     *)
(* ========================================================================= *)

needs "src/pc_cmp_relvol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Positivity of sn_K below r, a left-limit lemma, absolute integrability of *)
(* continuous functions on balls, and the Gunther density bound mu_K <=      *)
(* sqrt(det G) on the tangent ball.                                          *)
(* ========================================================================= *)

let CMPU_SN_POS = prove
 (`!K r t. &0 <= K /\ sqrt K * r <= pi /\ &0 < t /\ t < r ==> &0 < cmp_sn K t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `K = &0` THENL [DISJ1_TAC THEN ASM_REAL_ARITH_TAC; DISJ2_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt K * r` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC);;

let CMPU_LEFT_LIMIT_LE = prove
 (`!f:real->real r v.
        &0 < r /\ f real_continuous_on real_interval[&0,r] /\
        (!s. &0 < s /\ s < r ==> f s <= v)
        ==> f r <= v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `(f:real->real) real_continuous_on real_interval[&0,r]` THEN
  REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->real) r - v`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (r / &2) (r - d / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max (r / &2) (r - d / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CMPU_CONT_AI_BALL = prove
 (`!(f:real^N->real^1) a r.
        f continuous_on cball(a,r) ==> f absolutely_integrable_on ball(a,r)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `cball(a:real^N,r)` THEN
  REWRITE_TAC[BALL_SUBSET_CBALL; LEBESGUE_MEASURABLE_BALL] THEN
  SUBGOAL_THEN `bounded (IMAGE (f:real^N->real^1) (cball(a,r)))` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^N. lift B` THEN
  ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_CBALL] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_CBALL]);;

let CMPU_POW_ALG = prove
 (`!sn t. &0 < t
          ==> (sn / t) pow (dimindex(:N) - 1) * t pow dimindex(:N) =
              t * sn pow (dimindex(:N) - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dimindex(:N) = (dimindex(:N) - 1) + 1` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < t pow (dimindex(:N) - 1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < t pow (dimindex(:N) - 1)`; `&0 < t`] THEN
  CONV_TAC REAL_FIELD);;

(* Gunther's density bound on the tangent ball. *)

let CMPU_DENSITY_LOWER = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K r w.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < r /\
        mfd_tball g x r SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y e1 e2. y IN mfd_ball (top,atlas) g x r /\ ~collinear {vec 0,e1,e2}
                   ==> mfd_sectional atlas g y e1 e2 <= K) /\
        (!t. &0 < t /\ t < r ==> &0 < cmp_sn K t) /\
        norm w < r
        ==> (cmp_sn K (norm w) / norm w) pow (dimindex(:N) - 1) <=
            sqrt(det(cmp_expmetric (top,atlas) g x E w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`] CMPP_EXPMETRIC_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DET_I; SQRT_1; NORM_0; real_div; REAL_INV_0; REAL_MUL_RZERO;
                REAL_POW_ZERO] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `r:real`; `w:real^N`]
    CMPR_RAY_DATA_SEC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                       `Rm:real->real^N^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "met"))))) THEN
  MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `Rm:real->real^N^N`;
                 `r:real`; `K:real`] CMPJ_GUNTHER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `norm(w:real^N)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(w:real^N) % inv(norm w) % w = w` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `r:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w`;
                 `P:real^N^N`; `(A:real->real^N^N) (norm(w:real^N))`; `norm(w:real^N)`]
    CMPD_RAY_DET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CMPP_EXPMETRIC_SYM] THEN X_GEN_TAC `a:real^N` THEN
    USE_THEN "met" (MP_TAC o SPECL [`norm(w:real^N)`; `a:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  ASM_SIMP_TAC[CMPU_POW_ALG] THEN ASM_REAL_ARITH_TAC);;

(* For r' < r: V_K(r') <= vol B(x,r). *)

let CMPU_SMALL_BALL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K r r' v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\
        &0 < r /\ sqrt K * r <= pi /\ mfd_inj_ball (top,atlas) g x r /\
        (!y e1 e2. y IN mfd_ball (top,atlas) g x r /\ ~collinear {vec 0,e1,e2}
                   ==> mfd_sectional atlas g y e1 e2 <= K) /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\
        &0 < r' /\ r' < r
        ==> cmp_vmodel (:N) K r' <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x r SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL [ASM_MESON_TAC[mfd_inj_ball]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 < t /\ t < r ==> &0 < cmp_sn K t` (LABEL_TAC "sn") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPU_SN_POS THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. norm w < r
               ==> (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x`
  (LABEL_TAC "dom") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `r:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CMPQ_FRAME_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift(sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w))))
    absolutely_integrable_on ball(vec 0,r')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPU_CONT_AI_BALL THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^N,r)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMPB_SQRTDET_CONT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real`; `r':real`] CMPV_MODEL_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sn" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o AP_TERM `drop`)) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `ball(vec 0:real^N,r')`]
    CMPD_IMAGE_VOLUME) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_BALL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN USE_THEN "dom" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL_0] THEN MAP_EVERY X_GEN_TAC [`w1:real^N`; `w2:real^N`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(E:real^N^N) ** w1 = E ** w2` MP_TAC THENL
     [MATCH_MP_TAC CMPS_INJ_BALL_INJ THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `g:A->real^N^N`; `x:A`; `r:real`] THEN
      ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\y:real^N. matrix_inv(E:real^N^N) ** y`) THEN
      ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]];
    DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `v0:real` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; LIFT_DROP] THEN
    REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMPU_DENSITY_LOWER THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_MONO THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `IMAGE (\w. mfd_exp (top,atlas) (g:A->real^N^N) x ((E:real^N^N) ** w))
           (ball(vec 0:real^N,r'))`;
    `mfd_ball (top,atlas) (g:A->real^N^N) x r`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0; mfd_ball; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `(E:real^N^N) ** w`] CMPH_EXP_DIST_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "dom" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[CMPP_TNORM_FRAME] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let CMPU_GUNTHER_MAIN = prove
 (`!top atlas (g:A->real^N^N) (x:A) K r v.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 <= K /\
        &0 < r /\ sqrt K * r <= pi /\ mfd_inj_ball (top,atlas) g x r /\
        (!y e1 e2. y IN mfd_ball (top,atlas) g x r /\ ~collinear {vec 0,e1,e2}
                   ==> mfd_sectional atlas g y e1 e2 <= K) /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v
        ==> cmp_vmodel (:N) K r <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  MATCH_MP_TAC CMPU_LEFT_LIMIT_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`K:real`; `r:real`] CMPV_VMODEL_FACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPU_SN_POS THEN
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPU_SMALL_BALL THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* S2: the statement CMP_GUNTHER_STATEMENT. *)

let CMP_GUNTHER = prove
 (`!(u:A->bool) (n:N->bool). CMP_GUNTHER_STATEMENT u n`,
  REWRITE_TAC[CMP_GUNTHER_STATEMENT; CMPU_GUNTHER_MAIN]);;

