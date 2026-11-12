(* ========================================================================= *)
(* Unit pc_cmp_relvol (comparison-geometry layer CMP): S1, CMP_RELVOL, the   *)
(* local relative volume comparison (Bishop-Gromov) under Ric >= -(n-1)K on  *)
(* a ball B(x,R) with compact closure.  In an orthonormal frame the volume   *)
(* of B(x,r) is the integral over B(0,r) of Phi mu_{-K}, where mu_{-K} is    *)
(* the model density and Phi = 1_D0 sqrt(det G) / mu_{-K} is at most 1       *)
(* (Bishop) and non-increasing along rays (CMPD_BISHOP_MONO); the Euclidean  *)
(* comparison CMPV_RADIAL_COMPARE and CMPV_MODEL_INTEGRAL finish.            *)
(* ========================================================================= *)

needs "src/pc_cmp_seg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The density along a ray of D0.  For w in D0 (s0 w in D with               *)
(* s0 > 1) the Jacobi matrix A of the ray of w is invertible on (0, s0|w|),  *)
(* sqrt(det G(t u)) = det A(t) / t^n there, det A(t) <= t sn_{-K}(t)^(n-1)   *)
(* (Bishop) and det A(t) / (t sn_{-K}(t)^(n-1)) is non-increasing.           *)
(* ========================================================================= *)

let CMPB_RAY_DENSITY = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K R w s0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y v. y IN mfd_ball (top,atlas) g x R
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        ~(w = vec 0) /\ &1 < s0 /\ norm(s0 % w) < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s0 % w))) =
        norm(s0 % w)
        ==> ?A:real->real^N^N.
              (!t. &0 < t /\ t < s0 * norm w
                   ==> &0 < det(A t) /\
                       sqrt(det(cmp_expmetric (top,atlas) g x E (t % inv(norm w) % w))) =
                       det(A t) / t pow dimindex(:N) /\
                       det(A t) <= t * cmp_sn (--K) t pow (dimindex(:N) - 1)) /\
              (!s t. &0 < s /\ s <= t /\ t < s0 * norm w
                     ==> det(A t) * (s * cmp_sn (--K) s pow (dimindex(:N) - 1)) <=
                         det(A s) * (t * cmp_sn (--K) t pow (dimindex(:N) - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((s0:real) % (w:real^N)) = s0 * norm w` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&1 < s ==> abs s = s`];
    ALL_TAC] THEN
  ABBREV_TAC `L = s0 * norm(w:real^N)` THEN
  SUBGOAL_THEN `&0 < L /\ L < R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `R:real`; `w:real^N`]
    CMPD_RAY_DATA_RIC_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`P:real^N^N`; `A:real->real^N^N`; `B:real->real^N^N`;
                       `Rm:real->real^N^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tr") (LABEL_TAC "ray"))))) THEN
  SUBGOAL_THEN `cmp_jsys (A:real->real^N^N) B Rm L` ASSUME_TAC THENL
   [MATCH_MP_TAC CMPH_JSYS_MONO THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 < t ==> &0 < cmp_sn (--K) t` (LABEL_TAC "sn") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 < t /\ t < L ==> invertible((A:real->real^N^N) t)`
  (LABEL_TAC "inv") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC CMPH_RAY_INVERTIBLE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
      `x:A`; `E:real^N^N`; `P:real^N^N`; `t:real`; `t % inv(norm(w:real^N)) % w`] THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CMPQ_FRAME_INVERTIBLE];
      MATCH_MP_TAC CMPQ_FRAME_DOM THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN USE_THEN "ray" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `h:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`; `w:real^N`; `s0:real`]
      CMPQ_SEG0_DEXP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`t / norm(w:real^N)`; `h:real^N`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
         rand(concl th) = `vec 0:real^N`)) THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC; real_div]];
    ALL_TAC] THEN
  EXISTS_TAC `A:real->real^N^N` THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `Rm:real->real^N^N`;
                   `L:real`] CMPJ_DET_POSITIVE) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)
                        (t % inv(norm(w:real^N)) % w)`;
                     `P:real^N^N`; `(A:real->real^N^N) t`; `t:real`] CMPD_RAY_DET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CMPP_EXPMETRIC_SYM THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CMPQ_FRAME_DOM THEN EXISTS_TAC `R:real` THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
          ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
          ASM_REAL_ARITH_TAC;
          GEN_TAC THEN USE_THEN "ray" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`]];
      MP_TAC(ISPECL [`A:real->real^N^N`; `B:real->real^N^N`; `Rm:real->real^N^N`;
                     `L:real`; `K:real`] CMPJ_BISHOP) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "tr" MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC;
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CMPD_BISHOP_MONO THEN
    MAP_EVERY EXISTS_TAC [`B:real->real^N^N`; `Rm:real->real^N^N`; `L:real`] THEN
    ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "tr" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The weight Phi = 1_D0 sqrt(det G) / mu_{-K} with                          *)
(* mu_{-K}(w) = (sn_{-K}(|w|)/|w|)^(n-1): 0 <= Phi <= 1, Phi mu_{-K} is the  *)
(* restricted density away from 0, and Phi is non-increasing along rays.     *)
(* ========================================================================= *)

let CMPB_RATIO_ALG = prove
 (`!d t sn. &0 < t /\ &0 < sn
            ==> (d / t pow dimindex(:N)) / (sn / t) pow (dimindex(:N) - 1) =
                d / (t * sn pow (dimindex(:N) - 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dimindex(:N) = (dimindex(:N) - 1) + 1` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < t pow (dimindex(:N) - 1) /\ &0 < sn pow (dimindex(:N) - 1)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < t pow (dimindex(:N) - 1)`; `&0 < sn pow (dimindex(:N) - 1)`; `&0 < t`] THEN
  CONV_TAC REAL_FIELD);;

let CMPB_DIV_LE = prove
 (`!a b c d. &0 < b /\ &0 < d /\ a * d <= c * b ==> a / b <= c / d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `b * d` THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN
  SUBGOAL_THEN `a / b * (b * d) = a * d /\ c / d * (b * d) = c * b`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MAP_EVERY UNDISCH_TAC [`&0 < b`; `&0 < d`] THEN CONV_TAC REAL_FIELD);;

let CMPB_PHI_RAY = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K R w s0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y v. y IN mfd_ball (top,atlas) g x R
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        ~(w = vec 0) /\ &1 < s0 /\ norm(s0 % w) < R /\
        mfd_dist (top,atlas) g x (mfd_exp (top,atlas) g x (E ** (s0 % w))) =
        norm(s0 % w)
        ==> !s. &0 < s /\ s <= &1
                ==> &0 <= sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
                          (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1) /\
                    sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
                    (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1) <= &1 /\
                    sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
                    (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1) <=
                    sqrt(det(cmp_expmetric (top,atlas) g x E (s % w))) /
                    (cmp_sn (--K) (norm(s % w)) / norm(s % w)) pow (dimindex(:N) - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `R:real`; `w:real^N`;
                 `s0:real`] CMPB_RAY_DENSITY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real->real^N^N`
    (CONJUNCTS_THEN2 (LABEL_TAC "den") (LABEL_TAC "mono"))) THEN
  SUBGOAL_THEN `&0 < norm(w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) < s0 * norm w` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((s:real) % (w:real^N)) = s * norm w` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * norm(w:real^N) /\ s * norm w <= norm w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 < t ==> &0 < cmp_sn (--K) t` (LABEL_TAC "sn") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) % inv(norm w) % w = w` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s * norm(w:real^N)) % inv(norm w) % w = s % w` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_RID];
    ALL_TAC] THEN
  USE_THEN "den" (MP_TAC o SPEC `norm(w:real^N)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "den" (MP_TAC o SPEC `s * norm(w:real^N)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ASM_SIMP_TAC[CMPB_RATIO_ALG] THEN
  SUBGOAL_THEN `&0 < norm(w:real^N) * cmp_sn (--K) (norm w) pow (dimindex(:N) - 1) /\
                &0 < (s * norm w) * cmp_sn (--K) (s * norm w) pow (dimindex(:N) - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN USE_THEN "sn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID];
    MATCH_MP_TAC CMPB_DIV_LE THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "mono" (MP_TAC o SPECL [`s * norm(w:real^N)`; `norm(w:real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;

let CMPB_PHI_FACTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K R (Phi:real^N->real).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\ &0 < R /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y v. y IN mfd_ball (top,atlas) g x R
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        (!w. Phi w =
             if w IN {w | ?s. &1 < s /\ norm(s % w) < R /\
                            mfd_dist (top,atlas) g x
                              (mfd_exp (top,atlas) g x (E ** (s % w))) = norm(s % w)}
             then sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
                  (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)
             else &0)
        ==> (!w. &0 <= Phi w /\ Phi w <= &1) /\
            (!w. ~(w = vec 0)
                 ==> Phi w * (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1) =
                     if w IN {w | ?s. &1 < s /\ norm(s % w) < R /\
                                  mfd_dist (top,atlas) g x
                                    (mfd_exp (top,atlas) g x (E ** (s % w))) = norm(s % w)}
                     then sqrt(det(cmp_expmetric (top,atlas) g x E w)) else &0) /\
            (!w s. &0 < s /\ s <= &1 ==> Phi w <= Phi(s % w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D0 = {w | ?s. &1 < s /\ norm(s % w) < R /\
                       mfd_dist (top,atlas) (g:A->real^N^N) x
                         (mfd_exp (top,atlas) g x ((E:real^N^N) ** (s % w))) =
                       norm(s % w)}` THEN
  SUBGOAL_THEN
   `!w. w IN D0 /\ ~(w = vec 0)
        ==> !s. &0 < s /\ s <= &1
                ==> &0 <= sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N) x
                                    (E:real^N^N) w)) /
                          (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1) /\
                    sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
                    (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1) <= &1 /\
                    sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
                    (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1) <=
                    sqrt(det(cmp_expmetric (top,atlas) g x E (s % w))) /
                    (cmp_sn (--K) (norm(s % w)) / norm(s % w)) pow (dimindex(:N) - 1)`
  (LABEL_TAC "ray") THENL
   [X_GEN_TAC `w:real^N` THEN EXPAND_TAC "D0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    MATCH_MP_TAC CMPB_PHI_RAY THEN
    MAP_EVERY EXISTS_TAC [`R:real`; `s0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w s. w IN D0 /\ &0 < s /\ s <= &1 ==> (s % w:real^N) IN D0` (LABEL_TAC "star") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D0" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s0 % (s:real) % (w:real^N) = s % s0 % w` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_SYM]; ALL_TAC] THEN
    MATCH_MP_TAC CMPQ_SEG_STAR THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. &0 <= (Phi:real^N->real) w /\ Phi w <= &1` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
    ASM_CASES_TAC `w:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0; real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_POW_ZERO] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `E:real^N^N`] CMPP_EXPMETRIC_ZERO) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[DET_I; SQRT_1] THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_INV_0; REAL_INV_1; REAL_MUL_RZERO; REAL_MUL_RID] THEN
      REAL_ARITH_TAC;
      USE_THEN "ray" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; REAL_LE_REFL] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_REWRITE_TAC[NORM_POS_LT] THEN MATCH_MP_TAC CMP_SN_POS THEN
    ASM_REWRITE_TAC[NORM_POS_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^N`; `s:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^N) IN D0` THENL
   [ALL_TAC;
    UNDISCH_TAC `!w. &0 <= (Phi:real^N->real) w /\ Phi w <= &1` THEN
    DISCH_THEN(MP_TAC o SPEC `(s:real) % (w:real^N)`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `(s % w:real^N) IN D0` ASSUME_TAC THENL
   [USE_THEN "star" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "ray" (MP_TAC o SPEC `w:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Integrability of Phi mu_{-K} on B(0,R), identification of                 *)
(* vol B(x,r) with the integral of Phi mu_{-K} over B(0,r), and S1.          *)
(* ========================================================================= *)

let CMPB_SQRTDET_CONT = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) R.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x
        ==> (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w)))) continuous_on
            ball(vec 0,R)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_SQRT_COMPOSE THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_DET_VECTORIZE THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{w | (E:real^N^N) ** w IN mfd_exp_dom (top,atlas) (g:A->real^N^N) x}` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`] CMPP_EXPMETRIC_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS o CONJUNCT2) THEN
    REWRITE_TAC[o_DEF];
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CMPP_BALL_IN_DOM THEN
    MAP_EVERY EXISTS_TAC [`g:A->real^N^N`; `x:A`; `R:real`] THEN ASM_REWRITE_TAC[]]);;

let CMPB_MU_POS_LE = prove
 (`!K (w:real^N). &0 <= K
        ==> &0 <= (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC CMP_SN_POS THEN
    ASM_REWRITE_TAC[NORM_POS_LT] THEN ASM_REAL_ARITH_TAC]);;

(* An abstract absolute integrability criterion: Phi mu agrees off 0 with  *)
(* the restriction of a continuous h to a measurable D, 0 <= Phi <= 1 and  *)
(* mu >= 0 is integrable.                                                  *)

let CMPB_ABS_INTEGRABLE = prove
 (`!(Phi:real^N->real) (mu:real^N->real) (h:real^N->real) D S.
        lebesgue_measurable D /\ lebesgue_measurable S /\
        (\w. lift(h w)) continuous_on S /\
        (!w. ~(w = vec 0) ==> Phi w * mu w = if w IN D then h w else &0) /\
        (!w. &0 <= Phi w /\ Phi w <= &1) /\ (!w. &0 <= mu w) /\
        (\w. lift(mu w)) integrable_on S
        ==> (\w. lift(Phi w * mu w)) absolutely_integrable_on S`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\w:real^N. lift(mu w)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE) THEN
    MAP_EVERY EXISTS_TAC
     [`\w:real^N. if w IN D then lift(h w) else vec 0`; `{vec 0:real^N}`] THEN
    REWRITE_TAC[NEGLIGIBLE_SING; IN_DIFF; IN_SING] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM];
      MATCH_MP_TAC MEASURABLE_ON_CASES THEN
      ASM_REWRITE_TAC[SET_RULE `!s:real^N->bool. {x | x IN s} = s`; MEASURABLE_ON_0] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    SUBGOAL_THEN `&0 <= (Phi:real^N->real) w /\ Phi w <= &1 /\ &0 <= (mu:real^N->real) w`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (Phi:real^N->real) w * (mu:real^N->real) w /\
                  Phi w * mu w <= &1 * mu w` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_RMUL] THEN
      ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]);;

(* Spiking at 0 and restricting: the integral of Phi mu over S is the      *)
(* integral of h over D cap S.                                              *)

let CMPB_SPIKE_INT = prove
 (`!(Phi:real^N->real) (mu:real^N->real) (h:real^N->real) D S.
        (!w. ~(w = vec 0) ==> Phi w * mu w = if w IN D then h w else &0)
        ==> ((\w. lift(Phi w * mu w)) integrable_on S <=>
             (\w. lift(h w)) integrable_on (D INTER S)) /\
            integral S (\w. lift(Phi w * mu w)) = integral (D INTER S) (\w. lift(h w))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_INTER; GSYM INTEGRAL_RESTRICT_INTER] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SPIKE_EQ; MATCH_MP_TAC INTEGRAL_SPIKE] THEN
  EXISTS_TAC `{vec 0:real^N}` THEN
  REWRITE_TAC[NEGLIGIBLE_SING; IN_DIFF; IN_SING] THEN
  X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LIFT_NUM]);;

(* The geometric facts: bounds and ray monotonicity of Phi, integrability  *)
(* of Phi mu_{-K} on B(0,R), and vol B(x,r) = int over B(0,r) of it.       *)

let CMPB_VOLUME_FACTS = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K R (Phi:real^N->real).
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\ &0 < R /\
        mfd_tball g x R SUBSET mfd_exp_dom (top,atlas) g x /\
        (!y v. y IN mfd_ball (top,atlas) g x R
               ==> --(&(dimindex(:N) - 1) * K) * (v dot (g y ** v)) <=
                   mfd_ricci atlas g y v v) /\
        (!w. Phi w =
             if w IN {w | ?s. &1 < s /\ norm(s % w) < R /\
                            mfd_dist (top,atlas) g x
                              (mfd_exp (top,atlas) g x (E ** (s % w))) = norm(s % w)}
             then sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
                  (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)
             else &0)
        ==> (!w. &0 <= Phi w /\ Phi w <= &1) /\
            (!w s. &0 < s /\ s <= &1 ==> Phi w <= Phi(s % w)) /\
            (\w. lift(Phi w * (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)))
            absolutely_integrable_on ball(vec 0,R) /\
            (!r v. &0 < r /\ r <= R /\
                   mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v
                   ==> v = drop(integral (ball(vec 0,r))
                             (\w. lift(Phi w * (cmp_sn (--K) (norm w) / norm w) pow
                                               (dimindex(:N) - 1)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP CMPB_PHI_FACTS th) THEN
                       MAP_EVERY ASSUME_TAC (butlast(CONJUNCTS th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "prod") ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`] CMPQ_SEG0_MEAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `R:real`] CMPQ_BALL_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "vol") THEN
  ABBREV_TAC `D0 = {w | ?s. &1 < s /\ norm(s % w) < R /\
                       mfd_dist (top,atlas) (g:A->real^N^N) x
                         (mfd_exp (top,atlas) g x ((E:real^N^N) ** (s % w))) =
                       norm(s % w)}` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\w:real^N. lift((cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)))
    absolutely_integrable_on ball(vec 0,R)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`--K:real`; `R:real`] CMPV_MODEL_INTEGRAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC CMPB_ABS_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC
     [`\w. sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w))`;
      `D0:real^N->bool`] THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; CMPB_MU_POS_LE] THEN
    MATCH_MP_TAC CMPB_SQRTDET_CONT THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `v:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Phi:real^N->real`;
                 `\w:real^N. (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)`;
                 `\w. sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N) w))`;
                 `D0:real^N->bool`; `ball(vec 0:real^N,r)`] CMPB_SPIKE_INT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w. lift((Phi:real^N->real) w * (cmp_sn (--K) (norm w) / norm w) pow
                                     (dimindex(:N) - 1))) integrable_on ball(vec 0,r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^N,R)` THEN
    ASM_SIMP_TAC[SUBSET_BALL; LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  USE_THEN "vol" (MP_TAC o SPEC `r:real`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_HAS_VOLUME_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `g:A->real^N^N`; `mfd_ball (top,atlas) (g:A->real^N^N) x r`] THEN
  ASM_REWRITE_TAC[]);;

let CMPB_RELVOL_MAIN = prove
 (`!top atlas (g:A->real^N^N) (x:A) K R r1 r2 v1 v2.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\ &0 <= K /\
        compact_in top (top closure_of mfd_ball (top,atlas) g x R) /\
        (!y w. y IN mfd_ball (top,atlas) g x R
               ==> --(&(dimindex(:N) - 1) * K) * (w dot (g y ** w)) <=
                   mfd_ricci atlas g y w w) /\
        &0 < r1 /\ r1 <= r2 /\ r2 <= R /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r1) v1 /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r2) v2
        ==> v2 * cmp_vmodel (:N) (--K) r1 <= v1 * cmp_vmodel (:N) (--K) r2 /\
            v1 <= cmp_vmodel (:N) (--K) r1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x R SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPQ_COMPACT_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  ABBREV_TAC
   `Phi = \w:real^N.
      if w IN {w | ?s. &1 < s /\ norm(s % w) < R /\
                     mfd_dist (top,atlas) (g:A->real^N^N) x
                       (mfd_exp (top,atlas) g x ((E:real^N^N) ** (s % w))) = norm(s % w)}
      then sqrt(det(cmp_expmetric (top,atlas) g x E w)) /
           (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)
      else &0` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `R:real`;
                 `Phi:real^N->real`] CMPB_VOLUME_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Phi" THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vol")))) THEN
  SUBGOAL_THEN `!t. &0 < t ==> &0 < cmp_sn (--K) t` (LABEL_TAC "sn") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r1 <= R` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift((Phi:real^N->real) w * (cmp_sn (--K) (norm w) / norm w) pow
                                     (dimindex(:N) - 1)))
    absolutely_integrable_on ball(vec 0,r1) /\
    (\w. lift(Phi w * (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1)))
    absolutely_integrable_on ball(vec 0,r2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^N,R)` THEN
    ASM_SIMP_TAC[SUBSET_BALL; LEBESGUE_MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v1 = drop(integral (ball(vec 0,r1))
           (\w. lift((Phi:real^N->real) w * (cmp_sn (--K) (norm w) / norm w) pow
                                             (dimindex(:N) - 1)))) /\
    v2 = drop(integral (ball(vec 0,r2))
           (\w. lift(Phi w * (cmp_sn (--K) (norm w) / norm w) pow (dimindex(:N) - 1))))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN USE_THEN "vol" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CMPV_RADIAL_COMPARE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`--K:real`; `r1:real`] CMPV_MODEL_INTEGRAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o AP_TERM `drop`)) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[CMPB_MU_POS_LE]]);;

(* S1, the statement CMP_RELVOL_STATEMENT of pc_cmp_defs. *)

let CMP_RELVOL = prove
 (`!(u:A->bool) (n:N->bool). CMP_RELVOL_STATEMENT u n`,
  REWRITE_TAC[CMP_RELVOL_STATEMENT; CMPB_RELVOL_MAIN]);;

