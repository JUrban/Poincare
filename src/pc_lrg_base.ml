(* ========================================================================= *)
(* Two pointwise estimates between nearby metrics on open subsets of real^3  *)
(* (local Riemannian geometry), the bodies of the statements                 *)
(* P2B_REQ_LRG_RM_NEAR_STATEMENT and P2B_REQ_LRG_BASE_STATEMENT of           *)
(* pc_p2b_defs (section S9), proved as closed theorems (pc_p2b_defs is not   *)
(* loaded):                                                                  *)
(*   LRG_RM_NEAR_BOUND (this file): the curvature tensor is bounded at       *)
(*     metrics that are C^2-close (lck_dist2 2 <= 1/4) to a metric with      *)
(*     bounded curvature;                                                    *)
(*   LRG_CK_BASE_CHANGE (pc_lrg_ckbase): change of the base metric of the    *)
(*     C^k distance.                                                         *)
(* The perturbation estimates follow pc_lrg_stab (LRG_PERT_G, LRG_PERT_T,    *)
(* LRG_PERT_L, LRG_RIEMANN_DIFF_Q), here without the smallness assumption    *)
(* delta <= 1/10 (delta <= 1/2 suffices for a bound).                        *)
(* ========================================================================= *)

needs "src/pc_lrg_stab.ml";;
needs "src/pc_rfa_rmderiv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Perturbation bounds in the frame norms of G0 for metrics G with |G - G0|, *)
(* |nabla h|, |nabla^2 h| at most delta <= 1/2 (no smallness as in           *)
(* pc_lrg_stab, only G >= G0 / 2): the difference of the Christoffel symbols *)
(* and of the curvature tensors; tensor norms from frame bounds.             *)
(* ========================================================================= *)

let GEOB_PERT_A = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &2 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3))
     ==> !a b. norm(M ** (christoffel G y a b - christoffel G0 y a b)) <=
               &3 * delta * norm(M ** a) * norm(M ** b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_T) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "T") THEN
  MATCH_MP_TAC LRG_QUAD_ROOT0 THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL; REAL_ARITH `&0 <= d ==> &0 <= &3 * d`] THEN
  USE_THEN "T" (MP_TAC o SPECL
    [`a:real^N`; `b:real^N`;
     `christoffel (G:real^N->real^N^N) y a b - christoffel G0 y a b`]) THEN
  USE_THEN "G1" (MP_TAC o SPEC
    `christoffel (G:real^N->real^N^N) y a b - christoffel G0 y a b`) THEN
  SUBGOAL_THEN
   `&0 <= (&1 / &2 - delta) *
          norm((M:real^N^N) **
               (christoffel (G:real^N->real^N^N) y a b - christoffel G0 y a b)) pow 2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let GEOB_PERT_ARITH1 = prove
 (`!d P l1 l2 g1 g2.
     &0 <= d /\ d <= &1 / &2 /\ &0 <= P /\
     abs l1 <= &3 / &2 * d * P /\ abs l2 <= &3 / &2 * d * P /\
     abs g1 <= (&1 + d) * (&9 * d pow 2 * P) /\
     abs g2 <= (&1 + d) * (&9 * d pow 2 * P)
     ==> abs(l1 - l2 + g1 - g2) <= &17 * d * P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d * P` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `d pow 2 * P <= &1 / &2 * (d * P)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d pow 3 * P <= &1 / &2 * (d pow 2 * P)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + d) * (&9 * d pow 2 * P) = &9 * (d pow 2 * P) + &9 * (d pow 3 * P)`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let GEOB_PERT_Q = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &2 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !u v w x.
           abs(x dot (G y ** (lriemann G y u v w - lriemann G0 y u v w))) <=
           &17 * delta * norm(M ** u) * norm(M ** v) * norm(M ** w) * norm(M ** x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] GEOB_PERT_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "A") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_L) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `u:real^N`; `v:real^N`; `w:real^N`; `x:real^N`]
         LRG_RIEMANN_DIFF_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC GEOB_PERT_ARITH1 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "L" (MP_TAC o SPECL [`v:real^N`; `w:real^N`; `x:real^N`; `u:real^N`]) THEN
    REAL_ARITH_TAC;
    USE_THEN "L" (MP_TAC o SPECL [`u:real^N`; `w:real^N`; `x:real^N`; `v:real^N`]) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + delta) *
                (&3 * delta * norm((M:real^N^N) ** u) * norm(M ** w)) *
                (&3 * delta * norm(M ** v) * norm(M ** x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_PERT_PROD THEN
      EXISTS_TAC `norm((M:real^N^N) **
                   (christoffel (G:real^N->real^N^N) y u w - christoffel G0 y u w))` THEN
      EXISTS_TAC `norm((M:real^N^N) **
                   (christoffel (G:real^N->real^N^N) y v x - christoffel G0 y v x))` THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= d ==> &0 <= &1 + d`];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + delta) *
                (&3 * delta * norm((M:real^N^N) ** v) * norm(M ** w)) *
                (&3 * delta * norm(M ** u) * norm(M ** x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_PERT_PROD THEN
      EXISTS_TAC `norm((M:real^N^N) **
                   (christoffel (G:real^N->real^N^N) y v w - christoffel G0 y v w))` THEN
      EXISTS_TAC `norm((M:real^N^N) **
                   (christoffel (G:real^N->real^N^N) y u x - christoffel G0 y u x))` THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= d ==> &0 <= &1 + d`];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING]]);;

let GEOB_PERT_R = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &2 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !u v w.
           norm(M ** (lriemann G y u v w - lriemann G0 y u v w)) <=
           &34 * delta * norm(M ** u) * norm(M ** v) * norm(M ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] GEOB_PERT_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "Q") THEN
  MATCH_MP_TAC LRG_QUAD_ROOT0 THEN REWRITE_TAC[NORM_POS_LE] THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Q" (MP_TAC o SPECL
    [`u:real^N`; `v:real^N`; `w:real^N`;
     `lriemann (G:real^N->real^N^N) y u v w - lriemann G0 y u v w`]) THEN
  USE_THEN "G1" (MP_TAC o SPEC
    `lriemann (G:real^N->real^N^N) y u v w - lriemann G0 y u v w`) THEN
  SUBGOAL_THEN
   `&0 <= (&1 / &2 - delta) *
          norm((M:real^N^N) **
               (lriemann (G:real^N->real^N^N) y u v w - lriemann G0 y u v w)) pow 2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* A (0,k)-tensor bounded by C in the frame norms of G (G y = M' M) has     *)
(* squared norm at most (number of index tuples) C^2.                       *)

let GEOB_LTNORM2_FRAME_LE = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (M:real^N^N) C.
     ltensor_field k U tf /\ y IN U /\ invertible M /\ G y = transp M ** M /\
     (!u. abs(tf y u) <= C * product(1..k) (\m. norm(M ** u m)))
     ==> ltnorm2 k G tf y <= &(CARD(index_tuples k (:N))) * C pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `matrix_inv((G:real^N->real^N^N) y) =
    transp(transp(matrix_inv(M:real^N^N))) ** transp(matrix_inv M)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[TRANSP_TRANSP; MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`;
                 `transp(matrix_inv(M:real^N^N))`] LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[TRANSP_TRANSP] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `p:num->num` THEN REWRITE_TAC[index_tuples; IN_ELIM_THM; IN_UNIV] THEN
  STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\m. matrix_inv(M:real^N^N) ** basis((p:num->num) m)`) THEN
  SUBGOAL_THEN
   `product(1..k) (\m. norm((M:real^N^N) ** (\m. matrix_inv M ** basis((p:num->num) m)) m)) =
    &1`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `product(1..k) (\m:num. &1)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[PRODUCT_ONE]] THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    MATCH_MP_TAC NORM_BASIS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* LRG_RM_NEAR_BOUND, the body of P2B_REQ_LRG_RM_NEAR_STATEMENT (pc_p2b_defs *)
(* S9).  At y take a frame M of G0 (G0 y = M' M).  The C^2                   *)
(* closeness gives |h|, |nabla h|, |nabla^2 h| <= 1/2 in the frame norms, so *)
(* |Rm(G) - Rm(G0)| <= 17 (GEOB_PERT_R with delta = 1/2) and |Rm(G0)| <=     *)
(* sqrt K0; then |lrm4 G| <= C in the frame norms of G0, its G0-norm is at   *)
(* most (number of tuples) C^2 (GEOB_LTNORM2_FRAME_LE), and G >= G0 / 2      *)
(* gives the G-norm within the factor 2^4 (LRG_LTNORM2_COMPARE).             *)
(* ========================================================================= *)

let GEOB_RM_NEAR_N = prove
 (`!K0. ?K. !s (G0:real^N->real^N^N) G y.
       metric_field s G0 /\ metric_field s G /\ y IN s /\
       lrm_deriv_norm2 0 G0 y <= K0 /\ lck_dist2 2 G0 G y <= &1 / &4
       ==> lrm_deriv_norm2 0 G y <= K`,
  GEN_TAC THEN
  EXISTS_TAC `&16 * &(CARD(index_tuples 4 (:N))) *
              (&3 / &2 * (sqrt(abs K0) + &17)) pow 2` THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`;
                       `G:real^N->real^N^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(&1 / &4) = &1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 2 (G0:real^N->real^N^N)
                    (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. abs(a dot ((G:real^N->real^N^N) y ** b) - a dot (G0 y ** b)) <=
          &1 / &2 * norm((M:real^N^N) ** a) * norm(M ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                   `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                   `&1 / &4`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lck_dist2 2 (G0:real^N->real^N^N) G y` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`2`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
      ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
      REWRITE_TAC[PRODUCT_2; lmetric2; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 2 (G0:real^N->real^N^N)
              (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u) y u) <=
        &1 / &2 * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 2 (G0:real^N->real^N^N)
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `&1 / &4`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 2 (G0:real^N->real^N^N) G y` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 3 (G0:real^N->real^N^N)
              (lnabla 2 G0
                (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u)) y u) <=
        &1 / &2 * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 3 (G0:real^N->real^N^N) (lnabla 2 G0
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u))`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `&1 / &4`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lck_dist2 2 (G0:real^N->real^N^N) G y` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lrm4 (G0:real^N->real^N^N) y u) <=
        sqrt(abs K0) * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lrm4 (G0:real^N->real^N^N)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `abs K0`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= k ==> x <= abs k`) THEN
    UNDISCH_TAC `lrm_deriv_norm2 0 (G0:real^N->real^N^N) y <= K0` THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `sqrt(abs K0)`] LRG_RM0_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; REAL_ABS_POS]; DISCH_THEN(LABEL_TAC "RM0")] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `&1 / &2`] GEOB_PERT_R) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "R")] THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `&1 / &2`] LRG_PERT_G) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  SUBGOAL_THEN
   `!u. abs(lrm4 (G:real^N->real^N^N) y u) <=
        (&3 / &2 * (sqrt(abs K0) + &17)) *
        product(1..4) (\m. norm((M:real^N^N) ** u m))`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num->real^N` THEN REWRITE_TAC[PRODUCT_4; lrm4] THEN
    SUBGOAL_THEN
     `norm((M:real^N^N) ** lriemann (G:real^N->real^N^N) y (u 1) (u 2) (u 4)) <=
      (sqrt(abs K0) + &17) *
      norm(M ** (u:num->real^N) 1) * norm(M ** u 2) * norm(M ** u 4)`
    ASSUME_TAC THENL
     [USE_THEN "RM0" (MP_TAC o SPECL
        [`(u:num->real^N) 1`; `(u:num->real^N) 2`; `(u:num->real^N) 4`]) THEN
      USE_THEN "R" (MP_TAC o SPECL
        [`(u:num->real^N) 1`; `(u:num->real^N) 2`; `(u:num->real^N) 4`]) THEN
      MP_TAC(ISPECL
        [`(M:real^N^N) ** lriemann (G0:real^N->real^N^N) y (u 1) (u 2) (u 4)`;
         `(M:real^N^N) ** (lriemann (G:real^N->real^N^N) y ((u:num->real^N) 1) (u 2) (u 4) -
                           lriemann G0 y (u 1) (u 2) (u 4))`] NORM_TRIANGLE) THEN
      REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ADD_LDISTRIB;
                  VECTOR_ARITH `a + (b - a):real^N = b`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &2) * norm((M:real^N^N) ** (u:num->real^N) 3) *
                norm(M ** lriemann (G:real^N->real^N^N) y (u 1) (u 2) (u 4))` THEN
    CONJ_TAC THENL
     [USE_THEN "G2" (MP_TAC o SPECL
        [`(u:num->real^N) 3`; `lriemann (G:real^N->real^N^N) y ((u:num->real^N) 1) (u 2) (u 4)`]) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + &1 / &2) * norm((M:real^N^N) ** (u:num->real^N) 3) *
                ((sqrt(abs K0) + &17) *
                 norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 4))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`; `lrm4 (G:real^N->real^N^N)`;
                 `y:real^N`; `M:real^N^N`; `&3 / &2 * (sqrt(abs K0) + &17)`]
         GEOB_LTNORM2_FRAME_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`; `G0:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`; `y:real^N`; `&2`] LRG_LTNORM2_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN
    USE_THEN "G1" (MP_TAC o SPEC `x:real^N`) THEN
    SUBGOAL_THEN `x dot ((G0:real^N->real^N^N) y ** x) = norm((M:real^N^N) ** x) pow 2`
    SUBST1_TAC THENL
     [REWRITE_TAC[NORM_POW_2] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LRG_FRAME_DOT THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
      REAL_ARITH_TAC];
    DISCH_TAC] THEN
  REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 pow 4 * ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G) y` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 pow 4 = &16` SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LRG_RM_NEAR_BOUND = prove
 (`!K0. ?K. !s (G0:real^3->real^3^3) G y.
       metric_field s G0 /\ metric_field s G /\ y IN s /\
       lrm_deriv_norm2 0 G0 y <= K0 /\ lck_dist2 2 G0 G y <= &1 / &4
       ==> lrm_deriv_norm2 0 G y <= K`,
  MATCH_ACCEPT_TAC GEOB_RM_NEAR_N);;

