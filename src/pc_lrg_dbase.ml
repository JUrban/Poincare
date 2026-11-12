(* ========================================================================= *)
(* LRG_DERIV_STABILITY (local Riemannian geometry), the body of the          *)
(* statement P2B_REQ_LRG_DERIV_STATEMENT (defined in pc_p2b_979s), proved as *)
(* a closed theorem: under C^4 closeness at a metric G0 with bounded Rm,     *)
(* nabla Rm, nabla^2 Rm, the squared norm of grad R, Lap R and the squared   *)
(* norm of Ric of G are close to those of G0.  Built on the change-of-base   *)
(* machinery of pc_lrg_ckbase and on the curvature-difference unit           *)
(* pc_p2c_cdiff.                                                             *)
(* ========================================================================= *)

needs "src/pc_lrg_ckbase.ml";;
needs "src/pc_p2c_cdiff.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Generic perturbation estimates at a point y, in a frame M of G0           *)
(* (G0 y = M' M) with |G - G0| <= delta in the frame norms: the norm of a    *)
(* tensor changes by a factor 1 + O(delta) (GEODB_LTNORM2_METRIC_PERT), the  *)
(* difference of two squared norms (GEODB_LTNORM2_DIFF_LE), and the          *)
(* contraction with G versus with G0 (GEODB_LTCONTR_PERT).                   *)
(* ========================================================================= *)

let GEODB_POW_PERT = prove
 (`!k x. &0 <= x /\ x <= &1 ==> (&1 + x) pow k - &1 <= &k * &2 pow k * x`,
  GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  INDUCT_TAC THENL [REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
  SUBGOAL_THEN `&1 <= (&1 + x) pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &2 pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x * ((&1 + x) pow k - &1) <= &1 * (&k * &2 pow k * x)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x * &1 <= x * &2 pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The norm of a fixed tensor under a small change of the metric. *)

let GEODB_LTNORM2_METRIC_PERT = prove
 (`!k s (G0:real^N->real^N^N) G y (M:real^N^N) delta X.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &2 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     ltensor_field k s X
     ==> abs(ltnorm2 k G X y - ltnorm2 k G0 X y) <=
         &k * &4 pow k * (&2 * delta) * ltnorm2 k G0 X y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  SUBGOAL_THEN `!x. x dot ((G0:real^N->real^N^N) y ** x) = norm((M:real^N^N) ** x) pow 2`
  (LABEL_TAC "D") THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LRG_FRAME_DOT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x dot ((G0:real^N->real^N^N) y ** x) <= (&1 + &2 * delta) * (x dot (G y ** x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN USE_THEN "D" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "G1" (MP_TAC o SPEC `x:real^N`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(&1 + &2 * delta) * ((&1 - delta) * norm((M:real^N^N) ** x) pow 2) <=
      (&1 + &2 * delta) * (x dot ((G:real^N->real^N^N) y ** x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= delta * (&1 - &2 * delta) * norm((M:real^N^N) ** x) pow 2`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x dot ((G:real^N->real^N^N) y ** x) <= (&1 + delta) * (x dot (G0 y ** x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN USE_THEN "D" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "G2" (MP_TAC o SPECL [`x:real^N`; `x:real^N`]) THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G:real^N->real^N^N`; `G0:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `y:real^N`; `&1 + &2 * delta`]
         LRG_LTNORM2_COMPARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `y:real^N`; `&1 + delta`]
         LRG_LTNORM2_COMPARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `&2 * delta`] GEODB_POW_PERT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `delta:real`] GEODB_POW_PERT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= ltnorm2 k (G0:real^N->real^N^N) X y /\ &0 <= ltnorm2 k G X y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + &2 * delta) pow k <= &2 pow k /\ &2 pow k <= &4 pow k /\
                &1 <= (&1 + delta) pow k /\ &2 pow k * &2 pow k = &4 pow k`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 pow k /\ &0 <= &4 pow k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `N0 = ltnorm2 k (G0:real^N->real^N^N) X y` THEN
  ABBREV_TAC `N1 = ltnorm2 k (G:real^N->real^N^N) X y` THEN
  ABBREV_TAC `p = (&1 + delta) pow k` THEN
  ABBREV_TAC `q = (&1 + &2 * delta) pow k` THEN
  ABBREV_TAC `t2 = &2 pow k` THEN
  ABBREV_TAC `t4 = &4 pow k` THEN
  SUBGOAL_THEN `&0 <= &k * t2 * delta /\ &0 <= &k * t4 * delta * N0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p - &1) * N1 <= (&k * t2 * delta) * (q * N0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&k * t2 * delta) * (q * N0) <= (&k * t2 * delta) * (t2 * N0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&k * t2 * delta) * (t2 * N0) = &k * t4 * delta * N0` ASSUME_TAC THENL
   [UNDISCH_TAC `t2 * t2 = t4` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q - &1) * N0 <= (&k * t2 * (&2 * delta)) * N0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&k * t2 * (&2 * delta)) * N0 <= (&k * t4 * (&2 * delta)) * N0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The difference of two squared norms, frame bounds for the first two slots *)
(* of a tensor, and the contraction of the first two slots with G versus     *)
(* with G0 (GEODB_LTCONTR_PERT): in the frame M of G0 the difference is the  *)
(* trace of x -> (G^-1 - G0^-1) B^T x, B the matrix of the first two slots,  *)
(* bounded with LRG_TRACE_FRAME_BOUND and LRG_ENDO_BOUND.                    *)
(* ========================================================================= *)

let GEODB_LTNORM2_DIFF_LE = prove
 (`!k U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B y.
     metric_field U G /\ y IN U /\ ltensor_field k U A /\ ltensor_field k U B
     ==> abs(ltnorm2 k G A y - ltnorm2 k G B y) <=
         sqrt(ltnorm2 k G (\z u. A z u - B z u) y) *
         (sqrt(ltnorm2 k G A y) + sqrt(ltnorm2 k G B y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ltensor_field k U (\z u. (A:real^N->(num->real^N)->real) z u - B z u) /\
                ltensor_field k U (\z u. (B:real^N->(num->real^N)->real) z u - A z u)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 k (G:real^N->real^N^N) (\z u. (B:real^N->(num->real^N)->real) z u - A z u) y =
    ltnorm2 k G (\z u. A z u - B z u) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltnorm2 k (G:real^N->real^N^N)
                  (\z u. --(&1) * ((A:real^N->(num->real^N)->real) z u - B z u)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[LRG_LTNORM2_CMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z u. (A:real^N->(num->real^N)->real) z u - B z u`;
                 `B:real^N->(num->real^N)->real`; `A:real^N->(num->real^N)->real`;
                 `y:real^N`] LRG_LTNORM2_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`;
                 `\z u. (B:real^N->(num->real^N)->real) z u - A z u`;
                 `B:real^N->(num->real^N)->real`;
                 `y:real^N`] LRG_LTNORM2_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= ltnorm2 k (G:real^N->real^N^N) A y /\ &0 <= ltnorm2 k G B y /\
    &0 <= ltnorm2 k G (\z u. (A:real^N->(num->real^N)->real) z u - B z u) y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `ltnorm2 k (G:real^N->real^N^N) A y` SQRT_POW_2) THEN
  MP_TAC(SPEC `ltnorm2 k (G:real^N->real^N^N) B y` SQRT_POW_2) THEN
  MP_TAC(SPEC `ltnorm2 k (G:real^N->real^N^N) A y` SQRT_POS_LE) THEN
  MP_TAC(SPEC `ltnorm2 k (G:real^N->real^N^N) B y` SQRT_POS_LE) THEN
  MP_TAC(SPEC `ltnorm2 k (G:real^N->real^N^N)
                 (\z u. (A:real^N->(num->real^N)->real) z u - B z u) y` SQRT_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = sqrt(ltnorm2 k (G:real^N->real^N^N) A y)` THEN
  ABBREV_TAC `b = sqrt(ltnorm2 k (G:real^N->real^N^N) B y)` THEN
  ABBREV_TAC `c = sqrt(ltnorm2 k (G:real^N->real^N^N)
                        (\z u. (A:real^N->(num->real^N)->real) z u - B z u) y)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (c - (a - b)) * (a + b) /\ &0 <= (c + (a - b)) * (a + b)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Frame bound for a tensor with its first two slots singled out. *)

let GEODB_PRODUCT_TUPLE2 = prove
 (`!k (M:real^N^N) (v:real^N) w (u:num->real^N).
     product(1..k + 2)
       (\m. norm(M ** (if m = 1 then v else if m = 2 then w else u(m - 2)))) =
     norm(M ** v) * norm(M ** w) * product(1..k) (\m. norm(M ** u m))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`\m. norm((M:real^N^N) ** (if m = 1 then v else if m = 2 then w
                               else (u:num->real^N)(m - 2)))`; `1`; `k + 2`]
   PRODUCT_CLAUSES_LEFT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= k + 2`] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\m. norm((M:real^N^N) ** (if m = 1 then v else if m = 2 then w
                               else (u:num->real^N)(m - 2)))`; `1 + 1`; `k + 2`]
   PRODUCT_CLAUSES_LEFT) THEN
  REWRITE_TAC[ARITH_RULE `1 + 1 <= k + 2`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `(1 + 1) + 1 = 1 + 2`; PRODUCT_OFFSET] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i + 2 = 1) /\ ~(i + 2 = 2) /\ (i + 2) - 2 = i`]);;

let GEODB_FRAME_BIL = prove
 (`!k U (G:real^N->real^N^N) (X:real^N->(num->real^N)->real) y (M:real^N^N) v w u.
     metric_field U G /\ ltensor_field (k + 2) U X /\ y IN U /\ G y = transp M ** M
     ==> abs(X y (\m. if m = 1 then v else if m = 2 then w else u(m - 2))) <=
         sqrt(ltnorm2 (k + 2) G X y) *
         norm(M ** v) * norm(M ** w) * product(1..k) (\m. norm(M ** u m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k + 2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `X:real^N->(num->real^N)->real`; `y:real^N`; `M:real^N^N`;
                 `\m. if m = 1 then (v:real^N) else if m = 2 then w
                      else (u:num->real^N)(m - 2)`] LRG_TENSOR_FRAME_BOUND) THEN
  ASM_REWRITE_TAC[GEODB_PRODUCT_TUPLE2]);;

(* Expansion of a tensor in its first and in its second slot. *)

let GEODB_SLOT_EXPAND12 = prove
 (`!k U (X:real^N->(num->real^N)->real) y (u:num->real^N) p q.
     ltensor_field (k + 2) U X /\ y IN U
     ==> X y (\m. if m = 1 then p else if m = 2 then q else u(m - 2)) =
         sum(1..dimindex(:N))
           (\a. p$a * X y (\m. if m = 1 then basis a else if m = 2 then q else u(m - 2))) /\
         X y (\m. if m = 1 then p else if m = 2 then q else u(m - 2)) =
         sum(1..dimindex(:N))
           (\b. q$b * X y (\m. if m = 1 then p else if m = 2 then basis b else u(m - 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ltensor_field]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "lin" o CONJUNCT2) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(X:real^N->(num->real^N)->real) y`; `1`;
                   `\m. if m = 1 then (p:real^N) else if m = 2 then q
                        else (u:num->real^N)(m - 2)`; `p:real^N`] LRG_SLOT_EXPAND) THEN
    ANTS_TAC THENL
     [USE_THEN "lin" (MP_TAC o SPECL [`1`; `\m. if m = 1 then (p:real^N) else if m = 2 then q
                                              else (u:num->real^N)(m - 2)`]) THEN
      REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= k + 2`];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `(a:real) = a' /\ (b:real) = b' ==> a = b ==> a' = b'`) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
      ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
      ASM_CASES_TAC `j = 2` THEN ASM_REWRITE_TAC[ARITH];
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `j:num` THEN
      ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
      ASM_CASES_TAC `j = 2` THEN ASM_REWRITE_TAC[ARITH]];
    MP_TAC(ISPECL [`(X:real^N->(num->real^N)->real) y`; `2`;
                   `\m. if m = 1 then (p:real^N) else if m = 2 then q
                        else (u:num->real^N)(m - 2)`; `q:real^N`] LRG_SLOT_EXPAND) THEN
    ANTS_TAC THENL
     [USE_THEN "lin" (MP_TAC o SPECL [`2`; `\m. if m = 1 then (p:real^N) else if m = 2 then q
                                              else (u:num->real^N)(m - 2)`]) THEN
      REWRITE_TAC[ARITH_RULE `1 <= 2 /\ 2 <= k + 2`];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `(a:real) = a' /\ (b:real) = b' ==> a = b ==> a' = b'`) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
      ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
      ASM_CASES_TAC `j = 2` THEN ASM_REWRITE_TAC[ARITH];
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
      BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `j:num` THEN
      ASM_CASES_TAC `j = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
      ASM_CASES_TAC `j = 2` THEN ASM_REWRITE_TAC[ARITH]]]);;

(* The two bilinear slot identities: z . (B^T x) = B(x, z). *)

let GEODB_SLOT12_DOT = prove
 (`!k U (X:real^N->(num->real^N)->real) y (u:num->real^N) x z.
     ltensor_field (k + 2) U X /\ y IN U
     ==> z dot
         (transp((lambda a b. X y (\m. if m = 1 then basis a else if m = 2 then basis b
                                       else u(m - 2))):real^N^N) ** x) =
         X y (\m. if m = 1 then x else if m = 2 then z else u(m - 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `X:real^N->(num->real^N)->real`; `y:real^N`;
                 `u:num->real^N`] GEODB_SLOT_EXPAND12) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "s12") THEN
  REWRITE_TAC[dot] THEN
  USE_THEN "s12" (fun th -> GEN_REWRITE_TAC RAND_CONV
    [CONJUNCT2(SPECL [`x:real^N`; `z:real^N`] th)]) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; ASSUME `1 <= b`; ASSUME `b <= dimindex(:N)`] THEN
  REWRITE_TAC[dot; TRANSP_COMPONENT] THEN
  USE_THEN "s12" (fun th -> GEN_REWRITE_TAC RAND_CONV
    [CONJUNCT1(SPECL [`x:real^N`; `basis b:real^N`] th)]) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SIMP_TAC[LAMBDA_BETA; ASSUME `1 <= a`; ASSUME `a <= dimindex(:N)`;
           ASSUME `1 <= b`; ASSUME `b <= dimindex(:N)`] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Contraction of the first two slots with G versus with G0.  In the frame M *)
(* of G0 the difference at (y, u) is the trace of x -> (G^-1 - G0^-1) B' x,  *)
(* B the matrix of the first two slots; and                                  *)
(*   (G^-1 - G0^-1) b = G^-1 (G0 - G) G0^-1 b,                               *)
(* bounded with LRG_ENDO_BOUND.                                              *)
(* ========================================================================= *)

let GEODB_LTCONTR_PERT = prove
 (`!k s (G0:real^N->real^N^N) G y (M:real^N^N) delta X.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     G0 y = transp M ** M /\ invertible M /\
     &0 <= delta /\ delta <= &1 / &10 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     ltensor_field (k + 2) s X
     ==> ltnorm2 k G0 (\z u. ltcontr G X z u - ltcontr G0 X z u) y <=
         &(CARD(index_tuples k (:N))) *
         (&(dimindex(:N)) * (&100 / &81 * delta * sqrt(ltnorm2 (k + 2) G0 X y))) pow 2`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(G0:real^N->real^N^N) y = transp (M:real^N^N) ** M` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MATCH_MP_TAC GEOB_LTNORM2_FRAME_LE THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `M:real^N^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
    MATCH_MP_TAC RFA_LTCONTR_FIELD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:num->real^N` THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "G1" o CONJUNCT1)] THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y) /\ invertible((G0:real^N->real^N^N) y)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ABBREV_TAC
   `Bm = (lambda a b. (X:real^N->(num->real^N)->real) y
            (\m. if m = 1 then basis a else if m = 2 then basis b
                 else (u:num->real^N)(m - 2))):real^N^N` THEN
  ABBREV_TAC `Dm = matrix_inv((G:real^N->real^N^N) y) - matrix_inv((G0:real^N->real^N^N) y)` THEN
  SUBGOAL_THEN
   `ltcontr (G:real^N->real^N^N) X y u - ltcontr G0 X y u =
    sum(1..dimindex(:N)) (\i. (((Dm:real^N^N) ** transp (Bm:real^N^N)) ** basis i)$i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LRG_TRACE_BASIS; trace; ltcontr] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SIMP_TAC[matrix_mul; LAMBDA_BETA; ASSUME `1 <= i`; ASSUME `i <= dimindex(:N)`] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    EXPAND_TAC "Dm" THEN EXPAND_TAC "Bm" THEN
    SIMP_TAC[MATRIX_SUB_COMPONENT; TRANSP_COMPONENT; LAMBDA_BETA;
             ASSUME `1 <= i`; ASSUME `i <= dimindex(:N)`;
             ASSUME `1 <= j`; ASSUME `j <= dimindex(:N)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D0 = sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) X y)` THEN
  ABBREV_TAC `P = product(1..k) (\m. norm((M:real^N^N) ** (u:num->real^N) m))` THEN
  SUBGOAL_THEN `&0 <= D0 /\ &0 <= P` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN EXPAND_TAC "P" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC LTNORM2_POS THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v w. abs((X:real^N->(num->real^N)->real) y
                (\m. if m = 1 then v else if m = 2 then w else (u:num->real^N)(m - 2))) <=
          D0 * norm((M:real^N^N) ** v) * norm(M ** w) * P`
  (LABEL_TAC "fb") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "D0" THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC GEODB_FRAME_BIL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x z. z dot (transp (Bm:real^N^N) ** x) =
                      (X:real^N->(num->real^N)->real) y
                        (\m. if m = 1 then x else if m = 2 then z else (u:num->real^N)(m - 2))`
  (LABEL_TAC "dot") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "Bm" THEN MATCH_MP_TAC GEODB_SLOT12_DOT THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(dimindex(:N)) * (&100 / &81 * delta * D0 * P)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING] THEN
  MP_TAC(ISPECL [`\x:real^N. ((Dm:real^N^N) ** transp (Bm:real^N^N)) ** x`; `M:real^N^N`;
                 `&100 / &81 * delta * D0 * P`] LRG_TRACE_FRAME_BOUND) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN
  ABBREV_TAC `be = transp (Bm:real^N^N) ** (x:real^N)` THEN
  ABBREV_TAC `w = matrix_inv((G0:real^N->real^N^N) y) ** be` THEN
  SUBGOAL_THEN
   `((Dm:real^N^N) ** transp (Bm:real^N^N)) ** (x:real^N) =
    matrix_inv((G:real^N->real^N^N) y) ** ((G0:real^N->real^N^N) y ** (w:real^N) - G y ** w)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(G0:real^N->real^N^N) y ** (w:real^N) = be /\
      matrix_inv((G:real^N->real^N^N) y) ** (G y ** w) = w`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID; MATRIX_MUL_LID;
               ASSUME `invertible((G:real^N->real^N^N) y)`;
               ASSUME `invertible((G0:real^N->real^N^N) y)`];
      ALL_TAC] THEN
    EXPAND_TAC "Dm" THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC;
                ASSUME `transp (Bm:real^N^N) ** (x:real^N) = be`] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G0:real^N->real^N^N) y`; `M:real^N^N`; `be:real^N`; `&0`;
                 `D0 * P * norm((M:real^N^N) ** x)`] LRG_ENDO_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASSUME `invertible((G0:real^N->real^N^N) y)`] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[NORM_POS_LE];
      X_GEN_TAC `z:real^N` THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID] THEN
      SUBGOAL_THEN `z dot ((G0:real^N->real^N^N) y ** z) = norm((M:real^N^N) ** z) pow 2`
      SUBST1_TAC THENL
       [REWRITE_TAC[NORM_POW_2] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC LRG_FRAME_DOT THEN ASM_REWRITE_TAC[];
        REAL_ARITH_TAC];
      X_GEN_TAC `z:real^N` THEN EXPAND_TAC "be" THEN
      USE_THEN "dot" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "fb" (MP_TAC o SPECL [`x:real^N`; `z:real^N`]) THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN CONV_TAC REAL_RING];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `M:real^N^N`;
                 `(G0:real^N->real^N^N) y ** (w:real^N) - G y ** w`; `delta:real`;
                 `delta * norm((M:real^N^N) ** (w:real^N))`] LRG_ENDO_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[DOT_RSUB] THEN
    UNDISCH_TAC
     `!a b. abs(a dot ((G:real^N->real^N^N) y ** b) - a dot (G0 y ** b)) <=
            delta * norm((M:real^N^N) ** a) * norm(M ** b)` THEN
    DISCH_THEN(MP_TAC o SPECL [`z:real^N`; `w:real^N`]) THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&10 / &9 * delta * norm((M:real^N^N) ** (w:real^N))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&10 / &9 * delta * (&10 / &9 * (D0 * P * norm((M:real^N^N) ** x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING]);;

(* ========================================================================= *)
(* The first two covariant derivatives of the curvature of G versus those of *)
(* G0, for G0 with bounded Rm, nabla Rm, nabla^2 Rm (the general case of     *)
(* P2C_DRM_IDS and P2C_DRM_BOUNDS of pc_p2c_cdiff, which assume              *)
(* nabla Rm(G0) = 0).  E = Rm(G) - Rm(G0), A = p2c_af G0 G:                  *)
(*   nabla_G Rm(G) - nabla_G0 Rm(G0) = nabla_G0 E - ins4(Rm(G), A),          *)
(*   nabla_G^2 Rm(G) - nabla_G0^2 Rm(G0) =                                    *)
(*     nabla_G0^2 E - nabla_G0 ins4(Rm(G), A) - ins5(nabla_G Rm(G), A).       *)
(* ========================================================================= *)

let GEODB_DRM_IDS = prove
 (`!s (G0:real^N->real^N^N) G.
     metric_field s G0 /\ metric_field s G
     ==> (!z u. z IN s ==>
            lnabla 4 G (lrm4 G) z u - lnabla 4 G0 (lrm4 G0) z u =
            lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) z u -
            p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) z u) /\
         (!z u. z IN s ==>
            lnabla 5 G (lnabla 4 G (lrm4 G)) z u -
            lnabla 5 G0 (lnabla 4 G0 (lrm4 G0)) z u =
            (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) z u -
             lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) z u) -
            p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G) z u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_RMD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_INS4_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lrm4 (G:real^N->real^N^N) z u - lrm4 G0 z u`]
                LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G0:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z u. z IN s ==>
       lnabla 4 G (lrm4 G) z u =
       (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) z u + lnabla 4 G0 (lrm4 G0) z u) -
       p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) (z:real^N) u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`; `z:real^N`; `u:num->real^N`]
                  P2C_CONN_DIFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `z:real^N`; `u:num->real^N`] P2C_NABLA_T_SPLIT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`5`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `z:real^N`; `u:num->real^N`]
                P2C_CONN_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `lnabla 5 (G0:real^N->real^N^N) (lnabla 4 G (lrm4 G)) z u =
    lnabla 5 G0
      (\y u. (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y u +
              lnabla 4 G0 (lrm4 G0) y u) -
             p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) y u) z u`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!X (v:num->real^N).
        (!u. smooth_map_on s (\y. lift((X:real^N->(num->real^N)->real) y u)))
        ==> (\x. lift(X x v)) differentiable at (z:real^N)`
  (LABEL_TAC "dif") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`5`; `G0:real^N->real^N^N`;
    `\y u. lnabla 4 G0 (\z u. lrm4 (G:real^N->real^N^N) z u - lrm4 G0 z u) y u +
           lnabla 4 G0 (lrm4 G0) y u`;
    `p2c_ins 4 G0 (lrm4 G) (p2c_af G0 (G:real^N->real^N^N))`;
    `z:real^N`; `u:num->real^N`] LRG_LNABLA_SUB)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC DIFFERENTIABLE_ADD THEN CONJ_TAC;
      ALL_TAC] THEN
    USE_THEN "dif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`5`; `G0:real^N->real^N^N`;
    `lnabla 4 G0 (\z u. lrm4 (G:real^N->real^N^N) z u - lrm4 G0 z u)`;
    `lnabla 4 G0 (lrm4 (G0:real^N->real^N^N))`;
    `z:real^N`; `u:num->real^N`] LRG_LNABLA_ADD)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN USE_THEN "dif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC);;

(* The arithmetic of the bounds. *)

let GEODB_DRM_ARITH = prove
 (`!d K CE Ci4 Di4 Ci5 E1 E2 A0 A1 R1 TT NT NG I4 DI4 I5 D1 D2.
     &0 <= CE /\ &0 <= Ci4 /\ &0 <= Di4 /\ &0 <= Ci5 /\ &0 <= d /\ d <= &1 /\
     &0 <= K /\ &0 <= A0 /\ &0 <= A1 /\ &0 <= TT /\ &0 <= NT /\ &0 <= NG /\
     E1 <= CE * d /\ E2 <= CE * d /\ A0 <= &12 * d /\ A1 <= &24 * d /\ R1 <= K /\
     TT <= &2 * CE + &2 * K /\ NT <= &2 * CE + &2 * K /\
     I4 <= Ci4 * TT * A0 /\ D1 <= &2 * E1 + &2 * I4 /\ NG <= &2 * D1 + &2 * R1 /\
     DI4 <= Di4 * (NT * A0 + TT * A1) /\ I5 <= Ci5 * NG * A0 /\
     D2 <= &2 * (&2 * E2 + &2 * DI4) + &2 * I5
     ==> D1 <= (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)) * d /\
         D2 <= (&4 * CE + &144 * Di4 * (&2 * CE + &2 * K) +
                &24 * Ci5 * (&2 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)) + &2 * K)) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = &2 * CE + &2 * K` THEN
  ABBREV_TAC `M1 = &2 * CE + &24 * Ci4 * B` THEN
  ABBREV_TAC `B2 = &2 * M1 + &2 * K` THEN
  SUBGOAL_THEN `&0 <= B /\ &0 <= M1 /\ &0 <= B2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B2"; "M1"; "B"] THEN
    SUBGOAL_THEN `&0 <= Ci4 * (&2 * CE + &2 * K)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `I4 <= Ci4 * (B * (&12 * d))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ci4 * TT * A0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `D1 <= M1 * d` ASSUME_TAC THENL
   [EXPAND_TAC "M1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M1 * d <= M1` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `NG <= B2` ASSUME_TAC THENL
   [EXPAND_TAC "B2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `DI4 <= Di4 * (B * (&12 * d) + B * (&24 * d))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Di4 * (NT * A0 + TT * A1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `I5 <= Ci5 * (B2 * (&12 * d))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ci5 * NG * A0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `D2 <= &2 * (&2 * E2 + &2 * DI4) + &2 * I5` THEN
  UNDISCH_TAC `DI4 <= Di4 * (B * (&12 * d) + B * (&24 * d))` THEN
  UNDISCH_TAC `I5 <= Ci5 * (B2 * (&12 * d))` THEN
  UNDISCH_TAC `E2 <= CE * d` THEN
  CONV_TAC REAL_ARITH);;

(* The bounds: the differences of nabla Rm and nabla^2 Rm are O(d). *)

let GEODB_DRM_BOUNDS = prove
 (`!K. ?C. &0 < C /\
     !s (G0:real^N->real^N^N) G y d.
       metric_field s G0 /\ metric_field s G /\ y IN s /\ C * d <= &1 /\
       (!l. l <= 4 ==> ltnorm2 (2 + l) G0 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <= d) /\
       ltnorm2 4 G0 (lrm4 G0) y <= K /\
       ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G0)) y <= K /\
       ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (lrm4 G0))) y <= K
       ==> ltnorm2 5 G0 (\z u. lnabla 4 G (lrm4 G) z u - lnabla 4 G0 (lrm4 G0) z u) y
           <= C * d /\
           ltnorm2 6 G0 (\z u. lnabla 5 G (lnabla 4 G (lrm4 G)) z u -
                               lnabla 5 G0 (lnabla 4 G0 (lrm4 G0)) z u) y <= C * d`,
  GEN_TAC THEN
  X_CHOOSE_THEN `Caf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "af"))
   (INST_TYPE [`:N`,`:N`] P2C_AF_BOUNDS) THEN
  X_CHOOSE_THEN `CE:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rmd"))
   (SPEC `K:real` (INST_TYPE [`:N`,`:N`] P2C_RMD_BOUNDS)) THEN
  X_CHOOSE_THEN `Ci4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ni4"))
   (MATCH_MP RFA_LBILIN_ON_NORM (INST_TYPE [`:N`,`:N`] P2C_INS4_LBILIN)) THEN
  X_CHOOSE_THEN `Di4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "di4"))
   (CONV_RULE NUM_REDUCE_CONV
     (MATCH_MP P2C_LBILIN_ON_DNORM (INST_TYPE [`:N`,`:N`] P2C_INS4_LBILIN))) THEN
  X_CHOOSE_THEN `Ci5:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ni5"))
   (MATCH_MP RFA_LBILIN_ON_NORM (INST_TYPE [`:N`,`:N`] P2C_INS5_LBILIN)) THEN
  ABBREV_TAC `M1 = &2 * CE + &24 * Ci4 * (&2 * CE + &2 * abs K)` THEN
  ABBREV_TAC `M2 = &4 * CE + &144 * Di4 * (&2 * CE + &2 * abs K) +
                   &24 * Ci5 * (&2 * M1 + &2 * abs K)` THEN
  SUBGOAL_THEN `&0 <= M1 /\ &0 <= M2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["M2"; "M1"] THEN
    MP_TAC(SPEC `K:real` REAL_ABS_POS) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= Ci4 * (&2 * CE + &2 * abs K)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= Di4 * (&2 * CE + &2 * abs K) /\
      &0 <= Ci5 * (&2 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * abs K)) + &2 * abs K)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `Caf + CE + &1 + M1 + M2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                       `y:real^N`; `d:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G0:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  UNDISCH_TAC `!l. l <= 4 ==> ltnorm2 (2 + l) (G0:real^N->real^N^N)
                                 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <= d` THEN
  DISCH_THEN(LABEL_TAC "dist") THEN
  (* fields *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_HD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_AF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                P2C_RMD_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_INS4_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lrm4 (G:real^N->real^N^N) z u - lrm4 G0 z u`] P2C_FIELD_D2) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G0:real^N->real^N^N)`] P2C_FIELD_D2) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`5`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_ins 4 G0 (lrm4 G) (p2c_af G0 (G:real^N->real^N^N))`]
                LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `p2c_af G0 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `p2c_af G0 (G:real^N->real^N^N)`]
         (MATCH_MP P2C_LBILIN_ON_SMOOTH P2C_INS5_LBILIN)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the identities *)
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
                GEODB_DRM_IDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "i1") (LABEL_TAC "i2")) THEN
  (* distance terms *)
  USE_THEN "dist" (fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
                             MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th) THEN
                             MP_TAC(SPEC `4` th)) THEN
  REWRITE_TAC[lnabla_iter; LRG_LNABLA_ITER_12; P2C_LNABLA_ITER_3; P2C_LNABLA_ITER_4] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  (* nonnegativity *)
  SUBGOAL_THEN
   `&0 <= ltnorm2 2 (G0:real^N->real^N^N) (p2c_hd G0 G) y /\
    &0 <= ltnorm2 4 G0 (lrm4 G0) y /\
    &0 <= ltnorm2 3 G0 (p2c_af G0 G) y /\
    &0 <= ltnorm2 4 G0 (lnabla 3 G0 (p2c_af G0 G)) y /\
    &0 <= ltnorm2 4 G0 (lrm4 G) y /\
    &0 <= ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G)) y /\
    &0 <= ltnorm2 5 G0 (lnabla 4 G (lrm4 G)) y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d /\ &0 <= K` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs K = K` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `d <= &1 /\ Caf * d <= &1 /\ CE * d <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Caf * d /\ &0 <= CE * d /\ &0 <= M1 * d /\ &0 <= M2 * d` MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(Caf + CE + &1 + M1 + M2) * d <= &1` THEN UNDISCH_TAC `&0 <= d` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* E bounds *)
  USE_THEN "rmd" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                  `G:real^N->real^N^N`; `y:real^N`; `d:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "dist" ACCEPT_TAC; STRIP_TAC] THEN
  (* af bounds *)
  USE_THEN "af" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                 `G:real^N->real^N^N`; `y:real^N`; `d:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN USE_THEN "dist" MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    STRIP_TAC] THEN
  (* |Rm(G)|^2 and |nabla_G0 Rm(G)|^2 *)
  SUBGOAL_THEN
   `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G) y <=
    &2 * ltnorm2 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y + &2 * ltnorm2 4 G0 (lrm4 G0) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 4 (G0:real^N->real^N^N)
                  (\y u. (\z u. lrm4 G z u - lrm4 G0 z u) y u + lrm4 G0 y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lrm4 G)) y <=
    &2 * ltnorm2 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y +
    &2 * ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G0)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 5 (G0:real^N->real^N^N)
                  (\y u. lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y u +
                         lnabla 4 G0 (lrm4 G0) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC P2C_NABLA_T_SPLIT THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Ins bounds *)
  USE_THEN "ni4" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "di4" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `lrm4 (G:real^N->real^N^N)`; `p2c_af G0 (G:real^N->real^N^N)`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "ni5" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
     `lnabla 4 G (lrm4 (G:real^N->real^N^N))`; `p2c_af G0 (G:real^N->real^N^N)`;
     `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* D1 by the first identity *)
  SUBGOAL_THEN
   `ltnorm2 5 (G0:real^N->real^N^N)
      (\z u. lnabla 4 G (lrm4 G) z u - lnabla 4 G0 (lrm4 G0) z u) y <=
    &2 * ltnorm2 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y +
    &2 * ltnorm2 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 5 (G0:real^N->real^N^N)
        (\y u. lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u) y u -
               p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "i1" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* |nabla_G Rm(G)|^2 <= 2 D1 + 2 |nabla Rm(G0)|^2 *)
  MP_TAC(ISPECL [`5`; `s:real^N->bool`; `lnabla 4 G (lrm4 (G:real^N->real^N^N))`;
                 `lnabla 4 G0 (lrm4 (G0:real^N->real^N^N))`] P2C_FIELD_ADD_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G (lrm4 G)) y <=
    &2 * ltnorm2 5 G0 (\z u. lnabla 4 G (lrm4 G) z u - lnabla 4 G0 (lrm4 G0) z u) y +
    &2 * ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G0)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 5 (G0:real^N->real^N^N)
        (\y u. (\z u. lnabla 4 G (lrm4 G) z u - lnabla 4 G0 (lrm4 G0) z u) y u +
               lnabla 4 G0 (lrm4 G0) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_LTNORM2_ADD_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* D2 by the second identity *)
  MP_TAC(ISPECL [`6`; `s:real^N->bool`;
                 `lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 (G:real^N->real^N^N) z u -
                                                   lrm4 G0 z u))`;
                 `lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 (G:real^N->real^N^N)))`]
                P2C_FIELD_ADD_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltnorm2 6 (G0:real^N->real^N^N)
      (\z u. lnabla 5 G (lnabla 4 G (lrm4 G)) z u -
             lnabla 5 G0 (lnabla 4 G0 (lrm4 G0)) z u) y <=
    &2 * (&2 * ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u))) y +
          &2 * ltnorm2 6 G0 (lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G))) y) +
    &2 * ltnorm2 6 G0 (p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G)) y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `ltnorm2 6 (G0:real^N->real^N^N)
        (\y u. (\y u. lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y u -
                      lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y u) y u -
               p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G) y u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN USE_THEN "i2" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `&2 * ltnorm2 6 (G0:real^N->real^N^N)
               (\y u. lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y u -
                      lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y u) y +
        &2 * ltnorm2 6 G0 (p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G)) y` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> &2 * a + c <= &2 * b + c`) THEN
        MATCH_MP_TAC P2C_LTNORM2_SUB_LE THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* arithmetic *)
  SUBGOAL_THEN `CE * d <= CE` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`d:real`; `K:real`; `CE:real`; `Ci4:real`; `Di4:real`; `Ci5:real`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u)) y`;
    `ltnorm2 6 (G0:real^N->real^N^N)
       (lnabla 5 G0 (lnabla 4 G0 (\z u. lrm4 G z u - lrm4 G0 z u))) y`;
    `ltnorm2 3 (G0:real^N->real^N^N) (p2c_af G0 G) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lnabla 3 G0 (p2c_af G0 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lrm4 G0)) y`;
    `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G0 (lrm4 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (lnabla 4 G (lrm4 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N) (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G)) y`;
    `ltnorm2 6 (G0:real^N->real^N^N) (lnabla 5 G0 (p2c_ins 4 G0 (lrm4 G) (p2c_af G0 G))) y`;
    `ltnorm2 6 (G0:real^N->real^N^N) (p2c_ins 5 G0 (lnabla 4 G (lrm4 G)) (p2c_af G0 G)) y`;
    `ltnorm2 5 (G0:real^N->real^N^N)
       (\z u. lnabla 4 G (lrm4 G) z u - lnabla 4 G0 (lrm4 G0) z u) y`;
    `ltnorm2 6 (G0:real^N->real^N^N)
       (\z u. lnabla 5 G (lnabla 4 G (lrm4 G)) z u -
              lnabla 5 G0 (lnabla 4 G0 (lrm4 G0)) z u) y`]
   GEODB_DRM_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["M2"; "M1"] THEN
  STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `(&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)) * d`;
    EXISTS_TAC `(&4 * CE + &144 * Di4 * (&2 * CE + &2 * K) +
                 &24 * Ci5 * (&2 * (&2 * CE + &24 * Ci4 * (&2 * CE + &2 * K)) + &2 * K)) * d`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`&0 <= M1`; `&0 <= M2`] THEN
  MAP_EVERY EXPAND_TAC ["M2"; "M1"] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Propagation of errors through contractions and slot permutations, in      *)
(* square-root norms of G0.  If Y is within ce rho of Z and |Z| <= bz, then  *)
(* contracting Y with G and Z with G0 gives tensors within (cK (bz + ce) +   *)
(* sqrt N ce) rho (GEODB_CHAIN_STEP), where delta <= rho is the frame        *)
(* closeness of G to G0.  GEODB_QUAD_FINAL compares the squared norms        *)
(* |W|_G^2 and |W0|_G0^2 at the end of a chain.                              *)
(* ========================================================================= *)

let GEODB_SQRT_LE_MUL = prove
 (`!x c a. x <= c * a pow 2 /\ &0 <= c /\ &0 <= a ==> sqrt x <= sqrt c * a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(c * a pow 2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SQRT_MUL] THEN ASM_SIMP_TAC[POW_2_SQRT; REAL_LE_REFL]]);;

let GEODB_LTCONTR_SUB = prove
 (`!(G:real^N->real^N^N) (Y:real^N->(num->real^N)->real) Z y u.
     ltcontr G (\z u. Y z u - Z z u) y u = ltcontr G Y y u - ltcontr G Z y u`,
  REWRITE_TAC[ltcontr; REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG]);;

let GEODB_LTPERM_SUB = prove
 (`!p (Y:real^N->(num->real^N)->real) Z z u.
     ltperm p (\z u. Y z u - Z z u) z u = ltperm p Y z u - ltperm p Z z u`,
  REWRITE_TAC[ltperm]);;

let GEODB_SQRT_TRIANGLE = prove
 (`!r U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B C y.
     metric_field U G /\ y IN U /\ ltensor_field r U A /\ ltensor_field r U B /\
     ltensor_field r U C
     ==> sqrt(ltnorm2 r G (\z u. A z u - C z u) y) <=
         sqrt(ltnorm2 r G (\z u. A z u - B z u) y) +
         sqrt(ltnorm2 r G (\z u. B z u - C z u) y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_LTNORM2_TRIANGLE THEN
  EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[]) THEN
  REAL_ARITH_TAC);;

let GEODB_CONTR_DIFF_SQRT = prove
 (`!k s (G0:real^N->real^N^N) G y (M:real^N^N) delta X.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     G0 y = transp M ** M /\ invertible M /\
     &0 <= delta /\ delta <= &1 / &10 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     ltensor_field (k + 2) s X
     ==> sqrt(ltnorm2 k G0 (\z u. ltcontr G X z u - ltcontr G0 X z u) y) <=
         (sqrt(&(CARD(index_tuples k (:N)))) * &(dimindex(:N)) * &100 / &81) *
         delta * sqrt(ltnorm2 (k + 2) G0 X y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL GEODB_LTCONTR_PERT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) X y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&(CARD(index_tuples k (:N)))) *
              (&(dimindex(:N)) * (&100 / &81 * delta *
                                  sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) X y)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GEODB_SQRT_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING]);;

(* One contraction step of an error chain. *)

let GEODB_CHAIN_STEP = prove
 (`!k s (G0:real^N->real^N^N) G y (M:real^N^N) delta rho Y Z bz ce.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     G0 y = transp M ** M /\ invertible M /\
     &0 <= delta /\ delta <= &1 / &10 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     delta <= rho /\ rho <= &1 /\ &0 <= bz /\ &0 <= ce /\
     ltensor_field (k + 2) s Y /\ ltensor_field (k + 2) s Z /\
     sqrt(ltnorm2 (k + 2) G0 Z y) <= bz /\
     sqrt(ltnorm2 (k + 2) G0 (\z u. Y z u - Z z u) y) <= ce * rho
     ==> sqrt(ltnorm2 k G0 (ltcontr G0 Z) y) <= sqrt(&(dimindex(:N))) * bz /\
         sqrt(ltnorm2 k G0 (\z u. ltcontr G Y z u - ltcontr G0 Z z u) y) <=
         ((sqrt(&(CARD(index_tuples k (:N)))) * &(dimindex(:N)) * &100 / &81) * (bz + ce) +
          sqrt(&(dimindex(:N))) * ce) * rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `cK = sqrt(&(CARD(index_tuples k (:N)))) * &(dimindex(:N)) * &100 / &81` THEN
  SUBGOAL_THEN `&0 <= cK /\ &0 <= sqrt(&(dimindex(:N)))` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cK" THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS] THEN TRY(MATCH_MP_TAC SQRT_POS_LE) THEN
      REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field (k + 2) s (\z u. (Y:real^N->(num->real^N)->real) z u - Z z u) /\
    ltensor_field k s (ltcontr (G0:real^N->real^N^N) Z) /\
    ltensor_field k s (ltcontr (G:real^N->real^N^N) Y) /\
    ltensor_field k s (ltcontr (G0:real^N->real^N^N) Y)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC RFA_LTCONTR_FIELD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!W. ltensor_field (k + 2) s W
        ==> sqrt(ltnorm2 k (G0:real^N->real^N^N) (ltcontr G0 W) y) <=
            sqrt(&(dimindex(:N))) * sqrt(ltnorm2 (k + 2) G0 W y)`
  (LABEL_TAC "c0") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEODB_SQRT_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN
    SUBGOAL_THEN `&0 <= ltnorm2 (k + 2) (G0:real^N->real^N^N) W y` ASSUME_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; SQRT_POS_LE] THEN
    MATCH_MP_TAC RFA_LTNORM2_LTCONTR THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&(dimindex(:N))) * sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) Z y)` THEN
    CONJ_TAC THENL
     [USE_THEN "c0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) Y y) <= bz + ce * rho`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k + 2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. (Y:real^N->(num->real^N)->real) z u - Z z u`;
                   `Z:real^N->(num->real^N)->real`; `Y:real^N->(num->real^N)->real`;
                   `y:real^N`] LRG_LTNORM2_TRIANGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. ltcontr (G:real^N->real^N^N) Y z u - ltcontr G0 Y z u`;
                 `ltcontr (G0:real^N->real^N^N) (\z u. (Y:real^N->(num->real^N)->real) z u -
                                                       Z z u)`;
                 `\z u. ltcontr (G:real^N->real^N^N) Y z u - ltcontr G0 Z z u`;
                 `y:real^N`] LRG_LTNORM2_TRIANGLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LTCONTR_FIELD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GEODB_LTCONTR_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`; `Y:real^N->(num->real^N)->real`]
         GEODB_CONTR_DIFF_SQRT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "c0" (MP_TAC o SPEC `\z u. (Y:real^N->(num->real^N)->real) z u - Z z u`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) Y y)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC LTNORM2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cK * delta * sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) Y y) <=
    cK * rho * (bz + ce)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `bz + ce * rho` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ce * rho <= ce * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&(dimindex(:N))) *
    sqrt(ltnorm2 (k + 2) (G0:real^N->real^N^N) (\z u. (Y:real^N->(num->real^N)->real) z u - Z z u) y) <=
    sqrt(&(dimindex(:N))) * (ce * rho)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cK * (bz + ce) + sqrt(&(dimindex(:N))) * ce) * rho =
    cK * rho * (bz + ce) + sqrt(&(dimindex(:N))) * (ce * rho)`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Slot permutations preserve the norms of tensors and of differences. *)

let GEODB_PERM_STEP = prove
 (`!r p s (G:real^N->real^N^N) y (Y:real^N->(num->real^N)->real) Z.
     p permutes 1..r /\ metric_field s G /\ y IN s /\
     ltensor_field r s Y /\ ltensor_field r s Z
     ==> ltnorm2 r G (ltperm p Z) y = ltnorm2 r G Z y /\
         ltnorm2 r G (\z u. ltperm p Y z u - ltperm p Z z u) y =
         ltnorm2 r G (\z u. Y z u - Z z u) y`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RFA_LTNORM2_LTPERM THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `ltnorm2 r (G:real^N->real^N^N)
                (ltperm p (\z u. (Y:real^N->(num->real^N)->real) z u - Z z u)) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[GEODB_LTPERM_SUB];
    MATCH_MP_TAC RFA_LTNORM2_LTPERM THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[]]);;

(* The end of a chain: squared norms of W (with G) and W0 (with G0). *)

let GEODB_QUAD_FINAL = prove
 (`!k s (G0:real^N->real^N^N) G y (M:real^N^N) delta rho W W0 bw cw.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &2 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     delta <= rho /\ rho <= &1 /\ &0 <= bw /\ &0 <= cw /\
     ltensor_field k s W /\ ltensor_field k s W0 /\
     sqrt(ltnorm2 k G0 W0 y) <= bw /\
     sqrt(ltnorm2 k G0 (\z u. W z u - W0 z u) y) <= cw * rho
     ==> abs(ltnorm2 k G W y - ltnorm2 k G0 W0 y) <=
         (&k * &4 pow k * &2 * (bw + cw) pow 2 + cw * (&2 * bw + cw)) * rho`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`; `W:real^N->(num->real^N)->real`]
         GEODB_LTNORM2_METRIC_PERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `W:real^N->(num->real^N)->real`; `W0:real^N->(num->real^N)->real`;
                 `y:real^N`] GEODB_LTNORM2_DIFF_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ltensor_field k s (\z u. (W:real^N->(num->real^N)->real) z u - W0 z u)`
  ASSUME_TAC THENL [MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. (W:real^N->(num->real^N)->real) z u - W0 z u`;
                 `W0:real^N->(num->real^N)->real`; `W:real^N->(num->real^N)->real`;
                 `y:real^N`] LRG_LTNORM2_TRIANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= ltnorm2 k (G0:real^N->real^N^N) W y /\ &0 <= ltnorm2 k G0 W0 y /\
    &0 <= ltnorm2 k G0 (\z u. (W:real^N->(num->real^N)->real) z u - W0 z u) y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `ltnorm2 k (G0:real^N->real^N^N) W y` SQRT_POW_2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `ltnorm2 k (G0:real^N->real^N^N) W y` SQRT_POS_LE) THEN
  MP_TAC(SPEC `ltnorm2 k (G0:real^N->real^N^N) W0 y` SQRT_POS_LE) THEN
  MP_TAC(SPEC `ltnorm2 k (G0:real^N->real^N^N)
                 (\z u. (W:real^N->(num->real^N)->real) z u - W0 z u) y` SQRT_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = sqrt(ltnorm2 k (G0:real^N->real^N^N) W y)` THEN
  ABBREV_TAC `b = sqrt(ltnorm2 k (G0:real^N->real^N^N) W0 y)` THEN
  ABBREV_TAC `c = sqrt(ltnorm2 k (G0:real^N->real^N^N)
                        (\z u. (W:real^N->(num->real^N)->real) z u - W0 z u) y)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `a <= bw + cw` ASSUME_TAC THENL
   [SUBGOAL_THEN `cw * rho <= cw * &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a pow 2 <= (bw + cw) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &k * &4 pow k * &2` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&k * &4 pow k * (&2 * delta) * ltnorm2 k (G0:real^N->real^N^N) W y <=
    (&k * &4 pow k * &2 * (bw + cw) pow 2) * rho`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&k * &4 pow k * &2) * (delta * a pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&k * &4 pow k * &2) * (rho * (bw + cw) pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * (a + b) <= (cw * rho) * (&2 * bw + cw)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The three quantities as contractions (from P2C_DSCALAR, P2C_HSCALAR,      *)
(* P2C_LLAP_CONTR and P2C_RIC_CONTR, as in the proof of                      *)
(* P2C_SCALAR_DERIV_TRACE), and their stability through GEODB_CHAIN_STEP.    *)
(* ========================================================================= *)

let GEODB_GRAD_REP = prove
 (`!s (G:real^N->real^N^N) y.
     metric_field s G /\ y IN s
     ==> lgrad2 G (lscalar G) y =
         ltnorm2 1 G (ltcontr G (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 G))))) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2C_LGRAD2_LTNORM2] THEN
  MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC P2C_DSCALAR THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let GEODB_LAP_REP = prove
 (`!s (G:real^N->real^N^N) y.
     metric_field s G /\ y IN s
     ==> llap G (lscalar G) y =
         ltcontr G (ltperm (swap(1,2))
           (ltcontr G (ltcontr G (ltperm (swap(2,3))
              (lnabla 5 G (lnabla 4 G (lrm4 G))))))) y (\m. basis 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field s (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 6 s (ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_SIMP_TAC[P2C_SW23_PERMUTES; ARITH];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `lscalar (G:real^N->real^N^N)`;
                 `y:real^N`] LRG_LLAP_LNABLA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(\z u. drop(frechet_derivative (\w. lift(lscalar G w)) (at z) (u 1))) =
    lnabla 0 G (\z u. lscalar (G:real^N->real^N^N) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lnabla] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_SUB_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2C_HSCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `ltensor_field 2 s (ltcontr G (ltcontr G (ltperm (swap(2,3))
       (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_LLAP_CONTR THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* The value of a 0-tensor is its norm. *)

let GEODB_ABS_LTNORM2_0 = prove
 (`!(G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B y.
     abs(A y (\m. basis 0) - B y (\m. basis 0)) =
     sqrt(ltnorm2 0 G (\z u. A z u - B z u) y)`,
  REWRITE_TAC[P2C_LTNORM2_0; POW_2_SQRT_ABS]);;

(* Stability of |grad R|^2 through the chain T = P(nabla Rm), C T, C C T. *)

let GEODB_Q1_STAB = prove
 (`!sK cD. &0 <= sK /\ &0 <= cD
     ==> ?C. &0 <= C /\
         !s (G0:real^N->real^N^N) G y (M:real^N^N) delta rho.
           metric_field s G0 /\ metric_field s G /\ y IN s /\
           G0 y = transp M ** M /\ invertible M /\
           &0 <= delta /\ delta <= &1 / &10 /\
           (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
                  delta * norm(M ** a) * norm(M ** b)) /\
           delta <= rho /\ rho <= &1 /\
           sqrt(ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G0)) y) <= sK /\
           sqrt(ltnorm2 5 G0 (\z u. lnabla 4 G (lrm4 G) z u -
                                    lnabla 4 G0 (lrm4 G0) z u) y) <= cD * rho
           ==> abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= C * rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sN = sqrt(&(dimindex(:N)))` THEN
  ABBREV_TAC `c3 = sqrt(&(CARD(index_tuples 3 (:N)))) * &(dimindex(:N)) * &100 / &81` THEN
  ABBREV_TAC `c1 = sqrt(&(CARD(index_tuples 1 (:N)))) * &(dimindex(:N)) * &100 / &81` THEN
  SUBGOAL_THEN `&0 <= sN /\ &0 <= c3 /\ &0 <= c1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sN"; "c3"; "c1"] THEN REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE) THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `b1 = sN * sK` THEN
  ABBREV_TAC `e1 = c3 * (sK + cD) + sN * cD` THEN
  ABBREV_TAC `b2 = sN * b1` THEN
  ABBREV_TAC `e2 = c1 * (b1 + e1) + sN * e1` THEN
  SUBGOAL_THEN `&0 <= b1 /\ &0 <= e1 /\ &0 <= b2 /\ &0 <= e2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e2"; "b2"; "e1"; "b1"] THEN
    REPEAT CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `&1 * &4 pow 1 * &2 * (b2 + e2) pow 2 + e2 * (&2 * b2 + e2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G0:real^N->real^N^N)`] LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..5` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_SW23_PERMUTES THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 5 s (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))) /\
    ltensor_field 5 s (ltperm (swap(2,3)) (lnabla 4 G0 (lrm4 (G0:real^N->real^N^N))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`5`; `swap(2,3)`; `s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `lnabla 4 G (lrm4 (G:real^N->real^N^N))`;
                 `lnabla 4 G0 (lrm4 (G0:real^N->real^N^N))`] GEODB_PERM_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL
   [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
    `M:real^N^N`; `delta:real`; `rho:real`;
    `ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`;
    `ltperm (swap(2,3)) (lnabla 4 G0 (lrm4 (G0:real^N->real^N^N)))`;
    `sK:real`; `cD:real`] GEODB_CHAIN_STEP)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 3 s (ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N))))) /\
    ltensor_field 3 s (ltcontr G0 (ltperm (swap(2,3)) (lnabla 4 G0 (lrm4 (G0:real^N->real^N^N)))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL
   [`1`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
    `M:real^N^N`; `delta:real`; `rho:real`;
    `ltcontr G (ltperm (swap(2,3)) (lnabla 4 G (lrm4 (G:real^N->real^N^N))))`;
    `ltcontr G0 (ltperm (swap(2,3)) (lnabla 4 G0 (lrm4 (G0:real^N->real^N^N))))`;
    `b1:real`; `e1:real`] GEODB_CHAIN_STEP)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] GEODB_GRAD_REP) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`] GEODB_GRAD_REP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC GEODB_QUAD_FINAL THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `M:real^N^N`; `delta:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[]);;

(* Stability of Lap R through the chain P(nabla^2 Rm), C, C, P', C. *)

let GEODB_Q2_STAB = prove
 (`!sK cD. &0 <= sK /\ &0 <= cD
     ==> ?C. &0 <= C /\
         !s (G0:real^N->real^N^N) G y (M:real^N^N) delta rho.
           metric_field s G0 /\ metric_field s G /\ y IN s /\
           G0 y = transp M ** M /\ invertible M /\
           &0 <= delta /\ delta <= &1 / &10 /\
           (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
                  delta * norm(M ** a) * norm(M ** b)) /\
           delta <= rho /\ rho <= &1 /\
           sqrt(ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (lrm4 G0))) y) <= sK /\
           sqrt(ltnorm2 6 G0 (\z u. lnabla 5 G (lnabla 4 G (lrm4 G)) z u -
                                    lnabla 5 G0 (lnabla 4 G0 (lrm4 G0)) z u) y) <= cD * rho
           ==> abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= C * rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `sN = sqrt(&(dimindex(:N)))` THEN
  ABBREV_TAC `c4 = sqrt(&(CARD(index_tuples 4 (:N)))) * &(dimindex(:N)) * &100 / &81` THEN
  ABBREV_TAC `c2 = sqrt(&(CARD(index_tuples 2 (:N)))) * &(dimindex(:N)) * &100 / &81` THEN
  ABBREV_TAC `c0 = sqrt(&(CARD(index_tuples 0 (:N)))) * &(dimindex(:N)) * &100 / &81` THEN
  SUBGOAL_THEN `&0 <= sN /\ &0 <= c4 /\ &0 <= c2 /\ &0 <= c0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sN"; "c4"; "c2"; "c0"] THEN REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE) THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `b1 = sN * sK` THEN
  ABBREV_TAC `e1 = c4 * (sK + cD) + sN * cD` THEN
  ABBREV_TAC `b2 = sN * b1` THEN
  ABBREV_TAC `e2 = c2 * (b1 + e1) + sN * e1` THEN
  ABBREV_TAC `e3 = c0 * (b2 + e2) + sN * e2` THEN
  SUBGOAL_THEN `&0 <= b1 /\ &0 <= e1 /\ &0 <= b2 /\ &0 <= e2 /\ &0 <= e3`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e3"; "e2"; "b2"; "e1"; "b1"] THEN
    REPEAT CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `e3:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                 `lrm4 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
  MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `lrm4 (G0:real^N->real^N^N)`] P2C_FIELD_D2) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..6 /\ swap(1,2) permutes 1..2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC P2C_SW23_PERMUTES THEN ARITH_TAC;
      MATCH_MP_TAC PERMUTES_SWAP THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `TG = ltperm (swap(2,3)) (lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N))))` THEN
  ABBREV_TAC `T0 = ltperm (swap(2,3)) (lnabla 5 G0 (lnabla 4 G0 (lrm4 (G0:real^N->real^N^N))))` THEN
  SUBGOAL_THEN `ltensor_field 6 s (TG:real^N->(num->real^N)->real) /\
                ltensor_field 6 s (T0:real^N->(num->real^N)->real)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["TG"; "T0"] THEN CONJ_TAC THEN MATCH_MP_TAC RFA_LTPERM_FIELD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`6`; `swap(2,3)`; `s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `lnabla 5 G (lnabla 4 G (lrm4 (G:real^N->real^N^N)))`;
                 `lnabla 5 G0 (lnabla 4 G0 (lrm4 (G0:real^N->real^N^N)))`] GEODB_PERM_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL
   [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
    `M:real^N^N`; `delta:real`; `rho:real`;
    `TG:real^N->(num->real^N)->real`; `T0:real^N->(num->real^N)->real`;
    `sK:real`; `cD:real`] GEODB_CHAIN_STEP)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `ltensor_field 4 s (ltcontr G (TG:real^N->(num->real^N)->real)) /\
    ltensor_field 4 s (ltcontr (G0:real^N->real^N^N) (T0:real^N->(num->real^N)->real))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL
   [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
    `M:real^N^N`; `delta:real`; `rho:real`;
    `ltcontr G (TG:real^N->(num->real^N)->real)`;
    `ltcontr (G0:real^N->real^N^N) (T0:real^N->(num->real^N)->real)`;
    `b1:real`; `e1:real`] GEODB_CHAIN_STEP)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `HG = ltcontr G (ltcontr G (TG:real^N->(num->real^N)->real))` THEN
  ABBREV_TAC `H0 = ltcontr (G0:real^N->real^N^N) (ltcontr G0 (T0:real^N->(num->real^N)->real))` THEN
  SUBGOAL_THEN `ltensor_field 2 s (HG:real^N->(num->real^N)->real) /\
                ltensor_field 2 s (H0:real^N->(num->real^N)->real)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["HG"; "H0"] THEN CONJ_TAC THEN
    MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC RFA_LTCONTR_FIELD THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `swap(1,2)`; `s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `HG:real^N->(num->real^N)->real`; `H0:real^N->(num->real^N)->real`]
         GEODB_PERM_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ltensor_field 2 s (ltperm (swap(1,2)) (HG:real^N->(num->real^N)->real)) /\
    ltensor_field 2 s (ltperm (swap(1,2)) (H0:real^N->(num->real^N)->real))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (ISPECL
   [`0`; `s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
    `M:real^N^N`; `delta:real`; `rho:real`;
    `ltperm (swap(1,2)) (HG:real^N->(num->real^N)->real)`;
    `ltperm (swap(1,2)) (H0:real^N->(num->real^N)->real)`;
    `b2:real`; `e2:real`] GEODB_CHAIN_STEP)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] GEODB_LAP_REP) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`] GEODB_LAP_REP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ISPEC `G0:real^N->real^N^N` GEODB_ABS_LTNORM2_0] THEN
  ASM_REWRITE_TAC[]);;

(* Stability of |Ric|^2 (P2C_RIC_DIFF_NORM for the difference). *)

let GEODB_Q3_STAB = prove
 (`!K. &0 <= K
     ==> ?C. &0 <= C /\
         !s (G0:real^N->real^N^N) G y (M:real^N^N) rho.
           metric_field s G0 /\ metric_field s G /\ y IN s /\
           G0 y = transp M ** M /\
           sqrt(lck_dist2 2 G0 G y) <= &1 / &10 /\
           (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
                  sqrt(lck_dist2 2 G0 G y) * norm(M ** a) * norm(M ** b)) /\
           sqrt(lck_dist2 2 G0 G y) <= rho /\ rho <= &1 /\
           ltnorm2 4 G0 (lrm4 G0) y <= K
           ==> abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= C * rho`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `bw = sqrt(&(dimindex(:N)) * K)` THEN
  ABBREV_TAC `cw = sqrt(&(CARD(index_tuples 2 (:N)))) * (&(dimindex(:N)) * &5)` THEN
  SUBGOAL_THEN `&0 <= bw /\ &0 <= cw` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bw"; "cw"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * &4 pow 2 * &2 * (bw + cw) pow 2 + cw * (&2 * bw + cw)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `delta = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= delta` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC P2C_LCK_DIST2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] P2C_RIC_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..4` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_SW23_PERMUTES THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ltensor_field 4 s (ltperm (swap(2,3)) (lrm4 (G0:real^N->real^N^N)))`
  ASSUME_TAC THENL [MATCH_MP_TAC RFA_LTPERM_FIELD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GEODB_QUAD_FINAL THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `M:real^N^N`; `delta:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXPAND_TAC "bw" THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `ltnorm2 2 (G0:real^N->real^N^N)
                  (ltcontr G0 (ltperm (swap(2,3)) (lrm4 G0))) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC P2C_RIC_CONTR THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `ltperm (swap(2,3)) (lrm4 (G0:real^N->real^N^N))`; `y:real^N`]
           RFA_LTNORM2_LTCONTR) THEN
    MP_TAC(ISPECL [`4`; `swap(2,3)`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lrm4 (G0:real^N->real^N^N)`; `y:real^N`] RFA_LTNORM2_LTPERM) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(dimindex(:N)) * ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G0) y` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `y:real^N`] P2C_RIC_DIFF_NORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&(CARD(index_tuples 2 (:N)))) * (&(dimindex(:N)) * &5 * delta)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GEODB_SQRT_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ltnorm2 2 (G0:real^N->real^N^N) (\z u. lric2 G z u - lric2 G0 z u) y <=
                     &(CARD(index_tuples 2 (:N))) * (&(dimindex(:N)) * &5 * delta) pow 2` THEN
        REWRITE_TAC[];
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC];
      EXPAND_TAC "cw" THEN
      SUBGOAL_THEN `&0 <= sqrt(&(CARD(index_tuples 2 (:N)))) * (&(dimindex(:N)) * &5)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_POS];
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(sqrt(&(CARD(index_tuples 2 (:N)))) * (&(dimindex(:N)) * &5)) * delta` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]]]);;

(* ========================================================================= *)
(* LRG_DERIV_STABILITY, the body of P2B_REQ_LRG_DERIV_STATEMENT              *)
(* (pc_p2b_979s).  With d = lck_dist2 4 G0 G y and rho = sqrt d: the frame   *)
(* closeness is delta = sqrt(lck_dist2 2) <= rho (P2C_FRAME_SETUP), the      *)
(* curvature derivatives differ by sqrt(C d) (GEODB_DRM_BOUNDS), and the     *)
(* three quantities differ by C_i rho (GEODB_Q1_STAB, GEODB_Q2_STAB,         *)
(* GEODB_Q3_STAB); take eta small.                                           *)
(* ========================================================================= *)

let GEODB_DERIV_N = prove
 (`!K0 alpha. &0 < alpha
      ==> ?eta. &0 < eta /\
            !s (G0:real^N->real^N^N) G y.
               metric_field s G0 /\ metric_field s G /\ y IN s /\
               lrm_deriv_norm2 0 G0 y <= K0 /\ lrm_deriv_norm2 1 G0 y <= K0 /\
               lrm_deriv_norm2 2 G0 y <= K0 /\ lck_dist2 4 G0 G y < eta pow 2
               ==> abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= alpha /\
                   abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= alpha /\
                   abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= alpha`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = abs K0` THEN
  SUBGOAL_THEN `&0 <= K /\ K0 <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  X_CHOOSE_THEN `CD:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "drm"))
   (SPEC `K:real` (INST_TYPE [`:N`,`:N`] GEODB_DRM_BOUNDS)) THEN
  SUBGOAL_THEN `&0 <= sqrt K /\ &0 <= sqrt CD` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`sqrt K`; `sqrt CD`] (INST_TYPE [`:N`,`:N`] GEODB_Q1_STAB)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q1"))) THEN
  MP_TAC(SPECL [`sqrt K`; `sqrt CD`] (INST_TYPE [`:N`,`:N`] GEODB_Q2_STAB)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q2"))) THEN
  MP_TAC(SPEC `K:real` (INST_TYPE [`:N`,`:N`] GEODB_Q3_STAB)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "q3"))) THEN
  ABBREV_TAC `Ct = C1 + C2 + C3 + &1` THEN
  SUBGOAL_THEN `&0 < Ct /\ &0 < CD + &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ct" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (min (&1 / &10) (inv(CD + &1))) (alpha / Ct)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_LT_DIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                       `y:real^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `eta = min (min (&1 / &10) (inv(CD + &1))) (alpha / Ct)` THEN
  SUBGOAL_THEN `&0 < eta /\ eta <= &1 / &10 /\ eta <= inv(CD + &1) /\ eta <= alpha / Ct`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN ASM_SIMP_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LT_INV_EQ;
                                       REAL_LT_DIV; REAL_LE_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lck_dist2 2 (G0:real^N->real^N^N) G y <= lck_dist2 4 G0 G y /\
    (!l. l <= 4 ==> ltnorm2 (2 + l) G0 (lnabla_iter 2 l G0 (p2c_hd G0 G)) y <=
                    lck_dist2 4 G0 G y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LCK_DIST_MONO THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      X_GEN_TAC `l:num` THEN DISCH_TAC THEN REWRITE_TAC[p2c_hd] THEN
      MATCH_MP_TAC LRG_LCK_DIST2_TERM_LE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `d = lck_dist2 4 (G0:real^N->real^N^N) G y` THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC P2C_LCK_DIST2_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt d /\ sqrt d < eta /\ sqrt d pow 2 = d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt(eta pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rho = sqrt d` THEN
  SUBGOAL_THEN `rho <= &1 /\ rho <= &1 / &10` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `CD * d <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `d <= rho` ASSUME_TAC THENL
     [UNDISCH_TAC `rho pow 2 = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `d * (CD + &1) <= &1` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `delta = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= delta /\ delta <= rho` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["delta"; "rho"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC P2C_LCK_DIST2_POS THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`] P2C_FRAME_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC))) THEN
  (* the bounds of Rm(G0) and its derivatives *)
  SUBGOAL_THEN
   `ltnorm2 4 (G0:real^N->real^N^N) (lrm4 G0) y <= K /\
    ltnorm2 5 G0 (lnabla 4 G0 (lrm4 G0)) y <= K /\
    ltnorm2 6 G0 (lnabla 5 G0 (lnabla 4 G0 (lrm4 G0))) y <= K`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`lrm_deriv_norm2 0 (G0:real^N->real^N^N) y <= K0`;
      `lrm_deriv_norm2 1 (G0:real^N->real^N^N) y <= K0`;
      `lrm_deriv_norm2 2 (G0:real^N->real^N^N) y <= K0`] THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; LRG_LNABLA_ITER_12] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the derivative differences *)
  USE_THEN "drm" (MP_TAC o SPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                                  `G:real^N->real^N^N`; `y:real^N`; `d:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!x. &0 <= x /\ x <= CD * d ==> sqrt x <= sqrt CD * rho` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEODB_SQRT_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x <= K ==> sqrt x <= sqrt K` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `C1 * rho <= alpha /\ C2 * rho <= alpha /\ C3 * rho <= alpha`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `Ct * rho <= alpha` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Ct * eta` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `eta <= alpha / Ct` THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `C1 * rho <= Ct * rho /\ C2 * rho <= Ct * rho /\ C3 * rho <= Ct * rho`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      EXPAND_TAC "Ct" THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= ltnorm2 5 (G0:real^N->real^N^N)
            (\z u. lnabla 4 G (lrm4 G) z u - lnabla 4 G0 (lrm4 G0) z u) y /\
    &0 <= ltnorm2 6 G0 (\z u. lnabla 5 G (lnabla 4 G (lrm4 G)) z u -
                             lnabla 5 G0 (lnabla 4 G0 (lrm4 G0)) z u) y`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRM4_TENSOR_FIELD) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G:real^N->real^N^N`;
                   `lrm4 (G:real^N->real^N^N)`] P2C_FIELD_D2) THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lrm4 (G0:real^N->real^N^N)`] P2C_FIELD_D2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    CONJ_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_TENSOR_FIELD_SUB THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * rho` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "q1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `M:real^N^N`; `delta:real`] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C2 * rho` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "q2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `M:real^N^N`; `delta:real`] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C3 * rho` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "q3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `M:real^N^N`] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let LRG_DERIV_STABILITY = prove
 (`!K0 alpha. &0 < alpha
      ==> ?eta. &0 < eta /\
            !s (G0:real^3->real^3^3) G y.
               metric_field s G0 /\ metric_field s G /\ y IN s /\
               lrm_deriv_norm2 0 G0 y <= K0 /\ lrm_deriv_norm2 1 G0 y <= K0 /\
               lrm_deriv_norm2 2 G0 y <= K0 /\ lck_dist2 4 G0 G y < eta pow 2
               ==> abs(lgrad2 G (lscalar G) y - lgrad2 G0 (lscalar G0) y) <= alpha /\
                   abs(llap G (lscalar G) y - llap G0 (lscalar G0) y) <= alpha /\
                   abs(ltnorm2 2 G (lric2 G) y - ltnorm2 2 G0 (lric2 G0) y) <= alpha`,
  MATCH_ACCEPT_TAC GEODB_DERIV_N);;

