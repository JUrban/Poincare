(* ========================================================================= *)
(* Local Riemannian geometry for the Appendix layer: properties of the C^k   *)
(* distance lck_dist2 (triangle inequality, rescaling, change of base        *)
(* between the cylinders, monotonicity, C^0 control), the sectional          *)
(* curvature and the Christoffel symbols of the cylinder model, and          *)
(* curvature stability under C^2-closeness (LCK_CURVATURE_STABILITY).        *)
(* Builds on pc_lrg_evol (tensor calculus toolkit) and pc_rf_basic           *)
(* (cylinder_flow).                                                          *)
(* ========================================================================= *)

needs "src/pc_lrg_evol.ml";;
needs "src/pc_rf_basic.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Cauchy-Schwarz and Minkowski for finite sums; nonnegativity of the        *)
(* summands of lck_dist2; monotonicity in k (LCK_DIST_MONO).                 *)
(* ========================================================================= *)

let LRG_SUM_CAUCHY_SCHWARZ = prove
 (`!s (f:A->real) g.
        FINITE s
        ==> (sum s (\i. f i * g i)) pow 2 <=
            sum s (\i. f i pow 2) * sum s (\i. g i pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. &0 <= x pow 2 * sum s (\i. (f:A->real) i pow 2) +
              &2 * x * sum s (\i. f i * g i) + sum s (\i. g i pow 2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum s (\i. (x * (f:A->real) i + g i) pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `sum s (\i. (f:A->real) i pow 2) = &0` THENL
   [SUBGOAL_THEN `!i. i IN s ==> (f:A->real) i = &0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\i. (f:A->real) i pow 2`; `s:A->bool`] SUM_POS_EQ_0) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_POW_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sum s (\i. (f:A->real) i * g i) = &0` SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[REAL_MUL_LZERO]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sum s (\i. (f:A->real) i pow 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LE; SUM_POS_LE; REAL_LE_POW_2]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `--(sum s (\i. (f:A->real) i * g i)) / sum s (\i. f i pow 2)`) THEN
  UNDISCH_TAC `&0 < sum s (\i. (f:A->real) i pow 2)` THEN
  SPEC_TAC(`sum s (\i. (f:A->real) i pow 2)`, `a:real`) THEN
  SPEC_TAC(`sum s (\i. (f:A->real) i * g i)`, `b:real`) THEN
  SPEC_TAC(`sum s (\i. (g:A->real) i pow 2)`, `c:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(--b / a) pow 2 * a + &2 * (--b / a) * b + c = c - b pow 2 / a`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let LRG_SUM_MINKOWSKI = prove
 (`!s (f:A->real) g.
        FINITE s
        ==> sqrt(sum s (\i. (f i + g i) pow 2)) <=
            sqrt(sum s (\i. f i pow 2)) + sqrt(sum s (\i. g i pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum s (\i. ((f:A->real) i + g i) pow 2) =
    sum s (\i. f i pow 2) + &2 * sum s (\i. f i * g i) + sum s (\i. g i pow 2)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:A->bool`; `f:A->real`; `g:A->real`]
         LRG_SUM_CAUCHY_SCHWARZ) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sum s (\i. (f:A->real) i pow 2) /\
                &0 <= sum s (\i. (g:A->real) i pow 2)` MP_TAC THENL
   [ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_POW_2]; ALL_TAC] THEN
  SPEC_TAC(`sum s (\i. (f:A->real) i pow 2)`, `a:real`) THEN
  SPEC_TAC(`sum s (\i. (f:A->real) i * g i)`, `b:real`) THEN
  SPEC_TAC(`sum s (\i. (g:A->real) i pow 2)`, `c:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LE_ADD; SQRT_POS_LE] THEN
  SUBGOAL_THEN `b <= sqrt a * sqrt c` MP_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `a:real` SQRT_POW_2) THEN MP_TAC(SPEC `c:real` SQRT_POW_2) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LRG_LCK_DIST2_SUMMAND_POS = prove
 (`!s (G0:real^N->real^N^N) G y l.
        metric_field s G0 /\ metric_field s G /\ y IN s
        ==> &0 <= ltnorm2 (2 + l) G0
                    (lnabla_iter 2 l G0 (\z u. lmetric2 G z u - lmetric2 G0 z u)) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTNORM2_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_SIMP_TAC[LRG_LMETRIC2_DIFF_FIELD]);;

let LCK_DIST_MONO = prove
 (`!k k' s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ k <= k'
     ==> lck_dist2 k G0 G y <= lck_dist2 k' G0 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG] THEN ASM_REWRITE_TAC[LE_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let LRG_DOT_INV_TRANSP = prove
 (`!(G:real^N^N) (S:real^N^N) (a:real^N).
        invertible S /\ matrix_inv G = transp S ** S /\ invertible G
        ==> (matrix_inv(transp S) ** a) dot (matrix_inv(transp S) ** a) =
            a dot (G ** a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `G = matrix_inv(S:real^N^N) ** matrix_inv(transp S)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `matrix_inv(matrix_inv(G:real^N^N))` THEN
    CONJ_TAC THENL [REWRITE_TAC[MATRIX_INV_INV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MATRIX_INV_MUL THEN
    ASM_REWRITE_TAC[INVERTIBLE_TRANSP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`matrix_inv(S:real^N^N)`; `a:real^N`;
                 `matrix_inv(transp(S:real^N^N)) ** (a:real^N)`] DOT_LMUL_MATRIX) THEN
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP; GSYM MATRIX_INV_TRANSP;
              GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  MESON_TAC[]);;

let LRG_LTNORM2_BOUND = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y a.
        metric_field U G /\ ltensor_field k U tf /\ y IN U
        ==> (tf y a) pow 2 <=
            ltnorm2 k G tf y * product(1..k) (\m. a m dot (G y ** a m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ltensor_field]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(tf:real^N->(num->real^N)->real) y`; `k:num`;
                 `transp(S:real^N^N)`] LRG_MULTILINEAR_TRANSFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\u. (tf:real^N->(num->real^N)->real) y
                        (\m. transp(S:real^N^N) ** u m)`; `k:num`]
         LRG_MULTILINEAR_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\m. matrix_inv(transp(S:real^N^N)) ** (a:num->real^N) m`) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\m. transp(S:real^N^N) ** matrix_inv(transp S) ** (a:num->real^N) m) = a`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_TRANSP; MATRIX_VECTOR_MUL_LID];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL
     [`index_tuples k (:N)`;
      `\i. product(1..k) (\m. (matrix_inv(transp(S:real^N^N)) **
                               (a:num->real^N) m)$(i m))`;
      `\i. (tf:real^N->(num->real^N)->real) y
             (\m. transp(S:real^N^N) ** basis(i m))`]
     LRG_SUM_CAUCHY_SCHWARZ) THEN
  REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  MATCH_MP_TAC(MESON[] `!x b b' c:real. b = b' ==> x <= b * c ==> x <= b' * c`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product(1..k) (\m. sum(1..dimindex(:N))
       (\q. (matrix_inv(transp(S:real^N^N)) ** (a:num->real^N) m)$q *
            (matrix_inv(transp S) ** a m)$q))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LRG_PRODUCT_SUM_TUPLES; REAL_POW_2; GSYM PRODUCT_MUL_NUMSEG];
    REWRITE_TAC[GSYM dot] THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_DOT_INV_TRANSP THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C^0 control of the metric by the C^k distance (LCK_DIST_C0).              *)
(* ------------------------------------------------------------------------- *)

let LRG_ABS_LE_SQRT_MUL = prove
 (`!d L D q. d pow 2 <= L * q pow 2 /\ L <= D /\ &0 <= L /\ &0 <= q
             ==> abs d <= sqrt D * q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs d <= abs e /\ &0 <= e ==> abs d <= e`) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE; REAL_LE_SQUARE_ABS; REAL_POW_MUL;
               SQRT_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L * q pow 2` THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LE_POW_2]);;

let LRG_METRIC_NONNEG = prove
 (`!U (G:real^N->real^N^N) y w.
        metric_field U G /\ y IN U ==> &0 <= w dot (G y ** w)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `w:real^N = vec 0` THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[LRG_METRIC_POS]);;

let LCK_DIST_C0 = prove
 (`!k s (G0:real^N->real^N^N) G y w.
      metric_field s G0 /\ metric_field s G /\ y IN s
      ==> abs(w dot (G y ** w) - w dot (G0 y ** w))
          <= sqrt(lck_dist2 k G0 G y) * (w dot (G0 y ** w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_ABS_LE_SQRT_MUL THEN
  EXISTS_TAC `ltnorm2 2 (G0:real^N->real^N^N)
                (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) y` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                   `y:real^N`; `\m:num. (w:real^N)`] LRG_LTNORM2_BOUND) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LRG_LMETRIC2_DIFF_FIELD]; ALL_TAC] THEN
    REWRITE_TAC[PRODUCT_CONST_NUMSEG; lmetric2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MP_TAC(ISPECL [`0`; `k:num`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LCK_DIST_MONO) THEN
    ASM_REWRITE_TAC[LE_0; lck_dist2; SUM_SING_NUMSEG; lnabla_iter; ADD_CLAUSES];
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`; `0`]
           LRG_LCK_DIST2_SUMMAND_POS) THEN
    ASM_REWRITE_TAC[lnabla_iter; ADD_CLAUSES];
    ASM_MESON_TAC[LRG_METRIC_NONNEG]]);;

(* ------------------------------------------------------------------------- *)
(* Linear combinations of smooth tensor fields; linearity of the iterated    *)
(* covariant derivative; the triangle inequality for lck_dist2               *)
(* (LCK_DIST_TRIANGLE).                                                      *)
(* ------------------------------------------------------------------------- *)

let LRG_TENSOR_FIELD_LINCOMB = prove
 (`!k U (tf1:real^N->(num->real^N)->real) tf2 a b.
     open U /\ ltensor_field k U tf1 /\ (!u. smooth_map_on U (\y. lift(tf1 y u))) /\
     ltensor_field k U tf2 /\ (!u. smooth_map_on U (\y. lift(tf2 y u)))
     ==> ltensor_field k U (\x u. a * tf1 x u + b * tf2 x u) /\
         (!u. smooth_map_on U (\y. lift(a * tf1 y u + b * tf2 y u)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `ltensor_field k U (tf1:real^N->(num->real^N)->real)` THEN
    UNDISCH_TAC `ltensor_field k U (tf2:real^N->(num->real^N)->real)` THEN
    REWRITE_TAC[ltensor_field] THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`)) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THENL
     [BINOP_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_SIMP_TAC[]];
    GEN_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[]]);;

let LRG_LNABLA_ITER_LINCOMB = prove
 (`!k U (G:real^N->real^N^N) (tf1:real^N->(num->real^N)->real) tf2 a b.
     metric_field U G /\
     ltensor_field k U tf1 /\ (!u. smooth_map_on U (\y. lift(tf1 y u))) /\
     ltensor_field k U tf2 /\ (!u. smooth_map_on U (\y. lift(tf2 y u)))
     ==> !l y u. y IN U
                 ==> lnabla_iter k l G (\x u. a * tf1 x u + b * tf2 x u) y u =
                     a * lnabla_iter k l G tf1 y u + b * lnabla_iter k l G tf2 y u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf1:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `tf2:real^N->(num->real^N)->real`] LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL [REWRITE_TAC[lnabla_iter]; ALL_TAC] THEN
  REWRITE_TAC[lnabla_iter] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla (k + l) (G:real^N->real^N^N)
     (\x u. a * lnabla_iter k l G tf1 x u + b * lnabla_iter k l G tf2 x u) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(lnabla_iter k l (G:real^N->real^N^N) tf1 x u)) differentiable at y /\
    (\x. lift(lnabla_iter k l (G:real^N->real^N^N) tf2 x u)) differentiable at y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k + l:num`; `G:real^N->real^N^N`;
     `\x (u:num->real^N). a * lnabla_iter k l (G:real^N->real^N^N) tf1 x u`;
     `\x (u:num->real^N). b * lnabla_iter k l (G:real^N->real^N^N) tf2 x u`;
     `y:real^N`; `u:num->real^N`] LRG_LNABLA_ADD) THEN
  REWRITE_TAC[LIFT_CMUL] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_CMUL THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THEN MATCH_MP_TAC LRG_LNABLA_CMUL THEN ASM_REWRITE_TAC[]);;

let LRG_LTNORM2_TRIANGLE = prove
 (`!k U (G:real^N->real^N^N) (A:real^N->(num->real^N)->real) B C y.
     metric_field U G /\ y IN U /\ ltensor_field k U A /\
     ltensor_field k U B /\ ltensor_field k U C /\
     (!u. C y u = A y u + B y u)
     ==> sqrt(ltnorm2 k G C y) <= sqrt(ltnorm2 k G A y) + sqrt(ltnorm2 k G B y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `A:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `B:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `C:real^N->(num->real^N)->real`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC LRG_SUM_MINKOWSKI THEN REWRITE_TAC[LRG_INDEX_TUPLES_FINITE]);;

let LRG_SQRT_SUM_TRIANGLE = prove
 (`!s (a:A->real) b c.
     FINITE s /\
     (!i. i IN s ==> &0 <= a i /\ &0 <= b i /\ &0 <= c i /\
                     sqrt(c i) <= sqrt(a i) + sqrt(b i))
     ==> sqrt(sum s c) <= sqrt(sum s a) + sqrt(sum s b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(sum s (\i. (sqrt((a:A->real) i) + sqrt(b i)) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt((c:A->real) i) pow 2` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE]];
    MP_TAC(ISPECL [`s:A->bool`; `\i. sqrt((a:A->real) i)`; `\i. sqrt((b:A->real) i)`]
           LRG_SUM_MINKOWSKI) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sum s (\i. sqrt((a:A->real) i) pow 2) = sum s a /\
                  sum s (\i. sqrt((b:A->real) i) pow 2) = sum s b`
    (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_MESON_TAC[]]);;

let LCK_DIST_TRIANGLE = prove
 (`!k s (G0:real^N->real^N^N) G1 G2 y.
      metric_field s G0 /\ metric_field s G1 /\ metric_field s G2 /\ y IN s
      ==> sqrt(lck_dist2 k G0 G2 y)
          <= sqrt(lck_dist2 k G0 G1 y) +
             sqrt(lck_dist2 k G0 (\z. G0 z + G2 z - G1 z) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G1:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G2:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`;
     `\z u. lmetric2 (G2:real^N->real^N^N) z u - lmetric2 G0 z u`;
     `\z u. lmetric2 (G1:real^N->real^N^N) z u - lmetric2 G0 z u`;
     `&1`; `-- &1`] LRG_TENSOR_FIELD_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
     `\z u. lmetric2 (G2:real^N->real^N^N) z u - lmetric2 G0 z u`;
     `\z u. lmetric2 (G1:real^N->real^N^N) z u - lmetric2 G0 z u`;
     `&1`; `-- &1`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
     `\x u. &1 * (lmetric2 (G2:real^N->real^N^N) x u - lmetric2 G0 x u) +
            -- &1 * (lmetric2 (G1:real^N->real^N^N) x u - lmetric2 G0 x u)`]
     LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
     `\z u. lmetric2 (G1:real^N->real^N^N) z u - lmetric2 G0 z u`]
     LRG_LNABLA_ITER_FIELD) THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
     `\z u. lmetric2 (G2:real^N->real^N^N) z u - lmetric2 G0 z u`]
     LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[lck_dist2] THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. (G0:real^N->real^N^N) z + G2 z - G1 z) z u -
           lmetric2 G0 z u) =
    (\x u. &1 * (lmetric2 (G2:real^N->real^N^N) x u - lmetric2 G0 x u) +
           -- &1 * (lmetric2 (G1:real^N->real^N^N) x u - lmetric2 G0 x u))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lmetric2] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                DOT_RADD; DOT_RSUB] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SQRT_SUM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LRG_LTNORM2_TRIANGLE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Rescaling the metric (LCK_DIST_RESCALE): the norm of the metric is sqrt   *)
(* N, the metric is parallel to all orders, and ltnorm2 is quadratic.        *)
(* ------------------------------------------------------------------------- *)

let LRG_LTNORM2_CMUL = prove
 (`!k (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) c y.
     ltnorm2 k G (\x u. c * tf x u) y = c pow 2 * ltnorm2 k G tf y`,
  REWRITE_TAC[ltnorm2; GSYM SUM_LMUL] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let LRG_TENSOR_FIELD_CMUL = prove
 (`!k U (tf:real^N->(num->real^N)->real) c.
     ltensor_field k U tf ==> ltensor_field k U (\x u. c * tf x u)`,
  REWRITE_TAC[ltensor_field] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL
   [AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
    ASM_SIMP_TAC[]]);;

let LRG_SQRT_MUL_POW2 = prove
 (`!c x. &0 <= c ==> c * sqrt x = sqrt(c pow 2 * x)`,
  SIMP_TAC[SQRT_MUL; POW_2_SQRT]);;

let LRG_METRIC_FACTOR_ID = prove
 (`!(G:real^N^N) (S:real^N^N).
     invertible S /\ matrix_inv G = transp S ** S /\ invertible G
     ==> (S ** G) ** transp S = mat 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `G = matrix_inv(S:real^N^N) ** matrix_inv(transp S)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `matrix_inv(matrix_inv(G:real^N^N))` THEN
    CONJ_TAC THENL [REWRITE_TAC[MATRIX_INV_INV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MATRIX_INV_MUL THEN
    ASM_REWRITE_TAC[INVERTIBLE_TRANSP];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  ASM_SIMP_TAC[MATRIX_INV; INVERTIBLE_TRANSP; MATRIX_MUL_RID]);;

let LRG_LTNORM2_METRIC = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> ltnorm2 2 G (lmetric2 G) y = &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `((S:real^N^N) ** (G:real^N->real^N^N) y) ** transp S = mat 1` ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_METRIC_FACTOR_ID THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `U:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2(G:real^N->real^N^N)`; `y:real^N`; `S:real^N^N`]
         LRG_LTNORM2_SQUARES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LRG_LMETRIC2_FIELD]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2; lmetric2; ARITH_EQ] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1..dimindex(:N)) (\p. &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\q. if q = p then &1 else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      BETA_TAC THEN ASM_SIMP_TAC[DOT_BASIS_BASIS] THEN
      ASM_CASES_TAC `p:num = q` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBGOAL_THEN `~(q:num = p)` (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID]]);;

let LRG_LNABLA_ZERO = prove
 (`!k (G:real^N->real^N^N) y u. lnabla k G (\x u. &0) y u = &0`,
  REWRITE_TAC[lnabla; LIFT_NUM; FRECHET_DERIVATIVE_CONST_AT; DROP_VEC;
              SUM_0; REAL_SUB_REFL]);;

let LRG_LNABLA_ITER_METRIC = prove
 (`!U (G:real^N->real^N^N).
     metric_field U G
     ==> !l y u. y IN U ==> lnabla_iter 2 (SUC l) G (lmetric2 G) y u = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[lnabla_iter; ADD_CLAUSES] THEN ASM_MESON_TAC[LNABLA_METRIC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV) [CONJUNCT2 lnabla_iter] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla (2 + SUC l) (G:real^N->real^N^N) (\x u. &0) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[LRG_LNABLA_ZERO]]);;

(* The rescaling estimate LCK_DIST_RESCALE. *)

let LCK_DIST_RESCALE = prove
 (`!k s (G0:real^N->real^N^N) G c y.
      metric_field s G0 /\ metric_field s G /\ y IN s /\ &0 < c
      ==> sqrt(lck_dist2 k G0 (\z. c %% G z) y)
          <= c * sqrt(lck_dist2 k G0 G y) + abs(c - &1) * sqrt(&(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`;
     `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
     `lmetric2 (G0:real^N->real^N^N)`; `c:real`; `c - &1`]
     LRG_TENSOR_FIELD_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
     `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
     `lmetric2 (G0:real^N->real^N^N)`; `c:real`; `c - &1`]
     LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
     `\x u. c * (lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u) +
            (c - &1) * lmetric2 (G0:real^N->real^N^N) x u`]
     LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`]
         LRG_LNABLA_ITER_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lck_dist2] THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (\z. c %% (G:real^N->real^N^N) z) z u - lmetric2 G0 z u) =
    (\x u. c * (lmetric2 G x u - lmetric2 G0 x u) +
           (c - &1) * lmetric2 (G0:real^N->real^N^N) x u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; lmetric2; MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c * sqrt(sum(0..k) (\l. ltnorm2 (2 + l) (G0:real^N->real^N^N)
        (lnabla_iter 2 l G0
           (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)) y)) +
    abs(c - &1) * sqrt(&(dimindex(:N))) =
    sqrt(sum(0..k) (\l. c pow 2 * ltnorm2 (2 + l) G0
        (lnabla_iter 2 l G0 (\z u. lmetric2 G z u - lmetric2 G0 z u)) y)) +
    sqrt(sum(0..k) (\l. if l = 0 then (c - &1) pow 2 * &(dimindex(:N))
                        else &0))`
  SUBST1_TAC THENL
   [BINOP_TAC THENL
     [REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC LRG_SQRT_MUL_POW2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC LRG_SQRT_MUL_POW2 THEN REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SQRT_SUM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `l':num` SUBST_ALL_TAC)
    (SPEC `l:num` num_CASES) THENL
   [REWRITE_TAC[ADD_CLAUSES; lnabla_iter] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sqrt(ltnorm2 2 (G0:real^N->real^N^N)
        (\x u. c * (lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u)) y) +
      sqrt(ltnorm2 2 G0 (\x u. (c - &1) * lmetric2 G0 x u) y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_TRIANGLE THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[LRG_TENSOR_FIELD_CMUL; ETA_AX];
      REWRITE_TAC[LRG_LTNORM2_CMUL; ETA_AX] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
             LRG_LTNORM2_METRIC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[REAL_LE_REFL]];
    REWRITE_TAC[NOT_SUC; SQRT_0; REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ltnorm2 (2 + SUC l') (G0:real^N->real^N^N)
       (\x u. c * lnabla_iter 2 (SUC l') G0
          (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) x u) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_EQ THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_RID];
      REWRITE_TAC[LRG_LTNORM2_CMUL; ETA_AX]]]);;

(* ------------------------------------------------------------------------- *)
(* Curvature stability (LCK_CURVATURE_STABILITY), part 1: an orthonormal     *)
(* frame for G0 at y (G0 y = M' M), tensor bounds in that frame, and the     *)
(* difference of the Christoffel symbols in terms of the covariant           *)
(* derivative of G - G0.                                                     *)
(* ------------------------------------------------------------------------- *)

let LRG_FRAME = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> ?M:real^N^N. invertible M /\ G y = transp M ** M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  EXISTS_TAC `matrix_inv(transp(S:real^N^N))` THEN
  ASM_REWRITE_TAC[INVERTIBLE_MATRIX_INV; INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_INV_TRANSP; TRANSP_TRANSP] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `matrix_inv(matrix_inv((G:real^N->real^N^N) y))` THEN
  CONJ_TAC THENL [REWRITE_TAC[MATRIX_INV_INV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MATRIX_INV_MUL; INVERTIBLE_TRANSP; MATRIX_INV_TRANSP]);;

let LRG_FRAME_DOT = prove
 (`!(A:real^N^N) (M:real^N^N) a b.
     A = transp M ** M ==> (M ** a) dot (M ** b) = a dot (A ** b)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL]);;

let LRG_TENSOR_FRAME_BOUND = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (M:real^N^N) a.
     metric_field U G /\ ltensor_field k U tf /\ y IN U /\ G y = transp M ** M
     ==> abs(tf y a) <=
         sqrt(ltnorm2 k G tf y) * product(1..k) (\m. norm(M ** a m))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_ABS_LE_SQRT_MUL THEN
  EXISTS_TAC `ltnorm2 k (G:real^N->real^N^N) tf y` THEN
  REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `G:real^N->real^N^N`;
                   `tf:real^N->(num->real^N)->real`; `y:real^N`;
                   `a:num->real^N`] LRG_LTNORM2_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
    AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2; GSYM PRODUCT_MUL_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_POW_2; NORM_POW_2] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_FRAME_DOT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE]]);;

let LRG_NH_CHRISTOFFEL = prove
 (`!s (G0:real^N->real^N^N) G z u.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) z u =
         u 2 dot (G z ** (christoffel G z (u 3) (u 1) -
                          christoffel G0 z (u 3) (u 1))) +
         u 1 dot (G z ** (christoffel G z (u 3) (u 2) -
                          christoffel G0 z (u 3) (u 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. lift(u 1 dot ((G:real^N->real^N^N) x ** u 2) -
               u 1 dot (G0 x ** u 2))) has_derivative
     (\w. lift(u 1 dot (mderiv G z w ** u 2) -
               u 1 dot (mderiv G0 z w ** u 2)))) (at z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC LRG_HAS_DERIVATIVE_GDOT THEN
    ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
    ALL_TAC] THEN
  REWRITE_TAC[lnabla; lmetric2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[LIFT_DROP; SUM_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 3`; `(u:num->real^N) 2`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`;
                 `(u:num->real^N) 1`; `(u:num->real^N) 3`; `(u:num->real^N) 2`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`;
                 `christoffel (G0:real^N->real^N^N) z (u 3) (u 1)`;
                 `(u:num->real^N) 2`] LRG_METRIC_SYM) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`;
                 `christoffel (G0:real^N->real^N^N) z (u 3) (u 1)`;
                 `(u:num->real^N) 2`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN REAL_ARITH_TAC);;

(* The Christoffel difference A = Gamma(G) - Gamma(G0), lowered with G, is   *)
(* the Koszul combination of the G0-covariant derivative of G - G0, and so   *)
(* is its G0-covariant derivative.                                           *)

let LRG_CHRISTOFFEL_DIFF_K = prove
 (`!s (G0:real^N->real^N^N) G z u.
     metric_field s G0 /\ metric_field s G /\ z IN s
     ==> u 3 dot (G z ** (christoffel G z (u 1) (u 2) -
                          christoffel G0 z (u 1) (u 2))) =
         inv(&2) *
         (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) z
            (\m. u((swap(1,2) o swap(2,3)) m)) +
          lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) z
            (\m. u(swap(2,3) m)) -
          lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) z u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `z:real^N`] LRG_NH_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[o_THM; swap; ARITH] THEN
  MAP_EVERY (fun (a,b) ->
    MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; a; b]
           CHRISTOFFEL_SYM) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`; a; b]
           CHRISTOFFEL_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC)
   [`(u:num->real^N) 2`,`(u:num->real^N) 1`;
    `(u:num->real^N) 1`,`(u:num->real^N) 3`;
    `(u:num->real^N) 2`,`(u:num->real^N) 3`] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN REAL_ARITH_TAC);;

let LRG_LNABLA3_K = prove
 (`!s (G0:real^N->real^N^N) G y u.
     metric_field s G0 /\ metric_field s G /\ y IN s
     ==> lnabla 3 G0
           (\z u. u 3 dot (G z ** (christoffel G z (u 1) (u 2) -
                                   christoffel G0 z (u 1) (u 2)))) y u =
         inv(&2) *
         (lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u)) y
            (\m. u((swap(1,2) o swap(2,3)) m)) +
          lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u)) y
            (\m. u(swap(2,3) m)) -
          lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u)) y u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. (\x. lift(lnabla 2 (G0:real^N->real^N^N)
                   (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)
                   x v)) differentiable at y`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `swap(2,3) permutes 1..3 /\ (swap(1,2) o swap(2,3)) permutes 1..3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PERMUTES_SWAP;
      MATCH_MP_TAC PERMUTES_COMPOSE THEN CONJ_TAC THEN
      MATCH_MP_TAC PERMUTES_SWAP] THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lnabla 3 (G0:real^N->real^N^N)
     (\x u. inv(&2) *
       (lnabla 2 G0 (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) x
          (\m. u((swap(1,2) o swap(2,3)) m)) +
        lnabla 2 G0 (\z u. lmetric2 G z u - lmetric2 G0 z u) x
          (\m. u(swap(2,3) m)) -
        lnabla 2 G0 (\z u. lmetric2 G z u - lmetric2 G0 z u) x u)) y u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF_K THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`3`; `G0:real^N->real^N^N`;
     `\x u. lnabla 2 (G0:real^N->real^N^N)
              (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) x
              (\m. u((swap(1,2) o swap(2,3)) m)) +
            (lnabla 2 G0 (\z u. lmetric2 G z u - lmetric2 G0 z u) x
              (\m. u(swap(2,3) m)) -
             lnabla 2 G0 (\z u. lmetric2 G z u - lmetric2 G0 z u) x u)`;
     `inv(&2)`; `y:real^N`; `u:num->real^N`] LRG_LNABLA_CMUL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LIFT_ADD; LIFT_SUB; DIFFERENTIABLE_ADD; DIFFERENTIABLE_SUB];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`3`; `G0:real^N->real^N^N`;
     `\x u. lnabla 2 (G0:real^N->real^N^N)
              (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) x
              (\m. u((swap(1,2) o swap(2,3)) m))`;
     `\x u. lnabla 2 (G0:real^N->real^N^N)
              (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) x
              (\m. u(swap(2,3) m)) -
            lnabla 2 G0 (\z u. lmetric2 G z u - lmetric2 G0 z u) x u`;
     `y:real^N`; `u:num->real^N`] LRG_LNABLA_ADD) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LIFT_ADD; LIFT_SUB; DIFFERENTIABLE_ADD; DIFFERENTIABLE_SUB];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`3`; `G0:real^N->real^N^N`;
     `\x u. lnabla 2 (G0:real^N->real^N^N)
              (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u) x
              (\m. u(swap(2,3) m))`;
     `lnabla 2 (G0:real^N->real^N^N)
        (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
     `y:real^N`; `u:num->real^N`] LRG_LNABLA_SUB) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LIFT_ADD; LIFT_SUB; DIFFERENTIABLE_ADD; DIFFERENTIABLE_SUB];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`3`; `G0:real^N->real^N^N`;
     `lnabla 2 (G0:real^N->real^N^N)
        (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
     `swap(1,2) o swap(2,3)`; `y:real^N`; `u:num->real^N`]
     LRG_LNABLA_PERMUTE) THEN
  MP_TAC(ISPECL [`3`; `G0:real^N->real^N^N`;
     `lnabla 2 (G0:real^N->real^N^N)
        (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
     `swap(2,3)`; `y:real^N`; `u:num->real^N`]
     LRG_LNABLA_PERMUTE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

(* The derivative of the Christoffel difference, lowered with G, in terms of *)
(* the G0-covariant derivative of the lowered difference.                    *)

let LRG_DA_FORM = prove
 (`!s (G0:real^N->real^N^N) G y u.
     metric_field s G0 /\ metric_field s G /\ y IN s
     ==> u 3 dot (G y **
                  (frechet_derivative (\z. christoffel G z (u 1) (u 2)) (at y) (u 4) -
                   frechet_derivative (\z. christoffel G0 z (u 1) (u 2)) (at y) (u 4))) =
         lnabla 3 G0
           (\z u. u 3 dot (G z ** (christoffel G z (u 1) (u 2) -
                                   christoffel G0 z (u 1) (u 2)))) y u +
         u 3 dot (G y ** (christoffel G y (christoffel G0 y (u 4) (u 1)) (u 2) -
                          christoffel G0 y (christoffel G0 y (u 4) (u 1)) (u 2))) +
         u 3 dot (G y ** (christoffel G y (u 1) (christoffel G0 y (u 4) (u 2)) -
                          christoffel G0 y (u 1) (christoffel G0 y (u 4) (u 2)))) -
         (christoffel G y (u 1) (u 2) - christoffel G0 y (u 1) (u 2)) dot
         (G y ** (christoffel G y (u 4) (u 3) - christoffel G0 y (u 4) (u 3))) -
         u 3 dot (G y ** christoffel G y (u 4)
                          (christoffel G y (u 1) (u 2) - christoffel G0 y (u 1) (u 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. christoffel (G:real^N->real^N^N) z (u 1) (u 2) -
          christoffel G0 z (u 1) (u 2)) has_derivative
     (\w. frechet_derivative (\z. christoffel G z (u 1) (u 2)) (at y) w -
          frechet_derivative (\z. christoffel G0 z (u 1) (u 2)) (at y) w)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    CONJ_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`G:real^N->real^N^N`;
    `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                         (G:real^N->real^N^N)) (at y)`;
    `(\z. (u:num->real^N) 3):real^N->real^N`; `(\w. vec 0):real^N->real^N`;
    `\z. christoffel (G:real^N->real^N^N) z (u 1) (u 2) -
         christoffel G0 z (u 1) (u 2)`;
    `\w. frechet_derivative (\z. christoffel (G:real^N->real^N^N) z (u 1) (u 2))
           (at y) w -
         frechet_derivative (\z. christoffel G0 z (u 1) (u 2)) (at y) w`;
    `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_METRIC_FIELD_DIFF) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LZERO; REAL_ADD_LID; GSYM mderiv] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[lnabla; GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LIFT_DROP; SUM_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DOT_RADD] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(u:num->real^N) 3`; `(u:num->real^N) 4`;
                 `christoffel (G:real^N->real^N^N) y (u 1) (u 2) -
                  christoffel G0 y (u 1) (u 2)`]
         LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G0:real^N->real^N^N) y (u 4) (u 3)`;
                 `christoffel (G:real^N->real^N^N) y (u 1) (u 2) -
                  christoffel G0 y (u 1) (u 2)`]
         LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              DOT_RSUB; DOT_RADD] THEN
  REAL_ARITH_TAC);;

(* The difference of the curvature tensors, lowered with G:                  *)
(* g(R(u,v)w - R0(u,v)w, x) = (nabla_u T)(v,w,x) - (nabla_v T)(u,w,x)        *)
(*                            + g(A(u,w), A(v,x)) - g(A(v,w), A(u,x)),       *)
(* where T(a,b,c) = g(A(a,b), c), A = Gamma(G) - Gamma(G0), nabla from G0.    *)

let LRG_RIEMANN_DIFF_Q = prove
 (`!s (G0:real^N->real^N^N) G y u v w x.
     metric_field s G0 /\ metric_field s G /\ y IN s
     ==> x dot (G y ** (lriemann G y u v w - lriemann G0 y u v w)) =
         lnabla 3 G0
           (\z u. u 3 dot (G z ** (christoffel G z (u 1) (u 2) -
                                   christoffel G0 z (u 1) (u 2)))) y
           (\m. if m = 1 then v else if m = 2 then w else if m = 3 then x else u) -
         lnabla 3 G0
           (\z u. u 3 dot (G z ** (christoffel G z (u 1) (u 2) -
                                   christoffel G0 z (u 1) (u 2)))) y
           (\m. if m = 1 then u else if m = 2 then w else if m = 3 then x else v) +
         (christoffel G y u w - christoffel G0 y u w) dot
         (G y ** (christoffel G y v x - christoffel G0 y v x)) -
         (christoffel G y v w - christoffel G0 y v w) dot
         (G y ** (christoffel G y u x - christoffel G0 y u x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`;
                 `\m. if m = 1 then v else if m = 2 then w else if m = 3 then x
                      else u:real^N`] LRG_DA_FORM) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`;
                 `\m. if m = 1 then u else if m = 2 then w else if m = 3 then x
                      else v:real^N`] LRG_DA_FORM) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `christoffel (G:real^N->real^N^N) y u
      (christoffel G y v w - christoffel G0 y v w) =
    christoffel G y u (christoffel G y v w) -
    christoffel G y u (christoffel G0 y v w) /\
    christoffel G y v (christoffel G y u w - christoffel G0 y u w) =
    christoffel G y v (christoffel G y u w) -
    christoffel G y v (christoffel G0 y u w)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_CHRISTOFFEL_LINEAR) THEN
    ASM_SIMP_TAC[LINEAR_SUB];
    ALL_TAC] THEN
  REWRITE_TAC[lriemann] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              DOT_RSUB; DOT_RADD; DOT_LSUB] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Curvature stability, part 2: pointwise bounds in a G0-orthonormal frame.  *)
(* Hypotheses: G0 y = M' M and the bounds delta on G - G0, nabla(G - G0) and *)
(* nabla^2(G - G0) at y, all measured with the frame norms |M a|.           *)
(* ------------------------------------------------------------------------- *)

let LRG_TUPLE_EQ_TAC =
  REWRITE_TAC[FUN_EQ_THM; o_THM; swap] THEN X_GEN_TAC `m:num` THEN
  MAP_EVERY (fun n -> ASM_CASES_TAC (mk_eq(`m:num`, mk_small_numeral n)) THEN
                      ASM_REWRITE_TAC[ARITH]) [1;2;3;4];;

let LRG_QUAD_ROOT0 = prove
 (`!c t. &0 <= c /\ &0 <= t /\ t pow 2 <= c * t ==> t <= c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `t pow 2 <= c * t` THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ]);;

let LRG_QUAD_ROOT_BOUND = prove
 (`!c d p t. &0 <= c /\ &0 <= d /\ d <= &1 / &10 /\ &0 <= p /\ &0 <= t /\
             (&1 - d) * t pow 2 <= c * d * p * t
             ==> t <= &10 / &9 * c * d * p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - d) * t <= c * d * p` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 - d) * t pow 2 <= c * d * p * t` THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `d * t <= &1 / &10 * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let LRG_PERT_G = prove
 (`!(G0:real^N->real^N^N) G y (M:real^N^N) delta.
     G0 y = transp M ** M /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b))
     ==> (!x. (&1 - delta) * norm(M ** x) pow 2 <= x dot (G y ** x)) /\
         (!a b. abs(a dot (G y ** b)) <= (&1 + delta) * norm(M ** a) * norm(M ** b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H0")) THEN
  SUBGOAL_THEN
   `!a b. a dot ((G0:real^N->real^N^N) y ** b) = ((M:real^N^N) ** a) dot (M ** b)`
  (LABEL_TAC "D") THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_FRAME_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [USE_THEN "H0" (MP_TAC o SPECL [`x:real^N`; `x:real^N`]) THEN
    USE_THEN "D" (fun th -> REWRITE_TAC[th; GSYM NORM_POW_2]) THEN REAL_ARITH_TAC;
    USE_THEN "H0" (MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    MP_TAC(ISPECL [`(M:real^N^N) ** a`; `(M:real^N^N) ** b`]
           NORM_CAUCHY_SCHWARZ_ABS) THEN
    USE_THEN "D" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC]);;

let LRG_CHRISTOFFEL_DIFF_K3 = prove
 (`!s (G0:real^N->real^N^N) G y a b c.
     metric_field s G0 /\ metric_field s G /\ y IN s
     ==> c dot (G y ** (christoffel G y a b - christoffel G0 y a b)) =
         inv(&2) *
         (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y
            (\m. if m = 1 then b else if m = 2 then c else a) +
          lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y
            (\m. if m = 1 then a else if m = 2 then c else b) -
          lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y
            (\m. if m = 1 then a else if m = 2 then b else c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                 `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`]
         LNABLA_TENSOR_FIELD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ltensor_field] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `\m. if m = 1 then a else if m = 2 then b else c:real^N`]
         LRG_CHRISTOFFEL_DIFF_K) THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= m /\ m <= 3 <=> m = 1 \/ m = 2 \/ m = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM; swap; ARITH]);;

let LRG_LNABLA3_K4 = prove
 (`!s (G0:real^N->real^N^N) G y a b c x.
     metric_field s G0 /\ metric_field s G /\ y IN s
     ==> lnabla 3 G0
           (\z u. u 3 dot (G z ** (christoffel G z (u 1) (u 2) -
                                   christoffel G0 z (u 1) (u 2)))) y
           (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else x) =
         inv(&2) *
         (lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u)) y
            (\m. if m = 1 then b else if m = 2 then c else if m = 3 then a else x) +
          lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u)) y
            (\m. if m = 1 then a else if m = 2 then c else if m = 3 then b else x) -
          lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u)) y
            (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c else x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`;
                 `\m. if m = 1 then a else if m = 2 then b else if m = 3 then c
                      else x:real^N`]
         LRG_LNABLA3_K) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THENL [ALL_TAC; BINOP_TAC] THEN
  AP_TERM_TAC THEN LRG_TUPLE_EQ_TAC);;

(* Bounds on A = Gamma(G) - Gamma(G0), on nabla T, and on the difference of  *)
(* the curvature tensors, in the frame norms.                                *)

let LRG_PERT_T = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3))
     ==> !a b c. abs(c dot (G y ** (christoffel G y a b - christoffel G0 y a b))) <=
                 &3 / &2 * delta * norm(M ** a) * norm(M ** b) * norm(M ** c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `a:real^N`; `b:real^N`; `c:real^N`]
         LRG_CHRISTOFFEL_DIFF_K3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `\m. if m = 1 then (b:real^N) else if m = 2 then c else a` th) THEN
    MP_TAC(SPEC `\m. if m = 1 then (a:real^N) else if m = 2 then c else b` th) THEN
    MP_TAC(SPEC `\m. if m = 1 then (a:real^N) else if m = 2 then b else c` th)) THEN
  REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

let LRG_PERT_A = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &10 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3))
     ==> !a b. norm(M ** (christoffel G y a b - christoffel G0 y a b)) <=
               &2 * delta * norm(M ** a) * norm(M ** b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_T) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "T") THEN
  SUBGOAL_THEN `&0 <= delta * norm((M:real^N^N) ** a) * norm(M ** b)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&10 / &9 * &3 / &2 * delta * (norm((M:real^N^N) ** a) * norm(M ** b))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LRG_QUAD_ROOT_BOUND THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "T" (MP_TAC o SPECL
    [`a:real^N`; `b:real^N`;
     `christoffel (G:real^N->real^N^N) y a b - christoffel G0 y a b`]) THEN
  USE_THEN "G1" (MP_TAC o SPEC
    `christoffel (G:real^N->real^N^N) y a b - christoffel G0 y a b`) THEN
  REAL_ARITH_TAC);;

let LRG_PERT_L = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !a b c x.
           abs(lnabla 3 G0
                 (\z u. u 3 dot (G z ** (christoffel G z (u 1) (u 2) -
                                         christoffel G0 z (u 1) (u 2)))) y
                 (\m. if m = 1 then a else if m = 2 then b else if m = 3 then c
                      else x)) <=
           &3 / &2 * delta * norm(M ** a) * norm(M ** b) * norm(M ** c) *
           norm(M ** x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `a:real^N`; `b:real^N`; `c:real^N`; `x:real^N`]
         LRG_LNABLA3_K4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `\m. if m = 1 then (b:real^N) else if m = 2 then c
                     else if m = 3 then a else x` th) THEN
    MP_TAC(SPEC `\m. if m = 1 then (a:real^N) else if m = 2 then c
                     else if m = 3 then b else x` th) THEN
    MP_TAC(SPEC `\m. if m = 1 then (a:real^N) else if m = 2 then b
                     else if m = 3 then c else x` th)) THEN
  REWRITE_TAC[ARITH] THEN REAL_ARITH_TAC);;

let LRG_PERT_PROD = prove
 (`!d n1 n2 b1 b2 q.
     &0 <= d /\ &0 <= n1 /\ &0 <= n2 /\ n1 <= b1 /\ n2 <= b2 /\
     abs q <= d * n1 * n2
     ==> abs q <= d * b1 * b2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `d * n1 * n2` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

let LRG_PERT_ARITH1 = prove
 (`!d P l1 l2 g1 g2.
     &0 <= d /\ d <= &1 / &10 /\ &0 <= P /\
     abs l1 <= &3 / &2 * d * P /\ abs l2 <= &3 / &2 * d * P /\
     abs g1 <= (&1 + d) * (&4 * d pow 2 * P) /\
     abs g2 <= (&1 + d) * (&4 * d pow 2 * P)
     ==> abs(l1 - l2 + g1 - g2) <= &4 * d * P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= d * P` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `d pow 2 * P <= &1 / &10 * (d * P)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d pow 3 * P <= &1 / &10 * (d pow 2 * P)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 = SUC 2`; real_pow; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The difference of the curvature tensors is O(delta) in the frame norms;  *)
(* the curvature of G0 is bounded by the bound on |Rm(G0)|.                  *)

let LRG_PERT_Q = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &10 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !u v w x.
           abs(x dot (G y ** (lriemann G y u v w - lriemann G0 y u v w))) <=
           &4 * delta * norm(M ** u) * norm(M ** v) * norm(M ** w) * norm(M ** x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "A") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_L) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "L") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `u:real^N`; `v:real^N`; `w:real^N`; `x:real^N`]
         LRG_RIEMANN_DIFF_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LRG_PERT_ARITH1 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "L" (MP_TAC o SPECL [`v:real^N`; `w:real^N`; `x:real^N`; `u:real^N`]) THEN
    REAL_ARITH_TAC;
    USE_THEN "L" (MP_TAC o SPECL [`u:real^N`; `w:real^N`; `x:real^N`; `v:real^N`]) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 + delta) *
                (&2 * delta * norm((M:real^N^N) ** u) * norm(M ** w)) *
                (&2 * delta * norm(M ** v) * norm(M ** x))` THEN
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
                (&2 * delta * norm((M:real^N^N) ** v) * norm(M ** w)) *
                (&2 * delta * norm(M ** u) * norm(M ** x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_PERT_PROD THEN
      EXISTS_TAC `norm((M:real^N^N) **
                   (christoffel (G:real^N->real^N^N) y v w - christoffel G0 y v w))` THEN
      EXISTS_TAC `norm((M:real^N^N) **
                   (christoffel (G:real^N->real^N^N) y u x - christoffel G0 y u x))` THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= d ==> &0 <= &1 + d`];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING]]);;

let LRG_PERT_R = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &10 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !u v w.
           norm(M ** (lriemann G y u v w - lriemann G0 y u v w)) <=
           &5 * delta * norm(M ** u) * norm(M ** v) * norm(M ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "G1") (LABEL_TAC "G2")) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "Q") THEN
  SUBGOAL_THEN
   `&0 <= delta * norm((M:real^N^N) ** u) * norm(M ** v) * norm(M ** w)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&10 / &9 * &4 * delta *
              (norm((M:real^N^N) ** u) * norm(M ** v) * norm(M ** w))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC LRG_QUAD_ROOT_BOUND THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "Q" (MP_TAC o SPECL
    [`u:real^N`; `v:real^N`; `w:real^N`;
     `lriemann (G:real^N->real^N^N) y u v w - lriemann G0 y u v w`]) THEN
  USE_THEN "G1" (MP_TAC o SPEC
    `lriemann (G:real^N->real^N^N) y u v w - lriemann G0 y u v w`) THEN
  REAL_ARITH_TAC);;

let LRG_RM0_BOUND = prove
 (`!s (G0:real^N->real^N^N) y (M:real^N^N) K.
     metric_field s G0 /\ y IN s /\ G0 y = transp M ** M /\ &0 <= K /\
     (!u. abs(lrm4 G0 y u) <=
          K * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !u v w. norm(M ** lriemann G0 y u v w) <=
                 K * norm(M ** u) * norm(M ** v) * norm(M ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC LRG_QUAD_ROOT0 THEN
  ASM_SIMP_TAC[NORM_POS_LE; REAL_LE_MUL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `\m. if m = 1 then (u:real^N) else if m = 2 then v
        else if m = 3 then lriemann (G0:real^N->real^N^N) y u v w else w`) THEN
  REWRITE_TAC[lrm4; ARITH] THEN
  SUBGOAL_THEN
   `lriemann (G0:real^N->real^N^N) y u v w dot (G0 y ** lriemann G0 y u v w) =
    norm((M:real^N^N) ** lriemann G0 y u v w) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC LRG_FRAME_DOT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Traces in a frame; the Ricci and scalar curvature estimates.             *)

let LRG_TRACE_BASIS = prove
 (`!A:real^N^N. trace A = sum(1..dimindex(:N)) (\i. (A ** basis i)$i)`,
  GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]);;

let LRG_TRACE_FRAME = prove
 (`!(f:real^N->real^N) (M:real^N^N).
     linear f /\ invertible M
     ==> sum(1..dimindex(:N)) (\k. f(basis k)$k) =
         sum(1..dimindex(:N)) (\i. (M ** f(matrix_inv M ** basis i))$i)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `trace(matrix(f:real^N->real^N))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`matrix(f:real^N->real^N)`; `matrix_inv(M:real^N^N)`]
         TRACE_SIMILAR) THEN
  ASM_REWRITE_TAC[INVERTIBLE_MATRIX_INV; MATRIX_INV_INV] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LRG_TRACE_BASIS] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_WORKS]);;

let LRG_TRACE_FRAME_BOUND = prove
 (`!(f:real^N->real^N) (M:real^N^N) c.
     linear f /\ invertible M /\ (!x. norm(M ** f x) <= c * norm(M ** x))
     ==> abs(sum(1..dimindex(:N)) (\k. f(basis k)$k)) <= &(dimindex(:N)) * c`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LRG_TRACE_FRAME] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(CARD(1..dimindex(:N))) * c` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((M:real^N^N) ** f(matrix_inv M ** basis i))` THEN
  REWRITE_TAC[COMPONENT_LE_NORM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * norm((M:real^N^N) ** matrix_inv M ** basis i)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
               NORM_BASIS; REAL_MUL_RID; REAL_LE_REFL]);;

(* Ricci and scalar curvature: bounds through traces in the frame.          *)

let LRG_PERT_RICCI = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     invertible M /\ &0 <= delta /\ delta <= &1 / &10 /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !v w. abs(lricci G y v w - lricci G0 y v w) <=
               &(dimindex(:N)) * (&5 * delta * norm(M ** v) * norm(M ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_R) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[lricci; GSYM SUM_SUB_NUMSEG; GSYM VECTOR_SUB_COMPONENT] THEN
  MP_TAC(ISPECL
   [`\x. lriemann (G:real^N->real^N^N) y x v w - lriemann G0 y x v w`;
    `M:real^N^N`;
    `&5 * delta * norm((M:real^N^N) ** v) * norm(M ** w)`]
   LRG_TRACE_FRAME_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
             LRIEMANN_TRILINEAR) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
             LRIEMANN_TRILINEAR) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^N` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `v:real^N`; `w:real^N`]) THEN
      REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC]);;

let LRG_RICCI0_BOUND = prove
 (`!s (G0:real^N->real^N^N) y (M:real^N^N) K.
     metric_field s G0 /\ y IN s /\ G0 y = transp M ** M /\ invertible M /\
     &0 <= K /\
     (!u. abs(lrm4 G0 y u) <=
          K * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4))
     ==> !v w. abs(lricci G0 y v w) <=
               &(dimindex(:N)) * (K * norm(M ** v) * norm(M ** w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `K:real`] LRG_RM0_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[lricci] THEN
  MP_TAC(ISPECL
   [`\x. lriemann (G0:real^N->real^N^N) y x v w`; `M:real^N^N`;
    `K * norm((M:real^N^N) ** v) * norm(M ** w)`]
   LRG_TRACE_FRAME_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
             LRIEMANN_TRILINEAR) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^N` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `v:real^N`; `w:real^N`]) THEN
      REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC]);;

let LRG_LSCALAR_TRACE = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> lscalar G y =
         trace(matrix_inv(G y) **
               ((lambda i j. lricci G y (basis i) (basis j)):real^N^N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lscalar; trace] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[matrix_mul; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  BETA_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[LRICCI_SYM]);;

let LRG_QUAD_ROOT1 = prove
 (`!d q t. &0 <= d /\ d <= &1 / &10 /\ &0 <= q /\ &0 <= t /\
           (&1 - d) * t pow 2 <= q * t
           ==> t <= &10 / &9 * q`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - d) * t <= q` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 - d) * t pow 2 <= q * t` THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `d * t <= &1 / &10 * t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let LRG_ENDO_BOUND = prove
 (`!(A:real^N^N) (M:real^N^N) b delta q.
     invertible A /\ &0 <= delta /\ delta <= &1 / &10 /\ &0 <= q /\
     (!x. (&1 - delta) * norm(M ** x) pow 2 <= x dot (A ** x)) /\
     (!z. abs(z dot b) <= q * norm(M ** z))
     ==> norm(M ** (matrix_inv A ** b)) <= &10 / &9 * q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_QUAD_ROOT1 THEN
  EXISTS_TAC `delta:real` THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `matrix_inv(A:real^N^N) ** b`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `matrix_inv(A:real^N^N) ** b`) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  REAL_ARITH_TAC);;

(* The scalar curvature estimate. *)

let LRG_PERT_SCALAR = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta K.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     invertible M /\ &0 <= delta /\ delta <= &1 / &10 /\ &0 <= K /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!a b. abs(lricci G y a b - lricci G0 y a b) <=
            &(dimindex(:N)) * (&5 * delta * norm(M ** a) * norm(M ** b))) /\
     (!a b. abs(lricci G0 y a b) <=
            &(dimindex(:N)) * (K * norm(M ** a) * norm(M ** b)))
     ==> abs(lscalar G y - lscalar G0 y) <=
         &(dimindex(:N)) * (&6 * &(dimindex(:N)) * delta * (&1 + K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y) /\
                invertible((G0:real^N->real^N^N) y)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G0:real^N->real^N^N`; `G:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `delta:real`] LRG_PERT_G) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "G1" o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!x. (&1 - &0) * norm((M:real^N^N) ** x) pow 2 <=
        x dot ((G0:real^N->real^N^N) y ** x)`
  (LABEL_TAC "G01") THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; NORM_POW_2] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LRG_FRAME_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(G0:real^N->real^N^N) y = transp (M:real^N^N) ** M` THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_LSCALAR_TRACE) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
         LRG_LSCALAR_TRACE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM TRACE_SUB; LRG_TRACE_BASIS] THEN
  MP_TAC(ISPECL
   [`\x. (matrix_inv((G:real^N->real^N^N) y) **
          ((lambda i j. lricci G y (basis i) (basis j)):real^N^N) -
          matrix_inv((G0:real^N->real^N^N) y) **
          ((lambda i j. lricci G0 y (basis i) (basis j)):real^N^N)) ** x`;
    `M:real^N^N`;
    `&6 * &(dimindex(:N)) * delta * (&1 + K)`] LRG_TRACE_FRAME_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN X_GEN_TAC `x:real^N` THEN
  SUBGOAL_THEN
   `(matrix_inv((G:real^N->real^N^N) y) **
     ((lambda i j. lricci G y (basis i) (basis j)):real^N^N) -
     matrix_inv((G0:real^N->real^N^N) y) **
     ((lambda i j. lricci G0 y (basis i) (basis j)):real^N^N)) ** x =
    matrix_inv(G y) **
    ((((lambda i j. lricci G y (basis i) (basis j)):real^N^N) -
      ((lambda i j. lricci G0 y (basis i) (basis j)):real^N^N)) ** x +
     (G0 y - G y) **
     (matrix_inv(G0 y) **
      (((lambda i j. lricci G0 y (basis i) (basis j)):real^N^N) ** x)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(!v. (G0:real^N->real^N^N) y ** (matrix_inv(G0 y) ** v) = v) /\
      (!v. matrix_inv((G:real^N->real^N^N) y) ** (G y ** v) = v)`
    (fun th -> REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB;
                           MATRIX_VECTOR_MUL_ADD_LDISTRIB;
                           MATRIX_VECTOR_MUL_SUB_LDISTRIB;
                           GSYM MATRIX_VECTOR_MUL_ASSOC; th])
    THENL
     [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `Y0 = matrix_inv((G0:real^N->real^N^N) y) **
         (((lambda i j. lricci G0 y (basis i) (basis j)):real^N^N) ** x)` THEN
  SUBGOAL_THEN
   `norm((M:real^N^N) ** Y0) <=
    &10 / &9 * (&(dimindex(:N)) * K * norm(M ** x))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Y0" THEN MATCH_MP_TAC LRG_ENDO_BOUND THEN
    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; NORM_POS_LE] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                   `z:real^N`; `x:real^N`] LRG_LRICCI_DOT_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `x:real^N`]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&10 / &9 * (&(dimindex(:N)) * (&5 * delta * norm((M:real^N^N) ** x)) +
                          delta * norm(M ** Y0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_ENDO_BOUND THEN EXISTS_TAC `delta:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS; NORM_POS_LE];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; DOT_RADD; DOT_RSUB] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                   `z:real^N`; `x:real^N`] LRG_LRICCI_DOT_FORM) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `z:real^N`; `x:real^N`] LRG_LRICCI_DOT_FORM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `x:real^N`] o
                  check (fun th -> can (find_term ((=) `lricci (G:real^N->real^N^N) y`))
                                     (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `Y0:real^N`] o
                  check (fun th -> can (find_term ((=) `(G:real^N->real^N^N) y`))
                                     (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &(dimindex(:N)) * delta * norm((M:real^N^N) ** x) /\
                &0 <= &(dimindex(:N)) * K * delta * norm((M:real^N^N) ** x)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `delta * norm((M:real^N^N) ** Y0) <=
                delta * (&10 / &9 * (&(dimindex(:N)) * K * norm(M ** x)))`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The sectional curvature estimate: real arithmetic, and invariance of the *)
(* sectional curvature under v -> v - c u.                                  *)

let LRG_QUOT_ARITH = prove
 (`!NG N0 WG W0 c1 c2 e.
     &0 < W0 /\ &0 <= c1 /\ &0 <= c2 /\ &0 <= e /\ e <= &1 / &2 /\
     abs(WG - W0) <= e * W0 /\ abs(NG - N0) <= c1 * W0 /\ abs N0 <= c2 * W0
     ==> abs(NG / WG - N0 / W0) <= &2 * (c1 + c2 * e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e * W0 <= &1 / &2 * W0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < WG /\ W0 <= &2 * WG` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `NG / WG - N0 / W0 = ((NG - N0) * W0 + N0 * (W0 - WG)) / (WG * W0)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < WG`; `&0 < W0`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LT_MUL; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `abs((NG - N0) * W0) <= (c1 * W0) * W0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(N0 * (W0 - WG)) <= (c2 * W0) * (e * W0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c1 + c2 * e) * W0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `((c1 + c2 * e) * W0) * W0 <= ((c1 + c2 * e) * W0) * (&2 * WG)`
  ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let LRG_SECT_ARITH = prove
 (`!a b h1 h2 h3 d NG N0 c1 c2.
     &0 <= a /\ &0 <= b /\ &0 <= d /\ d <= &1 / &10 /\ &0 <= c1 /\ &0 <= c2 /\
     abs h1 <= d * a /\ abs h2 <= d * b /\ h3 pow 2 <= d pow 2 * (a * b) /\
     abs(NG - N0) <= c1 * (a * b) /\ abs N0 <= c2 * (a * b)
     ==> abs(NG / ((a + h1) * (b + h2) - h3 pow 2) - N0 / (a * b)) <=
         &2 * (c1 + c2 * (&3 * d))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a * b = &0` THENL
   [SUBGOAL_THEN `NG = &0 /\ N0 = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `abs(NG - N0) <= c1 * (a * b)` THEN
      UNDISCH_TAC `abs N0 <= c2 * (a * b)` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_ADD THEN
           CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a * b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_LE; REAL_LE_MUL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LRG_QUOT_ARITH THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a * abs h2 <= a * (d * b) /\ b * abs h1 <= b * (d * a) /\
                abs h1 * abs h2 <= (d * a) * (d * b)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d pow 2 * (a * b) <= &1 / &10 * (d * (a * b))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(a * h2) = a * abs h2 /\ abs(b * h1) = b * abs h1 /\
                abs(h1 * h2) = abs h1 * abs h2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`];
    ALL_TAC] THEN
  MP_TAC(SPEC `h3:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a + h1) * (b + h2) - h3 pow 2 - a * b =
                a * h2 + b * h1 + h1 * h2 - h3 pow 2`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let LSECTIONAL_SHEAR = prove
 (`!U (G:real^N->real^N^N) y u v c.
     metric_field U G /\ y IN U
     ==> lsectional G y u (v - c % u) = lsectional G y u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "l2") (LABEL_TAC "l3"))) THEN
  SUBGOAL_THEN `!w. lriemann (G:real^N->real^N^N) y u u w = vec 0` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `u:real^N`; `u:real^N`; `w:real^N`] LRIEMANN_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lriemann (G:real^N->real^N^N) y u (v - c % u) (v - c % u) =
    lriemann G y u v v - c % lriemann G y u v u`
  SUBST1_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
      [`\x. lriemann (G:real^N->real^N^N) y u x (v - c % u)`;
       `v:real^N`; `c % u:real^N`] LINEAR_SUB)) THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\x. lriemann (G:real^N->real^N^N) y u x (v - c % u)`;
       `c:real`; `u:real^N`] LINEAR_CMUL)) THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\x. lriemann (G:real^N->real^N^N) y u v x`;
       `v:real^N`; `c % u:real^N`] LINEAR_SUB)) THEN
    MP_TAC(BETA_RULE(ISPECL
      [`\x. lriemann (G:real^N->real^N^N) y u v x`;
       `c:real`; `u:real^N`] LINEAR_CMUL)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u dot ((G:real^N->real^N^N) y ** lriemann G y u v u) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `u:real^N`; `v:real^N`; `u:real^N`; `u:real^N`]
           LRIEMANN_METRIC_ANTISYM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `v:real^N`; `u:real^N`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_RSUB; DOT_RMUL; DOT_LSUB; DOT_LMUL] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* The sectional curvature estimate. *)

let LRG_PERT_SECT_ORTH = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta K u v.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &10 /\ &0 <= K /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4)) /\
     (!u v w. norm(M ** lriemann G0 y u v w) <=
              K * norm(M ** u) * norm(M ** v) * norm(M ** w)) /\
     u dot (G0 y ** v) = &0
     ==> abs(lsectional G y u v - lsectional G0 y u v) <= &8 * (&1 + K) * delta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H0")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "R0") (LABEL_TAC "O")))))))))))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "Q") THEN
  SUBGOAL_THEN
   `!a b. a dot ((G0:real^N->real^N^N) y ** b) = ((M:real^N^N) ** a) dot (M ** b)`
  (LABEL_TAC "D") THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_FRAME_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((M:real^N^N) ** u) dot (M ** v) = &0` ASSUME_TAC THENL
   [USE_THEN "D" (fun th -> USE_THEN "O" (MP_TAC o REWRITE_RULE[th])) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(u dot ((G:real^N->real^N^N) y ** u) - norm((M:real^N^N) ** u) pow 2) <=
    delta * norm(M ** u) pow 2 /\
    abs(v dot ((G:real^N->real^N^N) y ** v) - norm((M:real^N^N) ** v) pow 2) <=
    delta * norm(M ** v) pow 2 /\
    (u dot ((G:real^N->real^N^N) y ** v)) pow 2 <=
    delta pow 2 * (norm((M:real^N^N) ** u) pow 2 * norm(M ** v) pow 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "H0" (MP_TAC o SPECL [`u:real^N`; `u:real^N`]) THEN
      USE_THEN "D" (fun th -> REWRITE_TAC[th; GSYM NORM_POW_2]) THEN
      REAL_ARITH_TAC;
      USE_THEN "H0" (MP_TAC o SPECL [`v:real^N`; `v:real^N`]) THEN
      USE_THEN "D" (fun th -> REWRITE_TAC[th; GSYM NORM_POW_2]) THEN
      REAL_ARITH_TAC;
      USE_THEN "H0" (MP_TAC o SPECL [`u:real^N`; `v:real^N`]) THEN
      USE_THEN "D" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(delta * norm((M:real^N^N) ** u) * norm(M ** v)) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((M:real^N^N) ** lriemann G0 y u v v) <=
    K * norm(M ** u) * norm(M ** v) * norm(M ** v)`
  ASSUME_TAC THENL [USE_THEN "R0" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN
   `delta * norm((M:real^N^N) ** u) * norm(M ** lriemann G0 y u v v) <=
    delta * norm(M ** u) * (K * norm(M ** u) * norm(M ** v) * norm(M ** v)) /\
    norm((M:real^N^N) ** u) * norm(M ** lriemann G0 y u v v) <=
    norm(M ** u) * (K * norm(M ** u) * norm(M ** v) * norm(M ** v))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(u dot ((G:real^N->real^N^N) y ** lriemann G y u v v) -
        ((M:real^N^N) ** u) dot (M ** lriemann G0 y u v v)) <=
    ((&4 + K) * delta) * (norm(M ** u) pow 2 * norm(M ** v) pow 2) /\
    abs(((M:real^N^N) ** u) dot (M ** lriemann G0 y u v v)) <=
    K * (norm(M ** u) pow 2 * norm(M ** v) pow 2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "Q" (MP_TAC o SPECL [`u:real^N`; `v:real^N`; `v:real^N`; `u:real^N`]) THEN
      USE_THEN "H0" (MP_TAC o SPECL
        [`u:real^N`; `lriemann (G0:real^N->real^N^N) y u v v`]) THEN
      USE_THEN "D" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; DOT_RSUB] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`(M:real^N^N) ** u`; `(M:real^N^N) ** lriemann G0 y u v v`]
             NORM_CAUCHY_SCHWARZ_ABS) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[lsectional] THEN
  USE_THEN "D" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&0 pow 2 = &0`; REAL_SUB_RZERO] THEN
  MP_TAC(ISPECL
   [`norm((M:real^N^N) ** u) pow 2`; `norm((M:real^N^N) ** v) pow 2`;
    `u dot ((G:real^N->real^N^N) y ** u) - norm((M:real^N^N) ** u) pow 2`;
    `v dot ((G:real^N->real^N^N) y ** v) - norm((M:real^N^N) ** v) pow 2`;
    `u dot ((G:real^N->real^N^N) y ** v)`; `delta:real`;
    `u dot ((G:real^N->real^N^N) y ** lriemann G y u v v)`;
    `((M:real^N^N) ** u) dot (M ** lriemann G0 y u v v)`;
    `(&4 + K) * delta`; `K:real`] LRG_SECT_ARITH) THEN
  REWRITE_TAC[REAL_ARITH `a + (x - a) = x`] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_MUL; REAL_ARITH `&0 <= K ==> &0 <= &4 + K`]);;

let LRG_PERT_SECTIONAL = prove
 (`!s (G0:real^N->real^N^N) G y (M:real^N^N) delta K u v.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ G0 y = transp M ** M /\
     &0 <= delta /\ delta <= &1 / &10 /\ &0 <= K /\
     (!a b. abs(a dot (G y ** b) - a dot (G0 y ** b)) <=
            delta * norm(M ** a) * norm(M ** b)) /\
     (!u. abs(lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u) y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3)) /\
     (!u. abs(lnabla 3 G0 (lnabla 2 G0 (\x u. lmetric2 G x u - lmetric2 G0 x u))
                y u) <=
          delta * norm(M ** u 1) * norm(M ** u 2) * norm(M ** u 3) * norm(M ** u 4)) /\
     (!u v w. norm(M ** lriemann G0 y u v w) <=
              K * norm(M ** u) * norm(M ** v) * norm(M ** w))
     ==> abs(lsectional G y u v - lsectional G0 y u v) <= &8 * (&1 + K) * delta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `u:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[lsectional; DOT_LZERO; real_div; REAL_MUL_LZERO;
                    REAL_SUB_REFL; REAL_ABS_NUM] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u dot ((G0:real^N->real^N^N) y ** u)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                 `v:real^N`;
                 `(u dot ((G0:real^N->real^N^N) y ** v)) / (u dot (G0 y ** u))`]
         LSECTIONAL_SHEAR) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`; `u:real^N`;
                 `v:real^N`;
                 `(u dot ((G0:real^N->real^N^N) y ** v)) / (u dot (G0 y ** u))`]
         LSECTIONAL_SHEAR) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LRG_PERT_SECT_ORTH THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `M:real^N^N`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL;
              DOT_RSUB; DOT_RMUL] THEN
  UNDISCH_TAC `&0 < u dot ((G0:real^N->real^N^N) y ** u)` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Curvature stability (LCK_CURVATURE_STABILITY).                            *)
(* ------------------------------------------------------------------------- *)

let LRG_LCK_DIST2_TERM_LE = prove
 (`!k l s (G0:real^N->real^N^N) G y.
     metric_field s G0 /\ metric_field s G /\ y IN s /\ l <= k
     ==> ltnorm2 (2 + l) G0
           (lnabla_iter 2 l G0 (\z u. lmetric2 G z u - lmetric2 G0 z u)) y <=
         lck_dist2 k G0 G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lck_dist2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(l..l) (\l. ltnorm2 (2 + l) (G0:real^N->real^N^N)
     (lnabla_iter 2 l G0 (\z u. lmetric2 (G:real^N->real^N^N) z u -
                                lmetric2 G0 z u)) y)` THEN
  CONJ_TAC THENL [REWRITE_TAC[SUM_SING_NUMSEG; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG] THEN ASM_REWRITE_TAC[LE_0] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let LRG_LNABLA_ITER_12 = prove
 (`!k (G:real^N->real^N^N) tf.
     lnabla_iter k 1 G tf = lnabla k G tf /\
     lnabla_iter k 2 G tf = lnabla (k + 1) G (lnabla k G tf)`,
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; lnabla_iter; ADD_CLAUSES]);;

let LRG_FRAME_BOUND_DELTA = prove
 (`!k U (G:real^N->real^N^N) (tf:real^N->(num->real^N)->real) y (M:real^N^N) a D.
     metric_field U G /\ ltensor_field k U tf /\ y IN U /\ G y = transp M ** M /\
     ltnorm2 k G tf y <= D
     ==> abs(tf y a) <= sqrt D * product(1..k) (\m. norm(M ** a m))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(ltnorm2 k (G:real^N->real^N^N) tf y) *
              product(1..k) (\m. norm((M:real^N^N) ** a m))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_TENSOR_FRAME_BOUND THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_MONO_LE] THEN
    MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE]]);;

let LCK_CURVATURE_STABILITY = prove
 (`!K0 alpha. &0 < alpha
     ==> ?eta. &0 < eta /\
           !s (G0:real^N->real^N^N) G y.
              metric_field s G0 /\ metric_field s G /\ y IN s /\
              lrm_deriv_norm2 0 G0 y <= K0 pow 2 /\
              lck_dist2 2 G0 G y < eta pow 2
              ==> abs(lscalar G y - lscalar G0 y) <= alpha /\
                  (!w. abs(lricci G y w w - lricci G0 y w w)
                       <= alpha * (w dot (G0 y ** w))) /\
                  (!u v. ~collinear {vec 0,u,v}
                         ==> abs(lsectional G y u v - lsectional G0 y u v)
                             <= alpha)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_GE_1]; ALL_TAC] THEN
  ABBREV_TAC `P = &8 * &(dimindex(:N)) pow 2 * (&1 + abs K0)` THEN
  SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &10) (alpha / P)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `G0:real^N->real^N^N`;
                       `G:real^N->real^N^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `delta = sqrt(lck_dist2 2 (G0:real^N->real^N^N) G y)` THEN
  SUBGOAL_THEN `&0 <= lck_dist2 2 (G0:real^N->real^N^N) G y` ASSUME_TAC THENL
   [REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= delta /\ delta < min (&1 / &10) (alpha / P)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `sqrt(min (&1 / &10) (alpha / P) pow 2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SQRT_MONO_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN
    REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta <= &1 / &10 /\ delta * P < alpha` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_LT_MIN]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM REAL_LT_RDIV_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`]
         LRG_FRAME) THEN
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
  SUBGOAL_THEN
   `!a b. abs(a dot ((G:real^N->real^N^N) y ** b) - a dot (G0 y ** b)) <=
          delta * norm((M:real^N^N) ** a) * norm(M ** b)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u`;
                   `y:real^N`; `M:real^N^N`; `\m. if m = 1 then (a:real^N) else b`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`2`; `0`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                     `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
      ASM_REWRITE_TAC[LE_0; lnabla_iter; ADD_CLAUSES];
      REWRITE_TAC[PRODUCT_2; lmetric2; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 2 (G0:real^N->real^N^N)
              (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u) y u) <=
        delta * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`3`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 2 (G0:real^N->real^N^N)
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_3] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `1`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lnabla 3 (G0:real^N->real^N^N)
              (lnabla 2 G0
                (\x u. lmetric2 (G:real^N->real^N^N) x u - lmetric2 G0 x u)) y u) <=
        delta * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lnabla 3 (G0:real^N->real^N^N) (lnabla 2 G0
                      (\z u. lmetric2 (G:real^N->real^N^N) z u - lmetric2 G0 z u))`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `lck_dist2 2 (G0:real^N->real^N^N) G y`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`2`; `2`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `G:real^N->real^N^N`; `y:real^N`] LRG_LCK_DIST2_TERM_LE) THEN
    REWRITE_TAC[LRG_LNABLA_ITER_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. abs(lrm4 (G0:real^N->real^N^N) y u) <=
        abs K0 * norm((M:real^N^N) ** u 1) * norm(M ** u 2) * norm(M ** u 3) *
        norm(M ** u 4)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`4`; `s:real^N->bool`; `G0:real^N->real^N^N`;
                   `lrm4 (G0:real^N->real^N^N)`;
                   `y:real^N`; `M:real^N^N`; `u:num->real^N`;
                   `K0 pow 2`] LRG_FRAME_BOUND_DELTA) THEN
    ASM_REWRITE_TAC[PRODUCT_4; POW_2_SQRT_ABS] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `lrm_deriv_norm2 0 (G0:real^N->real^N^N) y <= K0 pow 2` THEN
    REWRITE_TAC[lrm_deriv_norm2; lnabla_iter; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                 `y:real^N`; `M:real^N^N`; `delta:real`] LRG_PERT_RICCI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "RIC") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `abs(K0:real)`] LRG_RM0_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN DISCH_THEN(LABEL_TAC "RM0") THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `y:real^N`;
                 `M:real^N^N`; `abs(K0:real)`] LRG_RICCI0_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS] THEN DISCH_THEN(LABEL_TAC "RIC0") THEN
  SUBGOAL_THEN `&1 <= &(dimindex(:N)) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= delta * &(dimindex(:N)) /\
    &0 <= delta * &(dimindex(:N)) * (&(dimindex(:N)) - &1) /\
    &0 <= delta * &(dimindex(:N)) pow 2 /\
    &0 <= delta * &(dimindex(:N)) pow 2 * abs K0 /\
    &0 <= delta * (&(dimindex(:N)) pow 2 - &1) /\
    &0 <= delta * (&(dimindex(:N)) pow 2 - &1) * abs K0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&8 * (delta * &(dimindex(:N)) pow 2) +
    &8 * (delta * &(dimindex(:N)) pow 2 * abs K0) < alpha`
  ASSUME_TAC THENL
   [UNDISCH_TAC `delta * P < alpha` THEN EXPAND_TAC "P" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `y:real^N`; `M:real^N^N`; `delta:real`; `abs(K0:real)`]
           LRG_PERT_SCALAR) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `w:real^N` THEN
    SUBGOAL_THEN `w dot ((G0:real^N->real^N^N) y ** w) = norm((M:real^N^N) ** w) pow 2`
    SUBST1_TAC THENL
     [REWRITE_TAC[NORM_POW_2] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LRG_FRAME_DOT THEN FIRST_ASSUM(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    SUBGOAL_THEN `&5 * &(dimindex(:N)) * delta <= alpha` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&5 * &(dimindex(:N)) * delta) * norm((M:real^N^N) ** w) pow 2` THEN
    CONJ_TAC THENL
     [USE_THEN "RIC" (MP_TAC o SPECL [`w:real^N`; `w:real^N`]) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `G0:real^N->real^N^N`; `G:real^N->real^N^N`;
                   `y:real^N`; `M:real^N^N`; `delta:real`; `abs(K0:real)`;
                   `u:real^N`; `v:real^N`] LRG_PERT_SECTIONAL) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The cylinder model: sectional curvature of cylinder_flow 0                *)
(* (LSECTIONAL_CYLINDER).                                                    *)
(* ------------------------------------------------------------------------- *)

let LRG_CYL0_EQ = prove
 (`cylinder_flow (&0) = \z:real^3. (&2 / norm z pow 2) %% mat 1`,
  REWRITE_TAC[FUN_EQ_THM; cylinder_flow; REAL_SUB_RZERO; real_div;
              REAL_MUL_LZERO; MATRIX_CMUL_LID; MATRIX_CMUL_LZERO;
              MATRIX_ADD_RID]);;

let LSECTIONAL_CYLINDER = prove
 (`!y u v:real^3.
     ~(y = vec 0) /\ ~collinear {vec 0,u,v}
     ==> lsectional (cylinder_flow (&0)) y u v =
         ((u dot u - (u dot y) pow 2 / norm y pow 2) *
          (v dot v - (v dot y) pow 2 / norm y pow 2) -
          (u dot v - (u dot y) * (v dot y) / norm y pow 2) pow 2) /
         (&2 * ((u dot u) * (v dot v) - (u dot v) pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_CYL0_EQ] THEN
  MP_TAC(ISPECL [`\z:real^3. (&2 / norm z pow 2) %% (mat 1:real^3^3)`;
                 `(:real^3) DELETE vec 0`; `\z:real^3. --(&1) / norm z pow 2`;
                 `&2 / (norm(y:real^3) pow 2) pow 2`; `y:real^3`; `u:real^3`;
                 `v:real^3`; `v:real^3`] LRG_RADIAL_RIEMANN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LRG_CYL_OPEN; IN_DELETE; IN_UNIV; LRG_CYL_CHRISTOFFEL;
                 LRG_CYL_M_DERIV];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[lsectional; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB; DOT_LMUL] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `((u:real^3) dot u) * ((v:real^3) dot v) - (u dot v) pow 2 = &0` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NORM_POW_2; DOT_SYM]) THEN
  REWRITE_TAC[NORM_POW_2; DOT_SYM] THENL
   [SUBGOAL_THEN
     `(&2 / ((y:real^3) dot y) * ((u:real^3) dot u)) *
      (&2 / (y dot y) * ((v:real^3) dot v)) -
      (&2 / (y dot y) * (u dot v)) pow 2 = &0`
    MP_TAC THENL
     [UNDISCH_TAC `((u:real^3) dot u) * ((v:real^3) dot v) - (u dot v) pow 2 = &0` THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REWRITE_TAC[DOT_SYM] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_MUL_LZERO];
    MAP_EVERY UNDISCH_TAC
     [`~(((u:real^3) dot u) * ((v:real^3) dot v) - (u dot v) pow 2 = &0)`;
      `&0 < (y:real^3) dot y`] THEN
    REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The cylinder model: the Christoffel symbols of cylinder_flow s do not     *)
(* depend on s (CHRISTOFFEL_CYLINDER_FLOW).                                  *)
(* ------------------------------------------------------------------------- *)

let LRG_HAS_DERIVATIVE_LIFT_MUL = prove
 (`!(f:real^N->real) f' g g' y.
     ((\x. lift(f x)) has_derivative (\h. lift(f' h))) (at y) /\
     ((\x. lift(g x)) has_derivative (\h. lift(g' h))) (at y)
     ==> ((\x. lift(f x * g x)) has_derivative
          (\h. lift(f y * g' h + f' h * g y))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f':real^N->real`;
                 `\x. lift((g:real^N->real) x)`; `\h. lift((g':real^N->real) h)`;
                 `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL]);;

let LRG_HAS_DERIVATIVE_LIFT_LINCOMB = prove
 (`!(f:real^N->real) f' g g' a b y.
     ((\x. lift(f x)) has_derivative (\h. lift(f' h))) (at y) /\
     ((\x. lift(g x)) has_derivative (\h. lift(g' h))) (at y)
     ==> ((\x. lift(a * f x + b * g x)) has_derivative
          (\h. lift(a * f' h + b * g' h))) (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[]);;

let LRG_CYL_FLOW_DOT = prove
 (`!s (z:real^3) w b.
     w dot (cylinder_flow s z ** b) =
     (&1 - s) * (w dot b) * (&2 / norm z pow 2) +
     s / &2 * ((&2 / norm z pow 2) * ((&2 / norm z pow 2) *
                                       ((b dot z) * (w dot z))))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `((lambda i j. (z:real^3)$i * z$j):real^3^3) ** b = (b dot z) % z`
  ASSUME_TAC THENL
   [SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA; VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[dot; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cylinder_flow; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_ADD_RDISTRIB;
                  MATRIX_VECTOR_MUL_LID; DOT_RMUL; DOT_RADD] THEN
  REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

let LRG_CYL_FLOW_MDERIV = prove
 (`!s (y:real^3) w a b.
     s < &1 /\ ~(y = vec 0)
     ==> w dot (mderiv (cylinder_flow s) y a ** b) =
         (&1 - s) * (w dot b) * (--(&4) * (y dot a) / (norm y pow 2) pow 2) +
         s / &2 *
         ((&2 / norm y pow 2) *
          ((&2 / norm y pow 2) * ((b dot y) * (w dot a) + (b dot a) * (w dot y)) +
           (--(&4) * (y dot a) / (norm y pow 2) pow 2) * ((b dot y) * (w dot y))) +
          (--(&4) * (y dot a) / (norm y pow 2) pow 2) *
          ((&2 / norm y pow 2) * ((b dot y) * (w dot y))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. lift(((b:real^3) dot z) * ((w:real^3) dot z))) has_derivative
     (\h. lift((b dot y) * (w dot h) + (b dot h) * (w dot y)))) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. (b:real^3) dot z`; `\h:real^3. (b:real^3) dot h`;
                   `\z:real^3. (w:real^3) dot z`; `\h:real^3. (w:real^3) dot h`;
                   `y:real^3`] LRG_HAS_DERIVATIVE_LIFT_MUL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_LIFT_DOT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_C_DERIV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\z. lift(&2 / norm z pow 2 * (((b:real^3) dot z) * ((w:real^3) dot z))))
     has_derivative
     (\h. lift(&2 / norm y pow 2 * ((b dot y) * (w dot h) + (b dot h) * (w dot y)) +
               (--(&4) * (y dot h) / (norm y pow 2) pow 2) *
               ((b dot y) * (w dot y))))) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. &2 / norm z pow 2`;
                   `\h:real^3. --(&4) * (y dot h) / (norm(y:real^3) pow 2) pow 2`;
                   `\z:real^3. ((b:real^3) dot z) * ((w:real^3) dot z)`;
                   `\h:real^3. ((b:real^3) dot y) * ((w:real^3) dot h) + (b dot h) * (w dot y)`;
                   `y:real^3`] LRG_HAS_DERIVATIVE_LIFT_MUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. lift(&2 / norm z pow 2 *
               (&2 / norm z pow 2 * (((b:real^3) dot z) * ((w:real^3) dot z)))))
     has_derivative
     (\h. lift(&2 / norm y pow 2 *
               (&2 / norm y pow 2 * ((b dot y) * (w dot h) + (b dot h) * (w dot y)) +
                (--(&4) * (y dot h) / (norm y pow 2) pow 2) *
                ((b dot y) * (w dot y))) +
               (--(&4) * (y dot h) / (norm y pow 2) pow 2) *
               (&2 / norm y pow 2 * ((b dot y) * (w dot y)))))) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. &2 / norm z pow 2`;
                   `\h:real^3. --(&4) * (y dot h) / (norm(y:real^3) pow 2) pow 2`;
                   `\z:real^3. &2 / norm z pow 2 * (((b:real^3) dot z) * ((w:real^3) dot z))`;
                   `\h:real^3. &2 / norm(y:real^3) pow 2 *
                               (((b:real^3) dot y) * ((w:real^3) dot h) + (b dot h) * (w dot y)) +
                               (--(&4) * (y dot h) / (norm y pow 2) pow 2) *
                               ((b dot y) * (w dot y))`;
                   `y:real^3`] LRG_HAS_DERIVATIVE_LIFT_MUL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. &2 / norm z pow 2`;
                 `\h:real^3. --(&4) * (y dot h) / (norm(y:real^3) pow 2) pow 2`;
                 `\z:real^3. &2 / norm z pow 2 *
                             (&2 / norm z pow 2 * (((b:real^3) dot z) * ((w:real^3) dot z)))`;
                 `\h:real^3. &2 / norm(y:real^3) pow 2 *
                    (&2 / norm y pow 2 * (((b:real^3) dot y) * ((w:real^3) dot h) +
                                          (b dot h) * (w dot y)) +
                     (--(&4) * (y dot h) / (norm y pow 2) pow 2) *
                     ((b dot y) * (w dot y))) +
                    (--(&4) * (y dot h) / (norm y pow 2) pow 2) *
                    (&2 / norm y pow 2 * ((b dot y) * (w dot y)))`;
                 `(&1 - s) * ((w:real^3) dot b)`; `s / &2`; `y:real^3`]
         LRG_HAS_DERIVATIVE_LIFT_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cylinder_flow s`; `y:real^3`; `w:real^3`; `b:real^3`]
         LRG_HAS_DERIVATIVE_GDOT) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow s`; `y:real^3`]
           LRG_METRIC_FIELD_DIFF) THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((w:real^3) dot (cylinder_flow s z ** b))) =
    (\x. lift(((&1 - s) * (w dot b)) * &2 / norm x pow 2 +
              s / &2 * (&2 / norm x pow 2 *
                        (&2 / norm x pow 2 * (((b:real^3) dot x) * (w dot x))))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_EQ; LRG_CYL_FLOW_DOT] THEN GEN_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(fun th1 -> FIRST_X_ASSUM(fun th2 ->
    MP_TAC(MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT (CONJ th1 th2)))) THEN
  REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN DISCH_THEN(MP_TAC o SPEC `a:real^3`) THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let LRG_CYL_FLOW_CHRISTOFFEL = prove
 (`!s (y:real^3) u v.
     s < &1 /\ ~(y = vec 0)
     ==> christoffel (cylinder_flow s) y u v =
         (--(&1) / norm y pow 2) % ((y dot u) % v + (y dot v) % u - (u dot v) % y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC [`(:real^3) DELETE vec 0`; `cylinder_flow s`; `y:real^3`] THEN
  ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `w:real^3` THEN
  MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow s`; `y:real^3`;
                 `u:real^3`; `v:real^3`; `w:real^3`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; IN_DELETE; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LRG_CYL_FLOW_MDERIV; LRG_CYL_FLOW_DOT] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB; DOT_LMUL; DOT_LADD; DOT_LSUB] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NORM_POW_2; DOT_SYM] THEN CONV_TAC REAL_FIELD);;

let CHRISTOFFEL_CYLINDER_FLOW = prove
 (`!s y u v.
     s < &1 /\ ~(y = vec 0)
     ==> christoffel (cylinder_flow s) y u v =
         christoffel (cylinder_flow (&0)) y u v`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LRG_CYL_FLOW_CHRISTOFFEL; REAL_ARITH `&0 < &1`]);;

(* ------------------------------------------------------------------------- *)
(* Comparison of tensor norms for comparable metrics: if G2 <= lambda G1 as  *)
(* quadratic forms at y, then |T|^2_G1 <= lambda^k |T|^2_G2 for k-tensors.    *)
(* Proof: interpolate slot by slot between G1^-1 and G2^-1 using mixed       *)
(* contractions, each of which is a sum of squares.                          *)
(* ------------------------------------------------------------------------- *)

let lmix2 = new_definition
 `lmix2 k (B:num->real^N^N) (tf:real^N->(num->real^N)->real) y =
    sum (index_tuples k (:N))
     (\i. sum (index_tuples k (:N))
           (\j. tf y (\m. basis(i m)) * tf y (\m. basis(j m)) *
                product(1..k) (\m. (B m)$(i m)$(j m))))`;;

let LRG_LMIX2_LTNORM2 = prove
 (`!k (G:real^N->real^N^N) tf y.
     ltnorm2 k G tf y = lmix2 k (\m. matrix_inv(G y)) tf y`,
  REWRITE_TAC[ltnorm2; lmix2]);;

let LRG_LMIX2_EQ = prove
 (`!k (B:num->real^N^N) B' tf y.
     (!m. 1 <= m /\ m <= k ==> B m = B' m)
     ==> lmix2 k B tf y = lmix2 k B' tf y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lmix2] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[]);;

let LRG_PRODUCT_TRANSP_MUL_MIX = prove
 (`!(S:num->real^N^N) k i j.
        i IN index_tuples k (:N) /\ j IN index_tuples k (:N)
        ==> product (1..k) (\m. (transp(S m) ** S m)$(i m)$(j m)) =
            sum (index_tuples k (:N))
                (\p. product (1..k) (\m. (S m)$(p m)$(i m)) *
                     product (1..k) (\m. (S m)$(p m)$(j m)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `product (1..k) (\m. sum (1..dimindex(:N))
                 (\q. (S m:real^N^N)$q$((i:num->num) m) * (S m)$q$((j:num->num) m)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC LRG_TRANSP_MUL_COMPONENT THEN
    MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    MP_TAC(ISPECL [`j:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LRG_PRODUCT_SUM_TUPLES] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[GSYM PRODUCT_MUL_NUMSEG]);;

let LRG_LMIX2_SQUARES = prove
 (`!k U (tf:real^N->(num->real^N)->real) y (S:num->real^N^N).
     ltensor_field k U tf /\ y IN U
     ==> lmix2 k (\m. transp(S m) ** S m) tf y =
         sum (index_tuples k (:N))
             (\p. (tf y (\m. transp(S m) ** basis(p m))) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. p IN index_tuples k (:N)
        ==> (tf:real^N->(num->real^N)->real) y (\m. transp(S m) ** basis(p m)) =
            sum (index_tuples k (:N))
                (\i. product (1..k) (\m. (S m:real^N^N)$(p m)$(i m)) *
                     tf y (\m. basis(i m)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                   `y:real^N`] LRG_TENSOR_FIELD_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC LRG_TRANSP_BASIS_COMPONENT THEN
    MP_TAC(ISPECL [`p:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    MP_TAC(ISPECL [`i:num->num`; `k:num`; `m:num`] LRG_INDEX_TUPLES_RANGE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (index_tuples k (:N))
     (\p. (sum (index_tuples k (:N))
             (\i. product (1..k) (\m. (S m:real^N^N)$(p m)$(i m)) *
                  (tf:real^N->(num->real^N)->real) y (\m. basis(i m)))) pow 2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SIMP_TAC[LRG_SUM_SQUARE_EXPAND; LRG_INDEX_TUPLES_FINITE] THEN
  REWRITE_TAC[lmix2] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN
  DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_PRODUCT_TRANSP_MUL_MIX THEN ASM_REWRITE_TAC[]);;

let LRG_LMIX2_POS = prove
 (`!k U (tf:real^N->(num->real^N)->real) y (S:num->real^N^N).
     ltensor_field k U tf /\ y IN U
     ==> &0 <= lmix2 k (\m. transp(S m) ** S m) tf y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                 `y:real^N`; `S:num->real^N^N`] LRG_LMIX2_SQUARES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_LE_POW_2; LRG_INDEX_TUPLES_FINITE]);;

let LRG_LMIX2_SLOT = prove
 (`!k (B1:num->real^N^N) B2 B3 a b m0 tf y.
     1 <= m0 /\ m0 <= k /\
     (!m. ~(m = m0) ==> B1 m = B3 m /\ B2 m = B3 m) /\
     B3 m0 = a %% B1 m0 + b %% B2 m0
     ==> lmix2 k B3 tf y = a * lmix2 k B1 tf y + b * lmix2 k B2 tf y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lmix2; GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[GSYM SUM_ADD; LRG_INDEX_TUPLES_FINITE] THEN
  SIMP_TAC[GSYM SUM_ADD; LRG_INDEX_TUPLES_FINITE] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN SIMP_TAC[GSYM SUM_ADD; LRG_INDEX_TUPLES_FINITE] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN
   `!B:num->real^N^N. product(1..k) (\m. (B m)$(i m)$(j m)) =
      (B m0)$(i m0)$(j m0) * product((1..k) DELETE m0) (\m. (B m)$(i m)$(j m))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`\m. ((B:num->real^N^N) m)$((i:num->num) m)$((j:num->num) m)`;
                   `1..k`; `m0:num`] PRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product((1..k) DELETE m0) (\m. ((B1:num->real^N^N) m)$(i m)$(j m)) =
    product((1..k) DELETE m0) (\m. ((B3:num->real^N^N) m)$(i m)$(j m)) /\
    product((1..k) DELETE m0) (\m. ((B2:num->real^N^N) m)$(i m)$(j m)) =
    product((1..k) DELETE m0) (\m. ((B3:num->real^N^N) m)$(i m)$(j m))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    REWRITE_TAC[IN_DELETE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_ADD_COMPONENT; MATRIX_CMUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* The comparison theorem for tensor norms. *)

let LRG_METRIC_CS = prove
 (`!U (G:real^N->real^N^N) y a b.
     metric_field U G /\ y IN U
     ==> (a dot (G y ** b)) pow 2 <= (a dot (G y ** a)) * (b dot (G y ** b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!p q. p dot ((G:real^N->real^N^N) y ** q) = ((M:real^N^N) ** p) dot (M ** q)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LRG_FRAME_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM; NORM_CAUCHY_SCHWARZ_ABS]);;

let LRG_METRIC_DUAL_COMPARE = prove
 (`!U (G1:real^N->real^N^N) G2 y lam.
     metric_field U G1 /\ metric_field U G2 /\ y IN U /\ &0 < lam /\
     (!x. x dot (G2 y ** x) <= lam * (x dot (G1 y ** x)))
     ==> !c. c dot (matrix_inv(G1 y) ** c) <=
             lam * (c dot (matrix_inv(G2 y) ** c))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))))) THEN
  X_GEN_TAC `c:real^N` THEN
  SUBGOAL_THEN `invertible((G1:real^N->real^N^N) y) /\
                invertible((G2:real^N->real^N^N) y)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `c dot (matrix_inv((G1:real^N->real^N^N) y) ** c) =
    (matrix_inv(G1 y) ** c) dot (G1 y ** matrix_inv(G1 y) ** c)`
  (LABEL_TAC "E1") THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c dot (matrix_inv((G2:real^N->real^N^N) y) ** c) =
    (matrix_inv(G2 y) ** c) dot (G2 y ** matrix_inv(G2 y) ** c)`
  (LABEL_TAC "E2") THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c dot (matrix_inv((G1:real^N->real^N^N) y) ** c) =
    (matrix_inv(G1 y) ** c) dot ((G2:real^N->real^N^N) y ** matrix_inv(G2 y) ** c)`
  (LABEL_TAC "E3") THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c dot (matrix_inv((G1:real^N->real^N^N) y) ** c) /\
                &0 <= c dot (matrix_inv((G2:real^N->real^N^N) y) ** c)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "E1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "E2" (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC LRG_METRIC_NONNEG THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_QUAD_ROOT0 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(matrix_inv((G1:real^N->real^N^N) y) ** c) dot
    (G2 y ** matrix_inv(G1 y) ** c) <=
    lam * (c dot (matrix_inv(G1 y) ** c))`
  ASSUME_TAC THENL
   [USE_THEN "E1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "H" (MATCH_ACCEPT_TAC o SPEC `matrix_inv((G1:real^N->real^N^N) y) ** c`);
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((matrix_inv((G1:real^N->real^N^N) y) ** c) dot
               (G2 y ** matrix_inv(G1 y) ** c)) *
              (c dot (matrix_inv((G2:real^N->real^N^N) y) ** c))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`;
                   `matrix_inv((G1:real^N->real^N^N) y) ** c`;
                   `matrix_inv((G2:real^N->real^N^N) y) ** c`] LRG_METRIC_CS) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "E3" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "E2" (fun th -> REWRITE_TAC[GSYM th]);
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let LRG_LTNORM2_COMPARE = prove
 (`!k U (G1:real^N->real^N^N) G2 tf y lam.
     metric_field U G1 /\ metric_field U G2 /\ ltensor_field k U tf /\ y IN U /\
     &0 < lam /\ (!x. x dot (G2 y ** x) <= lam * (x dot (G1 y ** x)))
     ==> ltnorm2 k G1 tf y <= lam pow k * ltnorm2 k G2 tf y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S1:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G2:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S2:real^N^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `y:real^N`; `lam:real`] LRG_METRIC_DUAL_COMPARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?SD:real^N^N. lam %% (transp (S2:real^N^N) ** S2) - transp (S1:real^N^N) ** S1 = transp (SD:real^N^N) ** SD`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM POSITIVE_SEMIDEFINITE_COVARIANCE_EQ] THEN
    REWRITE_TAC[positive_semidefinite; symmetric_matrix] THEN CONJ_TAC THENL
     [REWRITE_TAC[TRANSP_MATRIX_SUB; TRANSP_MATRIX_CMUL; MATRIX_TRANSP_MUL;
                  TRANSP_TRANSP];
      X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_VECTOR_LMUL;
                  DOT_RSUB; DOT_RMUL] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      UNDISCH_TAC `matrix_inv((G1:real^N->real^N^N) y) = transp (S1:real^N^N) ** S1` THEN
      UNDISCH_TAC `matrix_inv((G2:real^N->real^N^N) y) = transp (S2:real^N^N) ** S2` THEN
      REPEAT(DISCH_THEN SUBST1_TAC) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r <= k
        ==> lmix2 k (\m. if m <= 0 then transp (S2:real^N^N) ** S2 else transp (S1:real^N^N) ** S1)
                  (tf:real^N->(num->real^N)->real) y <=
            lam pow r *
            lmix2 k (\m. if m <= r then transp (S2:real^N^N) ** S2 else transp (S1:real^N^N) ** S1) tf y`
  MP_TAC THENL
   [INDUCT_TAC THENL [REWRITE_TAC[real_pow; REAL_MUL_LID; REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `x * y <= x * (l * z) ==> x * y <= l * x * z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    MP_TAC(ISPECL
     [`k:num`;
      `\m. if m <= SUC r then transp (S2:real^N^N) ** S2 else transp (S1:real^N^N) ** S1`;
      `\m:num. if m <= (r:num) then transp (S2:real^N^N) ** S2
               else transp (S1:real^N^N) ** S1`;
      `\m. transp((\m. if m = SUC r then SD
                       else if m <= r then S2 else S1:real^N^N) m) **
           (\m. if m = SUC r then SD else if m <= r then S2 else S1:real^N^N) m`;
      `lam:real`; `--(&1)`; `SUC r`; `tf:real^N->(num->real^N)->real`; `y:real^N`]
     LRG_LMIX2_SLOT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ARITH_TAC; ASM_ARITH_TAC;
        X_GEN_TAC `m:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `m <= r` THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC r <= r)`] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATRIX_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:num`; `U:real^N->bool`; `tf:real^N->(num->real^N)->real`;
                   `y:real^N`;
                   `\m. if m = SUC r then SD else if m <= r then S2 else S1:real^N^N`]
           LRG_LMIX2_POS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC(MESON[] `!a a' b b' c:real.
     a = a' /\ b = b' ==> a <= c * b ==> a' <= c * b'`) THEN
  REWRITE_TAC[LRG_LMIX2_LTNORM2] THEN CONJ_TAC THEN
  MATCH_MP_TAC LRG_LMIX2_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Base change between the cylinder metrics (LCK_DIST_CYLINDER_BASE).        *)
(* ------------------------------------------------------------------------- *)

let LRG_LNABLA_CHRISTOFFEL_EQ = prove
 (`!k (G1:real^N->real^N^N) G2 tf y u.
     (!a b. christoffel G1 y a b = christoffel G2 y a b)
     ==> lnabla k G1 tf y u = lnabla k G2 tf y u`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lnabla]);;

let LRG_LNABLA_ITER_CHRISTOFFEL_EQ = prove
 (`!k (G1:real^N->real^N^N) G2 tf s.
     open s /\ (!z a b. z IN s ==> christoffel G1 z a b = christoffel G2 z a b)
     ==> !l z u. z IN s
                 ==> lnabla_iter k l G1 tf z u = lnabla_iter k l G2 tf z u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC[lnabla_iter] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lnabla (k + l) (G2:real^N->real^N^N) (lnabla_iter k l G1 tf) z u` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRG_LNABLA_CHRISTOFFEL_EQ THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC LRG_LNABLA_LOCAL THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[]]);;

let LRG_CYL_COMPARE = prove
 (`!s (y:real^3) x.
     ~(y = vec 0)
     ==> x dot (cylinder_flow s y ** x) <=
         (&1 + abs s) * (x dot (cylinder_flow (&0) y ** x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_CYL_FLOW_DOT] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((x:real^3) dot y) pow 2 <= norm(y:real^3) pow 2 * (x dot x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm(y:real^3) pow 2` THEN
  ABBREV_TAC `X = (x:real^3) dot x` THEN
  ABBREV_TAC `t = ((x:real^3) dot y) pow 2 / r` THEN
  SUBGOAL_THEN `&0 <= t /\ t <= X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2; REAL_LT_IMP_LE;
                                     REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[DOT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `s / &2 * (&2 / r * (&2 / r * (((x:real^3) dot y) * (x dot y)))) =
    (&2 / r) * (s * t)`
  SUBST1_TAC THENL
   [EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; real_div; REAL_MUL_LZERO;
              REAL_ADD_RID] THEN
  REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `s * t - s * X <= abs s * X` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= s` THENL
     [SUBGOAL_THEN `s * t <= s * X` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= s * X` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= --s * t` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 / r` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `q * ((&1 - s) * X + s * t) <= q * ((&1 + abs s) * X)
    ==> (&1 - s) * X * q + q * (s * t) <= (&1 + abs s) * X * q`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let LRG_CYL0_INV = prove
 (`!y:real^3. ~(y = vec 0)
              ==> matrix_inv(cylinder_flow (&0) y) =
                  (norm y pow 2 / &2) %% mat 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_CYL0_EQ] THEN
  MATCH_MP_TAC MATRIX_INV_UNIQUE THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_MUL_LID; MATRIX_CMUL_ASSOC] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 / norm(y:real^3) pow 2 * norm y pow 2 / &2 = &1 /\
                norm(y:real^3) pow 2 / &2 * &2 / norm y pow 2 = &1`
  (fun th -> REWRITE_TAC[th; MATRIX_CMUL_LID]) THEN
  UNDISCH_TAC `&0 < norm(y:real^3) pow 2` THEN CONV_TAC REAL_FIELD);;

let LRG_CYL_D_NORM = prove
 (`!s (y:real^3).
     s < &1 /\ ~(y = vec 0)
     ==> ltnorm2 2 (cylinder_flow (&0))
           (\z u. lmetric2 (cylinder_flow s) z u - lmetric2 (cylinder_flow (&0)) z u) y =
         &2 * s pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = sqrt(norm(y:real^3) pow 2 / &2)` THEN
  SUBGOAL_THEN `c pow 2 = norm(y:real^3) pow 2 / &2` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC SQRT_POW_2 THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                 `\z u. lmetric2 (cylinder_flow s) z u -
                        lmetric2 (cylinder_flow (&0)) z u`;
                 `y:real^3`; `c %% (mat 1:real^3^3)`] LRG_LTNORM2_SQUARES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `cylinder_flow (&0)`;
                     `cylinder_flow s`] LRG_LMETRIC2_DIFF_FIELD) THEN
      ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
      ASM_REWRITE_TAC[IN_DELETE; IN_UNIV];
      ASM_SIMP_TAC[LRG_CYL0_INV] THEN
      REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_MUL_LMUL;
                  MATRIX_MUL_RMUL; MATRIX_MUL_LID; MATRIX_CMUL_ASSOC] THEN
      ASM_REWRITE_TAC[GSYM REAL_POW_2]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[LRG_SUM_INDEX_TUPLES_2; DIMINDEX_3; SUM_3] THEN
  REWRITE_TAC[lmetric2; ARITH; TRANSP_MATRIX_CMUL; TRANSP_MAT;
              MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; LRG_CYL_FLOW_DOT] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DOT_BASIS; DIMINDEX_3; ARITH] THEN
  UNDISCH_TAC `c pow 2 = norm(y:real^3) pow 2 / &2` THEN
  UNDISCH_TAC `&0 < norm(y:real^3) pow 2` THEN
  REWRITE_TAC[NORM_POW_2; DOT_3] THEN CONV_TAC REAL_FIELD);;

let LRG_CYL_NABLA_SPLIT = prove
 (`!s t (G:real^3->real^3^3).
     s < &1 /\ t SUBSET ((:real^3) DELETE vec 0) /\ metric_field t G
     ==> !l y u. y IN t
           ==> lnabla_iter 2 l (cylinder_flow (&0))
                 (\z u. lmetric2 G z u - lmetric2 (cylinder_flow (&0)) z u) y u =
               lnabla_iter 2 l (cylinder_flow s)
                 (\z u. lmetric2 G z u - lmetric2 (cylinder_flow s) z u) y u +
               (if l = 0
                then lmetric2 (cylinder_flow s) y u - lmetric2 (cylinder_flow (&0)) y u
                else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cylinder_flow (&0)) /\ metric_field t (cylinder_flow s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z a b. z IN t
            ==> christoffel (cylinder_flow (&0)) z a b =
                christoffel (cylinder_flow s) z a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CHRISTOFFEL_CYLINDER_FLOW THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`; `G:real^3->real^3^3`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow (&0)`; `cylinder_flow s`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow (&0)`] LRG_LMETRIC2_FIELD) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (G:real^3->real^3^3) z u - lmetric2 (cylinder_flow (&0)) z u) =
    (\x u. &1 * (lmetric2 G x u - lmetric2 (cylinder_flow s) x u) +
           &1 * (lmetric2 (cylinder_flow s) x u - lmetric2 (cylinder_flow (&0)) x u))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `t:real^3->bool`; `cylinder_flow (&0)`;
     `\z u. lmetric2 (G:real^3->real^3^3) z u - lmetric2 (cylinder_flow s) z u`;
     `\z u. lmetric2 (cylinder_flow s) z u - lmetric2 (cylinder_flow (&0)) z u`;
     `&1`; `&1`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(ISPECL [`2`; `cylinder_flow (&0)`; `cylinder_flow s`;
     `\z u. lmetric2 (G:real^3->real^3^3) z u - lmetric2 (cylinder_flow s) z u`;
     `t:real^3->bool`] LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_EQ_ADD_LCANCEL] THEN
  STRUCT_CASES_TAC(SPEC `l:num` num_CASES) THENL
   [REWRITE_TAC[lnabla_iter]; ALL_TAC] THEN
  REWRITE_TAC[NOT_SUC] THEN
  SUBGOAL_THEN
   `(\z u. lmetric2 (cylinder_flow s) z u - lmetric2 (cylinder_flow (&0)) z u) =
    (\x u. &1 * lmetric2 (cylinder_flow s) x u +
           --(&1) * lmetric2 (cylinder_flow (&0)) x u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `t:real^3->bool`; `cylinder_flow (&0)`;
     `lmetric2 (cylinder_flow s)`; `lmetric2 (cylinder_flow (&0))`;
     `&1`; `--(&1)`] LRG_LNABLA_ITER_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(ISPECL [`2`; `cylinder_flow (&0)`; `cylinder_flow s`;
     `lmetric2 (cylinder_flow s)`; `t:real^3->bool`]
     LRG_LNABLA_ITER_CHRISTOFFEL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`] LRG_LNABLA_ITER_METRIC) THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow (&0)`] LRG_LNABLA_ITER_METRIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REAL_ARITH_TAC);;

let LCK_DIST_CYLINDER_BASE = prove
 (`!k s t G y.
      abs s <= &1 / &2 /\ t SUBSET ((:real^3) DELETE vec 0) /\
      metric_field t G /\ y IN t
      ==> sqrt(lck_dist2 k (cylinder_flow (&0)) G y)
          <= (&1 + abs s) pow (k + 2) *
             (sqrt(lck_dist2 k (cylinder_flow s) G y) + &2 * abs s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field t (cylinder_flow (&0)) /\ metric_field t (cylinder_flow s)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_ARITH `&0 < &1`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real`; `t:real^3->bool`; `G:real^3->real^3^3`]
         LRG_CYL_NABLA_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "SPLIT") THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow s`; `G:real^3->real^3^3`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow (&0)`; `cylinder_flow s`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^3->bool`; `cylinder_flow (&0)`; `G:real^3->real^3^3`]
         LRG_LMETRIC2_DIFF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `t:real^3->bool`; `cylinder_flow s`;
                 `\z u. lmetric2 (G:real^3->real^3^3) z u -
                        lmetric2 (cylinder_flow s) z u`]
         LRG_LNABLA_ITER_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "FS") THEN
  ABBREV_TAC `lam = &1 + abs s` THEN
  SUBGOAL_THEN `&1 <= lam` ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= lam pow (k + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `L = lck_dist2 k (cylinder_flow s) (G:real^3->real^3^3) y` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[lck_dist2] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `t:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..k) (\l. ltnorm2 (2 + l) (cylinder_flow (&0))
                     (lnabla_iter 2 l (cylinder_flow s)
                       (\z u. lmetric2 (G:real^3->real^3^3) z u -
                              lmetric2 (cylinder_flow s) z u)) y) <=
    lam pow (k + 2) * L`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[lck_dist2; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam pow (2 + l) *
                ltnorm2 (2 + l) (cylinder_flow s)
                  (lnabla_iter 2 l (cylinder_flow s)
                    (\z u. lmetric2 (G:real^3->real^3^3) z u -
                           lmetric2 (cylinder_flow s) z u)) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_LTNORM2_COMPARE THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "lam" THEN ASM_SIMP_TAC[LRG_CYL_COMPARE];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sqrt(sum(0..k) (\l. ltnorm2 (2 + l) (cylinder_flow (&0))
                          (lnabla_iter 2 l (cylinder_flow s)
                            (\z u. lmetric2 (G:real^3->real^3^3) z u -
                                   lmetric2 (cylinder_flow s) z u)) y)) +
    sqrt(sum(0..k) (\l. if l = 0
                        then ltnorm2 2 (cylinder_flow (&0))
                               (\z u. lmetric2 (cylinder_flow s) z u -
                                      lmetric2 (cylinder_flow (&0)) z u) y
                        else &0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[lck_dist2] THEN MATCH_MP_TAC LRG_SQRT_SUM_TRIANGLE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LTNORM2_POS THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "FS" (fun th -> REWRITE_TAC[th]);
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      ASM_SIMP_TAC[LRG_CYL_D_NORM] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LRG_LCK_DIST2_SUMMAND_POS THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRUCT_CASES_TAC(SPEC `l:num` num_CASES) THENL
     [REWRITE_TAC[ADD_CLAUSES; lnabla_iter] THEN
      MATCH_MP_TAC LRG_LTNORM2_TRIANGLE THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[NOT_SUC; SQRT_0; REAL_ADD_RID] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC LRG_LTNORM2_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
      USE_THEN "SPLIT" (fun th -> ASM_SIMP_TAC[th]) THEN
      REWRITE_TAC[NOT_SUC; REAL_ADD_RID]];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
  ASM_SIMP_TAC[LRG_CYL_D_NORM] THEN
  SUBGOAL_THEN `sqrt(&2 * s pow 2) <= &2 * abs s` ASSUME_TAC THENL
   [REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(sum(0..k) (\l. ltnorm2 (2 + l) (cylinder_flow (&0))
                          (lnabla_iter 2 l (cylinder_flow s)
                            (\z u. lmetric2 (G:real^3->real^3^3) z u -
                                   lmetric2 (cylinder_flow s) z u)) y)) <=
    lam pow (k + 2) * sqrt L`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(lam pow (k + 2) * L)` THEN
    ASM_SIMP_TAC[SQRT_MONO_LE; SQRT_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * abs s <= lam pow (k + 2) * (&2 * abs s)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

