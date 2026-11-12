(* ========================================================================= *)
(* Unit pc_cmp_ode (comparison-geometry layer CMP): the one-dimensional      *)
(* comparison lemmas.  Calculus of the model functions sn_k, cs_k; the       *)
(* scalar Riccati comparison s' <= -s^2 - k  ==>  s sn_k <= cs_k (used for   *)
(* the upper Hessian bound along parallel fields and, with s = tr S / (n-1), *)
(* for the Laplacian and Bishop's density comparison); monotone functions    *)
(* with a limit at 0+; ratio monotonicity; elementary bounds of cot and      *)
(* coth.                                                                     *)
(* ========================================================================= *)

needs "src/pc_cmp_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Calculus of the model functions.                                          *)
(* ========================================================================= *)

let CMPO_SQRT_SQUARE = prove
 (`!k. &0 <= k ==> sqrt k * sqrt k = k /\ sqrt k pow 2 = k`,
  SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2]);;

let CMP_SN_HAS_DERIV = prove
 (`!k t. (cmp_sn k has_real_derivative cmp_cs k t) (atreal t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 < k` THENL
   [SUBGOAL_THEN `cmp_sn k = \t. sin(sqrt k * t) / sqrt k` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; cmp_sn] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[cmp_cs] THEN
    SUBGOAL_THEN `&0 < sqrt k` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    REAL_DIFF_TAC THEN UNDISCH_TAC `&0 < sqrt k` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cmp_sn (&0) = \t. t` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; CMP_SN_FLAT]; ALL_TAC] THEN
    REWRITE_TAC[CMP_CS_FLAT; HAS_REAL_DERIVATIVE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(--k)` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `cmp_sn k =
    \t. (exp(sqrt(--k) * t) - exp(--(sqrt(--k) * t))) / (&2 * sqrt(--k))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cmp_sn] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_cs] THEN
  REAL_DIFF_TAC THEN UNDISCH_TAC `&0 < sqrt(--k)` THEN CONV_TAC REAL_FIELD);;

let CMP_CS_HAS_DERIV = prove
 (`!k t. (cmp_cs k has_real_derivative (--k * cmp_sn k t)) (atreal t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 < k` THENL
   [SUBGOAL_THEN `cmp_cs k = \t. cos(sqrt k * t)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; cmp_cs] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[cmp_sn] THEN
    SUBGOAL_THEN `&0 < sqrt k` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    MP_TAC(SPEC `k:real` CMPO_SQRT_SQUARE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    REAL_DIFF_TAC THEN
    UNDISCH_TAC `&0 < sqrt k` THEN UNDISCH_TAC `sqrt k * sqrt k = k` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cmp_cs (&0) = \t. &1` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; CMP_CS_FLAT]; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_MUL_LZERO; HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(--k)` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `--k:real` CMPO_SQRT_SQUARE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `cmp_cs k = \t. (exp(sqrt(--k) * t) + exp(--(sqrt(--k) * t))) / &2`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; cmp_cs] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[cmp_sn] THEN
  REAL_DIFF_TAC THEN
  UNDISCH_TAC `&0 < sqrt(--k)` THEN UNDISCH_TAC `sqrt(--k) * sqrt(--k) = --k` THEN
  CONV_TAC REAL_FIELD);;

let CMP_SN_CS_PYTH = prove
 (`!k t. cmp_cs k t pow 2 + k * cmp_sn k t pow 2 = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmp_sn; cmp_cs] THEN
  ASM_CASES_TAC `&0 < k` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < sqrt k` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    MP_TAC(SPEC `k:real` CMPO_SQRT_SQUARE) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    STRIP_TAC THEN
    MP_TAC(SPEC `sqrt k * t` SIN_CIRCLE) THEN
    UNDISCH_TAC `&0 < sqrt k` THEN UNDISCH_TAC `sqrt k * sqrt k = k` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &0` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < --k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(--k)` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `--k:real` CMPO_SQRT_SQUARE) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`sqrt(--k) * t`; `--(sqrt(--k) * t)`] REAL_EXP_ADD) THEN
  REWRITE_TAC[REAL_ADD_RINV; REAL_EXP_0] THEN
  UNDISCH_TAC `&0 < sqrt(--k)` THEN UNDISCH_TAC `sqrt(--k) * sqrt(--k) = --k` THEN
  CONV_TAC REAL_FIELD);;

(* Positivity of sn_k on (0, pi / sqrt k) (on (0, infinity) for k <= 0). *)

let CMP_SN_POS = prove
 (`!k t. &0 < t /\ (k <= &0 \/ sqrt k * t < pi) ==> &0 < cmp_sn k t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REWRITE_TAC[cmp_sn] THEN
  ASM_CASES_TAC `&0 < k` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt k * t < pi` ASSUME_TAC THENL
     [UNDISCH_TAC `k <= &0 \/ sqrt k * t < pi` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < sqrt k` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIN_POS_PI THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `k = &0` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < --k` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(--k)` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[REAL_SUB_LT; REAL_EXP_MONO_LT] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> --x < x`) THEN ASM_SIMP_TAC[REAL_LT_MUL]);;

(* ========================================================================= *)
(* Monotone functions on (0,T) with a limit at 0+, and the                   *)
(* scalar Riccati comparison.                                                *)
(* ========================================================================= *)

(* Monotonicity on (0,T) from the sign of the derivative. *)

let CMPO_DECREASING_ON = prove
 (`!h h' L a b.
        (!t. &0 < t /\ t < L ==> (h has_real_derivative h' t) (atreal t) /\ h' t <= &0) /\
        &0 < a /\ a <= b /\ b < L
        ==> h b <= h a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --((h:real->real) x)`; `\x. --((h':real->real) x)`;
                 `real_interval(&0,L)`; `a:real`; `b:real`]
    HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_SIMP_TAC[];
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> &0 <= --x`) THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* A non-increasing function on (0,T) with limit 0 at 0+ is <= 0 there. *)

let CMPO_DECREASING_LIM0 = prove
 (`!h h' L.
        (!t. &0 < t /\ t < L ==> (h has_real_derivative h' t) (atreal t) /\ h' t <= &0) /\
        (h ---> &0) (atreal (&0) within {t | &0 < t})
        ==> !t. &0 < t /\ t < L ==> h t <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `((h:real->real) ---> &0) (atreal (&0) within {t | &0 < t})` THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real->real) t`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min t d / &2`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->real`; `h':real->real`; `L:real`; `min t d / &2`; `t:real`]
    CMPO_DECREASING_ON) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let CMPO_INCREASING_LIM0 = prove
 (`!h h' L.
        (!t. &0 < t /\ t < L ==> (h has_real_derivative h' t) (atreal t) /\ &0 <= h' t) /\
        (h ---> &0) (atreal (&0) within {t | &0 < t})
        ==> !t. &0 < t /\ t < L ==> &0 <= h t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --((h:real->real) x)`; `\x. --((h':real->real) x)`; `L:real`]
    CMPO_DECREASING_LIM0) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`) THEN ASM_SIMP_TAC[]];
      MP_TAC(ISPECL [`atreal (&0) within {t | &0 < t}`; `h:real->real`; `&0`]
        REALLIM_NEG) THEN
      ASM_REWRITE_TAC[REAL_NEG_0]];
    REWRITE_TAC[REAL_ARITH `--x <= &0 <=> &0 <= x`]]);;

(* Derivative of h = sn^2 s - sn cs. *)

let CMPO_RICCATI_H_DERIV = prove
 (`!k (s:real->real) s' t.
        (s has_real_derivative s') (atreal t)
        ==> ((\t. cmp_sn k t pow 2 * s t - cmp_sn k t * cmp_cs k t) has_real_derivative
             (((&2 * cmp_sn k t * cmp_cs k t) * s t + cmp_sn k t pow 2 * s') -
              (cmp_cs k t * cmp_cs k t + cmp_sn k t * (--k * cmp_sn k t))))
            (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:real`; `t:real`] CMP_SN_HAS_DERIV) THEN
  MP_TAC(SPECL [`k:real`; `t:real`] CMP_CS_HAS_DERIV) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `((\t. cmp_sn k t pow 2) has_real_derivative (&2 * cmp_sn k t * cmp_cs k t))
    (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cmp_sn k`; `cmp_cs k t`; `t:real`; `2`]
      HAS_REAL_DERIVATIVE_POW_ATREAL) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\t. cmp_sn k t pow 2`; `&2 * cmp_sn k t * cmp_cs k t`;
                           `s:real->real`; `s':real`; `t:real`]
    HAS_REAL_DERIVATIVE_MUL_ATREAL)) THEN
  MP_TAC(ISPECL [`cmp_sn k`; `cmp_cs k t`; `cmp_cs k`; `--k * cmp_sn k t`;
                 `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\t. cmp_sn k t pow 2 * (s:real->real) t`;
    `cmp_sn k t pow 2 * s' + (&2 * cmp_sn k t * cmp_cs k t) * (s:real->real) t`;
    `\t. cmp_sn k t * cmp_cs k t`;
    `cmp_sn k t * (--k * cmp_sn k t) + cmp_cs k t * cmp_cs k t`;
    `atreal t`] HAS_REAL_DERIVATIVE_SUB)) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* The scalar Riccati comparison: s' <= -s^2 - k on (0,T) with             *)
(* sn_k^2 s - sn_k cs_k -> 0 at 0+ gives s sn_k <= cs_k, i.e. s <= ct_k     *)
(* where sn_k > 0 (Petersen Cor 6.4.2 in the scalar form).                   *)

let CMP_RICCATI_COMPARISON = prove
 (`!k s s' L.
        (!t. &0 < t /\ t < L ==> &0 < cmp_sn k t) /\
        (!t. &0 < t /\ t < L
             ==> (s has_real_derivative s' t) (atreal t) /\
                 s' t <= --(s t pow 2) - k) /\
        ((\t. cmp_sn k t pow 2 * s t - cmp_sn k t * cmp_cs k t) ---> &0)
        (atreal (&0) within {t | &0 < t})
        ==> !t. &0 < t /\ t < L ==> s t * cmp_sn k t <= cmp_cs k t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. cmp_sn k t pow 2 * (s:real->real) t - cmp_sn k t * cmp_cs k t`;
    `\t. ((&2 * cmp_sn k t * cmp_cs k t) * (s:real->real) t +
          cmp_sn k t pow 2 * s' t) -
         (cmp_cs k t * cmp_cs k t + cmp_sn k t * (--k * cmp_sn k t))`;
    `L:real`] CMPO_DECREASING_LIM0) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMPO_RICCATI_H_DERIV THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `cmp_sn k t pow 2 * (s':real->real) t <=
        cmp_sn k t pow 2 * (--((s:real->real) t pow 2) - k)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      MP_TAC(SPEC `cmp_sn k t * (s:real->real) t - cmp_cs k t` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < cmp_sn k t` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `&0 < a /\ a pow 2 * b - a * c <= &0 ==> a * (b * a - c) <= a * &0`)) THEN
  SIMP_TAC[REAL_LE_LMUL_EQ; ASSUME `&0 < cmp_sn k t`] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Ratio monotonicity, the initial condition of the Riccati                  *)
(* comparison, and nonnegativity from a nonnegative derivative.              *)
(* ========================================================================= *)

(* If q > 0 and p' q <= p q' on (0,L), then p/q is non-increasing there.   *)

let CMPO_RATIO_DECREASING = prove
 (`!p p' q q' L a b.
        (!t. &0 < t /\ t < L
             ==> (p has_real_derivative p' t) (atreal t) /\
                 (q has_real_derivative q' t) (atreal t) /\
                 &0 < q t /\ p' t * q t <= p t * q' t) /\
        &0 < a /\ a <= b /\ b < L
        ==> p b * q a <= p a * q b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. (p:real->real) t / (q:real->real) t`;
                 `\t. ((p':real->real) t * (q:real->real) t - p t * (q':real->real) t) /
                      q t pow 2`;
                 `L:real`; `a:real`; `b:real`] CMPO_DECREASING_ON) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:real->real`; `(p':real->real) t`; `q:real->real`;
                     `(q':real->real) t`; `t:real`] HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> x <= &0`) THEN
      REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= --x * y ==> x * y <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (q:real->real) a /\ &0 < q b` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:real`); FIRST_X_ASSUM(MP_TAC o SPEC `b:real`)] THEN
    ANTS_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RAT_LEMMA4]);;

(* Nonnegativity on [0,a] from f(0) = 0 and f' >= 0. *)

let CMPO_MONO_FROM0 = prove
 (`!f f' a.
        &0 <= a /\ f(&0) = &0 /\
        (!x. &0 <= x /\ x <= a ==> (f has_real_derivative f' x) (atreal x) /\ &0 <= f' x)
        ==> !x. &0 <= x /\ x <= a ==> &0 <= f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `real_interval[&0,a]`;
                 `&0`; `x:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL; REAL_LE_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THEN X_GEN_TAC `y:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

(* The initial condition of the Riccati comparison holds as soon as t s(t) *)
(* is bounded near 0+.                                                       *)

let CMPO_RICCATI_INIT = prove
 (`!k (s:real->real) B d.
        &0 < d /\ (!t. &0 < t /\ t < d ==> abs(t * s t) <= B)
        ==> ((\t. cmp_sn k t pow 2 * s t - cmp_sn k t * cmp_cs k t) ---> &0)
            (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\ !t. abs t < d1 ==> abs(cmp_sn k t) <= &2 * abs t /\
                                                   abs(cmp_cs k t) <= &2`
  (X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d1p"))) THENL
   [MP_TAC(SPECL [`k:real`; `&0`] CMP_SN_HAS_DERIV) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; CMP_SN_ZERO; CMP_CS_ZERO] THEN
    REWRITE_TAC[REALLIM_ATREAL; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sn"))) THEN
    MP_TAC(SPECL [`k:real`; `&0`] CMP_CS_HAS_DERIV) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL; CMP_CS_ZERO; REALLIM_ATREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs"))) THEN
    EXISTS_TAC `min d2 d3` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t = &0` THENL
     [ASM_REWRITE_TAC[CMP_SN_ZERO; CMP_CS_ZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < abs t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "sn" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `&0 < abs t`) (ASSUME `abs t < d2`)))) THEN
      SIMP_TAC[REAL_FIELD `~(t = &0) ==> x / t - &1 = (x - t) / t`;
               ASSUME `~(t = &0)`] THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN SIMP_TAC[REAL_LT_LDIV_EQ; ASSUME `&0 < abs t`] THEN
      REAL_ARITH_TAC;
      USE_THEN "cs" (fun th -> MP_TAC(MATCH_MP th
        (CONJ (ASSUME `&0 < abs t`) (ASSUME `abs t < d3`)))) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < e / (&8 * (abs B + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min d (min d1 (e / (&8 * (abs B + &1))))` THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs t = t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(t * (s:real->real) t) <= B` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(cmp_sn k t) <= &2 * t /\ abs(cmp_cs k t) <= &2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "d1p" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs t < d1`))) THEN
    REWRITE_TAC[ASSUME `abs t = t`];
    ALL_TAC] THEN
  SUBGOAL_THEN `t * (&8 * (abs B + &1)) < e` ASSUME_TAC THENL
   [UNDISCH_TAC `abs t < e / (&8 * (abs B + &1))` THEN
    REWRITE_TAC[ASSUME `abs t = t`] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &8 * (abs B + &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(cmp_sn k t pow 2 * (s:real->real) t) <= &4 * t * abs B`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_POW_2] THEN
    SUBGOAL_THEN `abs(cmp_sn k t) * abs(cmp_sn k t) <= (&2 * t) * (&2 * t)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((&2 * t) * (&2 * t)) * abs((s:real->real) t)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
    UNDISCH_TAC `abs(t * (s:real->real) t) <= B` THEN
    REWRITE_TAC[REAL_ABS_MUL; ASSUME `abs t = t`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&4 * t) * (t * abs((s:real->real) t)) <= (&4 * t) * abs B`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(cmp_sn k t * cmp_cs k t) <= &4 * t` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= (&2 * t) * &2 ==> x <= &4 * t`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * abs B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Elementary bounds of sin, cos, sinh, cosh near 0, and the                 *)
(* resulting bounds of the model functions used by S4 and S7.               *)
(* ========================================================================= *)

let CMPO_SIN_LE_X = prove
 (`!x. &0 <= x ==> sin x <= x`,
  MP_TAC REAL_ABS_SIN_BOUND_LE THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let CMPO_COS_LOWER = prove
 (`!x. &0 <= x ==> &1 - x pow 2 / &2 <= cos x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. cos y - &1 + y pow 2 / &2`; `\y. --(sin y) + y`; `x:real`]
    CMPO_MONO_FROM0) THEN
  REWRITE_TAC[COS_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `y:real` CMPO_SIN_LE_X) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REAL_ARITH_TAC]);;

let CMPO_SIN_LOWER = prove
 (`!x. &0 <= x ==> x - x pow 3 / &6 <= sin x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. sin y - y + y pow 3 / &6`; `\y. cos y - &1 + y pow 2 / &2`;
                 `x:real`] CMPO_MONO_FROM0) THEN
  REWRITE_TAC[SIN_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `y:real` CMPO_COS_LOWER) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REAL_ARITH_TAC]);;

let CMPO_ONE_LT_PI2 = prove
 (`&1 < pi / &2`,
  MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

let CMPO_PHI = prove
 (`!x. &0 <= x /\ x <= &1 ==> (&1 - x pow 2) * sin x <= x * cos x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. y * cos y - (&1 - y pow 2) * sin y`;
                 `\y. y * sin y + y pow 2 * cos y`; `&1`] CMPO_MONO_FROM0) THEN
  REWRITE_TAC[SIN_0; COS_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC SIN_POS_PI_LE THEN MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
        ASM_CASES_TAC `y = &0` THEN ASM_REWRITE_TAC[COS_0; REAL_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC COS_POS_PI2 THEN
        MP_TAC CMPO_ONE_LT_PI2 THEN ASM_REAL_ARITH_TAC]];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Hyperbolic sine and cosine, written with exp. *)

let CMPO_SINH_POS = prove
 (`!x. &0 <= x ==> &0 <= (exp x - exp(--x)) / &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `b <= a ==> &0 <= (a - b) / &2`) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC);;

let CMPO_COSH_POS = prove
 (`!x. &0 < (exp x + exp(--x)) / &2`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_EXP_POS_LT) THEN
  MP_TAC(SPEC `--x:real` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC);;

let CMPO_COSH_GE_SINH = prove
 (`!x. (exp x - exp(--x)) / &2 <= (exp x + exp(--x)) / &2`,
  GEN_TAC THEN MP_TAC(SPEC `--x:real` REAL_EXP_POS_LT) THEN REAL_ARITH_TAC);;

let CMPO_COSH_LE2 = prove
 (`!x. &0 <= x /\ x <= &1 ==> (exp x + exp(--x)) / &2 <= &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp x <= exp(&1) /\ exp(--x) <= exp(&0)` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_0] THEN MP_TAC E_APPROX_32 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let CMPO_SINH_LE_2X = prove
 (`!x. &0 <= x /\ x <= &1 ==> (exp x - exp(--x)) / &2 <= &2 * x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. &2 * y - (exp y - exp(--y)) / &2`;
                 `\y. &2 - (exp y + exp(--y)) / &2`; `&1`] CMPO_MONO_FROM0) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `y:real` CMPO_COSH_LE2) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let CMPO_COSH_LE_QUAD = prove
 (`!x. &0 <= x /\ x <= &1 ==> (exp x + exp(--x)) / &2 <= &1 + x pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. &1 + y pow 2 - (exp y + exp(--y)) / &2`;
                 `\y. &2 * y - (exp y - exp(--y)) / &2`; `&1`] CMPO_MONO_FROM0) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `y:real` CMPO_SINH_LE_2X) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let CMPO_SINH_UPPER = prove
 (`!x. &0 <= x /\ x <= &1 ==> (exp x - exp(--x)) / &2 <= x + x pow 3 / &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. y + y pow 3 / &3 - (exp y - exp(--y)) / &2`;
                 `\y. &1 + y pow 2 - (exp y + exp(--y)) / &2`; `&1`] CMPO_MONO_FROM0) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `y:real` CMPO_COSH_LE_QUAD) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let CMPO_PSI = prove
 (`!x. &0 <= x
       ==> x * (exp x + exp(--x)) / &2 <= (&1 + x pow 2) * (exp x - exp(--x)) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. (&1 + y pow 2) * (exp y - exp(--y)) / &2 -
                      y * (exp y + exp(--y)) / &2`;
                 `\y. y * (exp y - exp(--y)) / &2 + y pow 2 * (exp y + exp(--y)) / &2`;
                 `x:real`] CMPO_MONO_FROM0) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; CMPO_SINH_POS; REAL_LT_IMP_LE; CMPO_COSH_POS]];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REAL_ARITH_TAC]);;

let CMPO_CHI = prove
 (`!x. &0 <= x
       ==> x * (exp x + exp(--x)) / &2 <= (&1 + x) * (exp x - exp(--x)) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. (&1 + y) * (exp y - exp(--y)) / &2 -
                      y * (exp y + exp(--y)) / &2`;
                 `\y. (exp y - exp(--y)) / &2 +
                      y * ((exp y + exp(--y)) / &2 - (exp y - exp(--y)) / &2)`;
                 `x:real`] CMPO_MONO_FROM0) THEN
  REWRITE_TAC[REAL_NEG_0; REAL_EXP_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[CMPO_SINH_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `y:real` CMPO_COSH_GE_SINH) THEN REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Bounds of the model functions (x = sqrt K r).                             *)
(* ========================================================================= *)

let CMPO_SQRT_PARAM = prove
 (`!K r. &0 < K /\ &0 < r /\ K * r pow 2 <= &1
         ==> &0 < sqrt K /\ K = sqrt K pow 2 /\
             &0 < sqrt K * r /\ sqrt K * r <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt K` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LT_MUL] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 * &1 < (sqrt K * r) * (sqrt K * r)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(sqrt K * r) * (sqrt K * r) = K * r pow 2` SUBST1_TAC THENL
   [MP_TAC(SPEC `K:real` CMPO_SQRT_SQUARE) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    CONV_TAC REAL_RING;
    ASM_REAL_ARITH_TAC]);;

(* ct_K(r) >= 1/r - K r for K r^2 <= 1 (lower Hessian bound of S4). *)

let CMP_CT_LOWER_BOUND = prove
 (`!K r. &0 <= K /\ &0 < r /\ K * r pow 2 <= &1
         ==> (inv r - K * r) * cmp_sn K r <= cmp_cs K r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[CMP_SN_FLAT; CMP_CS_FLAT; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`K:real`; `r:real`] CMPO_SQRT_PARAM) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CMP_SN_POS_CURV] THEN
  ABBREV_TAC `a = sqrt K` THEN STRIP_TAC THEN
  MP_TAC(SPEC `a * r` CMPO_PHI) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `(inv r - a pow 2 * r) * sin(a * r) / a =
    ((&1 - (a * r) pow 2) * sin(a * r)) / (a * r)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC]);;

(* ct_{-K}(r) <= 1/r + K r (upper Hessian bound of S4). *)

let CMP_CT_UPPER_NEG = prove
 (`!K r. &0 <= K /\ &0 < r
         ==> cmp_cs (--K) r <= (inv r + K * r) * cmp_sn (--K) r`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; CMP_SN_FLAT; CMP_CS_FLAT; REAL_MUL_LZERO;
                    REAL_ADD_RID] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CMP_SN_NEG_CURV] THEN
  SUBGOAL_THEN `&0 < sqrt K /\ K = sqrt K pow 2` MP_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `a = sqrt K` THEN STRIP_TAC THEN
  MP_TAC(SPEC `a * r` CMPO_PSI) THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `(inv r + a pow 2 * r) * (exp(a * r) - exp(--(a * r))) / (&2 * a) =
    ((&1 + (a * r) pow 2) * (exp(a * r) - exp(--(a * r))) / &2) / (a * r)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN REAL_ARITH_TAC]);;

(* sqrt K coth(sqrt K d) <= 1/d + sqrt K (Laplacian bound of S7). *)

let CMP_CT_UPPER_NEG_SQRT = prove
 (`!K d. &0 <= K /\ &0 < d
         ==> cmp_cs (--K) d <= (inv d + sqrt K) * cmp_sn (--K) d`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; CMP_SN_FLAT; CMP_CS_FLAT; SQRT_0; REAL_ADD_RID] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CMP_SN_NEG_CURV] THEN
  SUBGOAL_THEN `&0 < sqrt K` MP_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `a = sqrt K` THEN DISCH_TAC THEN
  MP_TAC(SPEC `a * d` CMPO_CHI) THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `(inv d + a) * (exp(a * d) - exp(--(a * d))) / (&2 * a) =
    ((&1 + a * d) * (exp(a * d) - exp(--(a * d))) / &2) / (a * d)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN REAL_ARITH_TAC]);;

(* (sn_K(r)/r)^2 >= 1/2 and (sn_{-K}(r)/r)^2 <= 2 for K r^2 <= 1 (metric   *)
(* comparability in S4).                                                     *)

let CMP_SN_LOWER_HALF = prove
 (`!K r. &0 <= K /\ &0 < r /\ K * r pow 2 <= &1
         ==> r pow 2 <= &2 * cmp_sn K r pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[CMP_SN_FLAT] THEN
    MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`K:real`; `r:real`] CMPO_SQRT_PARAM) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CMP_SN_POS_CURV] THEN
  ABBREV_TAC `a = sqrt K` THEN STRIP_TAC THEN
  MP_TAC(SPEC `a * r` CMPO_SIN_LOWER) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&5 / &6 * (a * r) <= sin(a * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * r - (a * r) pow 3 / &6` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a * r) pow 3 <= (a * r)` MP_TAC THENL
     [SUBGOAL_THEN `(a * r) pow 3 = (a * r) * (a * r) pow 2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&5 / &6 * (a * r)) pow 2 <= sin(a * r) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (sin(a * r) / a) pow 2 = (&2 * sin(a * r) pow 2) / a pow 2`
  SUBST1_TAC THENL [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 <= a pow 2 * r pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CMP_SN_UPPER_NEG_TWO = prove
 (`!K r. &0 <= K /\ &0 < r /\ K * r pow 2 <= &1
         ==> cmp_sn (--K) r pow 2 <= &2 * r pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `K = &0` THENL
   [ASM_REWRITE_TAC[REAL_NEG_0; CMP_SN_FLAT] THEN
    MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`K:real`; `r:real`] CMPO_SQRT_PARAM) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CMP_SN_NEG_CURV] THEN
  ABBREV_TAC `a = sqrt K` THEN STRIP_TAC THEN
  MP_TAC(SPEC `a * r` CMPO_SINH_UPPER) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MP_TAC(SPEC `a * r` CMPO_SINH_POS) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(exp(a * r) - exp(--(a * r))) / &2 <= &4 / &3 * (a * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * r + (a * r) pow 3 / &3` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a * r) pow 3 <= (a * r)` MP_TAC THENL
     [SUBGOAL_THEN `(a * r) pow 3 = (a * r) * (a * r) pow 2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((exp(a * r) - exp(--(a * r))) / &2) pow 2 <= (&4 / &3 * (a * r)) pow 2`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((exp(a * r) - exp(--(a * r))) / (&2 * a)) pow 2 =
    ((exp(a * r) - exp(--(a * r))) / &2) pow 2 / a pow 2`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `&0 <= a pow 2 * r pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The model cotangent ct_k = cs_k / sn_k solves the Riccati                 *)
(* equation, and sn_k, cs_k near 0.                                          *)
(* ========================================================================= *)

let CMP_CT_HAS_DERIV = prove
 (`!k t. ~(cmp_sn k t = &0)
         ==> ((\t. cmp_cs k t / cmp_sn k t) has_real_derivative
              (--k - (cmp_cs k t / cmp_sn k t) pow 2)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cmp_cs k`; `--k * cmp_sn k t`; `cmp_sn k`; `cmp_cs k t`; `t:real`]
    HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
  ASM_REWRITE_TAC[CMP_SN_HAS_DERIV; CMP_CS_HAS_DERIV; ETA_AX] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`k:real`; `t:real`] CMP_SN_CS_PYTH) THEN
  UNDISCH_TAC `~(cmp_sn k t = &0)` THEN CONV_TAC REAL_FIELD);;

let CMPO_SN_NEAR0 = prove
 (`!k. ?d. &0 < d /\
           !t. &0 < t /\ t < d
               ==> t / &2 <= cmp_sn k t /\ cmp_sn k t <= &2 * t /\
                   &1 / &2 <= cmp_cs k t /\ cmp_cs k t <= &2`,
  GEN_TAC THEN
  MP_TAC(SPECL [`k:real`; `&0`] CMP_SN_HAS_DERIV) THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; CMP_SN_ZERO; CMP_CS_ZERO] THEN
  REWRITE_TAC[REALLIM_ATREAL; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sn"))) THEN
  MP_TAC(SPECL [`k:real`; `&0`] CMP_CS_HAS_DERIV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ATREAL; CMP_CS_ZERO; REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `&1 / &2`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs"))) THEN
  EXISTS_TAC `min d2 d3` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < abs t /\ abs t = t /\ abs t < d2 /\ abs t < d3`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sn" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `&0 < abs t`) (ASSUME `abs t < d2`)))) THEN
  USE_THEN "cs" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `&0 < abs t`) (ASSUME `abs t < d3`)))) THEN
  SIMP_TAC[REAL_FIELD `&0 < t ==> x / t - &1 = (x - t) / t`; ASSUME `&0 < t`] THEN
  REWRITE_TAC[REAL_ABS_DIV; ASSUME `abs t = t`] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; ASSUME `&0 < t`] THEN
  REAL_ARITH_TAC);;

