(* ========================================================================= *)
(* Unit pc_rfa_s2ode: the real analysis of the J-free route for the          *)
(* 2-dimensional case of P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT.  The radial   *)
(* ODE F'' = 1/2 - C exp F with F(0) = max F and F'(0) = 0 has a first zero  *)
(* A of F', and the curvature gap there satisfies 0 < alpha < beta           *)
(* (RFA_S2_FIRST_ZERO, from the energy identity and log((1+t)/(1-t)) > 2t);  *)
(* a C^1 constant-speed closed curve on the unit circle, injective on        *)
(* [0,2 pi), has speed 1 (RFA_S2_CIRCLE); uniqueness for second-order ODEs   *)
(* with a Lipschitz bound (RFA_S2_ODE2_UNIQ).                                *)
(* ========================================================================= *)

needs "src/pc_rfa_shi.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Two logarithm inequalities (RFA_S2_LOG_GAP, RFA_S2_ROOT_GAP).             *)
(* ========================================================================= *)

let RFA_S2_LOG_GAP = prove
 (`!t. &0 < t /\ t < &1 ==> &2 * t < log((&1 + t) / (&1 - t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. log(&1 + x) - log(&1 - x) - &2 * x`;
                 `\x. inv(&1 + x) + inv(&1 - x) - &2`; `&0`; `t:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `inv(&1 + x) + inv(&1 - x) - &2` THEN
      REAL_DIFF_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REAL_DIFF_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL; REAL_ADD_RID; REAL_SUB_RZERO; LOG_1; REAL_MUL_RZERO;
              REAL_SUB_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv(&1 + x) + inv(&1 - x) - &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&1 + x) + inv(&1 - x) - &2 = (&2 * x pow 2) / ((&1 + x) * (&1 - x))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&1 + x = &0) /\ ~(&1 - x = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log((&1 + t) / (&1 - t)) = log(&1 + t) - log(&1 - t)` SUBST1_TAC THENL
   [MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (inv(&1 + x) + inv(&1 - x) - &2) * t` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let RFA_S2_ROOT_GAP = prove
 (`!a b. &0 < a /\ a < b /\ &1 < b /\ log b - log a = b - a ==> &2 < a + b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `c = (a + b) / &2` THEN ABBREV_TAC `s = (b - a) / &2` THEN
  SUBGOAL_THEN `b = c + s /\ a = c - s /\ &0 < s /\ s < c /\ c <= &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c"; "s"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s / c /\ s / c < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `s / c` RFA_S2_LOG_GAP) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 + s / c) / (&1 - s / c) = b / a` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(c = &0) /\ ~(c - s = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(b / a) = log b - log a` SUBST1_TAC THENL
   [MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 * s <= &2 * (s / c)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < s /\ s * c <= s * &1 ==> s * c <= s`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Mean value inequalities and the energy identity of the                    *)
(* radial ODE (RFA_S2_MVT_LE, RFA_S2_MVT_GE, RFA_S2_ENERGY).                  *)
(* ========================================================================= *)

let RFA_S2_MVT_LE = prove
 (`!(f:real->real) f' a b c.
     a < b /\ (!x. (f has_real_derivative f' x) (atreal x)) /\
     (!x. a < x /\ x < b ==> f' x <= c)
     ==> f b - f a <= c * (b - a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

let RFA_S2_MVT_GE = prove
 (`!(f:real->real) f' a b c.
     a < b /\ (!x. (f has_real_derivative f' x) (atreal x)) /\
     (!x. a < x /\ x < b ==> c <= f' x)
     ==> c * (b - a) <= f b - f a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `b:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]]);;

let RFA_S2_ENERGY = prove
 (`!(y:real->real) y' C m.
     (!r. (y has_real_derivative y' r) (atreal r)) /\
     (!r. (y' has_real_derivative (&1 / &2 - C * exp(y r))) (atreal r)) /\
     y(&0) = m /\ y'(&0) = &0
     ==> !r. y' r * y' r - y r + &2 * C * exp(y r) = &2 * C * exp m - m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (y':real->real) r * y' r - y r + &2 * C * exp(y r)`; `(:real)`]
                HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `r:real` THEN
    SUBGOAL_THEN
     `((\r. (y':real->real) r * y' r - y r + &2 * C * exp(y r)) has_real_derivative
       ((y' r * (&1 / &2 - C * exp(y r)) + (&1 / &2 - C * exp(y r)) * y' r) -
        y' r + &2 * C * (exp(y r) * y' r))) (atreal r)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
         [MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        MP_TAC(ISPECL [`y:real->real`; `exp`; `(y':real->real) r`; `exp((y:real->real) r)`;
                       `r:real`] REAL_DIFF_CHAIN_ATREAL) THEN
        ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_EXP; o_DEF] THEN
        REWRITE_TAC[REAL_MUL_SYM]];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN X_GEN_TAC `r:real` THEN
  FIRST_ASSUM(MP_TAC o SPEC `&0`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The first zero of F' and the gap 0 < alpha < beta                         *)
(* (RFA_S2_NEG_START, RFA_S2_FIRST_ZERO).                                     *)
(* ========================================================================= *)

let RFA_S2_NEG_START = prove
 (`!(f:real->real) f' x.
     (f has_real_derivative f') (atreal x) /\ f' < &0
     ==> ?e. &0 < e /\ !r. x < r /\ r <= x + e ==> f r < f x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `--f' / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r - x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = ((f:real->real) r - f x) / (r - x)` THEN
  SUBGOAL_THEN `(f:real->real) r - f x = q * (r - x)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < r - x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `q < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q * (r - x) < &0` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `a * b < &0 <=> &0 < --a * b`] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let RFA_S2_FIRST_ZERO = prove
 (`!(y:real->real) y' C m.
     &0 < C /\ &1 / &2 < C * exp m /\
     (!r. (y has_real_derivative y' r) (atreal r)) /\
     (!r. (y' has_real_derivative (&1 / &2 - C * exp(y r))) (atreal r)) /\
     y(&0) = m /\ y'(&0) = &0 /\ (!r. y r <= m)
     ==> ?A. &0 < A /\ y' A = &0 /\ (!r. &0 < r /\ r < A ==> y' r < &0) /\
             &0 < &1 / &2 - C * exp(y A) /\
             &1 / &2 - C * exp(y A) < C * exp m - &1 / &2`,
  REPEAT GEN_TAC THEN INTRO_TAC "C0 Cm dy ddy y0 dy0 ymax" THEN
  MP_TAC(ISPECL [`y:real->real`; `y':real->real`; `C:real`; `m:real`] RFA_S2_ENERGY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "en") THEN
  SUBGOAL_THEN `!r. (y':real->real) real_continuous atreal r` (LABEL_TAC "cdy") THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. (y':real->real) real_continuous_on real_interval[a,b]`
  (LABEL_TAC "cdyon") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. m - &2 * C * exp m <= (y:real->real) r` (LABEL_TAC "low") THENL
   [GEN_TAC THEN USE_THEN "en" (MP_TAC o SPEC `r:real`) THEN
    MP_TAC(SPEC `(y:real->real) r` REAL_EXP_POS_LT) THEN
    MP_TAC(SPEC `(y':real->real) r` REAL_LE_SQUARE) THEN
    SUBGOAL_THEN `&0 < C * exp((y:real->real) r)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y':real->real`; `&1 / &2 - C * exp m`; `&0`] RFA_S2_NEG_START) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `m = (y:real->real)(&0)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; USE_THEN "ddy" (ACCEPT_TAC o SPEC `&0`)];
      ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[REAL_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "neg1")))] THEN
  SUBGOAL_THEN `?z. &0 < z /\ (y':real->real) z = &0`
  (X_CHOOSE_THEN `z0:real` STRIP_ASSUME_TAC) THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN GEN_REWRITE_TAC RAND_CONV [NOT_EXISTS_THM] THEN
    DISCH_THEN(LABEL_TAC "nz") THEN
    SUBGOAL_THEN `!r. &0 < r ==> (y':real->real) r < &0` (LABEL_TAC "neg") THENL
     [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      ASM_CASES_TAC `r <= e1` THENL
       [USE_THEN "neg1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`y':real->real`; `e1:real`; `r:real`; `&0`] REAL_IVT_INCREASING) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "neg1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
        USE_THEN "nz" (MP_TAC o SPEC `z:real`) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `s0 = log(inv(&2 * C))` THEN
    SUBGOAL_THEN `C * exp s0 = &1 / &2` ASSUME_TAC THENL
     [EXPAND_TAC "s0" THEN
      SUBGOAL_THEN `&0 < inv(&2 * C)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[EXP_LOG] THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `?r2. &0 < r2 /\ (y:real->real) r2 < s0` STRIP_ASSUME_TAC THENL
     [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN GEN_REWRITE_TAC RAND_CONV [NOT_EXISTS_THM] THEN
      DISCH_THEN(LABEL_TAC "above") THEN
      SUBGOAL_THEN `!x. &0 < x ==> &1 / &2 - C * exp((y:real->real) x) <= &0`
      (LABEL_TAC "conc") THENL
       [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
        SUBGOAL_THEN `s0 <= (y:real->real) x` ASSUME_TAC THENL
         [USE_THEN "above" (MP_TAC o SPEC `x:real`) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `C * exp s0 <= C * exp((y:real->real) x)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `!r. e1 < r ==> (y':real->real) r <= y' e1` (LABEL_TAC "dec1") THENL
       [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`y':real->real`; `\r. &1 / &2 - C * exp((y:real->real) r)`;
                       `e1:real`; `r:real`; `&0`] RFA_S2_MVT_LE) THEN
        BETA_TAC THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "conc" MATCH_MP_TAC THEN
          ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y':real->real) e1 < &0` ASSUME_TAC THENL
       [USE_THEN "neg1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `R = e1 + ((y:real->real) e1 - (m - &2 * C * exp m) + &1) / --(y' e1)` THEN
      SUBGOAL_THEN `e1 < R` ASSUME_TAC THENL
       [EXPAND_TAC "R" THEN REWRITE_TAC[REAL_LT_ADDR] THEN MATCH_MP_TAC REAL_LT_DIV THEN
        USE_THEN "low" (MP_TAC o SPEC `e1:real`) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`y:real->real`; `y':real->real`; `e1:real`; `R:real`;
                     `(y':real->real) e1`] RFA_S2_MVT_LE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "dec1" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(y':real->real) e1 * (R - e1) =
                    --((y:real->real) e1 - (m - &2 * C * exp m) + &1)`
      SUBST1_TAC THENL
       [EXPAND_TAC "R" THEN UNDISCH_TAC `(y':real->real) e1 < &0` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      USE_THEN "low" (MP_TAC o SPEC `R:real`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 / &2 - C * exp((y:real->real) r2)` ASSUME_TAC THENL
     [SUBGOAL_THEN `C * exp((y:real->real) r2) < C * exp s0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LT]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `c = &1 / &2 - C * exp((y:real->real) r2)` THEN
    SUBGOAL_THEN `!x. r2 < x ==> c <= &1 / &2 - C * exp((y:real->real) x)` (LABEL_TAC "conv")
    THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN EXPAND_TAC "c" THEN
      MATCH_MP_TAC(REAL_ARITH `b <= a ==> &1 / &2 - a <= &1 / &2 - b`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_MONO_LE] THEN
      MP_TAC(ISPECL [`y:real->real`; `y':real->real`; `r2:real`; `x:real`; `&0`]
                    RFA_S2_MVT_LE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        USE_THEN "neg" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y':real->real) r2 < &0` ASSUME_TAC THENL
     [USE_THEN "neg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `R = r2 + (&1 - (y':real->real) r2) / c` THEN
    SUBGOAL_THEN `r2 < R` ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC[REAL_LT_ADDR] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`y':real->real`; `\r. &1 / &2 - C * exp((y:real->real) r)`;
                   `r2:real`; `R:real`; `c:real`] RFA_S2_MVT_GE) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "conv" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `c * (R - r2) = &1 - (y':real->real) r2` SUBST1_TAC THENL
     [EXPAND_TAC "R" THEN UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    USE_THEN "neg" (MP_TAC o SPEC `R:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 < z0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "neg1" (MP_TAC o SPEC `z0:real`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Z = {r | e1 <= r /\ (y':real->real) r = &0}` THEN
  MP_TAC(ISPEC `Z:real->bool` INF) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `z0:real` THEN EXPAND_TAC "Z" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `e1:real` THEN EXPAND_TAC "Z" THEN SIMP_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `A = inf Z` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "infle") (LABEL_TAC "infge")) THEN
  SUBGOAL_THEN `e1 <= A` ASSUME_TAC THENL
   [USE_THEN "infge" MATCH_MP_TAC THEN EXPAND_TAC "Z" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(y':real->real) A = &0` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    USE_THEN "cdy" (MP_TAC o SPEC `A:real`) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL; REALLIM_ATREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `abs((y':real->real) A)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "infge" (MP_TAC o SPEC `A + d`) THEN ANTS_TAC THENL
     [X_GEN_TAC `x:real` THEN EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `A <= x` ASSUME_TAC THENL
       [USE_THEN "infle" MATCH_MP_TAC THEN EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      ASM_CASES_TAC `x:real = A` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 < r /\ r < A ==> (y':real->real) r < &0` (LABEL_TAC "negA") THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r <= e1` THENL
     [USE_THEN "neg1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`y':real->real`; `e1:real`; `r:real`; `&0`] REAL_IVT_INCREASING) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "neg1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
      USE_THEN "infle" (MP_TAC o SPEC `z:real`) THEN ANTS_TAC THENL
       [EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `A:real` THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real->real) A < m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y:real->real`; `y':real->real`; `&0`; `A:real`] REAL_MVT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
    USE_THEN "negA" (MP_TAC o SPEC `xi:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `(y':real->real) xi * (A - &0) < &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * b < &0 <=> &0 < --a * b`] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "en" (MP_TAC o REWRITE_RULE[ASSUME `(y':real->real) A = &0`; REAL_MUL_LZERO;
                                        REAL_SUB_LZERO] o SPEC `A:real`) THEN
  DISCH_TAC THEN
  ABBREV_TAC `aa = &2 * C * exp((y:real->real) A)` THEN
  ABBREV_TAC `bb = &2 * C * exp m` THEN
  SUBGOAL_THEN `&0 < aa /\ aa < bb /\ &1 < bb` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `log bb - log aa = bb - aa` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN
    SUBGOAL_THEN `&0 < &2 * C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_EXP_POS_LT; LOG_EXP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `aa < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\s. s - &2 * C * exp s`; `\s. &1 - &2 * C * exp s`;
                   `(y:real->real) A`; `m:real`] REAL_MVT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        EXISTS_TAC `&1 - &2 * C * exp x` THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `aa < &2 * C * exp xi` ASSUME_TAC THENL
     [EXPAND_TAC "aa" THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - &2 * C * exp xi) * (m - (y:real->real) A) < &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `a * b < &0 <=> &0 < --a * b`] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(m - &2 * C * exp m) - ((y:real->real) A - &2 * C * exp(y A)) =
                 (&1 - &2 * C * exp xi) * (m - y A)` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`aa:real`; `bb:real`] RFA_S2_ROOT_GAP) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aa < &1` THEN MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The circle lemma (RFA_S2_CIRCLE) and uniqueness for second-               *)
(* order ODEs (RFA_S2_ODE2_UNIQ).                                             *)
(* ========================================================================= *)

let RFA_S2_CIRCLE = prove
 (`!(x:real->real) y x' y' c.
     &0 < c /\
     (!t. (x has_real_derivative x' t) (atreal t)) /\
     (!t. (y has_real_derivative y' t) (atreal t)) /\
     (!t. x' real_continuous atreal t) /\ (!t. y' real_continuous atreal t) /\
     (!t. x t pow 2 + y t pow 2 = &1) /\
     (!t. x' t pow 2 + y' t pow 2 = c pow 2) /\
     x(&2 * pi) = x(&0) /\ y(&2 * pi) = y(&0) /\
     (!t. &0 < t /\ t < &2 * pi ==> ~(x t = x(&0) /\ y t = y(&0)))
     ==> c = &1`,
  REPEAT GEN_TAC THEN INTRO_TAC "c0 dx dy cx cy circ spd px py inj" THEN
  SUBGOAL_THEN `!t. (x:real->real) t * x' t + y t * y' t = &0` (LABEL_TAC "orth") THENL
   [X_GEN_TAC `t:real` THEN
    MP_TAC(ISPECL [`\t. (x:real->real) t pow 2 + y t pow 2`;
                   `t:real`; `&2 * (x:real->real) t pow 1 * x' t + &2 * y t pow 1 * y' t`;
                   `&0`] REAL_DERIVATIVE_UNIQUE_ATREAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`x:real->real`; `(x':real->real) t`; `t:real`; `2`]
                        HAS_REAL_DERIVATIVE_POW_ATREAL);
          MP_TAC(ISPECL [`y:real->real`; `(y':real->real) t`; `t:real`; `2`]
                        HAS_REAL_DERIVATIVE_POW_ATREAL)] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
        ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]];
      REWRITE_TAC[REAL_POW_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `w = \t. (x:real->real) t * y' t - y t * x' t` THEN
  SUBGOAL_THEN `!t. (w:real->real) t pow 2 = c pow 2` (LABEL_TAC "w2") THENL
   [X_GEN_TAC `t:real` THEN EXPAND_TAC "w" THEN
    USE_THEN "circ" (MP_TAC o SPEC `t:real`) THEN USE_THEN "spd" (MP_TAC o SPEC `t:real`) THEN
    USE_THEN "orth" (MP_TAC o SPEC `t:real`) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (x':real->real) t = --((y:real->real) t * w t) /\ y' t = x t * w t`
  (LABEL_TAC "rot") THENL
   [X_GEN_TAC `t:real` THEN EXPAND_TAC "w" THEN
    USE_THEN "circ" (MP_TAC o SPEC `t:real`) THEN
    USE_THEN "orth" (MP_TAC o SPEC `t:real`) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (w:real->real) real_continuous atreal t` (LABEL_TAC "cw") THENL
   [X_GEN_TAC `t:real` THEN EXPAND_TAC "w" THEN
    MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = (w:real->real)(&0)` THEN
  SUBGOAL_THEN `!t. (w:real->real) t = e` (LABEL_TAC "wconst") THENL
   [X_GEN_TAC `t:real` THEN
    SUBGOAL_THEN `!s. ~((w:real->real) s = &0)` (LABEL_TAC "wnz") THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "w2" (MP_TAC o SPEC `s:real`) THEN
      UNDISCH_TAC `(w:real->real) s = &0` THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `&0 < c pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real->real) t = e \/ w t = --e` MP_TAC THENL
     [USE_THEN "w2" (MP_TAC o SPEC `t:real`) THEN USE_THEN "w2" (MP_TAC o SPEC `&0`) THEN
      UNDISCH_TAC `(w:real->real)(&0) = e` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!a b. a <= b ==> (w:real->real) real_continuous_on real_interval[a,b]`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(e = &0)` ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN USE_THEN "wnz" (ACCEPT_TAC o SPEC `&0`); ALL_TAC] THEN
    SUBGOAL_THEN `?s. (w:real->real) s = &0` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `&0 < e \/ e < &0` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `&0 <= t \/ t <= &0`) THENL
     [MP_TAC(ISPECL [`w:real->real`; `&0`; `t:real`; `&0`] REAL_IVT_DECREASING);
      MP_TAC(ISPECL [`w:real->real`; `t:real`; `&0`; `&0`] REAL_IVT_INCREASING);
      MP_TAC(ISPECL [`w:real->real`; `&0`; `t:real`; `&0`] REAL_IVT_INCREASING);
      MP_TAC(ISPECL [`w:real->real`; `t:real`; `&0`; `&0`] REAL_IVT_DECREASING)] THEN
    (ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; MESON_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (x':real->real) t = --((y:real->real) t * e) /\ y' t = x t * e`
  (LABEL_TAC "rot2") THENL
   [GEN_TAC THEN USE_THEN "rot" (MP_TAC o SPEC `t:real`) THEN
    USE_THEN "wconst" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. ((\t. (x:real->real) t * cos(e * t) + y t * sin(e * t)) has_real_derivative &0)
          (atreal t) /\
        ((\t. --((x:real->real) t) * sin(e * t) + y t * cos(e * t)) has_real_derivative &0)
          (atreal t)`
  (LABEL_TAC "pq") THENL
   [X_GEN_TAC `t:real` THEN
    SUBGOAL_THEN `((\t. cos(e * t)) has_real_derivative --(sin(e * t)) * e) (atreal t) /\
                  ((\t. sin(e * t)) has_real_derivative cos(e * t) * e) (atreal t)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `((\t. (x:real->real) t * cos(e * t) + y t * sin(e * t)) has_real_derivative
         (x t * --(sin(e * t)) * e + x' t * cos(e * t)) +
         (y t * cos(e * t) * e + y' t * sin(e * t))) (atreal t)`
      MP_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[];
        USE_THEN "rot2" (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
      SUBGOAL_THEN
       `((\t. --((x:real->real) t) * sin(e * t) + y t * cos(e * t)) has_real_derivative
         (--(x t) * cos(e * t) * e + --(x' t) * sin(e * t)) +
         (y t * --(sin(e * t)) * e + y' t * cos(e * t))) (atreal t)`
      MP_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN REPEAT CONJ_TAC THEN
        TRY(MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG) THEN ASM_REWRITE_TAC[];
        USE_THEN "rot2" (fun th -> REWRITE_TAC[th]) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (x:real->real) t * cos(e * t) + y t * sin(e * t) = x(&0) /\
        --(x t) * sin(e * t) + y t * cos(e * t) = y(&0)`
  (LABEL_TAC "pq0") THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t. (x:real->real) t * cos(e * t) + y t * sin(e * t)`; `(:real)`]
                    HAS_REAL_DERIVATIVE_ZERO_CONSTANT);
      MP_TAC(ISPECL [`\t. --((x:real->real) t) * sin(e * t) + y t * cos(e * t)`; `(:real)`]
                    HAS_REAL_DERIVATIVE_ZERO_CONSTANT)] THEN
    (REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN
     ANTS_TAC THENL [USE_THEN "pq" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
     DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
     FIRST_ASSUM(MP_TAC o SPEC `&0`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
     REWRITE_TAC[REAL_MUL_RZERO; COS_0; SIN_0] THEN REAL_ARITH_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. (x:real->real) t = x(&0) * cos(e * t) - y(&0) * sin(e * t) /\
        y t = x(&0) * sin(e * t) + y(&0) * cos(e * t)`
  (LABEL_TAC "form") THENL
   [GEN_TAC THEN USE_THEN "pq0" (MP_TAC o SPEC `t:real`) THEN
    MP_TAC(SPEC `e * t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `cos(e * &2 * pi) = &1` ASSUME_TAC THENL
   [USE_THEN "form" (MP_TAC o SPEC `&2 * pi`) THEN
    USE_THEN "px" SUBST1_TAC THEN USE_THEN "py" SUBST1_TAC THEN
    USE_THEN "circ" (MP_TAC o SPEC `&0`) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `e pow 2 = c pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN USE_THEN "w2" (ACCEPT_TAC o SPEC `&0`); ALL_TAC] THEN
  MP_TAC(SPEC `e * &2 * pi` COS_EQ_1) THEN REWRITE_TAC[ASSUME `cos(e * &2 * pi) = &1`] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real) = n` SUBST_ALL_TAC THENL
   [MP_TAC PI_POS THEN UNDISCH_TAC `e * &2 * pi = &2 * n * pi` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs n = c` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < c /\ (n = c \/ n = --c) ==> abs n = c`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `n pow 2 = c pow 2` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> lhs(concl th) = `abs n`)) THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `abs(&0) = c` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 <= c /\ ~(&1 < c) ==> c = &1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&2 <= c` ASSUME_TAC THENL
   [MP_TAC(SPEC `abs n - &1` REAL_ABS_INTEGER_LEMMA) THEN
    ASM_SIMP_TAC[INTEGER_SUB; INTEGER_ABS; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t0 = &2 * pi / c` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < &2 * pi` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN MP_TAC PI_POS THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < pi / c /\ pi / c < pi` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[REAL_LT_LDIV_EQ; ASSUME `&0 < c`] THEN
      SUBGOAL_THEN `pi * &1 < pi * c` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `cos(n * t0) = &1 /\ sin(n * t0) = &0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `n * t0 = &2 * pi \/ n * t0 = --(&2 * pi)` MP_TAC THENL
     [EXPAND_TAC "t0" THEN
      SUBGOAL_THEN `(n:real) = c \/ n = --c` MP_TAC THENL
       [UNDISCH_TAC `abs n = c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[COS_NEG; SIN_NEG] THEN
    MP_TAC(SPEC `2` COS_NPI) THEN MP_TAC(SPEC `2` SIN_NPI) THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[REAL_NEG_0];
    ALL_TAC] THEN
  USE_THEN "form" (MP_TAC o SPEC `t0:real`) THEN
  REWRITE_TAC[ASSUME `cos(n * t0) = &1`; ASSUME `sin(n * t0) = &0`] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_LID] THEN
  STRIP_TAC THEN USE_THEN "inj" (MP_TAC o SPEC `t0:real`) THEN
  REWRITE_TAC[ASSUME `&0 < t0`; ASSUME `t0 < &2 * pi`] THEN
  REWRITE_TAC[ASSUME `(x:real->real) t0 = x(&0)`; ASSUME `(y:real->real) t0 = y(&0)`]);;

let RFA_S2_ODE2_UNIQ = prove
 (`!(u:real->real) u' u'' v v' v'' L R.
     &0 <= L /\ &0 < R /\
     (!r. (u has_real_derivative u' r) (atreal r)) /\
     (!r. (u' has_real_derivative u'' r) (atreal r)) /\
     (!r. (v has_real_derivative v' r) (atreal r)) /\
     (!r. (v' has_real_derivative v'' r) (atreal r)) /\
     (!r. &0 <= r /\ r <= R ==> abs(u'' r - v'' r) <= L * abs(u r - v r)) /\
     u(&0) = v(&0) /\ u'(&0) = v'(&0)
     ==> !r. &0 <= r /\ r <= R ==> u r = v r`,
  REPEAT GEN_TAC THEN INTRO_TAC "L0 R0 du ddu dv ddv lip i0 i1" THEN
  ABBREV_TAC `q = \r. ((u:real->real) r - v r) pow 2 + (u' r - v' r) pow 2` THEN
  SUBGOAL_THEN
   `!r. ((q:real->real) has_real_derivative
         &2 * (u r - v r) * (u' r - v' r) + &2 * (u' r - v' r) * (u'' r - v'' r))
        (atreal r)`
  (LABEL_TAC "dq") THENL
   [X_GEN_TAC `r:real` THEN EXPAND_TAC "q" THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\r. (u:real->real) r - v r`; `(u':real->real) r - v' r`; `r:real`; `2`]
                    HAS_REAL_DERIVATIVE_POW_ATREAL);
      MP_TAC(ISPECL [`\r. (u':real->real) r - v' r`; `(u'':real->real) r - v'' r`; `r:real`;
                     `2`] HAS_REAL_DERIVATIVE_POW_ATREAL)] THEN
    (BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_1] THEN
     ANTS_TAC THENL
      [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[];
       SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 <= r /\ r <= R ==> (q:real->real) r = &0` ASSUME_TAC THENL
   [X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r = &0` THENL
     [EXPAND_TAC "q" THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`q:real->real`;
                   `\r. &2 * ((u:real->real) r - v r) * (u' r - v' r) +
                        &2 * (u' r - v' r) * (u'' r - v'' r)`;
                   `&1 + L`; `&0`; `r:real`] RFA_GRONWALL_2SIDED) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
        USE_THEN "dq" (fun th -> MESON_TAC[th]);
        REPEAT STRIP_TAC THEN USE_THEN "dq" (ACCEPT_TAC o SPEC `s:real`);
        X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "q" THEN BETA_TAC THEN
        USE_THEN "lip" (MP_TAC o SPEC `s:real`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ABBREV_TAC `a = (u:real->real) s - v s` THEN
        ABBREV_TAC `b = (u':real->real) s - v' s` THEN
        ABBREV_TAC `dd = (u'':real->real) s - v'' s` THEN DISCH_TAC THEN
        SUBGOAL_THEN `&2 * abs a * abs b <= a pow 2 + b pow 2` ASSUME_TAC THENL
         [MP_TAC(SPEC `abs a - abs b` REAL_LE_POW_2) THEN
          MP_TAC(SPEC `a:real` REAL_POW2_ABS) THEN MP_TAC(SPEC `b:real` REAL_POW2_ABS) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `abs(&2 * b * dd) <= L * (&2 * abs a * abs b)` ASSUME_TAC THENL
         [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * abs b * (L * abs a)` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
            REAL_ARITH_TAC];
          ALL_TAC] THEN
        SUBGOAL_THEN `L * (&2 * abs a * abs b) <= L * (a pow 2 + b pow 2)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `abs(&2 * a * b) = &2 * abs a * abs b` ASSUME_TAC THENL
         [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "q" THEN BETA_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "q" THEN
  BETA_TAC THEN
  MP_TAC(SPEC `(u':real->real) r - v' r` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `(u:real->real) r - v r` REAL_LE_POW_2) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `((u:real->real) r - v r) pow 2 = &0` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN REAL_ARITH_TAC]);;

