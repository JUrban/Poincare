(* ========================================================================= *)
(* pc_p2a_gtail: the Gaussian tail, leaf L10 P2A_GAUSS_TAIL_STATEMENT (MT    *)
(* Lemma 8.9, pure analysis).  The integral of 8 exp(-|Z|^2) over            *)
(* |Z| >= R in real^3 is bounded on balls by dyadic shells (measure of a     *)
(* ball <= (2 r)^3) and extended by monotone convergence; it is at most      *)
(* 1024 R^3 exp(-R^2) for R^2 >= 4, which is below eps^(3/2) for             *)
(* R^2 = 1/(64 eps) and eps small.                                           *)
(* The first part: arithmetic.                                               *)
(* ========================================================================= *)

needs "src/pc_p2a_defs.ml";;

prioritize_real();;
type_invention_error := true;;

let P2AG_EXP_QUARTIC = prove
 (`!x. &0 <= x ==> (x / &4) pow 4 <= exp x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `exp x = exp(x / &4) pow 4` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x / &4` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC);;

let P2AG_POW4_GE = prove
 (`!j. &j + &1 <= &4 pow j`,
  INDUCT_TAC THEN REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
  ASM_REAL_ARITH_TAC);;

let P2AG_SHELL_INDEX = prove
 (`!R t. &0 < R /\ R pow 2 <= t
         ==> ?j. &4 pow j * R pow 2 <= t /\ t < &4 pow (j + 1) * R pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < R pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. t < &4 pow n * R pow 2` MP_TAC THENL
   [MP_TAC(SPECL [`&4`; `t / R pow 2`] REAL_ARCH_POW) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `t < &4 pow 0 * R pow 2` THEN REWRITE_TAC[real_pow] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `n - 1` THEN
  SUBGOAL_THEN `n - 1 + 1 = n` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  USE_THEN "min" (MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* One dyadic shell: 8 exp(-4^j R^2) (2 2^(j+1) R)^3 <= 512 R^3 exp(-R^2) / 2^j. *)

let P2AG_SHELL_TERM = prove
 (`!R j. &2 <= R
         ==> &8 * exp(--(&4 pow j * R pow 2)) * (&2 * &2 pow (j + 1) * R) pow 3 <=
             &512 * R pow 3 * exp(--(R pow 2)) * inv(&2) pow j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&2 pow j) pow 3 = &8 pow j` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_POW] THEN
    SUBGOAL_THEN `&8 = &2 pow 3` SUBST1_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * &2 pow (j + 1) * R) pow 3 = &64 * (&8 pow j) * R pow 3`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_MUL] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 pow j = &16 pow j * inv(&2) pow j` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&4 pow j * R pow 2)) * &16 pow j <= exp(--(R pow 2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(&4 pow j * R pow 2)) * exp(&j * &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_N] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `exp(&4) = exp(&1) pow 4` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&16 = &2 pow 4` SUBST1_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE] THEN
      MP_TAC(SPEC `j:num` P2AG_POW4_GE) THEN
      SUBGOAL_THEN `&4 <= R pow 2` MP_TAC THENL
       [SUBGOAL_THEN `&4 = &2 pow 2` SUBST1_TAC THENL
         [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SPEC_TAC(`R pow 2`,`q:real`) THEN SPEC_TAC(`&4 pow j`,`p:real`) THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(&j + &1) * q <= p * q /\ &j * &4 <= &j * q` MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
        REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= R pow 3 /\ &0 <= inv(&2) pow j` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&8 * exp(--(&4 pow j * R pow 2)) * &64 * (&16 pow j * inv(&2) pow j) * R pow 3 =
    &512 * R pow 3 * (exp(--(&4 pow j * R pow 2)) * &16 pow j) * inv(&2) pow j`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The dyadic-shell majorant on balls and its integral.                      *)
(* ------------------------------------------------------------------------- *)

let P2AG_SHELL_SUM = prove
 (`!R k. &2 <= R
         ==> sum (0..k) (\j. &8 * exp(--(&4 pow j * R pow 2)) *
                             (&2 * &2 pow (j + 1) * R) pow 3) <=
             &1024 * R pow 3 * exp(--(R pow 2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (0..k) (\j. (&512 * R pow 3 * exp(--(R pow 2))) * inv(&2) pow j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC P2AG_SHELL_TERM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_GP; LT] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ABBREV_TAC `X = &512 * R pow 3 * exp(--(R pow 2))` THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 / &2) pow SUC k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1024 * R pow 3 * exp(--(R pow 2)) = &2 * X` SUBST1_TAC THENL
   [EXPAND_TAC "X" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 / &2`] THEN
  SUBGOAL_THEN `&0 <= X * (&1 / &2) pow SUC k` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

let P2AG_POW2_GE = prove
 (`!j. &j + &1 <= &2 pow j`,
  INDUCT_TAC THEN REWRITE_TAC[real_pow; GSYM REAL_OF_NUM_SUC] THEN
  ASM_REAL_ARITH_TAC);;

(* The majorant on balls.                                                    *)

let P2AG_MAJORANT_POINT = prove
 (`!R k (Z:real^3).
     &2 <= R /\ R pow 2 <= Z dot Z /\ Z IN cball(vec 0,&k)
     ==> &8 * exp(--(Z dot Z)) <=
         sum (0..k) (\j. if Z IN cball(vec 0,&2 pow (j + 1) * R)
                         then &8 * exp(--(&4 pow j * R pow 2)) else &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`R:real`; `(Z:real^3) dot Z`] P2AG_SHELL_INDEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Z:real^3) dot Z <= &k pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `(Z:real^3) IN cball(vec 0,&k)` THEN
    REWRITE_TAC[IN_CBALL; DIST_0; GSYM NORM_POW_2] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 pow j = (&2 pow j) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_POW] THEN
    SUBGOAL_THEN `&4 = &2 pow 2` SUBST1_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `j IN 0..k` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG; LE_0] THEN
    SUBGOAL_THEN `&2 * (&j + &1) <= &k` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
      REWRITE_TAC[ARITH_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Z:real^3) dot Z` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&4 pow j * R pow 2` THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 2 * (&2 pow j) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[P2AG_POW2_GE] THEN REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {j} (\j. if (Z:real^3) IN cball(vec 0,&2 pow (j + 1) * R)
                           then &8 * exp(--(&4 pow j * R pow 2)) else &0)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_SING] THEN
    SUBGOAL_THEN `(Z:real^3) IN cball(vec 0,&2 pow (j + 1) * R)` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[IN_CBALL; DIST_0] THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN
      EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ; NORM_POW_2] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      UNDISCH_TAC `(Z:real^3) dot Z < &4 pow (j + 1) * R pow 2` THEN
      SUBGOAL_THEN `&4 pow (j + 1) = (&2 pow (j + 1)) pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_POW] THEN
        SUBGOAL_THEN `&4 = &2 pow 2` SUBST1_TAC THENL
         [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[REAL_POW_MUL]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&8 * x <= &8 * y <=> x <= y`; REAL_EXP_MONO_LE] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Integrals.  The majorant has integral at most 1024 R^3 exp(-R^2); hence   *)
(* so has 8 exp(-|Z|^2) on |Z| >= R inside every ball, and by monotone       *)
(* convergence on |Z| >= R.                                                  *)
(* ------------------------------------------------------------------------- *)

let P2AG_MAJORANT_INTEGRAL = prove
 (`!R k. &2 <= R
         ==> (\Z:real^3. lift(sum (0..k) (\j. if Z IN cball(vec 0,&2 pow (j + 1) * R)
                                               then &8 * exp(--(&4 pow j * R pow 2))
                                               else &0)))
             integrable_on (:real^3) /\
             drop(integral (:real^3)
                    (\Z:real^3. lift(sum (0..k) (\j. if Z IN cball(vec 0,&2 pow (j + 1) * R)
                                                      then &8 * exp(--(&4 pow j * R pow 2))
                                                      else &0)))) <=
             &1024 * R pow 3 * exp(--(R pow 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!j. ((\Z:real^3. lift(if Z IN cball(vec 0,&2 pow (j + 1) * R)
                          then &8 * exp(--(&4 pow j * R pow 2)) else &0)) has_integral
         lift((&8 * exp(--(&4 pow j * R pow 2))) *
              measure(cball(vec 0:real^3,&2 pow (j + 1) * R)))) (:real^3)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[COND_RAND; LIFT_NUM] THEN
    REWRITE_TAC[HAS_INTEGRAL_RESTRICT_UNIV] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `&2 pow (j + 1) * R`] MEASURABLE_CBALL) THEN
    REWRITE_TAC[HAS_MEASURE_MEASURE; has_measure] THEN
    DISCH_THEN(MP_TAC o SPEC `&8 * exp(--(&4 pow j * R pow 2))` o
      MATCH_MP HAS_INTEGRAL_CMUL) THEN
    REWRITE_TAC[GSYM LIFT_EQ_CMUL; GSYM LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\Z:real^3. lift(sum (0..k) (\j. if Z IN cball(vec 0,&2 pow (j + 1) * R)
                                      then &8 * exp(--(&4 pow j * R pow 2)) else &0)))
     has_integral
     lift(sum (0..k) (\j. (&8 * exp(--(&4 pow j * R pow 2))) *
                          measure(cball(vec 0:real^3,&2 pow (j + 1) * R))))) (:real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HAS_INTEGRAL_INTEGRABLE]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (0..k) (\j. &8 * exp(--(&4 pow j * R pow 2)) *
                              (&2 * &2 pow (j + 1) * R) pow 3)` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC P2AG_SHELL_SUM THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `&2 pow (j + 1) * R`] MEASURE_CBALL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let P2AG_CONT = prove
 (`(\Z:real^3. lift(&8 * exp(--(Z dot Z)))) continuous_on (:real^3)`,
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `Z0:real^3` THEN
  DISCH_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_CMUL THEN
  SUBGOAL_THEN `(\Z:real^3. lift(exp(--(Z dot Z)))) =
                (lift o exp o drop) o (\Z. --(lift(Z dot Z)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; DROP_NEG; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_NEG THEN MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN
    REWRITE_TAC[CONTINUOUS_AT_ID];
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL; REAL_CONTINUOUS_AT_EXP]]);;

let P2AG_BALL_BOUND = prove
 (`!R k. &2 <= R
         ==> (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) integrable_on
             ({Z | R pow 2 <= Z dot Z} INTER cball(vec 0,&k)) /\
             drop(integral ({Z | R pow 2 <= Z dot Z} INTER cball(vec 0,&k))
                    (\Z:real^3. lift(&8 * exp(--(Z dot Z))))) <=
             &1024 * R pow 3 * exp(--(R pow 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `closed {Z:real^3 | R pow 2 <= Z dot Z}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{Z:real^3 | R pow 2 <= Z dot Z} =
                  {Z | (\Z. lift(Z dot Z)) Z IN {y | R pow 2 <= drop y}}`
    SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
    REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_LIFT_DOT2 THEN REWRITE_TAC[CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\Z:real^3. lift(&8 * exp(--(Z dot Z)))) integrable_on
                ({Z | R pow 2 <= Z dot Z} INTER cball(vec 0,&k))` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPEC `cball(vec 0:real^3,&k)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC[BOUNDED_CBALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` ASSUME_TAC)) THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `interval[a:real^3,b]` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[P2AG_CONT; SUBSET_UNIV];
      ASM SET_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED THEN
      MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[CLOSED_CBALL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`R:real`; `k:num`] P2AG_MAJORANT_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^3)
                (\Z:real^3. lift(sum (0..k) (\j. if Z IN cball(vec 0,&2 pow (j + 1) * R)
                                                  then &8 * exp(--(&4 pow j * R pow 2))
                                                  else &0))))` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
  X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_ELIM_THM]) THEN
    REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC P2AG_MAJORANT_POINT THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Monotone convergence over balls, and L10.                                 *)
(* ------------------------------------------------------------------------- *)

let P2AG_TAIL_BOUND = prove
 (`!R. &2 <= R
       ==> (\Z:real^3. lift(&8 * exp(--(Z dot Z)))) absolutely_integrable_on
           {Z | R pow 2 <= Z dot Z} /\
           drop(integral {Z | R pow 2 <= Z dot Z}
                  (\Z:real^3. lift(&8 * exp(--(Z dot Z))))) <=
           &1024 * R pow 3 * exp(--(R pow 2))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. (\Z:real^3. if Z IN cball(vec 0,&k) then lift(&8 * exp(--(Z dot Z))) else vec 0)
        integrable_on {Z | R pow 2 <= Z dot Z} /\
        &0 <= drop(integral {Z | R pow 2 <= Z dot Z}
                     (\Z:real^3. if Z IN cball(vec 0,&k)
                                 then lift(&8 * exp(--(Z dot Z))) else vec 0)) /\
        drop(integral {Z | R pow 2 <= Z dot Z}
               (\Z:real^3. if Z IN cball(vec 0,&k)
                           then lift(&8 * exp(--(Z dot Z))) else vec 0)) <=
        &1024 * R pow 3 * exp(--(R pow 2))`
  (LABEL_TAC "K") THENL
   [GEN_TAC THEN REWRITE_TAC[INTEGRABLE_RESTRICT_INTER; INTEGRAL_RESTRICT_INTER] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MP_TAC(SPECL [`R:real`; `k:num`] P2AG_BALL_BOUND) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k:num Z:real^3. if Z IN cball(vec 0,&k)
                                     then lift(&8 * exp(--(Z dot Z))) else vec 0`;
                 `\Z:real^3. lift(&8 * exp(--(Z dot Z)))`;
                 `{Z:real^3 | R pow 2 <= Z dot Z}`] MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "K" (fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`k:num`; `Z:real^3`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= &8 * exp(--((Z:real^3) dot Z))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP; REAL_LE_REFL] THEN
      UNDISCH_TAC `(Z:real^3) IN cball(vec 0,&k)` THEN
      UNDISCH_TAC `~((Z:real^3) IN cball(vec 0,&(SUC k)))` THEN
      REWRITE_TAC[IN_CBALL_0; GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
      X_GEN_TAC `Z:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      MP_TAC(SPEC `norm(Z:real^3)` REAL_ARCH_SIMPLE) THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_CBALL_0] THEN
      SUBGOAL_THEN `norm(Z:real^3) <= &n` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `&1024 * R pow 3 * exp(--(R pow 2)) + &1` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&0 <= &1024 * R pow 3 * exp(--(R pow 2))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
          MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        X_GEN_TAC `k:num` THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
        USE_THEN "K" (MP_TAC o SPEC `k:num`) THEN
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN
        MATCH_ACCEPT_TAC(REAL_ARITH `!d b. &0 <= d /\ d <= b ==> abs d <= b + &1`)]];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN ASM_REWRITE_TAC[DIMINDEX_1] THEN
    REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM drop; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_UBOUND) THEN
    EXISTS_TAC `\k. integral {Z:real^3 | R pow 2 <= Z dot Z}
                      (\Z. if Z IN cball(vec 0,&k)
                           then lift(&8 * exp(--(Z dot Z))) else vec 0)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `k:num` THEN
    USE_THEN "K" (MP_TAC o SPEC `k:num`) THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* L10: with R = 1/(8 sqrt eps), 1024 R^3 exp(-R^2) <= eps^(3/2) once        *)
(* eps <= 1/(2 256^4) (exp x >= (x/4)^4).                                    *)
(* ------------------------------------------------------------------------- *)

let P2AG_GAUSS_TAIL = prove
 (`P2A_GAUSS_TAIL_STATEMENT`,
  REWRITE_TAC[P2A_GAUSS_TAIL_STATEMENT] THEN
  EXISTS_TAC `inv(&8589934592)` THEN CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  X_GEN_TAC `eps:real` THEN STRIP_TAC THEN
  ABBREV_TAC `u = sqrt eps` THEN
  SUBGOAL_THEN `&0 < u /\ u pow 2 = eps` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&8589934592 * u pow 2 <= &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `eps <= inv(&8589934592)` THEN
    SIMP_TAC[REAL_ARITH `inv(&8589934592) = &1 / &8589934592`; REAL_LE_RDIV_EQ;
             REAL_ARITH `&0 < &8589934592`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= &1 / &16` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&1 / &16) pow 2 < u pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&8 * u) pow 2 = &1 / (&64 * eps)` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN UNDISCH_TAC `&0 < u` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `{Z:real^3 | &1 <= &64 * eps * (Z dot Z)} =
                {Z | inv(&8 * u) pow 2 <= Z dot Z}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `Z:real^3` THEN
    SUBGOAL_THEN `&0 < &64 * eps` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `inv(&8 * u)` P2AG_TAIL_BOUND) THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
    SUBGOAL_THEN `&0 < &8 * u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1024 * inv(&8 * u) pow 3 * exp(--(inv(&8 * u) pow 2))` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    concl th = `inv(&8 * u) pow 2 = &1 / (&64 * eps)`)) THEN
  ABBREV_TAC `x = &1 / (&64 * eps)` THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--x) <= (&256 * u pow 2) pow 4` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (x / &4) pow 4` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `exp(--x) * (x / &4) pow 4 <= (&256 * u pow 2) pow 4 * (x / &4) pow 4`
    MP_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LE_RMUL_EQ]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--x) * exp x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC P2AG_EXP_QUARTIC THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_EXP_NEG_MUL] THEN
      SUBGOAL_THEN `(x / &4) pow 4 * (&256 * u pow 2) pow 4 = &1` (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
      EXPAND_TAC "x" THEN EXPAND_TAC "eps" THEN UNDISCH_TAC `&0 < u` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1024 * inv(&8 * u) pow 3 * (&256 * u pow 2) pow 4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1024 * inv(&8 * u) pow 3 * (&256 * u pow 2) pow 4 =
                u pow 3 * (&8589934592 * u pow 2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < u` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `eps * u = u pow 3 * &1` SUBST1_TAC THENL
   [EXPAND_TAC "eps" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC);;

