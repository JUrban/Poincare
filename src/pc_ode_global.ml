(* ========================================================================= *)
(* pc_ode_global: uniform existence time, the extension criterion, global   *)
(* existence (confinement, linear growth, linear systems, compact support),  *)
(* restriction to open subsets, parametric fields, scalar comparison.        *)
(* ========================================================================= *)

needs "src/pc_ode_found.ml";;

prioritize_real();;
type_invention_error := true;;

let ODE_DOMAIN_UNIFORM_TIME = prove
 (`!(f:real^(1,N)finite_sum->real^N) D K.
    open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\
    compact K /\ K SUBSET D
    ==> ?e. &0 < e /\
            !z t. z IN K /\ abs(drop t - drop(fstcart z)) <= e
                  ==> t IN ode_maxint f D z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K:real^(1,N)finite_sum->bool`] ODE_LOCAL_EXISTENCE_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^(1,N)finite_sum`; `t:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`;
                 `interval[fstcart(z:real^(1,N)finite_sum) - lift e,fstcart z + lift e]`;
                 `u:real^1->real^N`] ODE_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[SUBSET] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `abs(drop t - drop(fstcart(z:real^(1,N)finite_sum))) <= e` THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* A point of the trajectory lying in K extends the maximal interval by the  *)
(* uniform existence time for K.                                             *)

let ODE_MAXINT_EXTEND_COMPACT = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z K e t.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\ z IN D /\
        &0 < e /\
        (!w. w IN K
             ==> ?u. u(fstcart w) = sndcart w /\
                     ode_solution f D
                       (interval[fstcart w - lift e,fstcart w + lift e]) u) /\
        t IN ode_maxint f D z /\ pastecart t (ode_flow f D t z) IN K
        ==> interval[t - lift e,t + lift e] SUBSET ode_maxint f D z`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t z)`) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `I1 = interval[t - lift e,t + lift e]` THEN
  SUBGOAL_THEN `(t:real^1) IN I1` ASSUME_TAC THENL
   [EXPAND_TAC "I1" THEN REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `ode_maxint (f:real^(1,N)finite_sum->real^N) D z`; `I1:real^1->bool`;
                 `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z`;
                 `v:real^1->real^N`; `t:real^1`] ODE_SOLUTION_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `ode_maxint (f:real^(1,N)finite_sum->real^N) D z`; `I1:real^1->bool`;
                 `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z`;
                 `v:real^1->real^N`] ODE_SOLUTION_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`;
                 `ode_maxint (f:real^(1,N)finite_sum->real^N) D z UNION I1`;
                 `\s. if s IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z
                      then (\t. ode_flow f D t z) s else (v:real^1->real^N) s`]
         ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ODE_MAXINT_INITIAL; IN_UNION];
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN SET_TAC[]]);;

let ODE_MAXINT_LEAVES_COMPACT = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z K.
    open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\ z IN D /\
    compact K /\ K SUBSET D
    ==> (?t1. t1 IN ode_maxint f D z /\
              !t. t IN ode_maxint f D z /\ drop t1 <= drop t
                  ==> ~(pastecart t (ode_flow f D t z) IN K)) /\
        (?t1. t1 IN ode_maxint f D z /\
              !t. t IN ode_maxint f D z /\ drop t <= drop t1
                  ==> ~(pastecart t (ode_flow f D t z) IN K))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K:real^(1,N)finite_sum->bool`] ODE_LOCAL_EXISTENCE_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t z) IN K
        ==> abs(drop t) <= B`
  (LABEL_TAC "bd") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t z))` THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPEC `pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t z)`
           NORM_FSTCART) THEN
    REWRITE_TAC[FSTCART_PASTECART; NORM_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fstcart(z:real^(1,N)finite_sum) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
  ASSUME_TAC THENL [ASM_SIMP_TAC[ODE_MAXINT_INITIAL]; ALL_TAC] THEN
  SUBGOAL_THEN `is_interval(ode_maxint (f:real^(1,N)finite_sum->real^N) D z)`
  ASSUME_TAC THENL [REWRITE_TAC[ODE_MAXINT_IS_INTERVAL]; ALL_TAC] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(LABEL_TAC "neg") THENL
   [SUBGOAL_THEN
     `!n. fstcart(z:real^(1,N)finite_sum) + lift(&n * e) IN
          ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
    ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_LZERO; LIFT_NUM; VECTOR_ADD_RID]; ALL_TAC] THEN
      USE_THEN "neg" (MP_TAC o SPEC
        `fstcart(z:real^(1,N)finite_sum) + lift(&n * e)`) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; ASSUME
        `fstcart(z:real^(1,N)finite_sum) + lift(&n * e) IN
         ode_maxint (f:real^(1,N)finite_sum->real^N) D z`] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                     `z:real^(1,N)finite_sum`; `K:real^(1,N)finite_sum->bool`;
                     `e:real`; `t:real^1`] ODE_MAXINT_EXTEND_COMPACT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
      MAP_EVERY EXISTS_TAC
       [`fstcart(z:real^(1,N)finite_sum) + lift(&n * e)`; `t + lift e`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
        UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
        DISJ1_TAC THEN
        UNDISCH_TAC `drop(fstcart(z:real^(1,N)finite_sum) + lift(&n * e)) <= drop t` THEN
        UNDISCH_TAC `&0 < e` THEN
        REWRITE_TAC[DROP_ADD; LIFT_DROP; GSYM REAL_OF_NUM_SUC] THEN
        REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPEC `e:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num` o SPEC `B - drop(fstcart(z:real^(1,N)finite_sum))`) THEN
    USE_THEN "neg" (MP_TAC o SPEC
      `fstcart(z:real^(1,N)finite_sum) + lift(&n * e)`) THEN
    REWRITE_TAC[ASSUME
      `!n. fstcart(z:real^(1,N)finite_sum) + lift(&n * e) IN
           ode_maxint (f:real^(1,N)finite_sum->real^N) D z`] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME
      `pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t z) IN K`)) THEN
    UNDISCH_TAC `drop(fstcart(z:real^(1,N)finite_sum) + lift(&n * e)) <= drop t` THEN
    UNDISCH_TAC `B - drop(fstcart(z:real^(1,N)finite_sum)) < &n * e` THEN
    REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `!n. fstcart(z:real^(1,N)finite_sum) - lift(&n * e) IN
          ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
    ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_LZERO; LIFT_NUM; VECTOR_SUB_RZERO]; ALL_TAC] THEN
      USE_THEN "neg" (MP_TAC o SPEC
        `fstcart(z:real^(1,N)finite_sum) - lift(&n * e)`) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; ASSUME
        `fstcart(z:real^(1,N)finite_sum) - lift(&n * e) IN
         ode_maxint (f:real^(1,N)finite_sum->real^N) D z`] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                     `z:real^(1,N)finite_sum`; `K:real^(1,N)finite_sum->bool`;
                     `e:real`; `t:real^1`] ODE_MAXINT_EXTEND_COMPACT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
      MAP_EVERY EXISTS_TAC
       [`fstcart(z:real^(1,N)finite_sum) - lift(&n * e)`; `t - lift e`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
        UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
        DISJ2_TAC THEN
        UNDISCH_TAC `drop t <= drop(fstcart(z:real^(1,N)finite_sum) - lift(&n * e))` THEN
        UNDISCH_TAC `&0 < e` THEN
        REWRITE_TAC[DROP_SUB; LIFT_DROP; GSYM REAL_OF_NUM_SUC] THEN
        REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPEC `e:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num` o SPEC `B + drop(fstcart(z:real^(1,N)finite_sum))`) THEN
    USE_THEN "neg" (MP_TAC o SPEC
      `fstcart(z:real^(1,N)finite_sum) - lift(&n * e)`) THEN
    REWRITE_TAC[ASSUME
      `!n. fstcart(z:real^(1,N)finite_sum) - lift(&n * e) IN
           ode_maxint (f:real^(1,N)finite_sum->real^N) D z`] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME
      `pastecart t (ode_flow (f:real^(1,N)finite_sum->real^N) D t z) IN K`)) THEN
    UNDISCH_TAC `drop t <= drop(fstcart(z:real^(1,N)finite_sum) - lift(&n * e))` THEN
    UNDISCH_TAC `B + drop(fstcart(z:real^(1,N)finite_sum)) < &n * e` THEN
    REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Global existence on product domains J PCROSS U.                           *)
(* ------------------------------------------------------------------------- *)

let ODE_MAXINT_REACH_FORWARD = prove
 (`!(f:real^(1,N)finite_sum->real^N) J U z C t.
        open J /\ is_interval J /\ open U /\
        f continuous_on (J PCROSS U) /\ ode_locally_lipschitz f (J PCROSS U) /\
        z IN J PCROSS U /\ compact C /\ C SUBSET U /\ t IN J /\
        drop(fstcart z) <= drop t /\
        (!s. s IN ode_maxint f (J PCROSS U) z /\ drop(fstcart z) <= drop s /\
             drop s <= drop t ==> ode_flow f (J PCROSS U) s z IN C)
        ==> t IN ode_maxint f (J PCROSS U) z`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(1,N)finite_sum) IN J PCROSS U` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fstcart(z:real^(1,N)finite_sum) IN
    ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z`
  ASSUME_TAC THENL [ASM_SIMP_TAC[ODE_MAXINT_INITIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `(J:real^1->bool) PCROSS (U:real^N->bool)`;
                 `z:real^(1,N)finite_sum`;
                 `interval[fstcart(z:real^(1,N)finite_sum),t] PCROSS (C:real^N->bool)`]
         ODE_MAXINT_LEAVES_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
    MAP_EVERY EXISTS_TAC [`fstcart(z:real^(1,N)finite_sum)`; `t:real^1`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t1:real^1`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leave")) o CONJUNCT1)] THEN
  SUBGOAL_THEN
   `!s. s IN ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z
        ==> drop s < drop t`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(t IN ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
    MAP_EVERY EXISTS_TAC [`fstcart(z:real^(1,N)finite_sum)`; `s:real^1`] THEN
    ASM_REWRITE_TAC[ODE_MAXINT_IS_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. s IN ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z /\
        drop(fstcart z) <= drop s /\ drop t1 <= drop s`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `drop t1 <= drop(fstcart(z:real^(1,N)finite_sum))` THENL
     [EXISTS_TAC `fstcart(z:real^(1,N)finite_sum)`; EXISTS_TAC `t1:real^1`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `drop s <= drop t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ode_flow (f:real^(1,N)finite_sum->real^N) (J PCROSS U) s z IN C`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "leave" (MP_TAC o SPEC `s:real^1`) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1]);;

let ODE_MAXINT_REACH_BACKWARD = prove
 (`!(f:real^(1,N)finite_sum->real^N) J U z C t.
        open J /\ is_interval J /\ open U /\
        f continuous_on (J PCROSS U) /\ ode_locally_lipschitz f (J PCROSS U) /\
        z IN J PCROSS U /\ compact C /\ C SUBSET U /\ t IN J /\
        drop t <= drop(fstcart z) /\
        (!s. s IN ode_maxint f (J PCROSS U) z /\ drop t <= drop s /\
             drop s <= drop(fstcart z) ==> ode_flow f (J PCROSS U) s z IN C)
        ==> t IN ode_maxint f (J PCROSS U) z`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(1,N)finite_sum) IN J PCROSS U` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `fstcart(z:real^(1,N)finite_sum) IN
    ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z`
  ASSUME_TAC THENL [ASM_SIMP_TAC[ODE_MAXINT_INITIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `(J:real^1->bool) PCROSS (U:real^N->bool)`;
                 `z:real^(1,N)finite_sum`;
                 `interval[t,fstcart(z:real^(1,N)finite_sum)] PCROSS (C:real^N->bool)`]
         ODE_MAXINT_LEAVES_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
    MAP_EVERY EXISTS_TAC [`t:real^1`; `fstcart(z:real^(1,N)finite_sum)`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t1:real^1`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "leave")) o CONJUNCT2)] THEN
  SUBGOAL_THEN
   `!s. s IN ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z
        ==> drop t < drop s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC I [GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(t IN ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
    MAP_EVERY EXISTS_TAC [`s:real^1`; `fstcart(z:real^(1,N)finite_sum)`] THEN
    ASM_REWRITE_TAC[ODE_MAXINT_IS_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?s. s IN ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z /\
        drop s <= drop(fstcart z) /\ drop s <= drop t1`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `drop(fstcart(z:real^(1,N)finite_sum)) <= drop t1` THENL
     [EXISTS_TAC `fstcart(z:real^(1,N)finite_sum)`; EXISTS_TAC `t1:real^1`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `drop t <= drop s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ode_flow (f:real^(1,N)finite_sum->real^N) (J PCROSS U) s z IN C`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "leave" (MP_TAC o SPEC `s:real^1`) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1]);;

let ODE_MAXINT_CONFINED_FORWARD = prove
 (`!(f:real^(1,N)finite_sum->real^N) J U z C.
    open J /\ is_interval J /\ open U /\
    f continuous_on (J PCROSS U) /\ ode_locally_lipschitz f (J PCROSS U) /\
    z IN J PCROSS U /\ compact C /\ C SUBSET U /\
    (!t. t IN ode_maxint f (J PCROSS U) z /\ drop(fstcart z) <= drop t
         ==> ode_flow f (J PCROSS U) t z IN C)
    ==> !t. t IN J /\ drop(fstcart z) <= drop t
            ==> t IN ode_maxint f (J PCROSS U) z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ODE_MAXINT_REACH_FORWARD THEN
  EXISTS_TAC `C:real^N->bool` THEN ASM_SIMP_TAC[]);;

let ODE_MAXINT_SUBSET_TIMES = prove
 (`!(f:real^(1,N)finite_sum->real^N) J U z.
        ode_maxint f (J PCROSS U) z SUBSET J`,
  REWRITE_TAC[SUBSET; ODE_IN_MAXINT; ode_solution] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
  ASM_SIMP_TAC[PASTECART_IN_PCROSS]);;

let ODE_MAXINT_CONFINED = prove
 (`!(f:real^(1,N)finite_sum->real^N) J U z C.
    open J /\ is_interval J /\ open U /\
    f continuous_on (J PCROSS U) /\ ode_locally_lipschitz f (J PCROSS U) /\
    z IN J PCROSS U /\ compact C /\ C SUBSET U /\
    (!t. t IN ode_maxint f (J PCROSS U) z
         ==> ode_flow f (J PCROSS U) t z IN C)
    ==> ode_maxint f (J PCROSS U) z = J`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; ODE_MAXINT_SUBSET_TIMES] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH
   `drop(fstcart(z:real^(1,N)finite_sum)) <= drop t \/
    drop t <= drop(fstcart z)`) THENL
   [MATCH_MP_TAC ODE_MAXINT_REACH_FORWARD;
    MATCH_MP_TAC ODE_MAXINT_REACH_BACKWARD] THEN
  EXISTS_TAC `C:real^N->bool` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linear growth and linear systems.                                         *)
(* ------------------------------------------------------------------------- *)

let ODE_LINEAR_GROWTH_BOUND = prove
 (`!(f:real^(1,N)finite_sum->real^N) J z a b A B.
        open J /\ is_interval J /\
        f continuous_on (J PCROSS (:real^N)) /\
        ode_locally_lipschitz f (J PCROSS (:real^N)) /\
        z IN J PCROSS (:real^N) /\ fstcart z IN interval[a,b] /\
        interval[a,b] SUBSET J /\ &0 <= A /\ &0 <= B /\
        (!t x. t IN interval[a,b] ==> norm(f(pastecart t x)) <= A + B * norm x)
        ==> ?R. !s. s IN ode_maxint f (J PCROSS (:real^N)) z INTER interval[a,b]
                    ==> norm(ode_flow f (J PCROSS (:real^N)) s z) <= R`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = (J:real^1->bool) PCROSS (:real^N)` THEN
  SUBGOAL_THEN `open(D:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `M = ode_maxint (f:real^(1,N)finite_sum->real^N) D z` THEN
  ABBREV_TAC `P = \s. ode_flow (f:real^(1,N)finite_sum->real^N) D s z` THEN
  SUBGOAL_THEN `!s. ode_flow (f:real^(1,N)finite_sum->real^N) D s z = P s`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `c = A + &2 * B` THEN
  MP_TAC(ISPECL
   [`\s. &1 + (P:real^1->real^N) s dot P s`;
    `\s. &2 * ((P:real^1->real^N) s dot (f:real^(1,N)finite_sum->real^N)(pastecart s (P s)))`;
    `c:real`; `M INTER interval[a:real^1,b]`;
    `fstcart(z:real^(1,N)finite_sum)`] ODE_GRONWALL_DERIV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IS_INTERVAL_INTER THEN ASM_REWRITE_TAC[IS_INTERVAL_INTERVAL];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      SUBGOAL_THEN
       `((\s. lift(&1 + (P:real^1->real^N) s dot P s)) has_vector_derivative
         (vec 0 + (lift(P s dot f(pastecart s (P s))) +
                   lift((f:real^(1,N)finite_sum->real^N)(pastecart s (P s)) dot P s))))
        (at s)`
      MP_TAC THENL
       [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
        REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
        MP_TAC(ISPECL
         [`\x y:real^N. lift(x dot y)`; `P:real^1->real^N`; `P:real^1->real^N`;
          `(f:real^(1,N)finite_sum->real^N)(pastecart s (P s))`;
          `(f:real^(1,N)finite_sum->real^N)(pastecart s (P s))`; `s:real^1`]
         HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
        REWRITE_TAC[BILINEAR_DOT; ETA_AX] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[VECTOR_ADD_LID; GSYM LIFT_ADD; LIFT_EQ] THEN
        REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `pastecart (s:real^1) ((P:real^1->real^N) s) IN D` ASSUME_TAC
    THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `p = norm((P:real^1->real^N) s)` THEN
    ABBREV_TAC `q = norm((f:real^(1,N)finite_sum->real^N)(pastecart s (P s)))` THEN
    SUBGOAL_THEN `&0 <= p /\ q <= A + B * p` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN ASM_SIMP_TAC[NORM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(&2 * ((P:real^1->real^N) s dot
                (f:real^(1,N)finite_sum->real^N)(pastecart s (P s))))
      <= &2 * (p * q)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MAP_EVERY EXPAND_TAC ["p"; "q"] THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS];
      ALL_TAC] THEN
    SUBGOAL_THEN `p * q <= p * (A + B * p)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(P:real^1->real^N) s dot P s = p pow 2` SUBST1_TAC THENL
     [EXPAND_TAC "p" THEN REWRITE_TAC[NORM_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= A * (p - &1) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN
     `c * (&1 + p pow 2) - &2 * (p * (A + B * p)) =
      A * (p - &1) pow 2 + &2 * B`
    MP_TAC THENL [EXPAND_TAC "c" THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    UNDISCH_TAC `&0 <= B` THEN
    UNDISCH_TAC `abs(&2 * ((P:real^1->real^N) s dot
                (f:real^(1,N)finite_sum->real^N)(pastecart s (P s))))
                 <= &2 * (p * q)` THEN
    UNDISCH_TAC `p * q <= p * (A + B * p)` THEN
    UNDISCH_TAC `&0 <= A * (p - &1) pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(&1 + (P:real^1->real^N)(fstcart(z:real^(1,N)finite_sum)) dot
                     P(fstcart z)) * exp(c * (drop b - drop a))` THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `n <= &1 + d /\ x <= y ==> &1 + d <= x ==> n <= y`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_POW_2] THEN
    MP_TAC(SPEC `norm((P:real^1->real^N) s)` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `norm((P:real^1->real^N) s) - &1` REAL_LE_POW_2) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    REWRITE_TAC[DOT_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `s IN M INTER interval[a:real^1,b]` THEN
  UNDISCH_TAC `fstcart(z:real^(1,N)finite_sum) IN interval[a,b]` THEN
  REWRITE_TAC[IN_INTER; IN_INTERVAL_1] THEN REAL_ARITH_TAC);;

let ODE_LINEAR_GROWTH_INTERVAL = prove
 (`!(f:real^(1,N)finite_sum->real^N) J z a b A B.
        open J /\ is_interval J /\
        f continuous_on (J PCROSS (:real^N)) /\
        ode_locally_lipschitz f (J PCROSS (:real^N)) /\
        z IN J PCROSS (:real^N) /\ fstcart z IN interval[a,b] /\
        interval[a,b] SUBSET J /\ &0 <= A /\ &0 <= B /\
        (!t x. t IN interval[a,b] ==> norm(f(pastecart t x)) <= A + B * norm x)
        ==> interval[a,b] SUBSET ode_maxint f (J PCROSS (:real^N)) z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `J:real^1->bool`;
                 `z:real^(1,N)finite_sum`; `a:real^1`; `b:real^1`;
                 `A:real`; `B:real`] ODE_LINEAR_GROWTH_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R:real` (LABEL_TAC "R")) THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^1) IN J` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH
   `drop(fstcart(z:real^(1,N)finite_sum)) <= drop t \/
    drop t <= drop(fstcart z)`) THENL
   [MATCH_MP_TAC ODE_MAXINT_REACH_FORWARD;
    MATCH_MP_TAC ODE_MAXINT_REACH_BACKWARD] THEN
  EXISTS_TAC `cball(vec 0:real^N,R)` THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; SUBSET_UNIV; OPEN_UNIV; IN_CBALL_0] THEN
  X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  USE_THEN "R" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
  UNDISCH_TAC `fstcart(z:real^(1,N)finite_sum) IN interval[a,b]` THEN
  UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let ODE_MAXINT_LINEAR_GROWTH = prove
 (`!(f:real^(1,N)finite_sum->real^N) J z.
    open J /\ is_interval J /\
    f continuous_on (J PCROSS (:real^N)) /\
    ode_locally_lipschitz f (J PCROSS (:real^N)) /\
    (!C. compact C /\ C SUBSET J
         ==> ?a b. !t x. t IN C ==> norm(f(pastecart t x)) <= a + b * norm x) /\
    z IN J PCROSS (:real^N)
    ==> ode_maxint f (J PCROSS (:real^N)) z = J`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; ODE_MAXINT_SUBSET_TIMES] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN J` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(1,N)finite_sum) IN J PCROSS (:real^N)` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN J /\ b IN J /\ fstcart(z:real^(1,N)finite_sum) IN interval[a,b]
          ==> interval[a,b] SUBSET
              ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS (:real^N)) z`
  (LABEL_TAC "int") THENL
   [MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `interval[a:real^1,b] SUBSET J` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
      MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `interval[a:real^1,b]`) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `a0:real` (X_CHOOSE_TAC `b0:real`)) THEN
    MATCH_MP_TAC ODE_LINEAR_GROWTH_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`abs a0`; `abs b0`] THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `a0 + b0 * norm(x:real^N)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `b * n <= abs b * n ==> a + b * n <= abs a + abs b * n`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH
   `drop(fstcart(z:real^(1,N)finite_sum)) <= drop t \/
    drop t <= drop(fstcart z)`) THENL
   [REMOVE_THEN "int" (MP_TAC o SPECL [`fstcart(z:real^(1,N)finite_sum)`; `t:real^1`]);
    REMOVE_THEN "int" (MP_TAC o SPECL [`t:real^1`; `fstcart(z:real^(1,N)finite_sum)`])] THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL]);;

(* Continuity of maps factoring through the time coordinate. *)

let ODE_CONTINUOUS_ON_FSTCART_COMPOSE = prove
 (`!(h:real^1->real^P) J.
        h continuous_on J
        ==> (\z:real^(1,N)finite_sum. h(fstcart z)) continuous_on
            (J PCROSS (:real^N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (h:real^1->real^P)(fstcart z)) =
                h o fstcart` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `J:real^1->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
  SIMP_TAC[]);;

(* Properties of linear fields (t,x) |-> A t ** x + g t. *)

let ODE_LINEAR_FIELD_PROPS = prove
 (`!(A:real^1->real^N^N) (g:real^1->real^N) J.
        open J /\
        (!i j. (\t. lift(A t$i$j)) continuous_on J) /\ g continuous_on J
        ==> (\z. A(fstcart z) ** sndcart z + g(fstcart z)) continuous_on
            (J PCROSS (:real^N)) /\
            ode_locally_lipschitz (\z. A(fstcart z) ** sndcart z + g(fstcart z))
                                  (J PCROSS (:real^N)) /\
            (!C. compact C /\ C SUBSET J
                 ==> ?a b. !t x. t IN C ==> norm(A t ** x + g t) <= a + b * norm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\t. vectorize((A:real^1->real^N^N) t)) continuous_on J`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_ON_VECTORIZE_COMPONENTWISE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[ODE_CONTINUOUS_ON_FSTCART_COMPOSE] THEN
    ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT] THEN
    MP_TAC(ISPECL
     [`\z:real^(1,N)finite_sum. ((A:real^1->real^N^N)(fstcart z))$k`;
      `sndcart:real^(1,N)finite_sum->real^N`;
      `\x y:real^N. lift(x dot y)`; `(J:real^1->bool) PCROSS (:real^N)`]
     BILINEAR_CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC ODE_CONTINUOUS_ON_FSTCART_COMPOSE THEN
    ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[ode_locally_lipschitz] THEN X_GEN_TAC `z:real^(1,N)finite_sum` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN J` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(1,N)finite_sum) IN J PCROSS (:real^N)` THEN
      ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
      SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `fstcart(z:real^(1,N)finite_sum)` o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\t. vectorize((A:real^1->real^N^N) t)`; `J:real^1->bool`;
                   `cball(fstcart(z:real^(1,N)finite_sum),r)`] ODE_COMPACT_BOUND) THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `L:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`; `y:real^N`] THEN
    REWRITE_TAC[IN_INTER; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    STRIP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(a + c) - (b + c:real^N) = a - b`] THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_SUB_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize((A:real^1->real^N^N) t)) * norm(x - y:real^N)` THEN
    REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `pastecart (t:real^1) (x:real^N) IN ball(z,r)` THEN
    REWRITE_TAC[IN_BALL; IN_CBALL; dist] THEN
    MP_TAC(ISPEC `z - pastecart (t:real^1) (x:real^N)` NORM_FSTCART) THEN
    REWRITE_TAC[FSTCART_SUB; FSTCART_PASTECART] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\t. vectorize((A:real^1->real^N^N) t)`; `J:real^1->bool`;
                   `C:real^1->bool`] ODE_COMPACT_BOUND) THEN
    MP_TAC(ISPECL [`g:real^1->real^N`; `J:real^1->bool`;
                   `C:real^1->bool`] ODE_COMPACT_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Bg:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `Ba:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`Bg:real`; `Ba:real`] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^N) <= p /\ norm(b:real^N) <= q ==> norm(a + b) <= q + p`) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vectorize((A:real^1->real^N^N) t)) * norm(x:real^N)` THEN
    REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE]]);;

let ODE_LINEAR_GLOBAL = prove
 (`!(A:real^1->real^N^N) (g:real^1->real^N) J t0 x0.
    open J /\ is_interval J /\ t0 IN J /\
    (!i j. (\t. lift(A t$i$j)) continuous_on J) /\ g continuous_on J
    ==> ode_maxint (\z. A(fstcart z) ** sndcart z + g(fstcart z))
                   (J PCROSS (:real^N)) (pastecart t0 x0) = J`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^1->real^N^N`; `g:real^1->real^N`; `J:real^1->bool`]
         ODE_LINEAR_FIELD_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC ODE_MAXINT_LINEAR_GROWTH THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; FSTCART_PASTECART;
                  SNDCART_PASTECART]);;

let ODE_LINEAR_INTERVAL = prove
 (`!(A:real^1->real^N^N) (g:real^1->real^N) a b t0 x0.
    t0 IN interval[a,b] /\
    (!i j. (\t. lift(A t$i$j)) continuous_on interval[a,b]) /\
    g continuous_on interval[a,b]
    ==> ?u. u t0 = x0 /\
            (!t. t IN interval[a,b]
                 ==> (u has_vector_derivative (A t ** u t + g t))
                     (at t within interval[a,b])) /\
            (!v. v t0 = x0 /\
                 (!t. t IN interval[a,b]
                      ==> (v has_vector_derivative (A t ** v t + g t))
                          (at t within interval[a,b]))
                 ==> !t. t IN interval[a,b] ==> v t = u t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^1,b] = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `cp = closest_point(interval[a:real^1,b])` THEN
  SUBGOAL_THEN
   `cp continuous_on (:real^1) /\
    (!t. (cp:real^1->real^1) t IN interval[a,b]) /\
    (!t. t IN interval[a,b] ==> (cp:real^1->real^1) t = t)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cp" THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CONVEX_INTERVAL; CLOSED_INTERVAL;
                 CLOSEST_POINT_IN_SET; CLOSEST_POINT_SELF];
    ALL_TAC] THEN
  ABBREV_TAC `A' = \t. (A:real^1->real^N^N)((cp:real^1->real^1) t)` THEN
  ABBREV_TAC `g' = \t. (g:real^1->real^N)((cp:real^1->real^1) t)` THEN
  SUBGOAL_THEN
   `(!i j. (\t. lift((A':real^1->real^N^N) t$i$j)) continuous_on (:real^1)) /\
    (g':real^1->real^N) continuous_on (:real^1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A'"; "g'"] THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      SUBGOAL_THEN
       `(\t. lift((A:real^1->real^N^N)((cp:real^1->real^1) t)$i$j)) =
        (\s. lift(A s$i$j)) o cp`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC];
      SUBGOAL_THEN
       `(\t. (g:real^1->real^N)((cp:real^1->real^1) t)) = g o cp`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,b]` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A':real^1->real^N^N`; `g':real^1->real^N`; `(:real^1)`]
         ODE_LINEAR_FIELD_PROPS) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN STRIP_TAC THEN
  ABBREV_TAC `F' = \z. (A':real^1->real^N^N)(fstcart z) ** sndcart z +
                       (g':real^1->real^N)(fstcart z)` THEN
  SUBGOAL_THEN `open((:real^1) PCROSS (:real^N))` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`F':real^(1,N)finite_sum->real^N`;
                 `(:real^1) PCROSS (:real^N)`;
                 `pastecart (t0:real^1) (x0:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MP_TAC(ISPECL [`A':real^1->real^N^N`; `g':real^1->real^N`; `(:real^1)`;
                 `t0:real^1`; `x0:real^N`] ODE_LINEAR_GLOBAL) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_UNIV; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  EXISTS_TAC `\t. ode_flow (F':real^(1,N)finite_sum->real^N)
                    ((:real^1) PCROSS (:real^N)) t (pastecart t0 x0)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN
    EXPAND_TAC "F'" THEN MAP_EVERY EXPAND_TAC ["A'"; "g'"] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^1->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`F':real^(1,N)finite_sum->real^N`;
                 `(:real^1) PCROSS (:real^N)`;
                 `pastecart (t0:real^1) (x0:real^N)`; `interval[a:real^1,b]`;
                 `v:real^1->real^N`] ODE_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_PCROSS; OPEN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ode_solution; IS_INTERVAL_INTERVAL; PASTECART_IN_PCROSS; IN_UNIV] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    EXPAND_TAC "F'" THEN MAP_EVERY EXPAND_TAC ["A'"; "g'"] THEN
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Compact support, restriction to open subsets, parametric fields.          *)
(* ------------------------------------------------------------------------- *)

let ODE_MAXINT_COMPACT_SUPPORT = prove
 (`!(f:real^(1,N)finite_sum->real^N) J U K z.
    open J /\ is_interval J /\ open U /\
    f continuous_on (J PCROSS U) /\ ode_locally_lipschitz f (J PCROSS U) /\
    compact K /\ K SUBSET U /\
    (!t x. t IN J /\ x IN U /\ ~(x IN K) ==> f(pastecart t x) = vec 0) /\
    z IN J PCROSS U
    ==> ode_maxint f (J PCROSS U) z = J /\
        (sndcart z IN K
         ==> !t. t IN J ==> ode_flow f (J PCROSS U) t z IN K) /\
        (~(sndcart z IN K)
         ==> !t. t IN J ==> ode_flow f (J PCROSS U) t z = sndcart z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open((J:real^1->bool) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN J /\ sndcart z IN U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^(1,N)finite_sum) IN J PCROSS U` THEN
    ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN U /\ ~(y IN K)
        ==> ode_solution (f:real^(1,N)finite_sum->real^N) (J PCROSS U) J (\t. y)`
  (LABEL_TAC "const") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC ODE_SOLUTION_CONST THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `(J:real^1->bool) PCROSS (U:real^N->bool)`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `fstcart(z:real^(1,N)finite_sum) IN
    ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z`
  ASSUME_TAC THENL [ASM_SIMP_TAC[ODE_MAXINT_INITIAL]; ALL_TAC] THEN
  ASM_CASES_TAC `sndcart(z:real^(1,N)finite_sum) IN K` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `!t. t IN ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z
          ==> ode_flow f (J PCROSS U) t z IN K`
    ASSUME_TAC THENL
     [X_GEN_TAC `t1:real^1` THEN DISCH_TAC THEN
      GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `ode_flow (f:real^(1,N)finite_sum->real^N) (J PCROSS U) t1 z IN U /\ t1 IN J`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) (J PCROSS U)
                      (ode_maxint f (J PCROSS U) z) (\t. ode_flow f (J PCROSS U) t z)` THEN
        REWRITE_TAC[ode_solution] THEN
        DISCH_THEN(MP_TAC o SPEC `t1:real^1` o CONJUNCT2) THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN SIMP_TAC[];
        ALL_TAC] THEN
      USE_THEN "const" (MP_TAC o C MATCH_MP (CONJ
        (ASSUME `ode_flow (f:real^(1,N)finite_sum->real^N) (J PCROSS U) t1 z IN U`)
        (ASSUME `~(ode_flow (f:real^(1,N)finite_sum->real^N) (J PCROSS U) t1 z IN K)`))) THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`;
                     `(J:real^1->bool) PCROSS (U:real^N->bool)`;
                     `ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z`;
                     `J:real^1->bool`;
                     `\t. ode_flow (f:real^(1,N)finite_sum->real^N) (J PCROSS U) t z`;
                     `\t:real^1. ode_flow (f:real^(1,N)finite_sum->real^N)
                                   (J PCROSS U) t1 z`;
                     `t1:real^1`] ODE_SOLUTION_UNIQUE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `fstcart(z:real^(1,N)finite_sum)`) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `J:real^1->bool`;
                   `U:real^N->bool`; `z:real^(1,N)finite_sum`; `K:real^N->bool`]
           ODE_MAXINT_CONFINED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    USE_THEN "const" (MP_TAC o C MATCH_MP (CONJ
      (ASSUME `sndcart(z:real^(1,N)finite_sum) IN U`)
      (ASSUME `~(sndcart(z:real^(1,N)finite_sum) IN K)`))) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`;
                   `(J:real^1->bool) PCROSS (U:real^N->bool)`;
                   `z:real^(1,N)finite_sum`; `J:real^1->bool`;
                   `\t:real^1. sndcart(z:real^(1,N)finite_sum)`]
           ODE_MAXIMAL_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; ODE_MAXINT_SUBSET_TIMES] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]);;

let ODE_SOLUTION_DOMAIN_CHANGE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D D' J u.
        ode_solution f D J u /\ (!t. t IN J ==> pastecart t (u t) IN D')
        ==> ode_solution f D' J u`,
  REWRITE_TAC[ode_solution] THEN MESON_TAC[]);;

let ODE_FLOW_RESTRICT = prove
 (`!(f:real^(1,N)finite_sum->real^N) D D' z.
    open D /\ open D' /\ D' SUBSET D /\
    f continuous_on D /\ ode_locally_lipschitz f D /\ z IN D'
    ==> ode_maxint f D' z =
          connected_component
            {t | t IN ode_maxint f D z /\ pastecart t (ode_flow f D t z) IN D'}
            (fstcart z) /\
        !t. t IN ode_maxint f D' z ==> ode_flow f D' t z = ode_flow f D t z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(f:real^(1,N)finite_sum->real^N) continuous_on D' /\
    ode_locally_lipschitz f D' /\ (z:real^(1,N)finite_sum) IN D`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; ODE_LOCALLY_LIPSCHITZ_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D':real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `fstcart(z:real^(1,N)finite_sum) IN ode_maxint (f:real^(1,N)finite_sum->real^N) D' z /\
    fstcart z IN ode_maxint f D z`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ODE_MAXINT_INITIAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`;
                 `ode_maxint (f:real^(1,N)finite_sum->real^N) D' z`;
                 `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D' t z`]
         ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ODE_SOLUTION_MONO THEN
    EXISTS_TAC `D':real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "agree" o BETA_RULE))] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `S = {t | t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z /\
             pastecart t (ode_flow f D t z) IN D'}` THEN
  SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; ODE_MAXINT_IS_INTERVAL] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "agree" (MP_TAC o C MATCH_MP (ASSUME
      `t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D' z`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) D'
                   (ode_maxint f D' z) (\t. ode_flow f D' t z)` THEN
    REWRITE_TAC[ode_solution] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C = connected_component S (fstcart(z:real^(1,N)finite_sum))` THEN
  SUBGOAL_THEN
   `is_interval(C:real^1->bool) /\ fstcart(z:real^(1,N)finite_sum) IN C /\
    C SUBSET S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN
    REWRITE_TAC[IS_INTERVAL_CONNECTED_1; CONNECTED_CONNECTED_COMPONENT;
                CONNECTED_COMPONENT_SUBSET] THEN
    REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C SUBSET ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
  ASSUME_TAC THENL
   [UNDISCH_TAC `C SUBSET (S:real^1->bool)` THEN EXPAND_TAC "S" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D':real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`; `C:real^1->bool`;
                 `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z`]
         ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ODE_SOLUTION_DOMAIN_CHANGE THEN
    EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN
      EXISTS_TAC `ode_maxint (f:real^(1,N)finite_sum->real^N) D z` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `C SUBSET (S:real^1->bool)` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]];
    SIMP_TAC[]]);;

(* Derivatives of linear images of curves. *)

let ODE_HAS_VECTOR_DERIVATIVE_LINEAR_AT = prove
 (`!(h:real^M->real^N) (u:real^1->real^M) u' t.
        linear h /\ (u has_vector_derivative u') (at t)
        ==> ((\s. h(u s)) has_vector_derivative h u') (at t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\s. (h:real^M->real^N)((u:real^1->real^M) s)) = h o u`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. drop x % (h:real^M->real^N) u') = h o (\x. drop x % u')`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR]);;

let ODE_FLOW_PARAM_SOLUTION = prove
 (`!(g:real^(1,(N,P)finite_sum)finite_sum->real^N) D t0 x0 p.
    open D /\ continuously_differentiable 1 D g /\
    pastecart t0 (pastecart x0 p) IN D
    ==> !t. t IN ode_maxint (ode_param_field g) D (pastecart t0 (pastecart x0 p))
            ==> sndcart(ode_flow (ode_param_field g) D t
                          (pastecart t0 (pastecart x0 p))) = p /\
                ((\s. fstcart(ode_flow (ode_param_field g) D s
                                (pastecart t0 (pastecart x0 p))))
                 has_vector_derivative
                 g(pastecart t
                     (pastecart (fstcart(ode_flow (ode_param_field g) D t
                                           (pastecart t0 (pastecart x0 p))))
                                p))) (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 D
     (ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ode_param_field] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,P)finite_sum)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,P)finite_sum)finite_sum->bool`;
                 `pastecart (t0:real^1) (pastecart (x0:real^N) (p:real^P))`]
         ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  ABBREV_TAC
   `M = ode_maxint (ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)) D
          (pastecart t0 (pastecart x0 p))` THEN
  ABBREV_TAC
   `Q = \s. ode_flow (ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)) D s
              (pastecart t0 (pastecart x0 p))` THEN
  SUBGOAL_THEN
   `!s. ode_flow (ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)) D s
          (pastecart t0 (pastecart x0 p)) = (Q:real^1->real^(N,P)finite_sum) s`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN M ==> sndcart((Q:real^1->real^(N,P)finite_sum) s) = p`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. sndcart((Q:real^1->real^(N,P)finite_sum) s)`; `M:real^1->bool`;
                   `t0:real^1`; `p:real^P`] HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE) THEN
    ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; SNDCART_PASTECART] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`sndcart:real^(N,P)finite_sum->real^P`;
                   `Q:real^1->real^(N,P)finite_sum`;
                   `ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)
                      (pastecart s ((Q:real^1->real^(N,P)finite_sum) s))`;
                   `s:real^1`] ODE_HAS_VECTOR_DERIVATIVE_LINEAR_AT) THEN
    ASM_SIMP_TAC[LINEAR_SNDCART; ETA_AX] THEN
    REWRITE_TAC[ode_param_field; SNDCART_PASTECART; has_vector_derivative;
                VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`fstcart:real^(N,P)finite_sum->real^N`;
                 `Q:real^1->real^(N,P)finite_sum`;
                 `ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)
                    (pastecart t ((Q:real^1->real^(N,P)finite_sum) t))`;
                 `t:real^1`] ODE_HAS_VECTOR_DERIVATIVE_LINEAR_AT) THEN
  ASM_SIMP_TAC[LINEAR_FSTCART; ETA_AX] THEN
  REWRITE_TAC[ode_param_field; FSTCART_PASTECART] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM PASTECART_FST_SND] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Scalar comparison principle.                                              *)
(* ------------------------------------------------------------------------- *)

let ODE_GRONWALL_FORWARD_1 = prove
 (`!(e:real^1->real) e' c J t0.
        is_interval J /\ t0 IN J /\
        (!t. t IN J
             ==> ((\t. lift(e t)) has_vector_derivative lift(e' t))
                 (at t within J) /\
                 e' t <= c * e t)
        ==> !t. t IN J /\ drop t0 <= drop t
                ==> e t <= e t0 * exp(c * (drop t - drop t0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_realinterval(IMAGE drop J)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IS_REALINTERVAL_IS_INTERVAL; GSYM IMAGE_o; IMAGE_LIFT_DROP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(e:real^1->real) o lift`; `(e':real^1->real) o lift`; `c:real`;
                 `IMAGE drop J`; `drop t0`] ODE_GRONWALL_REAL_FORWARD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[ODE_HAS_REAL_DERIVATIVE_OF_VECTOR];
    DISCH_THEN(MP_TAC o SPEC `drop t`) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; o_THM; LIFT_DROP]]);;

let ODE_SCALAR_COMPARISON = prove
 (`!(fs:real^(1,1)finite_sum->real^1) D J (u:real^1->real^1) v t0.
    open D /\ fs continuous_on D /\ ode_locally_lipschitz fs D /\
    ode_solution fs D J v /\ t0 IN J /\
    (!t. t IN J
         ==> pastecart t (u t) IN D /\
             ?u'. (u has_vector_derivative u') (at t within J) /\
                  drop u' <= drop(fs(pastecart t (u t)))) /\
    drop(u t0) <= drop(v t0)
    ==> !t. t IN J /\ drop t0 <= drop t ==> drop(u t) <= drop(v t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?du. !t. t IN J
             ==> pastecart t ((u:real^1->real^1) t) IN D /\
                 (u has_vector_derivative du t) (at t within J) /\
                 drop(du t) <= drop((fs:real^(1,1)finite_sum->real^1)(pastecart t (u t)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(GEN_REWRITE_RULE I [ode_solution]
    (ASSUME `ode_solution (fs:real^(1,1)finite_sum->real^1) D J v`)) THEN
  STRIP_TAC THEN
  X_GEN_TAC `t2:real^1` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `interval[t0:real^1,t2] SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
    MAP_EVERY EXISTS_TAC [`t0:real^1`; `t2:real^1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^1->real^1) continuous_on J /\ (v:real^1->real^1) continuous_on J`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[ODE_SOLUTION_CONTINUOUS]];
    ALL_TAC] THEN
  ABBREV_TAC `II = interval[t0:real^1,t2]` THEN
  SUBGOAL_THEN
   `compact(IMAGE (\t. pastecart t ((u:real^1->real^1) t)) II UNION
            IMAGE (\t. pastecart t ((v:real^1->real^1) t)) II) /\
    IMAGE (\t. pastecart t ((u:real^1->real^1) t)) II UNION
    IMAGE (\t. pastecart t ((v:real^1->real^1) t)) II SUBSET D`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      (CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "II" THEN REWRITE_TAC[COMPACT_INTERVAL]]) THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `J:real^1->bool` THEN
      ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[UNION_SUBSET; SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`fs:real^(1,1)finite_sum->real^1`; `D:real^(1,1)finite_sum->bool`;
                 `IMAGE (\t. pastecart t ((u:real^1->real^1) t)) II UNION
                  IMAGE (\t. pastecart t ((v:real^1->real^1) t)) II`]
         ODE_LOCALLY_LIPSCHITZ_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `w = \t. drop((u:real^1->real^1) t) - drop((v:real^1->real^1) t)` THEN
  SUBGOAL_THEN `(\t. lift((w:real^1->real) t)) continuous_on II` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `J:real^1->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Z = {s | s IN II /\ (\t. lift((w:real^1->real) t)) s IN {y:real^1 | y$1 <= &0}}` THEN
  SUBGOAL_THEN `compact(Z:real^1->bool) /\ (t0:real^1) IN Z /\ Z SUBSET II`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `II:real^1->bool` THEN
      CONJ_TAC THENL [EXPAND_TAC "II" THEN REWRITE_TAC[BOUNDED_INTERVAL]; SET_TAC[]];
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN
      EXPAND_TAC "II" THEN REWRITE_TAC[CLOSED_INTERVAL];
      REWRITE_TAC[IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN EXPAND_TAC "w" THEN
      EXPAND_TAC "II" THEN REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`drop`; `Z:real^1->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
    DISCH_THEN(X_CHOOSE_THEN `s0:real^1` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(s0:real^1) IN II /\ (w:real^1->real) s0 <= &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s0:real^1) IN Z` THEN EXPAND_TAC "Z" THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (w:real^1->real) t2` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `drop s0 < drop t2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s0:real^1 = t2` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ] THEN
      UNDISCH_TAC `(s0:real^1) IN II` THEN EXPAND_TAC "II" THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[s0:real^1,t2] SUBSET II` ASSUME_TAC THENL
   [UNDISCH_TAC `(s0:real^1) IN II` THEN EXPAND_TAC "II" THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^1->real) s0 = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. lift((w:real^1->real) t)`; `s0:real^1`; `t2:real^1`; `&0`; `1`]
           IVT_INCREASING_COMPONENT_ON_1) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `II:real^1->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `c:real^1` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(c:real^1) IN Z` ASSUME_TAC THENL
     [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `c:real^1 = s0` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[GSYM DROP_EQ] THEN
    UNDISCH_TAC `(c:real^1) IN interval[s0,t2]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^1`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN interval[s0:real^1,t2] ==> &0 <= (w:real^1->real) r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    ASM_CASES_TAC `r:real^1 = s0` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real^1) IN Z` MP_TAC THENL
     [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM; GSYM drop; LIFT_DROP] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th))] THEN
    UNDISCH_TAC `(r:real^1) IN interval[s0,t2]` THEN
    UNDISCH_TAC `~(r:real^1 = s0)` THEN
    REWRITE_TAC[GSYM DROP_EQ; IN_INTERVAL_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`w:real^1->real`;
    `\r. drop((du:real^1->real^1) r) - drop((fs:real^(1,1)finite_sum->real^1)
                                              (pastecart r ((v:real^1->real^1) r)))`;
    `L:real`; `interval[s0:real^1,t2]`; `s0:real^1`] ODE_GRONWALL_FORWARD_1) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IS_INTERVAL_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real^1) IN J /\ r IN II` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `J:real^1->bool` THEN
      (CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]]) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop((fs:real^(1,1)finite_sum->real^1)(pastecart r ((u:real^1->real^1) r))) -
      drop(fs(pastecart r ((v:real^1->real^1) r)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - c <= b - c`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * norm((u:real^1->real^1) r - v r)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `norm((fs:real^(1,1)finite_sum->real^1)(pastecart r ((u:real^1->real^1) r)) -
             fs(pastecart r ((v:real^1->real^1) r)))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[NORM_1; DROP_SUB] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
        CONJ_TAC THENL
         [DISJ1_TAC THEN EXISTS_TAC `r:real^1` THEN ASM_REWRITE_TAC[];
          DISJ2_TAC THEN EXISTS_TAC `r:real^1` THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^1`) THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[NORM_1; DROP_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t2:real^1`) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL; REAL_MUL_LZERO] THEN
  ASM_REAL_ARITH_TAC);;

