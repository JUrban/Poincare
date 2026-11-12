(* ========================================================================= *)
(* pc_ode_vf: flows of autonomous vector fields, the group law, smooth      *)
(* dependence, flow diffeomorphisms, complete flows of compactly supported  *)
(* fields, isotopies, and naturality under diffeomorphisms.                  *)
(* ========================================================================= *)

needs "src/pc_ode_ck.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The autonomous field (\z. X(sndcart z)) on (:real^1) PCROSS U.            *)
(* ------------------------------------------------------------------------- *)

let ODE_VF_FIELD_CK = prove
 (`!n (X:real^N->real^N) U.
        open U /\ continuously_differentiable n U X
        ==> open((:real^1) PCROSS U) /\
            continuously_differentiable n ((:real^1) PCROSS U) (\z. X(sndcart z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open((:real^1) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)) = X o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ODE_IN_UNIV_PCROSS]);;

let ODE_VF_FIELD_FACTS = prove
 (`!(X:real^N->real^N) U.
        open U /\ continuously_differentiable 1 U X
        ==> open((:real^1) PCROSS U) /\
            continuously_differentiable 1 ((:real^1) PCROSS U) (\z. X(sndcart z)) /\
            (\z. X(sndcart z)) continuous_on ((:real^1) PCROSS U) /\
            ode_locally_lipschitz (\z. X(sndcart z)) ((:real^1) PCROSS U)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ODE_VF_FIELD_CK) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ODE_C1_IMP_LOCALLY_LIPSCHITZ THEN
  ASM_REWRITE_TAC[]);;

let ODE_VF_MAXIMAL = prove
 (`!(X:real^N->real^N) U x.
    open U /\ continuously_differentiable 1 U X /\ x IN U
    ==> open(ode_vf_maxint X U x) /\ is_interval(ode_vf_maxint X U x) /\
        vec 0 IN ode_vf_maxint X U x /\ ode_vf_flow X U (vec 0) x = x /\
        !t. t IN ode_vf_maxint X U x
            ==> ode_vf_flow X U t x IN U /\
                ((\s. ode_vf_flow X U s x) has_vector_derivative
                 X(ode_vf_flow X U t x)) (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`;
                 `pastecart (vec 0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; FSTCART_PASTECART;
                  SNDCART_PASTECART; ode_vf_maxint; ode_vf_flow] THEN
  SIMP_TAC[]);;

(* Translation in time for the autonomous problem.                           *)

let ODE_VF_TIME_SHIFT = prove
 (`!(X:real^N->real^N) U s x.
    open U /\ continuously_differentiable 1 U X /\ x IN U
    ==> ode_maxint (\z. X(sndcart z)) ((:real^1) PCROSS U) (pastecart s x) =
        IMAGE (\t. s + t) (ode_vf_maxint X U x) /\
        !t. t IN ode_vf_maxint X U x
            ==> ode_flow (\z. X(sndcart z)) ((:real^1) PCROSS U) (s + t)
                         (pastecart s x) = ode_vf_flow X U t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[ode_vf_maxint; ode_vf_flow] THEN
  ABBREV_TAC `f = \z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)` THEN
  ABBREV_TAC `D = (:real^1) PCROSS (U:real^N->bool)` THEN
  SUBGOAL_THEN `!t y. (f:real^(1,N)finite_sum->real^N) (pastecart t y) = X y`
  ASSUME_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[SNDCART_PASTECART]; ALL_TAC] THEN
  SUBGOAL_THEN `!t y. pastecart (t:real^1) y IN (D:real^(1,N)finite_sum->bool) <=>
                     (y:real^N) IN U` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (vec 0:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s0")))))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (s:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1")))))) THEN
  ABBREV_TAC `M0 = ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart (vec 0) x)` THEN
  ABBREV_TAC `M1 = ode_maxint (f:real^(1,N)finite_sum->real^N) D (pastecart s x)` THEN
  MP_TAC(ISPECL
   [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
    `pastecart (s:real^1) (x:real^N)`; `{t | t - s IN (M0:real^1->bool)}`;
    `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D (t - s) (pastecart (vec 0) x)`]
   ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM;
                    VECTOR_SUB_REFL] THEN
    REWRITE_TAC[ode_solution] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`M0:real^1->bool`; `s:real^1`] ODE_IS_INTERVAL_SHIFT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REMOVE_THEN "s0" (MP_TAC o SPEC `t - s:real^1`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC(REWRITE_RULE[]
     (ISPECL [`\r. ode_flow (f:real^(1,N)finite_sum->real^N) D r (pastecart (vec 0) x)`]
             ODE_HAS_VECTOR_DERIVATIVE_SHIFT_SUB)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fsub") (LABEL_TAC "feq")) THEN
  MP_TAC(ISPECL
   [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
    `pastecart (vec 0:real^1) (x:real^N)`; `{t | t + s IN (M1:real^1->bool)}`;
    `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D (t + s) (pastecart s x)`]
   ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM;
                    VECTOR_ADD_LID] THEN
    REWRITE_TAC[ode_solution] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`M1:real^1->bool`; `s:real^1`] ODE_IS_INTERVAL_SHIFT) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REMOVE_THEN "s1" (MP_TAC o SPEC `t + s:real^1`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC(REWRITE_RULE[]
     (ISPECL [`\r. ode_flow (f:real^(1,N)finite_sum->real^N) D r (pastecart s x)`]
             ODE_HAS_VECTOR_DERIVATIVE_SHIFT)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "bsub") (K ALL_TAC)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `t - s:real^1` THEN
      CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "bsub" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(t - s) + s:real^1 = t`];
      DISCH_THEN(X_CHOOSE_THEN `r:real^1` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN REMOVE_THEN "fsub" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(s + r) - s:real^1 = r`]];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "feq" (MP_TAC o SPEC `s + t:real^1`) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(s + t) - s:real^1 = t`] THEN
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

let ODE_VF_ZERO = prove
 (`!(X:real^N->real^N) U x.
    open U /\ continuously_differentiable 1 U X /\ x IN U /\ X x = vec 0
    ==> ode_vf_maxint X U x = (:real^1) /\ !t. ode_vf_flow X U t x = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`; `(:real^1)`; `x:real^N`]
         ODE_SOLUTION_CONST) THEN
  ASM_REWRITE_TAC[IS_INTERVAL_UNIV; IN_UNIV; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`;
                 `pastecart (vec 0:real^1) (x:real^N)`; `(:real^1)`; `\t:real^1. x:real^N`]
         ODE_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[ode_vf_maxint; ode_vf_flow] THEN
  MESON_TAC[SUBSET_ANTISYM; SUBSET_UNIV]);;

let ODE_VF_UNIQUE = prove
 (`!(X:real^N->real^N) U J (u:real^1->real^N) t0.
    open U /\ continuously_differentiable 1 U X /\
    is_interval J /\ t0 IN J /\
    (!t. t IN J
         ==> u t IN U /\ (u has_vector_derivative X(u t)) (at t within J))
    ==> !t. t IN J
            ==> t - t0 IN ode_vf_maxint X U (u t0) /\
                u t = ode_vf_flow X U (t - t0) (u t0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^1->real^N) t0 IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`;
                 `pastecart (t0:real^1) ((u:real^1->real^N) t0)`; `J:real^1->bool`;
                 `u:real^1->real^N`] ODE_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ANTS_TAC THENL
   [REWRITE_TAC[ode_solution; PASTECART_IN_PCROSS; IN_UNIV; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sub") (LABEL_TAC "eq")) THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `t0:real^1`;
                 `(u:real^1->real^N) t0`] ODE_VF_TIME_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "im") (LABEL_TAC "fl")) THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `t - t0 IN ode_vf_maxint (X:real^N->real^N) U ((u:real^1->real^N) t0)`
  ASSUME_TAC THENL
   [REMOVE_THEN "sub" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "im" SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^1` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(t0 + r) - t0:real^1 = r`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "eq" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REMOVE_THEN "fl" (MP_TAC o SPEC `t - t0:real^1`) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `t0 + (t - t0):real^1 = t`]);;

let ODE_VF_GROUP = prove
 (`!(X:real^N->real^N) U x s.
    open U /\ continuously_differentiable 1 U X /\ x IN U /\
    s IN ode_vf_maxint X U x
    ==> ode_vf_maxint X U (ode_vf_flow X U s x) = IMAGE (\t. t - s) (ode_vf_maxint X U x) /\
        !t. t IN ode_vf_maxint X U (ode_vf_flow X U s x)
            ==> ode_vf_flow X U t (ode_vf_flow X U s x) = ode_vf_flow X U (s + t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `x:real^N`] ODE_VF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^1` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`;
                 `pastecart (vec 0:real^1) (x:real^N)`; `s:real^1`] ODE_FLOW_COCYCLE) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; GSYM ode_vf_maxint; GSYM ode_vf_flow] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mx") (LABEL_TAC "cf")) THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `s:real^1`;
                 `ode_vf_flow (X:real^N->real^N) U s x`] ODE_VF_TIME_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "im") (LABEL_TAC "fl")) THEN
  SUBGOAL_THEN
   `ode_vf_maxint (X:real^N->real^N) U x =
    IMAGE (\t. s + t) (ode_vf_maxint X U (ode_vf_flow X U s x))`
  (LABEL_TAC "key") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "key" SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `t:real^1` THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `s + t:real^1` THEN
      CONJ_TAC THENL [VECTOR_ARITH_TAC; EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `r:real^1` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^1` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(s + p) - s:real^1 = p`]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  REMOVE_THEN "fl" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REMOVE_THEN "cf" MATCH_MP_TAC THEN
  USE_THEN "key" SUBST1_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]);;

let ODE_VF_DOMAIN_UNIFORM_TIME = prove
 (`!(X:real^N->real^N) U K.
    open U /\ continuously_differentiable 1 U X /\ compact K /\ K SUBSET U
    ==> ?e. &0 < e /\ !x t. x IN K /\ abs(drop t) <= e ==> t IN ode_vf_maxint X U x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`;
                 `IMAGE (\x:real^N. pastecart (vec 0:real^1) x) K`]
         ODE_DOMAIN_UNIFORM_TIME) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^1`] THEN STRIP_TAC THEN
  REWRITE_TAC[ode_vf_maxint] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; DROP_VEC; REAL_SUB_RZERO; IN_IMAGE] THEN
  EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* C^k and smooth dependence of autonomous flows, and the variational        *)
(* equation (ODE_VF_FLOW_CK, ODE_VF_FLOW_SMOOTH, ODE_VF_VARIATIONAL).        *)
(* ------------------------------------------------------------------------- *)

let ODE_VF_DOMAIN_IN = prove
 (`!(X:real^N->real^N) U w.
        w IN ode_vf_domain X U <=>
        pastecart (fstcart w) (pastecart (vec 0) (sndcart w)) IN
        ode_domain (\z. X(sndcart z)) ((:real^1) PCROSS U)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ODE_IN_DOMAIN; PASTECART_IN_PCROSS; IN_UNIV; GSYM ode_vf_maxint] THEN
  REWRITE_TAC[ode_vf_domain; IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`fstcart(w:real^(1,N)finite_sum)`;
                          `sndcart(w:real^(1,N)finite_sum)`] THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND]]);;

let ODE_VF_FLOW_CK = prove
 (`!k (X:real^N->real^N) U.
    open U /\ continuously_differentiable (SUC k) U X
    ==> open(ode_vf_domain X U) /\
        continuously_differentiable (SUC k) (ode_vf_domain X U)
          (\w. ode_vf_flow X U (fstcart w) (sndcart w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 U (X:real^N->real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN
    EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC k`; `X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_CK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`] ODE_FLOW_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`] ODE_FLOW_CK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `E = \w:real^(1,N)finite_sum. pastecart (fstcart w) (pastecart (vec 0:real^1) (sndcart w))` THEN
  SUBGOAL_THEN
   `linear(E:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN ode_vf_domain (X:real^N->real^N) U <=>
        (E:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum) w IN
        ode_domain (\z. X(sndcart z)) ((:real^1) PCROSS U)`
  ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[ODE_VF_DOMAIN_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `open(ode_vf_domain (X:real^N->real^N) U)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `ode_vf_domain (X:real^N->real^N) U =
      {w | (E:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum) w IN
           ode_domain (\z. X(sndcart z)) ((:real^1) PCROSS U)}`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\w. ode_vf_flow (X:real^N->real^N) U (fstcart w) (sndcart w)) =
    (\w. ode_flow (\z. X(sndcart z)) ((:real^1) PCROSS U) (fstcart w) (sndcart w)) o
    (E:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum)`
  SUBST1_TAC THENL
   [EXPAND_TAC "E" THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; ode_vf_flow; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `ode_domain (\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z))
                         ((:real^1) PCROSS U)` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]);;

let ODE_VF_FLOW_SMOOTH = prove
 (`!(X:real^N->real^N) U.
    open U /\ smooth_map_on U X
    ==> open(ode_vf_domain X U) /\
        smooth_map_on (ode_vf_domain X U) (\w. ode_vf_flow X U (fstcart w) (sndcart w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_map_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FLOW_CK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON];
    MP_TAC(ISPECL [`n:num`; `X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FLOW_CK) THEN
    ASM_SIMP_TAC[]]);;

(* The derivative of the autonomous field.                                   *)

let ODE_VF_FIELD_FRECHET = prove
 (`!(X:real^N->real^N) U t y v.
    open U /\ continuously_differentiable 1 U X /\ y IN U
    ==> frechet_derivative (\z:real^(1,N)finite_sum. X(sndcart z)) (at (pastecart t y)) v =
        frechet_derivative X (at y) (sndcart v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_C1_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sndcart:real^(1,N)finite_sum->real^N`; `X:real^N->real^N`;
                 `sndcart:real^(1,N)finite_sum->real^N`;
                 `frechet_derivative (X:real^N->real^N) (at y)`;
                 `pastecart (t:real^1) (y:real^N)`] DIFF_CHAIN_AT) THEN
  ASM_SIMP_TAC[SNDCART_PASTECART; HAS_DERIVATIVE_LINEAR; LINEAR_SNDCART] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]);;

let ODE_VF_VARIATIONAL = prove
 (`!(X:real^N->real^N) U x h.
    open U /\ continuously_differentiable 1 U X /\ x IN U
    ==> frechet_derivative (\w. ode_vf_flow X U (fstcart w) (sndcart w))
          (at (pastecart (vec 0) x)) (pastecart (vec 0) h) = h /\
        !t. t IN ode_vf_maxint X U x
            ==> ((\s. frechet_derivative (\w. ode_vf_flow X U (fstcart w) (sndcart w))
                        (at (pastecart s x)) (pastecart (vec 0) h))
                 has_vector_derivative
                 frechet_derivative X (at (ode_vf_flow X U t x))
                   (frechet_derivative (\w. ode_vf_flow X U (fstcart w) (sndcart w))
                      (at (pastecart t x)) (pastecart (vec 0) h))) (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `x:real^N`] ODE_VF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "vm" o last o CONJUNCTS) THEN
  MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                 `(:real^1) PCROSS (U:real^N->bool)`; `vec 0:real^1`; `x:real^N`;
                 `h:real^N`] ODE_FLOW_VARIATIONAL_FIXED_TIME) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN
  REWRITE_TAC[GSYM ode_vf_maxint; GSYM ode_vf_flow] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "vm" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `t:real^1`;
                 `ode_vf_flow (X:real^N->real^N) U t x`;
                 `pastecart (vec 0:real^1)
                    (frechet_derivative
                       (\w. ode_vf_flow (X:real^N->real^N) U (fstcart w) (sndcart w))
                       (at (pastecart t x)) (pastecart (vec 0) h))`]
         ODE_VF_FIELD_FRECHET) THEN
  ASM_REWRITE_TAC[SNDCART_PASTECART] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* Flow maps are diffeomorphisms; complete flows of compactly supported     *)
(* fields; isotopies (ODE_FLOW_DIFFEO, ODE_VF_FLOW_DIFFEO, ODE_VF_COMPLETE, *)
(* ODE_FLOW_ISOTOPY).                                                       *)
(* ------------------------------------------------------------------------- *)

let ODE_IN_PCROSS = prove
 (`!(w:real^(M,N)finite_sum) s t. w IN s PCROSS t <=> fstcart w IN s /\ sndcart w IN t`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS]);;

(* Going from time s to time t and back.                                    *)

let ODE_FLOW_INVOLUTION = prove
 (`!(f:real^(1,N)finite_sum->real^N) D s t x.
    open D /\ continuously_differentiable 1 D f /\
    pastecart t (pastecart s x) IN ode_domain f D
    ==> pastecart s (pastecart t (ode_flow f D t (pastecart s x))) IN ode_domain f D /\
        ode_flow f D s (pastecart t (ode_flow f D t (pastecart s x))) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODE_IN_DOMAIN] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (s:real^1) (x:real^N)`; `t:real^1`] ODE_FLOW_COCYCLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c"))) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (s:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "c" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[]);;

let ODE_FLOW_DIFFEO = prove
 (`!(f:real^(1,N)finite_sum->real^N) D s t.
    open D /\ smooth_map_on D f
    ==> diffeomorphism_on {x | pastecart t (pastecart s x) IN ode_domain f D}
                          {y | pastecart s (pastecart t y) IN ode_domain f D}
                          (\x. ode_flow f D t (pastecart s x))
                          (\y. ode_flow f D s (pastecart t y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 D (f:real^(1,N)finite_sum->real^N)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b:real^1. open {x | pastecart a (pastecart b x) IN
                           ode_domain (f:real^(1,N)finite_sum->real^N) D} /\
                 smooth_map_on {x | pastecart a (pastecart b x) IN ode_domain f D}
                   (\x. ode_flow f D a (pastecart b x))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `(\x:real^N. pastecart (a:real^1) (pastecart (b:real^1) x)) continuous_on (:real^N) /\
      smooth_map_on (:real^N) (\x:real^N. pastecart (a:real^1) (pastecart (b:real^1) x))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
      [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
              REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]);
       REPEAT(MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
              REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID])];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open {x | pastecart (a:real^1) (pastecart (b:real^1) x) IN
                ode_domain (f:real^(1,N)finite_sum->real^N) D}`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x:real^N. pastecart (a:real^1) (pastecart (b:real^1) x)`;
                     `(:real^N)`; `ode_domain (f:real^(1,N)finite_sum->real^N) D`]
             CONTINUOUS_OPEN_PREIMAGE) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\x. ode_flow (f:real^(1,N)finite_sum->real^N) D a (pastecart b x)) =
      (\w. ode_flow f D (fstcart w) (sndcart w)) o
      (\x:real^N. pastecart (a:real^1) (pastecart (b:real^1) x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ode_domain (f:real^(1,N)finite_sum->real^N) D` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!x. pastecart t (pastecart s x) IN ode_domain (f:real^(1,N)finite_sum->real^N) D
         ==> pastecart s (pastecart t (ode_flow f D t (pastecart s x))) IN ode_domain f D /\
             ode_flow f D s (pastecart t (ode_flow f D t (pastecart s x))) = x) /\
    (!y. pastecart s (pastecart t y) IN ode_domain f D
         ==> pastecart t (pastecart s (ode_flow f D s (pastecart t y))) IN ode_domain f D /\
             ode_flow f D t (pastecart s (ode_flow f D s (pastecart t y))) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC ODE_FLOW_INVOLUTION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN
    EXISTS_TAC `ode_flow (f:real^(1,N)finite_sum->real^N) D s (pastecart t y)` THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN
    EXISTS_TAC `ode_flow (f:real^(1,N)finite_sum->real^N) D t (pastecart s y)` THEN
    ASM_SIMP_TAC[]]);;

let ODE_VF_INVOLUTION = prove
 (`!(X:real^N->real^N) U t x.
    open U /\ continuously_differentiable 1 U X /\ x IN U /\
    t IN ode_vf_maxint X U x
    ==> ode_vf_flow X U t x IN U /\
        --t IN ode_vf_maxint X U (ode_vf_flow X U t x) /\
        ode_vf_flow X U (--t) (ode_vf_flow X U t x) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `x:real^N`] ODE_VF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `x:real^N`; `t:real^1`]
         ODE_VF_GROUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gr")) THEN
  SUBGOAL_THEN `--t IN ode_vf_maxint (X:real^N->real^N) U (ode_vf_flow X U t x)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^1` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REMOVE_THEN "gr" (MP_TAC o SPEC `--t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `t + --t:real^1 = vec 0`]);;

let ODE_VF_FLOW_DIFFEO = prove
 (`!(X:real^N->real^N) U t.
    open U /\ smooth_map_on U X
    ==> diffeomorphism_on {x | x IN U /\ t IN ode_vf_maxint X U x}
                          {y | y IN U /\ --t IN ode_vf_maxint X U y}
                          (ode_vf_flow X U t) (ode_vf_flow X U (--t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 U (X:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a:real^1. open {x | x IN U /\ a IN ode_vf_maxint (X:real^N->real^N) U x} /\
               smooth_map_on {x | x IN U /\ a IN ode_vf_maxint X U x} (ode_vf_flow X U a)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `{x | x IN U /\ a IN ode_vf_maxint (X:real^N->real^N) U x} =
      {x | x IN (:real^N) /\ pastecart a x IN ode_vf_domain X U}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; ode_vf_domain] THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^1`; `y:real^N`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[PASTECART_INJ] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x:real^N. pastecart (a:real^1) x) continuous_on (:real^N) /\
      smooth_map_on (:real^N) (\x:real^N. pastecart (a:real^1) x)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
        REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open {x | x IN (:real^N) /\ pastecart (a:real^1) x IN
                ode_vf_domain (X:real^N->real^N) U}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_UNIV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ode_vf_flow (X:real^N->real^N) U a =
      (\w. ode_vf_flow X U (fstcart w) (sndcart w)) o (\x:real^N. pastecart a x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ode_vf_domain (X:real^N->real^N) U` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!x. x IN U /\ t IN ode_vf_maxint (X:real^N->real^N) U x
         ==> ode_vf_flow X U t x IN U /\
             --t IN ode_vf_maxint X U (ode_vf_flow X U t x) /\
             ode_vf_flow X U (--t) (ode_vf_flow X U t x) = x) /\
    (!y. y IN U /\ --t IN ode_vf_maxint X U y
         ==> ode_vf_flow X U (--t) y IN U /\
             t IN ode_vf_maxint X U (ode_vf_flow X U (--t) y) /\
             ode_vf_flow X U t (ode_vf_flow X U (--t) y) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [MATCH_MP_TAC ODE_VF_INVOLUTION THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `--t:real^1`; `y:real^N`]
             ODE_VF_INVOLUTION) THEN
      ASM_REWRITE_TAC[VECTOR_NEG_NEG]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN EXISTS_TAC `ode_vf_flow (X:real^N->real^N) U (--t) y` THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[];
    DISCH_TAC THEN EXISTS_TAC `ode_vf_flow (X:real^N->real^N) U t y` THEN
    ASM_SIMP_TAC[]]);;

let ODE_VF_COMPLETE = prove
 (`!(X:real^N->real^N) U K.
    open U /\ smooth_map_on U X /\ compact K /\ K SUBSET U /\
    (!x. x IN U /\ ~(x IN K) ==> X x = vec 0)
    ==> (!x. x IN U ==> ode_vf_maxint X U x = (:real^1)) /\
        ode_vf_domain X U = (:real^1) PCROSS U /\
        (!t. diffeomorphism_on U U (ode_vf_flow X U t) (ode_vf_flow X U (--t))) /\
        (!t x. x IN U /\ ~(x IN K) ==> ode_vf_flow X U t x = x) /\
        (!t x. x IN K ==> ode_vf_flow X U t x IN K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 U (X:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN U
        ==> ode_vf_maxint (X:real^N->real^N) U x = (:real^1) /\
            (x IN K ==> !t. ode_vf_flow X U t x IN K) /\
            (~(x IN K) ==> !t. ode_vf_flow X U t x = x)`
  (LABEL_TAC "cs") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\z:real^(1,N)finite_sum. (X:real^N->real^N)(sndcart z)`;
                   `(:real^1)`; `U:real^N->bool`; `K:real^N->bool`;
                   `pastecart (vec 0:real^1) (x:real^N)`]
           ODE_MAXINT_COMPACT_SUPPORT) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_UNIV; IN_UNIV; PASTECART_IN_PCROSS;
                    SNDCART_PASTECART; GSYM ode_vf_maxint; GSYM ode_vf_flow] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. {x | x IN U /\ a IN ode_vf_maxint (X:real^N->real^N) U x} = U`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN ASM_CASES_TAC `(y:real^N) IN U` THEN
    ASM_SIMP_TAC[IN_UNIV];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; ODE_IN_UNIV_PCROSS] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    REWRITE_TAC[ode_vf_domain; IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[SNDCART_PASTECART];
      DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`fstcart(w:real^(1,N)finite_sum)`;
                            `sndcart(w:real^(1,N)finite_sum)`] THEN
      ASM_SIMP_TAC[IN_UNIV; PASTECART_FST_SND]];
    GEN_TAC THEN
    MP_TAC(ISPECL [`X:real^N->real^N`; `U:real^N->bool`; `t:real^1`]
           ODE_VF_FLOW_DIFFEO) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN U` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let ODE_FLOW_ISOTOPY = prove
 (`!(f:real^(1,N)finite_sum->real^N) J U K.
    open J /\ is_interval J /\ open U /\ smooth_map_on (J PCROSS U) f /\
    compact K /\ K SUBSET U /\
    (!t x. t IN J /\ x IN U /\ ~(x IN K) ==> f(pastecart t x) = vec 0)
    ==> ode_domain f (J PCROSS U) = J PCROSS (J PCROSS U) /\
        smooth_map_on (J PCROSS (J PCROSS U))
          (\w. ode_flow f (J PCROSS U) (fstcart w) (sndcart w)) /\
        (!s t. s IN J /\ t IN J
               ==> diffeomorphism_on U U
                     (\x. ode_flow f (J PCROSS U) t (pastecart s x))
                     (\y. ode_flow f (J PCROSS U) s (pastecart t y))) /\
        (!s t x. s IN J /\ t IN J /\ x IN U /\ ~(x IN K)
                 ==> ode_flow f (J PCROSS U) t (pastecart s x) = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open((J:real^1->bool) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 ((J:real^1->bool) PCROSS (U:real^N->bool))
      (f:real^(1,N)finite_sum->real^N)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`;
                 `(J:real^1->bool) PCROSS (U:real^N->bool)`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN (J:real^1->bool) PCROSS (U:real^N->bool)
        ==> ode_maxint (f:real^(1,N)finite_sum->real^N) (J PCROSS U) z = J /\
            (sndcart z IN K ==> !t. t IN J ==> ode_flow f (J PCROSS U) t z IN K) /\
            (~(sndcart z IN K)
             ==> !t. t IN J ==> ode_flow f (J PCROSS U) t z = sndcart z)`
  (LABEL_TAC "cs") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `J:real^1->bool`;
                   `U:real^N->bool`; `K:real^N->bool`; `z:real^(1,N)finite_sum`]
           ODE_MAXINT_COMPACT_SUPPORT) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_domain (f:real^(1,N)finite_sum->real^N) ((J:real^1->bool) PCROSS (U:real^N->bool)) =
    J PCROSS (J PCROSS U)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `w:real^(1,(1,N)finite_sum)finite_sum` THEN
    REWRITE_TAC[ODE_IN_DOMAIN_ALT] THEN
    GEN_REWRITE_TAC RAND_CONV [ODE_IN_PCROSS] THEN
    ASM_CASES_TAC
     `sndcart(w:real^(1,(1,N)finite_sum)finite_sum) IN
      (J:real^1->bool) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`;
                 `(J:real^1->bool) PCROSS (U:real^N->bool)`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`;
                   `(J:real^1->bool) PCROSS (U:real^N->bool)`; `s:real^1`; `t:real^1`]
           ODE_FLOW_DIFFEO) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[SET_RULE `{x:real^N | x IN U} = U`];
    REPEAT STRIP_TAC THEN
    REMOVE_THEN "cs" (MP_TAC o SPEC `pastecart (s:real^1) (x:real^N)`) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Naturality of flows under diffeomorphisms (ODE_FLOW_NATURAL,              *)
(* ODE_VF_FLOW_NATURAL).                                                     *)
(* ------------------------------------------------------------------------- *)

let ODE_HAS_VECTOR_DERIVATIVE_CHAIN = prove
 (`!(u:real^1->real^M) (psi:real^M->real^N) u' D t.
        (u has_vector_derivative u') (at t) /\ (psi has_derivative D) (at (u t))
        ==> ((\s. psi(u s)) has_vector_derivative D u') (at t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(D:real^M->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^1->real^M`; `psi:real^M->real^N`;
                 `\x:real^1. drop x % (u':real^M)`; `D:real^M->real^N`; `t:real^1`]
         DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL]);;

let ODE_DIFFEO_DERIVATIVE_INVERSE = prove
 (`!U V (psi:real^M->real^N) phi x k.
        diffeomorphism_on U V psi phi /\ x IN U
        ==> frechet_derivative phi (at (psi x)) (frechet_derivative psi (at x) k) = k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(psi:real^M->real^N) x IN V` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `psi:real^M->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `phi:real^N->real^M`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(psi:real^M->real^N) x`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`psi:real^M->real^N`; `phi:real^N->real^M`;
                 `frechet_derivative (psi:real^M->real^N) (at x)`;
                 `frechet_derivative (phi:real^N->real^M) (at ((psi:real^M->real^N) x))`;
                 `x:real^M`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((phi:real^N->real^M) o (psi:real^M->real^N) has_derivative (\h. h)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`\y:real^M. y`; `U:real^M->bool`] THEN
    ASM_SIMP_TAC[o_THM; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(phi:real^N->real^M) o (psi:real^M->real^N)`;
                 `frechet_derivative (phi:real^N->real^M) (at ((psi:real^M->real^N) x)) o
                  frechet_derivative psi (at x)`;
                 `\h:real^M. h`; `x:real^M`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `k:real^M`) THEN
  REWRITE_TAC[o_THM]);;

let ODE_FLOW_NATURAL = prove
 (`!(f:real^(1,M)finite_sum->real^M) (g:real^(1,N)finite_sum->real^N)
   J U V (psi:real^M->real^N) phi.
    open J /\ continuously_differentiable 1 (J PCROSS U) f /\
    diffeomorphism_on U V psi phi /\
    (!t x. t IN J /\ x IN U
           ==> g(pastecart t (psi x)) =
               frechet_derivative psi (at x) (f(pastecart t x)))
    ==> !t0 x. t0 IN J /\ x IN U
               ==> ode_maxint g (J PCROSS V) (pastecart t0 (psi x)) =
                   ode_maxint f (J PCROSS U) (pastecart t0 x) /\
                   !t. t IN ode_maxint f (J PCROSS U) (pastecart t0 x)
                       ==> ode_flow g (J PCROSS V) t (pastecart t0 (psi x)) =
                           psi(ode_flow f (J PCROSS U) t (pastecart t0 x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `open((J:real^1->bool) PCROSS (U:real^M->bool)) /\
    open((J:real^1->bool) PCROSS (V:real^N->bool))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN U ==> (psi:real^M->real^N) x IN V) /\
    (!y. y IN V ==> (phi:real^N->real^M) y IN U)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,M)finite_sum->real^M`;
                 `(J:real^1->bool) PCROSS (U:real^M->bool)`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t y. t IN J /\ y IN V
          ==> (g:real^(1,N)finite_sum->real^N)(pastecart t y) =
              frechet_derivative (psi:real^M->real^N) (at (phi y))
                ((f:real^(1,M)finite_sum->real^M)(pastecart t (phi y)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(phi:real^N->real^M) y IN U /\ (psi:real^M->real^N)((phi:real^N->real^M) y) = y`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`t:real^1`; `(phi:real^N->real^M) y`] (ASSUME
     `!t x. t IN J /\ x IN U
            ==> (g:real^(1,N)finite_sum->real^N)(pastecart t ((psi:real^M->real^N) x)) =
                frechet_derivative psi (at x)
                  ((f:real^(1,M)finite_sum->real^M)(pastecart t x))`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 ((J:real^1->bool) PCROSS (V:real^N->bool))
      (g:real^(1,N)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC
     `\w. frechet_derivative (psi:real^M->real^N)
            (at ((phi:real^N->real^M)(sndcart w)))
            ((f:real^(1,M)finite_sum->real^M)
               (pastecart (fstcart w) (phi(sndcart(w:real^(1,N)finite_sum)))))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,N)finite_sum` THEN REWRITE_TAC[ODE_IN_PCROSS] THEN
      STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC ODE_CK_FRECHET_APPLY THEN EXISTS_TAC `U:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[smooth_map_on];
      SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum. (phi:real^N->real^M)(sndcart w)) = phi o sndcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
      EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ODE_IN_PCROSS] THEN SIMP_TAC[];
        ASM_MESON_TAC[smooth_map_on]];
      SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum.
           (f:real^(1,M)finite_sum->real^M)
             (pastecart (fstcart w) ((phi:real^N->real^M)(sndcart w)))) =
        f o (\w. pastecart (fstcart w) (phi(sndcart w)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
      EXISTS_TAC `(J:real^1->bool) PCROSS (U:real^M->bool)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ODE_IN_PCROSS; FSTCART_PASTECART;
                    SNDCART_PASTECART] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
      ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_FSTCART; ETA_AX] THEN
      SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum. (phi:real^N->real^M)(sndcart w)) = phi o sndcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
      EXISTS_TAC `V:real^N->bool` THEN
      ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ODE_IN_PCROSS] THEN SIMP_TAC[];
        ASM_MESON_TAC[smooth_map_on]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ODE_IN_PCROSS] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,N)finite_sum->real^N`;
                 `(J:real^1->bool) PCROSS (V:real^N->bool)`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^M->bool`; `psi:real^M->real^N`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `phi:real^N->real^M`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dphi") THEN
  DISCH_THEN(LABEL_TAC "dpsi") THEN
  MAP_EVERY X_GEN_TAC [`t0:real^1`; `x:real^M`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,M)finite_sum->real^M`;
                 `(J:real^1->bool) PCROSS (U:real^M->bool)`;
                 `pastecart (t0:real^1) (x:real^M)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fs")))))) THEN
  MP_TAC(ISPECL [`g:real^(1,N)finite_sum->real^N`;
                 `(J:real^1->bool) PCROSS (V:real^N->bool)`;
                 `pastecart (t0:real^1) ((psi:real^M->real^N) x)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_SIMP_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gs")))))) THEN
  MP_TAC(ISPECL
   [`g:real^(1,N)finite_sum->real^N`; `(J:real^1->bool) PCROSS (V:real^N->bool)`;
    `pastecart (t0:real^1) ((psi:real^M->real^N) x)`;
    `ode_maxint (f:real^(1,M)finite_sum->real^M) (J PCROSS U) (pastecart t0 x)`;
    `\t. (psi:real^M->real^N)
           (ode_flow (f:real^(1,M)finite_sum->real^M) (J PCROSS U) t (pastecart t0 x))`]
   ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[ode_solution] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "fs" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_CHAIN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^(1,M)finite_sum->real^M`; `(J:real^1->bool) PCROSS (U:real^M->bool)`;
    `pastecart (t0:real^1) (x:real^M)`;
    `ode_maxint (g:real^(1,N)finite_sum->real^N) (J PCROSS V)
       (pastecart t0 ((psi:real^M->real^N) x))`;
    `\t. (phi:real^N->real^M)
           (ode_flow (g:real^(1,N)finite_sum->real^N) (J PCROSS V) t
              (pastecart t0 ((psi:real^M->real^N) x)))`]
   ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[ode_solution] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REMOVE_THEN "gs" (MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    ABBREV_TAC
     `y = ode_flow (g:real^(1,N)finite_sum->real^N) (J PCROSS V) t
            (pastecart t0 ((psi:real^M->real^N) x))` THEN
    SUBGOAL_THEN
     `(f:real^(1,M)finite_sum->real^M)(pastecart t ((phi:real^N->real^M) y)) =
      frechet_derivative phi (at y) ((g:real^(1,N)finite_sum->real^N)(pastecart t y))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`U:real^M->bool`; `V:real^N->bool`; `psi:real^M->real^N`;
                     `phi:real^N->real^M`; `(phi:real^N->real^M) y`;
                     `(f:real^(1,M)finite_sum->real^M)
                        (pastecart t ((phi:real^N->real^M) y))`]
             ODE_DIFFEO_DERIVATIVE_INVERSE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_CHAIN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN ASM_MESON_TAC[]);;

let ODE_VF_FLOW_NATURAL = prove
 (`!(X:real^M->real^M) (Y:real^N->real^N) U V (psi:real^M->real^N) phi.
    continuously_differentiable 1 U X /\ diffeomorphism_on U V psi phi /\
    (!x. x IN U ==> Y(psi x) = frechet_derivative psi (at x) (X x))
    ==> !x. x IN U
            ==> ode_vf_maxint Y V (psi x) = ode_vf_maxint X U x /\
                !t. t IN ode_vf_maxint X U x
                    ==> ode_vf_flow Y V t (psi x) = psi(ode_vf_flow X U t x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^M->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^(1,M)finite_sum. (X:real^M->real^M)(sndcart z)`;
                 `\z:real^(1,N)finite_sum. (Y:real^N->real^N)(sndcart z)`;
                 `(:real^1)`; `U:real^M->bool`; `V:real^N->bool`;
                 `psi:real^M->real^N`; `phi:real^N->real^M`] ODE_FLOW_NATURAL) THEN
  MP_TAC(ISPECL [`1`; `X:real^M->real^M`; `U:real^M->bool`] ODE_VF_FIELD_CK) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SNDCART_PASTECART] THEN
  DISCH_THEN(K ALL_TAC) THEN
  DISCH_THEN(fun th -> X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`vec 0:real^1`; `x:real^M`] th)) THEN
  ASM_REWRITE_TAC[ode_vf_maxint; ode_vf_flow]);;

