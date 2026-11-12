(* ========================================================================= *)
(* pc_ode_found: local existence, uniqueness and maximal solutions of       *)
(* u' = f(t,u) on an open set D of time-state points (see pc_ode_defs).     *)
(* ========================================================================= *)

needs "src/pc_ode_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Imported blocks, adapted from earlier HOL Light work: time reflection,    *)
(* gluing, the left and two-sided Picard-Lindelof theorems, and the Gronwall *)
(* inequality.  Names are prefixed with ODE_.                                *)
(* ------------------------------------------------------------------------- *)

let ode_pl_has_const name tm =
  can (find_term (fun u -> is_const u && fst(dest_const u) = name)) tm;;

let ode_pl_has_var name tm =
  can (find_term (fun u -> is_var u && fst(dest_var u) = name)) tm;;

let ODE_PL_HAS_DERIVATIVE_WITHIN_UNION = prove
 (`!f:real^M->real^N f' x s t.
        (f has_derivative f') (at x within (s UNION t)) <=>
        (f has_derivative f') (at x within s) /\
        (f has_derivative f') (at x within t)`,
  REWRITE_TAC[has_derivative_within; LIM_WITHIN_UNION] THEN CONV_TAC TAUT);;

let ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_UNION = prove
 (`!f:real^1->real^N f' x s t.
        (f has_vector_derivative f') (at x within (s UNION t)) <=>
        (f has_vector_derivative f') (at x within s) /\
        (f has_vector_derivative f') (at x within t)`,
  REWRITE_TAC[has_vector_derivative; ODE_PL_HAS_DERIVATIVE_WITHIN_UNION]);;

let ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_TRIVIAL = prove
 (`!f:real^1->real^N f' x s.
        closed s /\ ~(x IN s)
        ==> (f has_vector_derivative f') (at x within s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_vector_derivative; has_derivative_within] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC LIM_TRIVIAL THEN REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
    ASM_MESON_TAC[CLOSED_LIMPT]]);;

let ODE_PL_HAS_VECTOR_DERIVATIVE_REFLECT = prove
 (`!w:real^1->real^N w' t0 t s.
        (w has_vector_derivative w') (at (&2 % t0 - t) within IMAGE (\t. &2 % t0 - t) s)
        ==> ((\t. w(&2 % t0 - t)) has_vector_derivative (--w')) (at t within s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t:real^1. &2 % t0 - t`; `w:real^1->real^N`; `--vec 1:real^1`; `w':real^N`;
                 `s:real^1->bool`; `t:real^1`] VECTOR_DIFF_CHAIN_WITHIN) THEN
  ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `--vec 1:real^1 = vec 0 - vec 1` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; HAS_VECTOR_DERIVATIVE_ID];
    REWRITE_TAC[DROP_NEG; DROP_VEC; VECTOR_MUL_LNEG; VECTOR_MUL_LID]]);;

let ODE_PL_IMAGE_REFLECT_INTERVAL = prove
 (`!c a b:real^1. IMAGE (\t. c - t) (interval[a,b]) = interval[c - b,c - a]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTERVAL_1; DROP_SUB] THEN
  X_GEN_TAC `x:real^1` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^1` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[DROP_SUB] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `c - x:real^1` THEN REWRITE_TAC[DROP_SUB] THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ASM_REAL_ARITH_TAC]]);;

let ODE_PL_REFLECT_CONTINUOUS = prove
 (`!t0:real^1 x:real^(1,N)finite_sum.
        (\z:real^(1,N)finite_sum. pastecart (&2 % t0 - fstcart z) (sndcart z)) continuous (at x)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[LINEAR_FSTCART];
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[LINEAR_SNDCART]]);;

let ODE_PL_REFLECT_INTERVALS = prove
 (`!t0 r. IMAGE (\t. &2 % t0 - t) (interval[t0 - lift r,t0]) = interval[t0,t0 + lift r] /\
          IMAGE (\t. &2 % t0 - t) (interval[t0,t0 + lift r]) = interval[t0 - lift r,t0]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ODE_PL_IMAGE_REFLECT_INTERVAL;
              VECTOR_ARITH `&2 % t0 - t0:real^1 = t0`;
              VECTOR_ARITH `&2 % t0 - (t0 - lift r):real^1 = t0 + lift r`;
              VECTOR_ARITH `&2 % t0 - (t0 + lift r):real^1 = t0 - lift r`]);;

let ODE_PL_REFLECT_MEMBER = prove
 (`!t0 r t:real^1.
        (t IN interval[t0 - lift r,t0] <=> &2 % t0 - t IN interval[t0,t0 + lift r]) /\
        (t IN interval[t0,t0 + lift r] <=> &2 % t0 - t IN interval[t0 - lift r,t0])`,
  REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let ODE_PICARD_LINDELOF_LEFT = prove
 (`!s (f:real^(1,N)finite_sum->real^N) t0 u0 r0 r1 B c.
     open s /\ f continuous_on s /\
     &0 < r0 /\ &0 < r1 /\ B * r0 < r1 /\ c * r0 < &1 /\
     interval[t0 - lift r0,t0] PCROSS cball(u0,r1) SUBSET s /\
     (!x. x IN s ==> norm(f x) <= B) /\
     (!t v w. t IN interval[t0 - lift r0,t0] /\
              v IN cball(u0,r1) /\ w IN cball(u0,r1)
              ==> norm(f(pastecart t v) - f(pastecart t w)) <= c * norm(v - w))
     ==> ?u. u t0 = u0 /\
             (!t. t IN interval[t0 - lift r0,t0]
                  ==> (u has_vector_derivative f(pastecart t (u t)))
                        (at t within interval[t0 - lift r0,t0])) /\
             (!v. (!t. t IN interval[t0 - lift r0,t0]
                  ==> pastecart t (v t) IN s) /\
                  v t0 = u0 /\
                  (!t. t IN interval[t0 - lift r0,t0]
                       ==> (v has_vector_derivative f(pastecart t (v t)))
                             (at t within interval[t0 - lift r0,t0]))
                  ==> (!t. t IN interval[t0 - lift r0,t0] ==> v t = u t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{z:real^(1,N)finite_sum | pastecart (&2 % t0 - fstcart z) (sndcart z) IN s}`;
    `\z:real^(1,N)finite_sum. --((f:real^(1,N)finite_sum->real^N)
                                   (pastecart (&2 % t0 - fstcart z) (sndcart z)))`;
    `t0:real^1`; `u0:real^N`; `r0:real`; `r1:real`; `B:real`; `c:real`]
   PICARD_LINDELOF_RIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_REWRITE_TAC[ODE_PL_REFLECT_CONTINUOUS];
      MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[ODE_PL_REFLECT_CONTINUOUS];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET) o check (ode_pl_has_const "continuous_on" o concl)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]];
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (ode_pl_has_const "PCROSS" o concl)) THEN
      REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_MESON_TAC[ODE_PL_REFLECT_MEMBER];
      REWRITE_TAC[IN_ELIM_THM; NORM_NEG] THEN ASM_SIMP_TAC[];
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      REWRITE_TAC[VECTOR_ARITH `--a - --b:real^N = --(a - b)`; NORM_NEG] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[ODE_PL_REFLECT_MEMBER]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^1->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t. (w:real^1->real^N) (&2 % t0 - t)` THEN
  REWRITE_TAC[VECTOR_ARITH `&2 % t0 - t0:real^1 = t0`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w:real^1->real^N`;
      `--((f:real^(1,N)finite_sum->real^N)
            (pastecart t ((w:real^1->real^N) (&2 % t0 - t))))`;
      `t0:real^1`; `t:real^1`; `interval[t0 - lift r0,t0]`]
      ODE_PL_HAS_VECTOR_DERIVATIVE_REFLECT) THEN
    REWRITE_TAC[VECTOR_NEG_NEG; ODE_PL_REFLECT_INTERVALS] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&2 % t0 - t:real^1` o check (fun th ->
      is_forall(concl th) && ode_pl_has_const "has_vector_derivative" (concl th) &&
      not (ode_pl_has_var "v" (concl th)))) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART;
                VECTOR_ARITH `&2 % t0 - (&2 % t0 - t):real^1 = t`] THEN
    ASM_MESON_TAC[ODE_PL_REFLECT_MEMBER];
    X_GEN_TAC `v:real^1->real^N` THEN STRIP_TAC THEN X_GEN_TAC `t:real^1` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\t. (v:real^1->real^N) (&2 % t0 - t)` o
      check (fun th -> is_forall(concl th) && ode_pl_has_var "v" (concl th) &&
             ode_pl_has_const "has_vector_derivative" (concl th) &&
             not (ode_pl_has_var "t" (concl th) && false))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                  VECTOR_ARITH `&2 % t0 - t0:real^1 = t0`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `tau:real^1` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          ode_pl_has_const "pastecart" (concl th) &&
          not (ode_pl_has_const "has_vector_derivative" (concl th)) &&
          ode_pl_has_var "v" (concl th))) THEN
        ASM_MESON_TAC[ODE_PL_REFLECT_MEMBER];
        X_GEN_TAC `tau:real^1` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`v:real^1->real^N`;
          `(f:real^(1,N)finite_sum->real^N)
             (pastecart (&2 % t0 - tau) ((v:real^1->real^N) (&2 % t0 - tau)))`;
          `t0:real^1`; `tau:real^1`; `interval[t0,t0 + lift r0]`]
          ODE_PL_HAS_VECTOR_DERIVATIVE_REFLECT) THEN
        REWRITE_TAC[ODE_PL_REFLECT_INTERVALS] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          ode_pl_has_const "has_vector_derivative" (concl th) &&
          ode_pl_has_var "v" (concl th))) THEN
        ASM_MESON_TAC[ODE_PL_REFLECT_MEMBER]];
      DISCH_THEN(MP_TAC o SPEC `&2 % t0 - t:real^1`) THEN
      REWRITE_TAC[VECTOR_ARITH `&2 % t0 - (&2 % t0 - t):real^1 = t`] THEN
      ASM_MESON_TAC[ODE_PL_REFLECT_MEMBER]]]);;

let ODE_PL_INTERVAL_SPLIT = prove
 (`!t0:real^1 r. &0 <= r
       ==> interval[t0 - lift r,t0 + lift r] =
           interval[t0 - lift r,t0] UNION interval[t0,t0 + lift r] /\
           interval[t0 - lift r,t0] SUBSET interval[t0 - lift r,t0 + lift r] /\
           interval[t0,t0 + lift r] SUBSET interval[t0 - lift r,t0 + lift r]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_UNION; IN_INTERVAL_1; DROP_SUB; DROP_ADD; LIFT_DROP] THEN
  ASM_REAL_ARITH_TAC);;

let ODE_PICARD_LINDELOF_TWO_SIDED = prove
 (`!s (f:real^(1,N)finite_sum->real^N) t0 u0 r0 r1 B c.
     open s /\ f continuous_on s /\
     &0 < r0 /\ &0 < r1 /\ B * r0 < r1 /\ c * r0 < &1 /\
     interval[t0 - lift r0,t0 + lift r0] PCROSS cball(u0,r1) SUBSET s /\
     (!x. x IN s ==> norm(f x) <= B) /\
     (!t v w. t IN interval[t0 - lift r0,t0 + lift r0] /\
              v IN cball(u0,r1) /\ w IN cball(u0,r1)
              ==> norm(f(pastecart t v) - f(pastecart t w)) <= c * norm(v - w))
     ==> ?u. u t0 = u0 /\
             (!t. t IN interval[t0 - lift r0,t0 + lift r0]
                  ==> (u has_vector_derivative f(pastecart t (u t)))
                        (at t within interval[t0 - lift r0,t0 + lift r0])) /\
             (!v. (!t. t IN interval[t0 - lift r0,t0 + lift r0]
                  ==> pastecart t (v t) IN s) /\
                  v t0 = u0 /\
                  (!t. t IN interval[t0 - lift r0,t0 + lift r0]
                       ==> (v has_vector_derivative f(pastecart t (v t)))
                             (at t within interval[t0 - lift r0,t0 + lift r0]))
                  ==> (!t. t IN interval[t0 - lift r0,t0 + lift r0] ==> v t = u t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t0:real^1`; `r0:real`] ODE_PL_INTERVAL_SPLIT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`s:real^(1,N)finite_sum->bool`; `f:real^(1,N)finite_sum->real^N`;
                 `t0:real^1`; `u0:real^N`; `r0:real`; `r1:real`; `B:real`; `c:real`]
         PICARD_LINDELOF_RIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interval[t0 - lift r0,t0 + lift r0] PCROSS cball(u0:real^N,r1)` THEN
      ASM_SIMP_TAC[PCROSS_MONO; SUBSET_REFL];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `uR:real^1->real^N` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`s:real^(1,N)finite_sum->bool`; `f:real^(1,N)finite_sum->real^N`;
                 `t0:real^1`; `u0:real^N`; `r0:real`; `r1:real`; `B:real`; `c:real`]
         ODE_PICARD_LINDELOF_LEFT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interval[t0 - lift r0,t0 + lift r0] PCROSS cball(u0:real^N,r1)` THEN
      ASM_SIMP_TAC[PCROSS_MONO; SUBSET_REFL];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `uL:real^1->real^N` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `u = \t. if drop t < drop t0 then (uL:real^1->real^N) t else uR t` THEN
  SUBGOAL_THEN
   `(!t. t IN interval[t0,t0 + lift r0] ==> (u:real^1->real^N) t = uR t) /\
    (!t. t IN interval[t0 - lift r0,t0] ==> u t = uL t)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_ADD; LIFT_DROP] THEN
    CONJ_TAC THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY ASM_REAL_ARITH_TAC THEN
    SUBGOAL_THEN `t:real^1 = t0` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 IN interval[t0,t0 + lift r0] /\ t0 IN interval[t0 - lift r0,t0]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_ADD; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `u:real^1->real^N` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [ASSUME `interval[t0 - lift r0,t0 + lift r0] =
              interval[t0 - lift r0,t0] UNION interval[t0,t0 + lift r0]`] THEN
    REWRITE_TAC[ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_UNION] THEN CONJ_TAC THENL
     [ASM_CASES_TAC `t IN interval[t0 - lift r0,t0]` THENL
       [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
        MAP_EVERY EXISTS_TAC [`uL:real^1->real^N`; `&1`] THEN
        REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
          FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
             ode_pl_has_var "uL" (concl th) && ode_pl_has_var "u" (concl th) &&
             not (ode_pl_has_const "has_vector_derivative" (concl th))
             then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `(u:real^1->real^N) t = uL t` SUBST1_TAC THENL
           [ASM_MESON_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
             ode_pl_has_var "uL" (concl th) &&
             ode_pl_has_const "has_vector_derivative" (concl th) &&
             not (ode_pl_has_var "v" (concl th))
             then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_TRIVIAL THEN
        ASM_REWRITE_TAC[CLOSED_INTERVAL]];
      ASM_CASES_TAC `t IN interval[t0,t0 + lift r0]` THENL
       [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
        MAP_EVERY EXISTS_TAC [`uR:real^1->real^N`; `&1`] THEN
        REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
          FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
             ode_pl_has_var "uR" (concl th) && ode_pl_has_var "u" (concl th) &&
             not (ode_pl_has_const "has_vector_derivative" (concl th))
             then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
          SUBGOAL_THEN `(u:real^1->real^N) t = uR t` SUBST1_TAC THENL
           [ASM_MESON_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
             ode_pl_has_var "uR" (concl th) &&
             ode_pl_has_const "has_vector_derivative" (concl th) &&
             not (ode_pl_has_var "v" (concl th))
             then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_TRIVIAL THEN
        ASM_REWRITE_TAC[CLOSED_INTERVAL]]];
    X_GEN_TAC `v:real^1->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
      ode_pl_has_const "UNION" (concl th))) THEN
    MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
      `interval[t0 - lift r0,t0] SUBSET interval[t0 - lift r0,t0 + lift r0]`)) THEN
    MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
      `interval[t0,t0 + lift r0] SUBSET interval[t0 - lift r0,t0 + lift r0]`)) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `(!t. t IN interval[t0,t0 + lift r0] ==> (v:real^1->real^N) t = uR t) /\
      (!t. t IN interval[t0 - lift r0,t0] ==> v t = uL t)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && ode_pl_has_var "uR" (concl th) &&
           not (ode_pl_has_var "u" (concl th)) && not (ode_pl_has_const "has_vector_derivative"
           (rand(snd(dest_forall(concl th)))))
           then MATCH_MP_TAC th else NO_TAC);
        FIRST_X_ASSUM(fun th -> if is_forall(concl th) && ode_pl_has_var "uL" (concl th) &&
           not (ode_pl_has_var "u" (concl th)) && not (ode_pl_has_const "has_vector_derivative"
           (rand(snd(dest_forall(concl th)))))
           then MATCH_MP_TAC th else NO_TAC)] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `y:real^1` THEN DISCH_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          ode_pl_has_var "v" (concl th) && ode_pl_has_const "IN" (rand(snd(dest_forall(concl th)))) &&
          not (ode_pl_has_const "has_vector_derivative" (concl th)))) THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC `interval[t0 - lift r0,t0 + lift r0]` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          ode_pl_has_var "v" (concl th) && ode_pl_has_const "has_vector_derivative" (concl th) &&
          not (ode_pl_has_var "uR" (concl th)) && not (ode_pl_has_var "uL" (concl th)))) THEN
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          ode_pl_has_var "v" (concl th) && ode_pl_has_const "IN" (rand(snd(dest_forall(concl th)))) &&
          not (ode_pl_has_const "has_vector_derivative" (concl th)))) THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
        EXISTS_TAC `interval[t0 - lift r0,t0 + lift r0]` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          ode_pl_has_var "v" (concl th) && ode_pl_has_const "has_vector_derivative" (concl th) &&
          not (ode_pl_has_var "uR" (concl th)) && not (ode_pl_has_var "uL" (concl th)))) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `t IN interval[t0 - lift r0,t0] \/ t IN interval[t0,t0 + lift r0]`
    MP_TAC THENL
     [UNDISCH_TAC `t IN interval[t0 - lift r0,t0 + lift r0]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_MESON_TAC[]]);;

let ODE_GRONWALL_G_DERIV = prove
 (`!(w:real->real) t0 e c L t s.
     w real_continuous_on real_interval[t0,e] /\ t IN real_interval[t0,e] /\
     s IN real_interval[t0,t]
     ==> ((\s. (c + L * real_integral (real_interval[t0,s]) w) * exp(--(L*(s - t0))))
          has_real_derivative
          ((c + L * real_integral (real_interval[t0,s]) w) * (--L * exp(--(L*(s-t0)))) +
           (L * w s) * exp(--(L*(s - t0)))))
         (atreal s within real_interval[t0,t])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s IN real_interval[t0,e]` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. c + L * real_integral (real_interval[t0,s]) w) has_real_derivative (L * w s))
    (atreal s within real_interval[t0,t])` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`w:real->real`;`t0:real`;`e:real`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_DERIVATIVE_WITHIN_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `real_interval[t0:real,t]`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `((\s. c + L * real_integral (real_interval[t0,s]) w) has_real_derivative (&0 + L * w s))
      (atreal s within real_interval[t0,t])` MP_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. exp(--(L*(s - t0)))) has_real_derivative (--L * exp(--(L*(s - t0)))))
    (atreal s within real_interval[t0,t])` ASSUME_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. c + L * real_integral (real_interval[t0,s]) (w:real->real)`;
    `L * (w:real->real) s`;
    `\s:real. exp(--(L*(s - t0)))`;
    `--L * exp(--(L*(s - t0)))`;
    `s:real`; `real_interval[t0:real,t]`] HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let ODE_GRONWALL = prove
 (`!(w:real->real) t0 e c L.
     &0 <= c /\ &0 <= L /\ t0 <= e /\
     w real_continuous_on real_interval[t0,e] /\
     (!t. t IN real_interval[t0,e] ==> &0 <= w t) /\
     (!t. t IN real_interval[t0,e] ==> w t <= c + L * real_integral (real_interval[t0,t]) w)
     ==> (!t. t IN real_interval[t0,e] ==> w t <= c * exp(L * (t - t0)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c + L * real_integral (real_interval[t0,t]) (w:real->real)` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `(c + L * real_integral (real_interval[t0,t]) (w:real->real)) * exp(--(L*(t - t0))) <= c`
   MP_TAC THENL
   [MP_TAC(ISPECL
     [`\s. --((c + L * real_integral (real_interval[t0,s]) (w:real->real)) * exp(--(L*(s - t0))))`;
      `\s. --((c + L * real_integral (real_interval[t0,s]) (w:real->real)) * (--L * exp(--(L*(s-t0)))) +
             (L * w s) * exp(--(L*(s - t0))))`;
      `real_interval[t0:real,t]`; `t0:real`; `t:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
        MATCH_MP_TAC ODE_GRONWALL_G_DERIV THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `s:real` THEN DISCH_TAC THEN
        REWRITE_TAC[REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
        SUBGOAL_THEN `s IN real_interval[t0,e]` ASSUME_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
          ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 <= (L * exp(--(L*(s - t0)))) *
                          ((c + L * real_integral (real_interval[t0,s]) (w:real->real)) - w s)`
         MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
            ASM_SIMP_TAC[REAL_SUB_LE]];
          MP_TAC(SPECL
           [`c + L * real_integral (real_interval[t0,s]) (w:real->real)`;
            `(w:real->real) s`; `L:real`; `exp(--(L*(s - t0)))`]
           (REAL_RING `!A ws L es:real.
              A * (--L * es) + (L * ws) * es = --((L * es) * (A - ws))`)) THEN
          REAL_ARITH_TAC];
        REWRITE_TAC[IN_REAL_INTERVAL] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
        RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_LE_NEG2; REAL_INTEGRAL_REFL] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_RID;
                  REAL_ADD_RID; REAL_LE_REFL]];
    SUBGOAL_THEN `exp(L * (t - t0)) = inv(exp(--(L*(t - t0))))` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_NEG] THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < exp(--(L*(t - t0)))` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; real_div; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]);;

let ODE_GRONWALL_VEC = prove
 (`!(w:real^1->real) t0 e c L.
     &0 <= c /\ &0 <= L /\ drop t0 <= drop e /\
     (\x. lift(w x)) continuous_on interval[t0,e] /\
     (!t. t IN interval[t0,e] ==> &0 <= w t) /\
     (!t. t IN interval[t0,e]
          ==> w t <= c + L * drop(integral (interval[t0,t]) (\s. lift(w s))))
     ==> (!t. t IN interval[t0,e] ==> w t <= c * exp(L * (drop t - drop t0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\x:real. (w:real^1->real)(lift x)`; `drop t0`; `drop e`; `c:real`; `L:real`]
    ODE_GRONWALL) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; IMAGE_LIFT_REAL_INTERVAL] THEN
      ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(\r:real. (w:real^1->real)(lift r)) real_integrable_on real_interval[drop t0, x]`
       (fun th -> ASSUME_TAC(MATCH_MP REAL_INTEGRAL th)) THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; IMAGE_LIFT_REAL_INTERVAL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[t0:real^1,e]` THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[ETA_AX];
          REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP]) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `lift x`) THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `drop t`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL; LIFT_DROP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[LIFT_DROP]]]);;

(* --- Continuous dependence on the perturbation ------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Basic facts about solutions on intervals.                                 *)
(* ------------------------------------------------------------------------- *)

let ODE_HAS_VECTOR_DERIVATIVE_WITHIN_LOCAL = prove
 (`!(u:real^1->real^N) u' t s s'.
        eventually (\x. x IN s <=> x IN s') (at t)
        ==> ((u has_vector_derivative u') (at t within s) <=>
             (u has_vector_derivative u') (at t within s'))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_vector_derivative; has_derivative_within] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIM_TRANSFORM_WITHIN_SET THEN
  ASM_REWRITE_TAC[]);;

let ODE_SOLUTION_SUBINTERVAL = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J J' u.
        ode_solution f D J u /\ is_interval J' /\ J' SUBSET J
        ==> ode_solution f D J' u`,
  REWRITE_TAC[ode_solution] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET; HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET]);;

let ODE_SOLUTION_MONO = prove
 (`!(f:real^(1,N)finite_sum->real^N) D D' J u.
        ode_solution f D J u /\ D SUBSET D' ==> ode_solution f D' J u`,
  REWRITE_TAC[ode_solution; SUBSET] THEN MESON_TAC[]);;

let ODE_SOLUTION_CONTINUOUS = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J u.
        ode_solution f D J u ==> u continuous_on J`,
  REWRITE_TAC[ode_solution; CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
  REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]);;

let ODE_SOLUTION_AT = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J u t.
        ode_solution f D J u /\ open J /\ t IN J
        ==> (u has_vector_derivative f(pastecart t (u t))) (at t)`,
  REWRITE_TAC[ode_solution; has_vector_derivative] THEN
  MESON_TAC[HAS_DERIVATIVE_WITHIN_OPEN]);;

let ODE_SOLUTION_EQ = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J u v.
        ode_solution f D J u /\ (!t. t IN J ==> v t = u t)
        ==> ode_solution f D J v`,
  REWRITE_TAC[ode_solution] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`u:real^1->real^N`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* Intervals of real^1 and gluing of solutions.                              *)
(* ------------------------------------------------------------------------- *)

let ODE_IS_INTERVAL_BETWEEN = prove
 (`!J a b x:real^1.
        is_interval J /\ a IN J /\ b IN J /\
        (drop a <= drop x /\ drop x <= drop b \/
         drop b <= drop x /\ drop x <= drop a)
        ==> x IN J`,
  REWRITE_TAC[IS_INTERVAL_1] THEN MESON_TAC[]);;

let ODE_IS_INTERVAL_UNION = prove
 (`!J1 J2:real^1->bool.
        is_interval J1 /\ is_interval J2 /\ ~(J1 INTER J2 = {})
        ==> is_interval(J1 UNION J2)`,
  REWRITE_TAC[IS_INTERVAL_CONNECTED_1] THEN MESON_TAC[CONNECTED_UNION]);;

let ODE_INTERVAL_CLOSURE_LEMMA = prove
 (`!J1 J2 t:real^1.
        is_interval J1 /\ is_interval J2 /\ ~(J1 INTER J2 = {}) /\
        t IN J1 /\ ~(t IN J2)
        ==> ~(t IN closure(J2 DIFF J1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; IN_DIFF] THEN
  DISCH_THEN(MP_TAC o SPEC `dist(s:real^1,t)`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_POS_LT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`J1:real^1->bool`; `s:real^1`; `t:real^1`; `y:real^1`]
         ODE_IS_INTERVAL_BETWEEN) THEN
  MP_TAC(SPECL [`J2:real^1->bool`; `s:real^1`; `y:real^1`; `t:real^1`]
         ODE_IS_INTERVAL_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `dist(y:real^1,t) < dist(s,t)` THEN
  REWRITE_TAC[DIST_REAL; GSYM drop] THEN REAL_ARITH_TAC);;

let ODE_HAS_VECTOR_DERIVATIVE_INTERVAL_UNION = prove
 (`!(u:real^1->real^N) u' t J1 J2.
        is_interval J1 /\ is_interval J2 /\ ~(J1 INTER J2 = {}) /\ t IN J1 /\
        (u has_vector_derivative u') (at t within J1) /\
        (t IN J2 ==> (u has_vector_derivative u') (at t within J2))
        ==> (u has_vector_derivative u') (at t within (J1 UNION J2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `(t:real^1) IN J2` THENL
   [ASM_MESON_TAC[ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_UNION]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `(J1:real^1->bool) UNION closure(J2 DIFF J1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_UNION] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ODE_PL_HAS_VECTOR_DERIVATIVE_WITHIN_TRIVIAL THEN
    REWRITE_TAC[CLOSED_CLOSURE] THEN
    MATCH_MP_TAC ODE_INTERVAL_CLOSURE_LEMMA THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `J2 DIFF (J1:real^1->bool)` CLOSURE_SUBSET) THEN SET_TAC[]]);;

let ODE_SOLUTION_GLUE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J1 J2 u1 u2.
        ode_solution f D J1 u1 /\ ode_solution f D J2 u2 /\
        ~(J1 INTER J2 = {}) /\ (!t. t IN J1 INTER J2 ==> u1 t = u2 t)
        ==> ode_solution f D (J1 UNION J2)
              (\t. if t IN J1 then u1 t else u2 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `w = \t:real^1. if t IN J1 then (u1:real^1->real^N) t else u2 t` THEN
  SUBGOAL_THEN `(!t. t IN J1 ==> (w:real^1->real^N) t = u1 t) /\
                (!t. t IN J2 ==> w t = u2 t)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN CONJ_TAC THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `ode_solution (f:real^(1,N)finite_sum->real^N) D J1 w /\
                ode_solution f D J2 w` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ODE_SOLUTION_EQ THENL
     [EXISTS_TAC `u1:real^1->real^N`; EXISTS_TAC `u2:real^1->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ode_solution] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ODE_IS_INTERVAL_UNION]; ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_INTERVAL_UNION THEN
    ASM_MESON_TAC[];
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN
    MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_INTERVAL_UNION THEN
    ASM_MESON_TAC[INTER_COMM]]);;

(* ------------------------------------------------------------------------- *)
(* Membership in the maximal interval, and its interval property.            *)
(* ------------------------------------------------------------------------- *)

let ODE_IN_MAXINT = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z t.
        t IN ode_maxint f D z <=>
        ?J u. fstcart z IN J /\ t IN J /\ u(fstcart z) = sndcart z /\
              ode_solution f D J u`,
  REWRITE_TAC[ode_maxint; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let ODE_MAXINT_IS_INTERVAL = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z. is_interval(ode_maxint f D z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_INTERVAL_1; ODE_IN_MAXINT] THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`; `x:real^1`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `Ja:real^1->bool`
     (X_CHOOSE_THEN `ua:real^1->real^N` STRIP_ASSUME_TAC))
   (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `Jb:real^1->bool`
       (X_CHOOSE_THEN `ub:real^1->real^N` STRIP_ASSUME_TAC))
     STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `is_interval(Ja:real^1->bool) /\ is_interval(Jb:real^1->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ode_solution]; ALL_TAC] THEN
  ASM_CASES_TAC `drop x <= drop(fstcart(z:real^(1,N)finite_sum))` THENL
   [MAP_EVERY EXISTS_TAC [`Ja:real^1->bool`; `ua:real^1->real^N`];
    MAP_EVERY EXISTS_TAC [`Jb:real^1->bool`; `ub:real^1->real^N`]] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THENL
   [EXISTS_TAC `a:real^1`; EXISTS_TAC `b:real^1`] THEN
  EXISTS_TAC `fstcart(z:real^(1,N)finite_sum)` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bounds and Lipschitz constants on compact sets; C^1 fields.              *)
(* ------------------------------------------------------------------------- *)

let ODE_COMPACT_BOUND = prove
 (`!(f:real^M->real^N) s K.
        f continuous_on s /\ compact K /\ K SUBSET s
        ==> ?B. &0 < B /\ !x. x IN K ==> norm(f x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `K:real^M->bool`]
         COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE]);;

let ODE_LOCALLY_LIPSCHITZ_SUBSET = prove
 (`!(f:real^(1,N)finite_sum->real^N) D D'.
        ode_locally_lipschitz f D /\ D' SUBSET D
        ==> ode_locally_lipschitz f D'`,
  REWRITE_TAC[ode_locally_lipschitz; IN_INTER; SUBSET] THEN MESON_TAC[]);;

(* A compact subset of an open set has a compact neighbourhood of uniform    *)
(* radius inside the open set.                                               *)

let ODE_COMPACT_THICKEN = prove
 (`!K D:real^M->bool.
        compact K /\ open D /\ K SUBSET D
        ==> ?R. &0 < R /\
                compact {x + y | x IN K /\ y IN cball(vec 0,R)} /\
                {x + y | x IN K /\ y IN cball(vec 0,R)} SUBSET D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^M->bool`; `(:real^M) DIFF D`]
         SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[COMPACT_CBALL];
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `x + y:real^M`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    UNDISCH_TAC `y IN cball(vec 0:real^M,d / &2)` THEN
    REWRITE_TAC[IN_CBALL_0; dist] THEN
    UNDISCH_TAC `&0 < d` THEN CONV_TAC NORM_ARITH]);;

let ODE_LOCALLY_LIPSCHITZ_COMPACT = prove
 (`!(f:real^(1,N)finite_sum->real^N) D K.
        f continuous_on D /\ ode_locally_lipschitz f D /\
        compact K /\ K SUBSET D
        ==> ?L. &0 <= L /\
                !t x y. pastecart t x IN K /\ pastecart t y IN K
                        ==> norm(f(pastecart t x) - f(pastecart t y))
                            <= L * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`;
                 `D:real^(1,N)finite_sum->bool`;
                 `K:real^(1,N)finite_sum->bool`] ODE_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~(~p)`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. ?t x y. pastecart t x IN K /\ pastecart t y IN K /\
                &n * norm(x - y) <
                norm((f:real^(1,N)finite_sum->real^N)(pastecart t x) -
                     f(pastecart t y))`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `&n:real`) THEN
    REWRITE_TAC[REAL_POS; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:num->real^1` (X_CHOOSE_THEN `xx:num->real^N`
    (X_CHOOSE_THEN `yy:num->real^N` (LABEL_TAC "seq")))) THEN
  FIRST_ASSUM(MP_TAC o SPEC
    `\n. pastecart ((tt:num->real^1) n) ((xx:num->real^N) n)` o
    GEN_REWRITE_RULE I [compact]) THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`l:real^(1,N)finite_sum`; `r:num->num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(l:real^(1,N)finite_sum) IN D` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `l:real^(1,N)finite_sum` o
    GEN_REWRITE_RULE I [ode_locally_lipschitz]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (X_CHOOSE_THEN `L0:real`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0 / &2` o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  ASM_REWRITE_TAC[REAL_HALF; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "conv")) THEN
  MP_TAC(SPEC `max L0 ((&4 * B) / r0) + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  ABBREV_TAC `m = (r:num->num)(N1 + N2 + 1)` THEN
  SUBGOAL_THEN `N1 + N2 + 1 <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_MESON_TAC[MONOTONE_BIGGER]; ALL_TAC] THEN
  REMOVE_THEN "conv" (MP_TAC o SPEC `N1 + N2 + 1`) THEN
  ANTS_TAC THENL [ARITH_TAC; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
  REMOVE_THEN "seq" (MP_TAC o SPEC `m:num`) THEN
  ABBREV_TAC `t = (tt:num->real^1) m` THEN
  ABBREV_TAC `x = (xx:num->real^N) m` THEN
  ABBREV_TAC `y = (yy:num->real^N) m` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `norm((f:real^(1,N)finite_sum->real^N)(pastecart t x) - f(pastecart t y))
    <= &2 * B` ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^N) <= B /\ norm(b:real^N) <= B ==> norm(a - b) <= &2 * B`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N2 <= &m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&4 * B) / r0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N2 /\ L0 < &N2 /\ (&4 * B) / r0 < &N2` STRIP_ASSUME_TAC
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * B < &N2 * r0` ASSUME_TAC THENL
   [UNDISCH_TAC `(&4 * B) / r0 < &N2` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&N2 * norm(x - y:real^N) <= &m * norm(x - y)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * norm(x - y:real^N) < r0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&2 * norm(x - y:real^N)`; `r0:real`; `&N2`]
           REAL_LT_LMUL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `&N2 * &2 * norm(x - y:real^N) = &2 * (&N2 * norm(x - y))`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((f:real^(1,N)finite_sum->real^N)(pastecart t x) - f(pastecart t y))
    <= L0 * norm(x - y)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `pastecart (t:real^1) (x:real^N) IN D /\ pastecart t y IN D`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN
    MP_TAC(ISPECL [`t:real^1`; `x:real^N`; `y:real^N`]
           (CONJUNCT2 DIST_PASTECART_CANCEL)) THEN
    UNDISCH_TAC `dist(pastecart (t:real^1) (x:real^N),l) < r0 / &2` THEN
    UNDISCH_TAC `&2 * norm(x - y:real^N) < r0` THEN
    REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `L0 * norm(x - y:real^N) <= &m * norm(x - y)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Slices of convex sets are convex. *)

let ODE_CONVEX_SLICE = prove
 (`!s:real^(M,N)finite_sum->bool t.
        convex s ==> convex {v:real^N | pastecart (t:real^M) v IN s}`,
  REWRITE_TAC[convex; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pastecart (t:real^M) (u % x + v % y:real^N) =
    u % pastecart t x + v % pastecart t y`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM PASTECART_CMUL; PASTECART_ADD; PASTECART_INJ] THEN
    ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_LID];
    ASM_MESON_TAC[]]);;

(* An explicit bound for a linear map in terms of the images of the basis. *)

let ODE_LINEAR_BOUND_BASIS = prove
 (`!h:real^M->real^N.
        linear h
        ==> !x. norm(h x) <= sum(1..dimindex(:M)) (\i. norm(h(basis i))) * norm x`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; IN_NUMSEG] THEN
  ASM_SIMP_TAC[o_DEF; NORM_MUL; LINEAR_CMUL] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; COMPONENT_LE_NORM]);;

let ODE_C1_IMP_LOCALLY_LIPSCHITZ = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
    open D /\ continuously_differentiable 1 D f
    ==> f continuous_on D /\ ode_locally_lipschitz f D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  UNDISCH_TAC `continuously_differentiable 1 D (f:real^(1,N)finite_sum->real^N)` THEN
  REWRITE_TAC[ONE] THEN ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
  REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^(1,N)finite_sum->real^(1,N)finite_sum->real^N`
    STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ode_locally_lipschitz] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^(1,N)finite_sum` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\p. lift(sum(1..dimindex(:N))
       (\i. norm((f':real^(1,N)finite_sum->real^(1,N)finite_sum->real^N) p
                  (pastecart (vec 0) (basis i)))))`;
    `D:real^(1,N)finite_sum->bool`;
    `cball(z:real^(1,N)finite_sum,r)`] ODE_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; NORM_LIFT] THEN ANTS_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `B:real`] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\v:real^N. (f:real^(1,N)finite_sum->real^N)(pastecart t v)`;
    `\v:real^N. \w:real^N.
       (f':real^(1,N)finite_sum->real^(1,N)finite_sum->real^N)
         (pastecart t v) (pastecart (vec 0) w)`;
    `{v:real^N | pastecart (t:real^1) v IN ball(z:real^(1,N)finite_sum,r)}`;
    `B:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ODE_CONVEX_SLICE THEN REWRITE_TAC[CONVEX_BALL];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    SUBGOAL_THEN
     `(\w:real^N. (f':real^(1,N)finite_sum->real^(1,N)finite_sum->real^N)
                    (pastecart t v) (pastecart (vec 0) w)) =
      f' (pastecart t v) o (\w. pastecart (vec 0) w)`
     SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\v:real^N. (f:real^(1,N)finite_sum->real^N)(pastecart t v)) =
      f o (\v. pastecart t v)`
     SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_ID];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `cball(z:real^(1,N)finite_sum,r) SUBSET D` THEN
      UNDISCH_TAC `pastecart (t:real^1) (v:real^N) IN ball(z,r)` THEN
      MP_TAC(ISPECL [`z:real^(1,N)finite_sum`; `r:real`] BALL_SUBSET_CBALL) THEN
      SET_TAC[]];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `pastecart (t:real^1) (v:real^N) IN D /\
                  pastecart t v IN cball(z,r)` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`z:real^(1,N)finite_sum`; `r:real`] BALL_SUBSET_CBALL) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `linear(\w:real^N. (f':real^(1,N)finite_sum->real^(1,N)finite_sum->real^N)
                          (pastecart t v) (pastecart (vec 0) w))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\w:real^N. (f':real^(1,N)finite_sum->real^(1,N)finite_sum->real^N)
                      (pastecart t v) (pastecart (vec 0) w)) =
        f' (pastecart t v) o (\w. pastecart (vec 0) w)`
       SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_COMPOSE THEN CONJ_TAC THENL
       [REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL] THEN
        REWRITE_TAC[VECTOR_ADD_LID; VECTOR_MUL_RZERO];
        ASM_MESON_TAC[has_derivative]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP ONORM) THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `w:real^N` THEN
    FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o MATCH_MP ODE_LINEAR_BOUND_BASIS) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (t:real^1) (v:real^N)`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let ODE_SMOOTH_IMP_LOCALLY_LIPSCHITZ = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
    open D /\ smooth_map_on D f
    ==> continuously_differentiable 1 D f /\
        f continuous_on D /\ ode_locally_lipschitz f D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 D (f:real^(1,N)finite_sum->real^N)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  ASM_SIMP_TAC[ODE_C1_IMP_LOCALLY_LIPSCHITZ]);;

(* ------------------------------------------------------------------------- *)
(* Local existence with a uniform time on compact sets.                      *)
(* ------------------------------------------------------------------------- *)

(* Adapted from earlier HOL Light work: extension of f from a compact convex *)
(* box by closest-point projection, keeping a given bound of f on the box.   *)

let ODE_BOX_EXTENSION = prove
 (`!(f:real^(1,N)finite_sum->real^N) i k B.
     convex i /\ compact i /\ ~(i = {}) /\ convex k /\ compact k /\ ~(k = {}) /\
     f continuous_on (i PCROSS k) /\
     (!z. z IN i PCROSS k ==> norm(f z) <= B)
     ==> ?g. g continuous_on (:real^(1,N)finite_sum) /\
             (!z. z IN i PCROSS k ==> g z = f z) /\
             (!z. norm(g z) <= B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed(i:real^1->bool) /\ closed(k:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  ABBREV_TAC `p = \z:real^(1,N)finite_sum.
                    pastecart (closest_point i (fstcart z))
                              (closest_point k (sndcart z))` THEN
  SUBGOAL_THEN `!z. (p:real^(1,N)finite_sum->real^(1,N)finite_sum) z IN i PCROSS k`
  ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    ASM_SIMP_TAC[CLOSEST_POINT_IN_SET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN i PCROSS k
        ==> (p:real^(1,N)finite_sum->real^(1,N)finite_sum) z = z`
  ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_SIMP_TAC[CLOSEST_POINT_SELF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^(1,N)finite_sum->real^(1,N)finite_sum) continuous_on
                (:real^(1,N)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; LINEAR_CONTINUOUS_ON;
                 LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  EXISTS_TAC `(f:real^(1,N)finite_sum->real^N) o
              (p:real^(1,N)finite_sum->real^(1,N)finite_sum)` THEN
  REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(i:real^1->bool) PCROSS (k:real^N->bool)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]);;

let ODE_LOCAL_EXISTENCE_UNIFORM = prove
 (`!(f:real^(1,N)finite_sum->real^N) D K.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\
        compact K /\ K SUBSET D
        ==> ?e. &0 < e /\
                !z. z IN K
                    ==> ?u. u(fstcart z) = sndcart z /\
                            ode_solution f D
                              (interval[fstcart z - lift e,fstcart z + lift e]) u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^(1,N)finite_sum->bool`; `D:real^(1,N)finite_sum->bool`]
         ODE_COMPACT_THICKEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R:real` MP_TAC) THEN
  ABBREV_TAC
   `K' = {x + y | x IN K /\ y IN cball(vec 0:real^(1,N)finite_sum,R)}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!z w:real^(1,N)finite_sum. z IN K /\ norm(w - z) <= R ==> w IN K'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`z:real^(1,N)finite_sum`; `w - z:real^(1,N)finite_sum`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K':real^(1,N)finite_sum->bool`] ODE_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K':real^(1,N)finite_sum->bool`] ODE_LOCALLY_LIPSCHITZ_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = R / &2` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < B + &1 /\ &0 < c + &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (r / (B + &1)) (&1 / (c + &1))` THEN
  SUBGOAL_THEN
   `&0 < min (r / (B + &1)) (&1 / (c + &1)) /\
    min (r / (B + &1)) (&1 / (c + &1)) * (B + &1) <= r /\
    min (r / (B + &1)) (&1 / (c + &1)) * (c + &1) <= &1`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_LT_01] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_MIN_LE; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `e = min (r / (B + &1)) (&1 / (c + &1))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `e <= r /\ B * e < r /\ c * e < &1` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`B:real`; `e:real`] REAL_MUL_SYM) THEN
    MP_TAC(ISPECL [`c:real`; `e:real`] REAL_MUL_SYM) THEN
    SUBGOAL_THEN `&0 <= e * B` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `e * (B + &1) <= r` THEN UNDISCH_TAC `e * (c + &1) <= &1` THEN
    UNDISCH_TAC `&0 < e` THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  ABBREV_TAC `t0 = fstcart(z:real^(1,N)finite_sum)` THEN
  ABBREV_TAC `x0 = sndcart(z:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `z = pastecart (t0:real^1) (x0:real^N)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t0"; "x0"] THEN REWRITE_TAC[PASTECART_FST_SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval[t0 - lift r,t0 + lift r] PCROSS cball(x0:real^N,r) SUBSET
    (K':real^(1,N)finite_sum->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `pastecart (t0:real^1) (x0:real^N)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PASTECART_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(t - t0:real^1) + norm(y - x0:real^N)` THEN
    REWRITE_TAC[NORM_PASTECART_LE] THEN
    SUBGOAL_THEN `norm(t - t0:real^1) <= r /\ norm(y - x0:real^N) <= r` MP_TAC THENL
     [UNDISCH_TAC `t IN interval[t0 - lift r,t0 + lift r]` THEN
      UNDISCH_TAC `y IN cball(x0:real^N,r)` THEN
      REWRITE_TAC[IN_INTERVAL_1; IN_CBALL; NORM_1; DROP_SUB; DROP_ADD;
                  LIFT_DROP; dist] THEN
      CONV_TAC NORM_ARITH;
      EXPAND_TAC "r" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`;
                 `interval[t0 - lift r,t0 + lift r]`; `cball(x0:real^N,r)`;
                 `B:real`] ODE_BOX_EXTENSION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; CONVEX_CBALL; COMPACT_CBALL;
                INTERVAL_EQ_EMPTY_1; CBALL_EQ_EMPTY; DROP_ADD; DROP_SUB;
                LIFT_DROP] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_MESON_TAC[SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^(1,N)finite_sum->real^N`
      STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`(:real^(1,N)finite_sum)`; `g:real^(1,N)finite_sum->real^N`;
                 `t0:real^1`; `x0:real^N`; `e:real`; `r:real`; `B:real`; `c:real`]
         ODE_PICARD_LINDELOF_TWO_SIDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `v:real^N`; `w:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `pastecart (t:real^1) (v:real^N) IN
        interval[t0 - lift r,t0 + lift r] PCROSS cball(x0,r) /\
      pastecart t w IN interval[t0 - lift r,t0 + lift r] PCROSS cball(x0,r)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `t IN interval[t0 - lift e,t0 + lift e]` THEN
      UNDISCH_TAC `e <= r` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `u:real^1->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))] THEN
  SUBGOAL_THEN
   `!t. t IN interval[t0 - lift e,t0 + lift e]
        ==> pastecart t ((u:real^1->real^N) t) IN
            interval[t0 - lift r,t0 + lift r] PCROSS cball(x0,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `t IN interval[t0 - lift e,t0 + lift e]` THEN
      UNDISCH_TAC `e <= r` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
      [`u:real^1->real^N`;
       `\t. (g:real^(1,N)finite_sum->real^N) (pastecart t ((u:real^1->real^N) t))`;
       `interval[t0 - lift e,t0 + lift e]`; `B:real`]
      VECTOR_DIFFERENTIABLE_BOUND) THEN
    ASM_SIMP_TAC[CONVEX_INTERVAL] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `t0:real^1`]) THEN
    SUBGOAL_THEN `t0 IN interval[t0 - lift e,t0 + lift e]` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; DROP_ADD; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN
    SUBGOAL_THEN `norm(t - t0:real^1) <= e` MP_TAC THENL
     [UNDISCH_TAC `t IN interval[t0 - lift e,t0 + lift e]` THEN
      REWRITE_TAC[IN_INTERVAL_1; NORM_1; DROP_SUB; DROP_ADD; LIFT_DROP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `B * norm(t - t0:real^1) <= B * e` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`x0:real^N`; `(u:real^1->real^N) t`] NORM_SUB) THEN
    UNDISCH_TAC `B * e < r` THEN REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `u:real^1->real^N` THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[ode_solution; IS_INTERVAL_INTERVAL] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `pastecart (t:real^1) ((u:real^1->real^N) t) IN
    interval[t0 - lift r,t0 + lift r] PCROSS cball(x0,r)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:real^(1,N)finite_sum->real^N)(pastecart t (u t)) =
    g(pastecart t ((u:real^1->real^N) t))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Gronwall inequalities in derivative form; uniqueness of solutions.        *)
(* ------------------------------------------------------------------------- *)

let ODE_GRONWALL_REAL_FORWARD = prove
 (`!(e:real->real) e' c s a.
        is_realinterval s /\ a IN s /\
        (!x. x IN s ==> (e has_real_derivative e' x) (atreal x within s) /\
                        e' x <= c * e x)
        ==> !x. x IN s /\ a <= x ==> e x <= e a * exp(c * (x - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\y. --((e:real->real) y * exp(--(c * (y - a))))`;
    `\y. (c * (e:real->real) y - e' y) * exp(--(c * (y - a)))`;
    `s:real->bool`; `a:real`; `x:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real` THEN DISCH_TAC THENL
     [SUBGOAL_THEN
       `((\y. exp(--(c * (y - a)))) has_real_derivative
         (--c * exp(--(c * (y - a))))) (atreal y within s)` ASSUME_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL
       [`e:real->real`; `(e':real->real) y`; `\y. exp(--(c * (y - a)))`;
        `--c * exp(--(c * (y - a)))`; `y:real`; `s:real->bool`]
       HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP HAS_REAL_DERIVATIVE_NEG) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RING;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_SIMP_TAC[REAL_SUB_LE]];
    BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0;
                REAL_MUL_RID; REAL_LE_NEG2] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(e:real->real) x = (e x * exp(--(c * (x - a)))) * exp(c * (x - a))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_LINV;
                  REAL_EXP_0; REAL_MUL_RID];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]]);;

let ODE_GRONWALL_REAL_BACKWARD = prove
 (`!(e:real->real) e' c s a.
        is_realinterval s /\ a IN s /\
        (!x. x IN s ==> (e has_real_derivative e' x) (atreal x within s) /\
                        --(c * e x) <= e' x)
        ==> !x. x IN s /\ x <= a ==> e x <= e a * exp(c * (a - x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\y. (e:real->real) y * exp(c * (y - a))`;
    `\y. (e' y + c * (e:real->real) y) * exp(c * (y - a))`;
    `s:real->bool`; `x:real`; `a:real`] HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real` THEN DISCH_TAC THENL
     [SUBGOAL_THEN
       `((\y. exp(c * (y - a))) has_real_derivative
         (c * exp(c * (y - a)))) (atreal y within s)` ASSUME_TAC THENL
       [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL
       [`e:real->real`; `(e':real->real) y`; `\y. exp(c * (y - a))`;
        `c * exp(c * (y - a))`; `y:real`; `s:real->bool`]
       HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
      ASM_SIMP_TAC[] THEN
      DISCH_THEN(MP_TAC o BETA_RULE) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC REAL_RING;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(e:real->real) x = (e x * exp(c * (x - a))) * exp(c * (a - x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
      REWRITE_TAC[REAL_ARITH `c * (x - a) + c * (a - x) = &0`] THEN
      REWRITE_TAC[REAL_EXP_0; REAL_MUL_RID];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]]);;

(* From derivatives of lifted functions on real^1 to real derivatives. *)

let ODE_HAS_REAL_DERIVATIVE_OF_VECTOR = prove
 (`!(e:real^1->real) e' J t.
        ((\t. lift(e t)) has_vector_derivative lift e') (at t within J)
        ==> ((e o lift) has_real_derivative e') (atreal (drop t) within IMAGE drop J)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; GSYM IMAGE_o] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP; IMAGE_ID; ETA_AX]);;

let ODE_GRONWALL_DERIV = prove
 (`!(e:real^1->real) e' c J t0.
        is_interval J /\ t0 IN J /\
        (!t. t IN J
             ==> ((\t. lift(e t)) has_vector_derivative lift(e' t))
                 (at t within J) /\
                 abs(e' t) <= c * e t)
        ==> !t. t IN J ==> e t <= e t0 * exp(c * abs(drop t - drop t0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `is_realinterval(IMAGE drop J)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IS_REALINTERVAL_IS_INTERVAL; GSYM IMAGE_o; IMAGE_LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN IMAGE drop J
        ==> (((e:real^1->real) o lift) has_real_derivative ((e' o lift) x))
            (atreal x within IMAGE drop J) /\
            abs((e' o lift) x) <= c * (e o lift) x`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; o_THM; LIFT_DROP] THEN
    ASM_SIMP_TAC[ODE_HAS_REAL_DERIVATIVE_OF_VECTOR];
    ALL_TAC] THEN
  ASM_CASES_TAC `drop t0 <= drop t` THENL
   [MP_TAC(ISPECL [`(e:real^1->real) o lift`; `(e':real^1->real) o lift`; `c:real`;
                   `IMAGE drop J`; `drop t0`] ODE_GRONWALL_REAL_FORWARD) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[REAL_ABS_LE; REAL_LE_TRANS];
      DISCH_THEN(MP_TAC o SPEC `drop t`)] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; o_THM; LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(e:real^1->real) o lift`; `(e':real^1->real) o lift`; `c:real`;
                   `IMAGE drop J`; `drop t0`] ODE_GRONWALL_REAL_BACKWARD) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_SIMP_TAC[] THEN
      REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `drop t`)] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; o_THM; LIFT_DROP] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b = c ==> a <= b ==> a <= c`) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC]);;

let ODE_SOLUTION_GRONWALL = prove
 (`!(f:real^(1,N)finite_sum->real^N) D S J u v t0 L.
    ode_solution f D J u /\ ode_solution f D J v /\ t0 IN J /\ &0 <= L /\
    (!t x y. pastecart t x IN S /\ pastecart t y IN S
             ==> norm(f(pastecart t x) - f(pastecart t y)) <= L * norm(x - y)) /\
    (!t. t IN J ==> pastecart t (u t) IN S /\ pastecart t (v t) IN S)
    ==> !t. t IN J
            ==> norm(u t - v t)
                <= norm(u t0 - v t0) * exp(L * abs(drop t - drop t0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ode_solution] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. ((u:real^1->real^N) t - v t) dot (u t - v t)`;
    `\t. &2 * (((u:real^1->real^N) t - v t) dot
               ((f:real^(1,N)finite_sum->real^N)(pastecart t (u t)) -
                f(pastecart t (v t))))`;
    `&2 * L`; `J:real^1->bool`; `t0:real^1`] ODE_GRONWALL_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\x y:real^N. lift(x dot y)`;
        `\t. (u:real^1->real^N) t - v t`; `\t. (u:real^1->real^N) t - v t`;
        `(f:real^(1,N)finite_sum->real^N)(pastecart t (u t)) - f(pastecart t (v t))`;
        `(f:real^(1,N)finite_sum->real^N)(pastecart t (u t)) - f(pastecart t (v t))`;
        `t:real^1`; `J:real^1->bool`] HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
      REWRITE_TAC[BILINEAR_DOT] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ] THEN
      REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((u:real^1->real^N) t - v t) *
                  norm((f:real^(1,N)finite_sum->real^N)(pastecart t (u t)) -
                       f(pastecart t (v t)))` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      REWRITE_TAC[GSYM NORM_POW_2; REAL_POW_2] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `L * a * a = a * L * a`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN
   `exp((&2 * L) * abs(drop t - drop t0)) = exp(L * abs(drop t - drop t0)) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N; REAL_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE; REAL_EXP_POS_LE]);;

(* Local uniqueness near a common value, and uniqueness on intervals. *)

let ODE_SOLUTION_UNIQUE_LOCAL = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J u v t1.
        f continuous_on D /\ ode_locally_lipschitz f D /\
        ode_solution f D J u /\ ode_solution f D J v /\
        t1 IN J /\ u t1 = v t1
        ==> ?d. &0 < d /\ !t. t IN J /\ dist(t,t1) < d ==> u t = v t`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(u:real^1->real^N) t1 = v t1` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `J:real^1->bool`; `u:real^1->real^N`] ODE_SOLUTION_CONTINUOUS) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `J:real^1->bool`; `v:real^1->real^N`] ODE_SOLUTION_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(GEN_REWRITE_RULE I [ode_solution]
    (ASSUME `ode_solution (f:real^(1,N)finite_sum->real^N) D J u`)) THEN
  MP_TAC(GEN_REWRITE_RULE I [ode_solution]
    (ASSUME `ode_solution (f:real^(1,N)finite_sum->real^N) D J v`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "u")) THEN
  SUBGOAL_THEN `pastecart (t1:real^1) ((u:real^1->real^N) t1) IN D` ASSUME_TAC
  THENL [USE_THEN "u" (MP_TAC o SPEC `t1:real^1`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `pastecart (t1:real^1) ((u:real^1->real^N) t1)` o
    GEN_REWRITE_RULE I [ode_locally_lipschitz]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(\t. pastecart t ((u:real^1->real^N) t)) continuous (at t1 within J) /\
    (\t. pastecart t ((v:real^1->real^N) t)) continuous (at t1 within J)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THENL
     [MP_TAC(SPEC `t1:real^1` (GEN_REWRITE_RULE I [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]
        (ASSUME `(u:real^1->real^N) continuous_on J`)));
      MP_TAC(SPEC `t1:real^1` (GEN_REWRITE_RULE I [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]
        (ASSUME `(v:real^1->real^N) continuous_on J`)))] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_within] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `r:real`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_interval(J INTER ball(t1:real^1,min d1 d2))` ASSUME_TAC THENL
   [MATCH_MP_TAC IS_INTERVAL_INTER THEN
    ASM_REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
    `D INTER ball(pastecart (t1:real^1) ((u:real^1->real^N) t1),r)`;
    `J INTER ball(t1:real^1,min d1 d2)`; `u:real^1->real^N`; `v:real^1->real^N`;
    `t1:real^1`; `abs L`] ODE_SOLUTION_GRONWALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN EXISTS_TAC `J:real^1->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN EXISTS_TAC `J:real^1->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; REAL_LT_MIN];
      REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real^1`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `L * norm(x - y:real^N)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        REAL_ARITH_TAC];
      X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_INTER; IN_BALL; REAL_LT_MIN] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `dist(s:real^1,t1) < d1 /\ dist(s,t1) < d2` STRIP_ASSUME_TAC
      THENL [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "u" (MP_TAC o SPEC `s:real^1`) THEN
      USE_THEN "v" (MP_TAC o SPEC `s:real^1`) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_BALL; VECTOR_SUB_REFL; NORM_0; REAL_MUL_LZERO] THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  REWRITE_TAC[NORM_LE_0; VECTOR_SUB_EQ]);;

let ODE_SOLUTION_UNIQUE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J J' u v t0.
    open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\
    ode_solution f D J u /\ ode_solution f D J' v /\
    t0 IN J /\ t0 IN J' /\ u t0 = v t0
    ==> !t. t IN J INTER J' ==> u t = v t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `is_interval(J INTER J':real^1->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC IS_INTERVAL_INTER THEN ASM_MESON_TAC[ode_solution]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_solution (f:real^(1,N)finite_sum->real^N) D (J INTER J') u /\
    ode_solution f D (J INTER J') v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN
    ASM_MESON_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPEC `J INTER J':real^1->bool` CONNECTED_CLOPEN) THEN
  ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1] THEN
  DISCH_THEN(MP_TAC o SPEC
   `{t | t IN J INTER J' /\ (u:real^1->real^N) t = v t}`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_CONTAINS_BALL; SUBSET_RESTRICT] THEN
      X_GEN_TAC `t1:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                     `J INTER J':real^1->bool`; `u:real^1->real^N`;
                     `v:real^1->real^N`; `t1:real^1`] ODE_SOLUTION_UNIQUE_LOCAL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
      ASM_MESON_TAC[DIST_SYM; IN_INTER];
      SUBGOAL_THEN
       `{t | t IN J INTER J' /\ (u:real^1->real^N) t = v t} =
        {t | t IN J INTER J' /\ (\t. u t - v t) t IN {vec 0}}`
      SUBST1_TAC THENL
       [REWRITE_TAC[IN_SING; VECTOR_SUB_EQ]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
      REWRITE_TAC[CLOSED_SING] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      ASM_MESON_TAC[ODE_SOLUTION_CONTINUOUS; ETA_AX]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN(MP_TAC o SPEC `t0:real^1`) THEN ASM_REWRITE_TAC[IN_INTER];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Maximal solutions: extension, openness of the maximal interval, the       *)
(* maximal solution, its uniqueness and the cocycle law.                     *)
(* ------------------------------------------------------------------------- *)

let ODE_SOLUTION_EXTEND = prove
 (`!(f:real^(1,N)finite_sum->real^N) D J u t.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\
        ode_solution f D J u /\ t IN J
        ==> ?e J' u'. &0 < e /\ J SUBSET J' /\
                      interval[t - lift e,t + lift e] SUBSET J' /\
                      ode_solution f D J' u' /\
                      !s. s IN J ==> u' s = u s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (t:real^1) ((u:real^1->real^N) t) IN D` ASSUME_TAC THENL
   [ASM_MESON_TAC[ode_solution]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `{pastecart (t:real^1) ((u:real^1->real^N) t)}`]
         ODE_LOCAL_EXISTENCE_UNIFORM) THEN
  ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET; IN_SING; FORALL_UNWIND_THM2;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `v:real^1->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `I1 = interval[t - lift e,t + lift e]` THEN
  SUBGOAL_THEN `(t:real^1) IN I1` ASSUME_TAC THENL
   [EXPAND_TAC "I1" THEN REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN J INTER I1 ==> (u:real^1->real^N) s = v s` ASSUME_TAC THENL
   [MATCH_MP_TAC ODE_SOLUTION_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`f:real^(1,N)finite_sum->real^N`;
                          `D:real^(1,N)finite_sum->bool`; `t:real^1`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `J UNION I1:real^1->bool`;
                        `\s. if s IN J then (u:real^1->real^N) s else v s`] THEN
  ASM_REWRITE_TAC[SUBSET_UNION] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ODE_SOLUTION_GLUE THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    SIMP_TAC[]]);;

let ODE_MAXINT_OPEN = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D
        ==> open(ode_maxint f D z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  X_GEN_TAC `t:real^1` THEN REWRITE_TAC[ODE_IN_MAXINT] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:real^1->bool` (X_CHOOSE_THEN `u:real^1->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `J:real^1->bool`; `u:real^1->real^N`; `t:real^1`]
         ODE_SOLUTION_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `J':real^1->bool`
    (X_CHOOSE_THEN `u':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[SUBSET; ODE_IN_MAXINT] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`J':real^1->bool`; `u':real^1->real^N`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `interval[t - lift e,t + lift e] SUBSET (J':real^1->bool)` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `s IN ball(t:real^1,e)` THEN
  REWRITE_TAC[IN_BALL; IN_INTERVAL_1; DIST_REAL; GSYM drop; DROP_ADD; DROP_SUB;
              LIFT_DROP] THEN
  REAL_ARITH_TAC);;

let ODE_MAXINT_SOLUTION = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\ z IN D
        ==> ?w. w(fstcart z) = sndcart z /\
                ode_solution f D (ode_maxint f D z) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. ?J (u:real^1->real^N).
        t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z
        ==> fstcart z IN J /\ t IN J /\ u(fstcart z) = sndcart z /\
            ode_solution f D J u`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM; ODE_IN_MAXINT]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `JJ:real^1->real^1->bool`
    (X_CHOOSE_THEN `uu:real^1->real^1->real^N` (LABEL_TAC "ch"))) THEN
  SUBGOAL_THEN
   `!J u t. fstcart(z:real^(1,N)finite_sum) IN J /\ t IN J /\
            u(fstcart z) = sndcart z /\
            ode_solution (f:real^(1,N)finite_sum->real^N) D J u
            ==> (uu:real^1->real^1->real^N) t t = u t`
  (LABEL_TAC "P") THENL
   [MAP_EVERY X_GEN_TAC [`J:real^1->bool`; `u:real^1->real^N`; `t:real^1`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
    ASSUME_TAC THENL
     [REWRITE_TAC[ODE_IN_MAXINT] THEN
      MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `u:real^1->real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ch" (MP_TAC o C MATCH_MP
      (ASSUME `t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z`)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `(JJ:real^1->real^1->bool) t`; `J:real^1->bool`;
                   `(uu:real^1->real^1->real^N) t`; `u:real^1->real^N`;
                   `fstcart(z:real^(1,N)finite_sum)`] ODE_SOLUTION_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  EXISTS_TAC `\t. (uu:real^1->real^1->real^N) t t` THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN
                  ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
    ASSUME_TAC THENL [ASM_SIMP_TAC[ODE_MAXINT_INITIAL]; ALL_TAC] THEN
    USE_THEN "ch" (MP_TAC o C MATCH_MP (ASSUME
      `fstcart(z:real^(1,N)finite_sum) IN
       ode_maxint (f:real^(1,N)finite_sum->real^N) D z`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ode_solution; ODE_MAXINT_IS_INTERVAL] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  USE_THEN "ch" (MP_TAC o C MATCH_MP
    (ASSUME `t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `(JJ:real^1->real^1->bool) t`; `(uu:real^1->real^1->real^N) t`;
                 `t:real^1`] ODE_SOLUTION_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `J':real^1->bool`
    (X_CHOOSE_THEN `u':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `fstcart(z:real^(1,N)finite_sum) IN J' /\ (t:real^1) IN J'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(JJ:real^1->real^1->bool) t SUBSET J'` THEN
    UNDISCH_TAC `fstcart(z:real^(1,N)finite_sum) IN (JJ:real^1->real^1->bool) t` THEN
    UNDISCH_TAC `(t:real^1) IN (JJ:real^1->real^1->bool) t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u':real^1->real^N)(fstcart z) = sndcart(z:real^(1,N)finite_sum)`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `fstcart(z:real^(1,N)finite_sum)` (ASSUME
      `!s. s IN (JJ:real^1->real^1->bool) t
           ==> (u':real^1->real^N) s = uu t s`)) THEN
    REWRITE_TAC[ASSUME
      `fstcart(z:real^(1,N)finite_sum) IN (JJ:real^1->real^1->bool) t`] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN J' ==> (uu:real^1->real^1->real^N) s s = u' s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "P" MATCH_MP_TAC THEN
    EXISTS_TAC `J':real^1->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `J' SUBSET ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; ODE_IN_MAXINT] THEN X_GEN_TAC `s:real^1` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`J':real^1->bool`; `u':real^1->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `t:real^1` (CONJUNCT2(GEN_REWRITE_RULE I [ode_solution]
    (ASSUME `ode_solution (f:real^(1,N)finite_sum->real^N) D J' u'`)))) THEN
  REWRITE_TAC[ASSUME `(t:real^1) IN J'`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(uu:real^1->real^1->real^N) t t = u' t` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((\t. (uu:real^1->real^1->real^N) t t) has_vector_derivative
     (f:real^(1,N)finite_sum->real^N)(pastecart t (u' t))) (at t within J')`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC [`u':real^1->real^N`; `&1`] THEN
    ASM_SIMP_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_WITHIN_LOCAL THEN
  REWRITE_TAC[EVENTUALLY_AT] THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^1) IN J'` ASSUME_TAC THENL
   [UNDISCH_TAC `interval[t - lift e,t + lift e] SUBSET (J':real^1->bool)` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `dist(s:real^1,t) < e` THEN
    REWRITE_TAC[IN_INTERVAL_1; DIST_REAL; GSYM drop; DROP_ADD; DROP_SUB;
                LIFT_DROP] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `J' SUBSET ode_maxint (f:real^(1,N)finite_sum->real^N) D z` THEN
    UNDISCH_TAC `(s:real^1) IN J'` THEN SET_TAC[]]);;

let ODE_FLOW_SOLUTION = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\ z IN D
        ==> ode_flow f D (fstcart z) z = sndcart z /\
            ode_solution f D (ode_maxint f D z) (\t. ode_flow f D t z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ODE_MAXINT_SOLUTION) THEN
  REWRITE_TAC[ode_flow] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[ETA_AX]);;

let ODE_MAXIMAL_SOLUTION = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z.
    open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\ z IN D
    ==> open(ode_maxint f D z) /\ is_interval(ode_maxint f D z) /\
        fstcart z IN ode_maxint f D z /\
        ode_flow f D (fstcart z) z = sndcart z /\
        ode_solution f D (ode_maxint f D z) (\t. ode_flow f D t z) /\
        !t. t IN ode_maxint f D z
            ==> pastecart t (ode_flow f D t z) IN D /\
                ((\s. ode_flow f D s z) has_vector_derivative
                 f(pastecart t (ode_flow f D t z))) (at t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ODE_MAXINT_OPEN; ODE_MAXINT_IS_INTERVAL; ODE_MAXINT_INITIAL] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) D
                   (ode_maxint f D z) (\t. ode_flow f D t z)` THEN
    REWRITE_TAC[ode_solution] THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `ode_maxint (f:real^(1,N)finite_sum->real^N) D z`;
                   `\s. ode_flow (f:real^(1,N)finite_sum->real^N) D s z`;
                   `t:real^1`] ODE_SOLUTION_AT) THEN
    ASM_SIMP_TAC[ODE_MAXINT_OPEN]]);;

let ODE_MAXIMAL_UNIQUE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z J u.
    open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\
    ode_solution f D J u /\ fstcart z IN J /\ u(fstcart z) = sndcart z
    ==> J SUBSET ode_maxint f D z /\
        !t. t IN J ==> u t = ode_flow f D t z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `J SUBSET ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; ODE_IN_MAXINT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^(1,N)finite_sum) IN D` ASSUME_TAC THENL
   [UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) D J u` THEN
    REWRITE_TAC[ode_solution] THEN
    DISCH_THEN(MP_TAC o SPEC `fstcart(z:real^(1,N)finite_sum)` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `J:real^1->bool`; `ode_maxint (f:real^(1,N)finite_sum->real^N) D z`;
                 `u:real^1->real^N`; `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z`;
                 `fstcart(z:real^(1,N)finite_sum)`] ODE_SOLUTION_UNIQUE) THEN
  ASM_SIMP_TAC[ODE_MAXINT_INITIAL] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN
  REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]);;

let ODE_FLOW_COCYCLE = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z s.
    open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\
    z IN D /\ s IN ode_maxint f D z
    ==> pastecart s (ode_flow f D s z) IN D /\
        ode_maxint f D (pastecart s (ode_flow f D s z)) = ode_maxint f D z /\
        !t. t IN ode_maxint f D z
            ==> ode_flow f D t (pastecart s (ode_flow f D s z)) =
                ode_flow f D t z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pastecart s (ode_flow (f:real^(1,N)finite_sum->real^N) D s z) IN D`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) D
                   (ode_maxint f D z) (\t. ode_flow f D t z)` THEN
    REWRITE_TAC[ode_solution] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart s (ode_flow (f:real^(1,N)finite_sum->real^N) D s z)`;
                 `ode_maxint (f:real^(1,N)finite_sum->real^N) D z`;
                 `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z`]
         ODE_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq")) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart s (ode_flow (f:real^(1,N)finite_sum->real^N) D s z)`]
         ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z:real^(1,N)finite_sum`;
                 `ode_maxint (f:real^(1,N)finite_sum->real^N) D
                    (pastecart s (ode_flow f D s z))`;
                 `\t. ode_flow (f:real^(1,N)finite_sum->real^N) D t
                        (pastecart s (ode_flow f D s z))`]
         ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `fstcart(z:real^(1,N)finite_sum) IN
      ode_maxint (f:real^(1,N)finite_sum->real^N) D z`
    ASSUME_TAC THENL [ASM_SIMP_TAC[ODE_MAXINT_INITIAL]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "eq" (MP_TAC o C MATCH_MP (ASSUME
      `fstcart(z:real^(1,N)finite_sum) IN
       ode_maxint (f:real^(1,N)finite_sum->real^N) D z`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  USE_THEN "eq" (MP_TAC o C MATCH_MP (ASSUME
    `t IN ode_maxint (f:real^(1,N)finite_sum->real^N) D z`)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

