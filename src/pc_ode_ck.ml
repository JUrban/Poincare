(* ========================================================================= *)
(* pc_ode_ck: C^k and smooth dependence of the flow on initial data and     *)
(* parameters, by a type-stable induction on parametric problems.           *)
(* ========================================================================= *)

needs "src/pc_ode_c1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Calculus lemmas.                                                          *)
(* ------------------------------------------------------------------------- *)

(* A frechet derivative of a C^(SUC n) map applied along C^n maps is C^n.   *)

let ODE_CK_FRECHET_APPLY = prove
 (`!n s t (g:real^M->real^N) (p:real^P->real^M) (v:real^P->real^M).
        open s /\ open t /\ continuously_differentiable (SUC n) t g /\
        continuously_differentiable n s p /\ continuously_differentiable n s v /\
        IMAGE p s SUBSET t
        ==> continuously_differentiable n s
              (\w. frechet_derivative g (at (p w)) (v w))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC
   `\w. vsum(1..dimindex(:M))
            (\i. drop(lift((v:real^P->real^M) w$i)) %
                 frechet_derivative (g:real^M->real^N) (at (p w)) (basis i))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^P` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN
     `linear(frechet_derivative (g:real^M->real^N) (at ((p:real^P->real^M) w)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      SUBGOAL_THEN `(g:real^M->real^N) differentiable_on t` MP_TAC THENL
       [ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_DIFFERENTIABLE_ON]; ALL_TAC] THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MUL_DROP_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift((v:real^P->real^M) w$i)) = (\x:real^M. lift(x$i)) o v`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LINEAR_O THEN
    ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    SUBGOAL_THEN
     `(\w. frechet_derivative (g:real^M->real^N) (at ((p:real^P->real^M) w)) (basis i)) =
      (\x. frechet_derivative g (at x) (basis i)) o p`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `t:real^M->bool` THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_FRECHET]]);;

(* The graph of the solution of a parametric problem lies in D.             *)

let ODE_PARAM_SOL_GRAPH = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H t q.
    open D /\ continuously_differentiable 1 D g /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D) /\
    pastecart t q IN ode_param_dom g h D H
    ==> ode_flow (ode_param_field g) D t (pastecart (vec 0) (pastecart (h q) q)) =
        pastecart (ode_param_sol g h D (pastecart t q)) q /\
        pastecart t (pastecart (ode_param_sol g h D (pastecart t q)) q) IN D`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ODE_PARAM_DOM_IN; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q) IN D`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_PARAM_FIELD_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `vec 0:real^1`;
                 `(h:real^Q->real^N) q`; `q:real^Q`] ODE_FLOW_PARAM_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `ode_flow (ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)) D t
      (pastecart (vec 0) (pastecart ((h:real^Q->real^N) q) q)) =
    pastecart (ode_param_sol g h D (pastecart t q)) q`
  ASSUME_TAC THENL
   [REWRITE_TAC[ode_param_sol; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ASM_MESON_TAC[PASTECART_FST_SND];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`;
                 `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q)`]
         ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1` o last o CONJUNCTS) THEN
  ASM_SIMP_TAC[]);;

(* The time derivative of the solution of a parametric problem.            *)

let ODE_PARAM_DERIVATIVE_TIME = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H t q a.
    open D /\ open H /\
    continuously_differentiable 1 D g /\ continuously_differentiable 1 H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D) /\
    pastecart t q IN ode_param_dom g h D H
    ==> frechet_derivative (ode_param_sol g h D) (at (pastecart t q))
          (pastecart a (vec 0)) =
        drop a % g(pastecart t (pastecart (ode_param_sol g h D (pastecart t q)) q))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_PARAM_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP ODE_C1_FRECHET) THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (t:real^1) (q:real^Q)` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `DP = frechet_derivative
           (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D)
           (at (pastecart (t:real^1) (q:real^Q)))` THEN
  UNDISCH_TAC `pastecart (t:real^1) (q:real^Q) IN
               ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H` THEN
  REWRITE_TAC[ODE_PARAM_DOM_IN; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q) IN D`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `vec 0:real^1`;
                 `(h:real^Q->real^N) q`; `q:real^Q`] ODE_FLOW_PARAM_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN
  ASM_REWRITE_TAC[has_vector_derivative] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL
   [`\s:real^1. pastecart s (q:real^Q)`;
    `ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D`;
    `\s:real^1. pastecart s (vec 0:real^Q)`;
    `DP:real^(1,Q)finite_sum->real^N`; `t:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\s. ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D
           (pastecart s (q:real^Q))) =
    (\s. fstcart(ode_flow (ode_param_field g) D s
                   (pastecart (vec 0) (pastecart (h q) q))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; ode_param_sol; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D
           (pastecart s (q:real^Q))`;
    `\s:real^1. (DP:real^(1,Q)finite_sum->real^N) (pastecart s (vec 0))`;
    `\x:real^1. drop x %
       (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
         (pastecart t (pastecart (fstcart(ode_flow (ode_param_field g) D t
                                   (pastecart (vec 0) (pastecart (h q) q)))) q))`;
    `t:real^1`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `a:real^1`) THEN
  REWRITE_TAC[ode_param_sol; FSTCART_PASTECART; SNDCART_PASTECART]);;

(* ------------------------------------------------------------------------- *)
(* The derivative problem.  For a direction e of the parameter, the          *)
(* parameter derivative of the solution solves a parametric problem of the   *)
(* same type: y' = Dg(t, x(t,q), q)(0, (y, e)), y(0) = Dh(q) e.              *)
(* ------------------------------------------------------------------------- *)

let ode_dparam_field = new_definition
 `ode_dparam_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D
                   (e:real^Q) =
    \w:real^(1,(N,Q)finite_sum)finite_sum.
      frechet_derivative g
        (at (pastecart (fstcart w)
               (pastecart (ode_param_sol g h D (pastecart (fstcart w) (sndcart(sndcart w))))
                          (sndcart(sndcart w)))))
        (pastecart (vec 0) (pastecart (fstcart(sndcart w)) e))`;;

let ode_dparam_dom = new_definition
 `ode_dparam_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H =
    {w:real^(1,(N,Q)finite_sum)finite_sum |
       pastecart (fstcart w) (sndcart(sndcart w)) IN ode_param_dom g h D H}`;;

let ODE_DPARAM_DOM_IN = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H t y q.
        pastecart t (pastecart y q) IN ode_dparam_dom g h D H <=>
        pastecart t q IN ode_param_dom g h D H`,
  REWRITE_TAC[ode_dparam_dom; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART]);;

let ODE_LINEAR_SND_SND = prove
 (`linear(\w:real^(1,(N,Q)finite_sum)finite_sum. pastecart (fstcart w) (sndcart(sndcart w))) /\
   linear(\w:real^(1,(N,Q)finite_sum)finite_sum. sndcart(sndcart w)) /\
   linear(\w:real^(1,(N,Q)finite_sum)finite_sum. fstcart(sndcart w))`,
  REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
              PASTECART_ADD; GSYM PASTECART_CMUL]);;

let ODE_DPARAM_DOM_OPEN = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H.
    open D /\ open H /\
    continuously_differentiable 1 D g /\ continuously_differentiable 1 H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D)
    ==> open(ode_dparam_dom g h D H)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ode_dparam_dom] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[ODE_PARAM_C1; LINEAR_CONTINUOUS_AT; ODE_LINEAR_SND_SND]);;

(* Regularity of the derivative field.                                       *)

let ODE_DPARAM_FIELD_CK = prove
 (`!k (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H e.
    open D /\ open H /\
    continuously_differentiable (SUC(SUC k)) D g /\ continuously_differentiable 1 H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D) /\
    continuously_differentiable (SUC k) (ode_param_dom g h D H) (ode_param_sol g h D)
    ==> continuously_differentiable (SUC k) (ode_dparam_dom g h D H)
          (ode_dparam_field g h D e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 D (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN
    EXISTS_TAC `SUC(SUC k)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_DPARAM_DOM_OPEN) THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_PARAM_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ode_dparam_field] THEN
  MATCH_MP_TAC ODE_CK_FRECHET_APPLY THEN
  EXISTS_TAC `D:real^(1,(N,Q)finite_sum)finite_sum->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_FSTCART; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; ODE_LINEAR_SND_SND] THEN
    SUBGOAL_THEN
     `(\w:real^(1,(N,Q)finite_sum)finite_sum.
         ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D
           (pastecart (fstcart w) (sndcart(sndcart w)))) =
      ode_param_sol g h D o
      (\w:real^(1,(N,Q)finite_sum)finite_sum. pastecart (fstcart w) (sndcart(sndcart w)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H` THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; ODE_LINEAR_SND_SND] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ode_dparam_dom; IN_ELIM_THM];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_CONST;
                 CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; ODE_LINEAR_SND_SND];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; ode_dparam_dom; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^(1,(N,Q)finite_sum)finite_sum` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                   `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                   `fstcart(w:real^(1,(N,Q)finite_sum)finite_sum)`;
                   `sndcart(sndcart(w:real^(1,(N,Q)finite_sum)finite_sum))`]
           ODE_PARAM_SOL_GRAPH) THEN
    ASM_SIMP_TAC[]]);;

(* On each parameter slice the derivative problem is solved by the          *)
(* parameter derivative of the solution, on the same maximal interval.      *)

let ODE_DPARAM_SLICE = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H e q.
    open D /\ open H /\
    continuously_differentiable 2 D g /\ continuously_differentiable 1 H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D) /\ q IN H
    ==> ode_maxint (ode_param_field (ode_dparam_field g h D e)) (ode_dparam_dom g h D H)
          (pastecart (vec 0) (pastecart (frechet_derivative h (at q) e) q)) =
        ode_maxint (ode_param_field g) D (pastecart (vec 0) (pastecart (h q) q)) /\
        !s. s IN ode_maxint (ode_param_field g) D (pastecart (vec 0) (pastecart (h q) q))
            ==> ode_flow (ode_param_field (ode_dparam_field g h D e))
                  (ode_dparam_dom g h D H) s
                  (pastecart (vec 0) (pastecart (frechet_derivative h (at q) e) q)) =
                pastecart (frechet_derivative (ode_param_sol g h D) (at (pastecart s q))
                             (pastecart (vec 0) e)) q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 D (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN
    EXISTS_TAC `2` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_PARAM_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_DPARAM_DOM_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`0`; `g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                 `e:real^Q`] ODE_DPARAM_FIELD_CK) THEN
  NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `ge = ode_dparam_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D (e:real^Q)` THEN
  ABBREV_TAC
   `De = ode_dparam_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H` THEN
  MP_TAC(ISPECL [`ge:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                 `De:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_PARAM_FIELD_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`ode_param_field (ge:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                 `De:real^(1,(N,Q)finite_sum)finite_sum->bool`]
         ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q) IN D`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `J = ode_maxint (ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)) D
          (pastecart (vec 0) (pastecart ((h:real^Q->real^N) q) q))` THEN
  SUBGOAL_THEN
   `!s. pastecart s q IN
        ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H <=> s IN J`
  ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN ASM_REWRITE_TAC[ODE_PARAM_DOM_IN; FSTCART_PASTECART;
                                        SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(J:real^1->bool) /\ is_interval J /\ (vec 0:real^1) IN J`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[ODE_MAXINT_IS_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ODE_MAXINT_OPEN THEN
      MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                     `D:real^(1,(N,Q)finite_sum)finite_sum->bool`]
             ODE_C1_IMP_LOCALLY_LIPSCHITZ) THEN
      MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                     `D:real^(1,(N,Q)finite_sum)finite_sum->bool`] ODE_PARAM_FIELD_C1) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                     `D:real^(1,(N,Q)finite_sum)finite_sum->bool`;
                     `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q)`]
             ODE_MAXINT_INITIAL) THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pastecart (vec 0:real^1) (pastecart (frechet_derivative (h:real^Q->real^N) (at q) e) q)
    IN De`
  ASSUME_TAC THENL
   [EXPAND_TAC "De" THEN ASM_REWRITE_TAC[ODE_DPARAM_DOM_IN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                 `q:real^Q`; `e:real^Q`] ODE_PARAM_VARIATIONAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "var")) THEN
  MP_TAC(ISPECL
   [`ode_param_field (ge:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
    `De:real^(1,(N,Q)finite_sum)finite_sum->bool`;
    `pastecart (vec 0:real^1) (pastecart (frechet_derivative (h:real^Q->real^N) (at q) e) q)`;
    `J:real^1->bool`;
    `\s. pastecart (frechet_derivative
                      (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D)
                      (at (pastecart s q)) (pastecart (vec 0) e)) (q:real^Q)`]
   ODE_MAXIMAL_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[ode_solution] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    EXPAND_TAC "De" THEN ASM_REWRITE_TAC[ODE_DPARAM_DOM_IN] THEN
    REWRITE_TAC[ode_param_field] THEN
    MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_PASTECART_CONST THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    EXPAND_TAC "ge" THEN
    REWRITE_TAC[ode_dparam_field; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REMOVE_THEN "var" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "feq")) THEN
  SUBGOAL_THEN
   `ode_maxint (ode_param_field (ge:real^(1,(N,Q)finite_sum)finite_sum->real^N)) De
      (pastecart (vec 0) (pastecart (frechet_derivative (h:real^Q->real^N) (at q) e) q))
    SUBSET J`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`ode_param_field (ge:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
      `De:real^(1,(N,Q)finite_sum)finite_sum->bool`;
      `pastecart (vec 0:real^1)
         (pastecart (frechet_derivative (h:real^Q->real^N) (at q) e) q)`]
     ODE_MAXIMAL_SOLUTION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^1` o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`ge:real^(1,(N,Q)finite_sum)finite_sum->real^N`;
                   `De:real^(1,(N,Q)finite_sum)finite_sum->bool`; `vec 0:real^1`;
                   `frechet_derivative (h:real^Q->real^N) (at q) e`; `q:real^Q`]
           ODE_FLOW_PARAM_SOLUTION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real^1`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM PASTECART_FST_SND] THEN
    EXPAND_TAC "De" THEN ASM_REWRITE_TAC[ODE_DPARAM_DOM_IN];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_ANTISYM]; ALL_TAC] THEN
  X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
  REMOVE_THEN "feq" (MP_TAC o SPEC `s:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let ODE_DPARAM_IDENT = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H e.
    open D /\ open H /\
    continuously_differentiable 2 D g /\ continuously_differentiable 1 H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D)
    ==> (!q. q IN H
             ==> pastecart (vec 0) (pastecart (frechet_derivative h (at q) e) q) IN
                 ode_dparam_dom g h D H) /\
        ode_param_dom (ode_dparam_field g h D e) (\q. frechet_derivative h (at q) e)
                      (ode_dparam_dom g h D H) H = ode_param_dom g h D H /\
        (!w. w IN ode_param_dom g h D H
             ==> ode_param_sol (ode_dparam_field g h D e)
                   (\q. frechet_derivative h (at q) e) (ode_dparam_dom g h D H) w =
                 frechet_derivative (ode_param_sol g h D) (at w) (pastecart (vec 0) e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `q:real^Q` THEN DISCH_TAC THEN
    REWRITE_TAC[ODE_DPARAM_DOM_IN; ODE_PARAM_DOM_IN; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)`;
                   `D:real^(1,(N,Q)finite_sum)finite_sum->bool`;
                   `pastecart (vec 0:real^1) (pastecart ((h:real^Q->real^N) q) q)`]
           ODE_MAXINT_INITIAL) THEN
    ASM_SIMP_TAC[FSTCART_PASTECART];
    REWRITE_TAC[EXTENSION; ODE_PARAM_DOM_IN] THEN
    X_GEN_TAC `w:real^(1,Q)finite_sum` THEN
    ASM_CASES_TAC `sndcart(w:real^(1,Q)finite_sum) IN H` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                   `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                   `e:real^Q`; `sndcart(w:real^(1,Q)finite_sum)`] ODE_DPARAM_SLICE) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^(1,Q)finite_sum` THEN
    REWRITE_TAC[ODE_PARAM_DOM_IN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                   `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                   `e:real^Q`; `sndcart(w:real^(1,Q)finite_sum)`] ODE_DPARAM_SLICE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `fstcart(w:real^(1,Q)finite_sum)` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[ode_param_sol; FSTCART_PASTECART]]);;

(* ------------------------------------------------------------------------- *)
(* The induction (ODE_PARAM_CK) and its smooth corollary.                   *)
(* ------------------------------------------------------------------------- *)

let ODE_PARAM_CK = prove
 (`!k (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H.
    open D /\ open H /\
    continuously_differentiable (SUC k) D g /\
    continuously_differentiable (SUC k) H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D)
    ==> continuously_differentiable (SUC k) (ode_param_dom g h D H)
          (ode_param_sol g h D)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[GSYM ONE] THEN MESON_TAC[ODE_PARAM_C1]; ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 D (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) /\
    continuously_differentiable 2 D g /\
    continuously_differentiable (SUC k) D g /\
    continuously_differentiable 1 H (h:real^Q->real^N) /\
    continuously_differentiable (SUC k) H h`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN
    EXISTS_TAC `SUC(SUC k)` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_PARAM_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable (SUC k)
      (ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H)
      (ode_param_sol g h D)`
  ASSUME_TAC THENL
   [USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D`;
                 `ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H`]
         ODE_C1_FRECHET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "hd") ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!e. continuously_differentiable (SUC k)
          (ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H)
          (\w. frechet_derivative (ode_param_sol g h D) (at w) (pastecart (vec 0) e))`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^Q` THEN
    MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                   `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                   `e:real^Q`] ODE_DPARAM_IDENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "deq")
      ASSUME_TAC)) THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC
     `ode_param_sol (ode_dparam_field (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D e)
                    (\q. frechet_derivative (h:real^Q->real^N) (at q) e)
                    (ode_dparam_dom g h D H)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "deq" (SUBST1_TAC o SYM) THEN
    USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ODE_DPARAM_DOM_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ODE_DPARAM_FIELD_CK THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_FRECHET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. continuously_differentiable (SUC k)
          (ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H)
          (\w. frechet_derivative (ode_param_sol g h D) (at w) (pastecart a (vec 0)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^1` THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
    EXISTS_TAC
     `\w. drop a % (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
                     (pastecart (fstcart w) (pastecart (ode_param_sol g h D w) (sndcart w)))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `w:real^(1,Q)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                     `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                     `fstcart(w:real^(1,Q)finite_sum)`; `sndcart(w:real^(1,Q)finite_sum)`;
                     `a:real^1`] ODE_PARAM_DERIVATIVE_TIME) THEN
      ASM_REWRITE_TAC[PASTECART_FST_SND];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\w. (g:real^(1,(N,Q)finite_sum)finite_sum->real^N)
             (pastecart (fstcart w) (pastecart (ode_param_sol g h D w) (sndcart w)))) =
      g o (\w:real^(1,Q)finite_sum.
             pastecart (fstcart w) (pastecart (ode_param_sol g h D w) (sndcart w)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
    EXISTS_TAC `D:real^(1,(N,Q)finite_sum)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `w:real^(1,Q)finite_sum` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                     `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`;
                     `fstcart(w:real^(1,Q)finite_sum)`; `sndcart(w:real^(1,Q)finite_sum)`]
             ODE_PARAM_SOL_GRAPH) THEN
      ASM_REWRITE_TAC[PASTECART_FST_SND] THEN SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
      ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_FSTCART; ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_PASTECART_OPEN THEN
      ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`SUC k`;
                 `ode_param_dom (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D H`;
                 `ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D`]
         CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC
   `\w. frechet_derivative
          (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D) (at w)` THEN
  CONJ_TAC THENL [REWRITE_TAC[] THEN USE_THEN "hd" ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `v:real^(1,Q)finite_sum` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC
   `\w. frechet_derivative
          (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D) (at w)
          (pastecart (fstcart v) (vec 0)) +
        frechet_derivative (ode_param_sol g h D) (at w) (pastecart (vec 0) (sndcart v))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(1,Q)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `linear(frechet_derivative
               (ode_param_sol (g:real^(1,(N,Q)finite_sum)finite_sum->real^N) h D) (at w))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN REWRITE_TAC[differentiable] THEN
      USE_THEN "hd" (fun th -> ASM_MESON_TAC[th]);
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM LINEAR_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID; PASTECART_FST_SND];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_ADD_OPEN THEN ASM_REWRITE_TAC[]]);;

let ODE_PARAM_SMOOTH = prove
 (`!(g:real^(1,(N,Q)finite_sum)finite_sum->real^N) (h:real^Q->real^N) D H.
    open D /\ open H /\ smooth_map_on D g /\ smooth_map_on H h /\
    (!q. q IN H ==> pastecart (vec 0) (pastecart (h q) q) IN D)
    ==> open(ode_param_dom g h D H) /\
        smooth_map_on (ode_param_dom g h D H) (ode_param_sol g h D)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_map_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^(1,(N,Q)finite_sum)finite_sum->real^N`; `h:real^Q->real^N`;
                 `D:real^(1,(N,Q)finite_sum)finite_sum->bool`; `H:real^Q->bool`]
         ODE_PARAM_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON];
    MATCH_MP_TAC ODE_PARAM_CK THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C^k and smooth dependence of the flow with variable initial time         *)
(* (ODE_FLOW_CK, ODE_FLOW_SMOOTH) and of the augmented parametric flow      *)
(* (ODE_FLOW_PARAM_SMOOTH).                                                 *)
(* ------------------------------------------------------------------------- *)

let ODE_TRANSLATE_SETUP_CK = prove
 (`!n (f:real^(1,N)finite_sum->real^N) D.
    open D /\ continuously_differentiable n D f
    ==> continuously_differentiable n
          {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
                pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                          (fstcart(sndcart w)) IN D}
          (\w. f(pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                           (fstcart(sndcart w))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `L = \w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
          pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w))` THEN
  SUBGOAL_THEN
   `linear(L:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^(1,N)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
       pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)) IN D} =
    {w | (L:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^(1,N)finite_sum) w
         IN D} /\
    (\w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
       (f:real^(1,N)finite_sum->real^N)
         (pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)))) =
    f o L`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `open {w | (L:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->
                            real^(1,N)finite_sum) w IN D}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM]);;

let ODE_FLOW_CK = prove
 (`!k (f:real^(1,N)finite_sum->real^N) D.
    open D /\ continuously_differentiable (SUC k) D f
    ==> continuously_differentiable (SUC k) (ode_domain f D)
          (\w. ode_flow f D (fstcart w) (sndcart w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 D (f:real^(1,N)finite_sum->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN
    EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC k`; `f:real^(1,N)finite_sum->real^N`;
                 `D:real^(1,N)finite_sum->bool`] ODE_TRANSLATE_SETUP_CK) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_TRANSLATE_SETUP) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_AS_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `D' = {w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum |
            pastecart (fstcart(sndcart(sndcart w)) + fstcart w)
                      (fstcart(sndcart w)) IN D}` THEN
  ABBREV_TAC
   `g = \w:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum.
          (f:real^(1,N)finite_sum->real^N)
            (pastecart (fstcart(sndcart(sndcart w)) + fstcart w) (fstcart(sndcart w)))` THEN
  DISCH_THEN(LABEL_TAC "ap") THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!q. q IN D
        ==> pastecart (vec 0:real^1) (pastecart (sndcart q) q) IN
            (D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real^(1,N)finite_sum` THEN DISCH_TAC THEN EXPAND_TAC "D'" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                    VECTOR_ADD_RID; PASTECART_FST_SND];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `sndcart:real^(1,N)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
                 `D:real^(1,N)finite_sum->bool`] ODE_PARAM_C1) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`;
                 `g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N`;
                 `sndcart:real^(1,N)finite_sum->real^N`;
                 `D':real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->bool`;
                 `D:real^(1,N)finite_sum->bool`] ODE_PARAM_CK) THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_SNDCART] THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `T0 = \w:real^(1,(1,N)finite_sum)finite_sum.
           pastecart (fstcart w - fstcart(sndcart w)) (sndcart w)` THEN
  SUBGOAL_THEN
   `linear(T0:real^(1,(1,N)finite_sum)finite_sum->real^(1,(1,N)finite_sum)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN
    REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                PASTECART_ADD; GSYM PASTECART_CMUL; PASTECART_INJ] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN ode_domain (f:real^(1,N)finite_sum->real^N) D
        ==> (T0:real^(1,(1,N)finite_sum)finite_sum->real^(1,(1,N)finite_sum)finite_sum) w
            IN ode_param_dom g sndcart D' D /\
            ode_flow f D (fstcart w) (sndcart w) = ode_param_sol g sndcart D' (T0 w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(1,(1,N)finite_sum)finite_sum` THEN
    REWRITE_TAC[ODE_IN_DOMAIN_ALT] THEN STRIP_TAC THEN EXPAND_TAC "T0" THEN
    REWRITE_TAC[] THEN
    REMOVE_THEN "ap" (MP_TAC o SPECL [`fstcart(w:real^(1,(1,N)finite_sum)finite_sum)`;
                                      `sndcart(w:real^(1,(1,N)finite_sum)finite_sum)`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_EQ_OPEN THEN
  EXISTS_TAC
   `ode_param_sol (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N) sndcart D' o
    (T0:real^(1,(1,N)finite_sum)finite_sum->real^(1,(1,N)finite_sum)finite_sum)` THEN
  ASM_SIMP_TAC[o_THM] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_COMPOSE_OPEN THEN
  EXISTS_TAC
   `ode_param_dom (g:real^(1,(N,(1,N)finite_sum)finite_sum)finite_sum->real^N)
                  sndcart D' D` THEN
  ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]);;

let ODE_FLOW_SMOOTH = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
    open D /\ smooth_map_on D f
    ==> open(ode_domain f D) /\
        smooth_map_on (ode_domain f D)
          (\w. ode_flow f D (fstcart w) (sndcart w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[smooth_map_on] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`]
         ODE_FLOW_C1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    ASM_MESON_TAC[CONTINUOUSLY_DIFFERENTIABLE_IMP_CONTINUOUS_ON];
    MATCH_MP_TAC ODE_FLOW_CK THEN ASM_REWRITE_TAC[]]);;

let ODE_FLOW_PARAM_SMOOTH = prove
 (`!(g:real^(1,(N,P)finite_sum)finite_sum->real^N) D.
    open D /\ smooth_map_on D g
    ==> open(ode_domain (ode_param_field g) D) /\
        smooth_map_on (ode_domain (ode_param_field g) D)
          (\w. fstcart(ode_flow (ode_param_field g) D (fstcart w) (sndcart w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on D (ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N))`
  ASSUME_TAC THENL
   [REWRITE_TAC[ode_param_field] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N)`;
                 `D:real^(1,(N,P)finite_sum)finite_sum->bool`] ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\w. fstcart(ode_flow (ode_param_field (g:real^(1,(N,P)finite_sum)finite_sum->real^N))
                   D (fstcart w) (sndcart w))) =
    (fstcart:real^(N,P)finite_sum->real^N) o
    (\w. ode_flow (ode_param_field g) D (fstcart w) (sndcart w))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[LINEAR_FSTCART]);;

