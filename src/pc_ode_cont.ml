(* ========================================================================= *)
(* pc_ode_cont: continuous (Lipschitz) dependence on initial data and the    *)
(* openness of the flow domain.                                              *)
(* ========================================================================= *)

needs "src/pc_ode_global.ml";;

prioritize_real();;
type_invention_error := true;;

(* The modified field: f composed with a retraction onto a compact tube     *)
(* around a solution curve over interval[a,b].                               *)

let ODE_TUBE_RETRACTION = prove
 (`!(u:real^1->real^N) a b R.
        u continuous_on interval[a,b] /\ ~(interval[a,b] = {}) /\ &0 < R
        ==> ?P. P continuous_on (:real^(1,N)finite_sum) /\
                (!w. fstcart(P w) IN interval[a,b] /\
                     norm(sndcart(P w) - u(fstcart(P w))) <= R) /\
                (!t y. t IN interval[a,b] /\ norm(y - u t) <= R
                       ==> P(pastecart t y) = pastecart t y) /\
                (!t y y'. fstcart(P(pastecart t y)) = fstcart(P(pastecart t y')) /\
                          norm(sndcart(P(pastecart t y)) - sndcart(P(pastecart t y')))
                          <= norm(y - y'))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `tc = closest_point(interval[a:real^1,b])` THEN
  ABBREV_TAC `pr = closest_point(cball(vec 0:real^N,R))` THEN
  SUBGOAL_THEN
   `tc continuous_on (:real^1) /\
    (!t. (tc:real^1->real^1) t IN interval[a,b]) /\
    (!t. t IN interval[a,b] ==> (tc:real^1->real^1) t = t)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tc" THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CONVEX_INTERVAL; CLOSED_INTERVAL;
                 CLOSEST_POINT_IN_SET; CLOSEST_POINT_SELF];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cball(vec 0:real^N,R) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[CBALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `pr continuous_on (:real^N) /\
    (!y. norm((pr:real^N->real^N) y) <= R) /\
    (!y. norm y <= R ==> (pr:real^N->real^N) y = y) /\
    (!y y'. norm((pr:real^N->real^N) y - pr y') <= norm(y - y'))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "pr" THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CONTINUOUS_ON_CLOSEST_POINT; CONVEX_CBALL; CLOSED_CBALL];
      GEN_TAC THEN REWRITE_TAC[GSYM IN_CBALL_0] THEN
      ASM_SIMP_TAC[CLOSEST_POINT_IN_SET; CLOSED_CBALL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSEST_POINT_SELF THEN
      ASM_REWRITE_TAC[IN_CBALL_0];
      REPEAT GEN_TAC THEN REWRITE_TAC[GSYM dist] THEN
      MATCH_MP_TAC CLOSEST_POINT_LIPSCHITZ THEN
      ASM_REWRITE_TAC[CONVEX_CBALL; CLOSED_CBALL]];
    ALL_TAC] THEN
  EXISTS_TAC
   `\w:real^(1,N)finite_sum.
      pastecart ((tc:real^1->real^1)(fstcart w))
                ((u:real^1->real^N)(tc(fstcart w)) +
                 (pr:real^N->real^N)(sndcart w - u(tc(fstcart w))))` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_SIMP_TAC[VECTOR_ARITH `(u + p) - u:real^N = p`] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    SUBGOAL_THEN
     `(\w:real^(1,N)finite_sum. (u:real^1->real^N)((tc:real^1->real^1)(fstcart w)))
      continuous_on (:real^(1,N)finite_sum)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum. (u:real^1->real^N)((tc:real^1->real^1)(fstcart w))) =
        u o tc o fstcart` SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[a:real^1,b]` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum. (tc:real^1->real^1)(fstcart w)) = tc o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(\w:real^(1,N)finite_sum. (pr:real^N->real^N)
           (sndcart w - (u:real^1->real^N)((tc:real^1->real^1)(fstcart w)))) =
        pr o (\w. sndcart w - u(tc(fstcart w)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[PASTECART_INJ] THEN ASM_SIMP_TAC[] THEN
    VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_ARITH `(u + p) - (u + q):real^N = p - q`] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`; `y':real^N`] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`y - (u:real^1->real^N)((tc:real^1->real^1) t)`;
      `y' - (u:real^1->real^N)((tc:real^1->real^1) t)`]) THEN
    REWRITE_TAC[VECTOR_ARITH `(y - c) - (y' - c):real^N = y - y'`]]);;

let ODE_FLOW_STABILITY = prove
 (`!(f:real^(1,N)finite_sum->real^N) D z0 a b.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\ z0 IN D /\
        interval[a,b] SUBSET ode_maxint f D z0
        ==> ?R C. &0 < R /\ &0 < C /\
                  !z. fstcart z IN interval[a,b] /\
                      norm(sndcart z - ode_flow f D (fstcart z) z0) <= R
                      ==> z IN D /\ interval[a,b] SUBSET ode_maxint f D z /\
                          !t. t IN interval[a,b]
                              ==> norm(ode_flow f D t z - ode_flow f D t z0)
                                  <= C * norm(sndcart z -
                                              ode_flow f D (fstcart z) z0)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THENL
   [MAP_EVERY EXISTS_TAC [`&1`; `&1`] THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z0:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `u = \t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z0` THEN
  SUBGOAL_THEN `!t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z0 = u t`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_solution (f:real^(1,N)finite_sum->real^N) D (interval[a,b]) u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN
    EXISTS_TAC `ode_maxint (f:real^(1,N)finite_sum->real^N) D z0` THEN
    ASM_REWRITE_TAC[IS_INTERVAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^1->real^N) continuous_on interval[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[ODE_SOLUTION_CONTINUOUS]; ALL_TAC] THEN
  ABBREV_TAC `G = IMAGE (\t. pastecart t ((u:real^1->real^N) t)) (interval[a,b])` THEN
  SUBGOAL_THEN `compact(G:real^(1,N)finite_sum->bool) /\ G SUBSET D`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_ID; ETA_AX];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) D (interval[a,b]) u` THEN
      REWRITE_TAC[ode_solution] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^(1,N)finite_sum->bool`; `D:real^(1,N)finite_sum->bool`]
         ODE_COMPACT_THICKEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `R0:real` MP_TAC) THEN
  ABBREV_TAC
   `K' = {x + y | x IN G /\ y IN cball(vec 0:real^(1,N)finite_sum,R0)}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!t y. t IN interval[a,b] /\ norm(y - (u:real^1->real^N) t) <= R0
          ==> pastecart t y IN K'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`pastecart t ((u:real^1->real^N) t)`;
      `pastecart (vec 0:real^1) (y - (u:real^1->real^N) t)`] THEN
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_RID; IN_CBALL_0; NORM_PASTECART_0] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `u + (y - u):real^N = y`] THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `t:real^1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K':real^(1,N)finite_sum->bool`] ODE_COMPACT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `K':real^(1,N)finite_sum->bool`] ODE_LOCALLY_LIPSCHITZ_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:real^1->real^N`; `a:real^1`; `b:real^1`; `R0:real`]
         ODE_TUBE_RETRACTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^(1,N)finite_sum->real^(1,N)finite_sum`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!w. (P:real^(1,N)finite_sum->real^(1,N)finite_sum) w IN K'`
  ASSUME_TAC THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM PASTECART_FST_SND] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g = (f:real^(1,N)finite_sum->real^N) o
                  (P:real^(1,N)finite_sum->real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN
   `(g:real^(1,N)finite_sum->real^N) continuous_on (:real^(1,N)finite_sum) /\
    (!w. norm(g w) <= B) /\
    (!t x y. norm(g(pastecart t x) - g(pastecart t y)) <= L * norm(x - y)) /\
    (!t y. t IN interval[a,b] /\ norm(y - (u:real^1->real^N) t) <= R0
           ==> g(pastecart t y) = f(pastecart t y))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:real^(1,N)finite_sum->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^N`; `y:real^N`] THEN
      MP_TAC(SPECL [`t:real^1`; `x:real^N`; `y:real^N`] (ASSUME
       `!t y y'. fstcart((P:real^(1,N)finite_sum->real^(1,N)finite_sum)
                           (pastecart t y)) = fstcart(P(pastecart t y')) /\
                 norm(sndcart(P(pastecart t y)) - sndcart(P(pastecart t y')))
                 <= norm(y - y')`)) THEN
      ABBREV_TAC `p = (P:real^(1,N)finite_sum->real^(1,N)finite_sum)(pastecart t x)` THEN
      ABBREV_TAC `q = (P:real^(1,N)finite_sum->real^(1,N)finite_sum)(pastecart t y)` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^(1,N)finite_sum) IN K' /\ (q:real^(1,N)finite_sum) IN K'`
      STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN ASM_REWRITE_TAC[];
                              ALL_TAC] THEN
      SUBGOAL_THEN
       `pastecart (fstcart(p:real^(1,N)finite_sum)) (sndcart(q:real^(1,N)finite_sum)) = q`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
      MP_TAC(SPECL [`fstcart(p:real^(1,N)finite_sum)`; `sndcart(p:real^(1,N)finite_sum)`;
                    `sndcart(q:real^(1,N)finite_sum)`] (ASSUME
       `!t x y. pastecart t x IN K' /\ pastecart t y IN K'
                ==> norm((f:real^(1,N)finite_sum->real^N)(pastecart t x) -
                         f(pastecart t y)) <= L * norm(x - y)`)) THEN
      REWRITE_TAC[PASTECART_FST_SND; ASSUME
       `pastecart (fstcart(p:real^(1,N)finite_sum)) (sndcart(q:real^(1,N)finite_sum)) = q`;
       ASSUME `(p:real^(1,N)finite_sum) IN K'`; ASSUME `(q:real^(1,N)finite_sum) IN K'`] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_locally_lipschitz (g:real^(1,N)finite_sum->real^N)
                          ((:real^1) PCROSS (:real^N)) /\
    open((:real^1) PCROSS (:real^N)) /\
    g continuous_on ((:real^1) PCROSS (:real^N)) /\
    (!z:real^(1,N)finite_sum. z IN (:real^1) PCROSS (:real^N))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[UNIV_PCROSS_UNIV; IN_UNIV; OPEN_UNIV] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ode_locally_lipschitz] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1`; `L:real`] THEN ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ode_maxint (g:real^(1,N)finite_sum->real^N) ((:real^1) PCROSS (:real^N)) z =
        (:real^1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ODE_MAXINT_LINEAR_GROWTH THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_UNIV] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`B:real`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  ABBREV_TAC `C = exp(L * (drop b - drop a))` THEN
  SUBGOAL_THEN `&1 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[GSYM REAL_EXP_0; REAL_EXP_MONO_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(interval[a:real^1,b] = {})` THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`R0 / C`; `C:real`] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN STRIP_TAC THEN
  ABBREV_TAC `s = fstcart(z:real^(1,N)finite_sum)` THEN
  ABBREV_TAC `x = sndcart(z:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `z = pastecart (s:real^1) (x:real^N)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "x"] THEN REWRITE_TAC[PASTECART_FST_SND]; ALL_TAC] THEN
  SUBGOAL_THEN `C * norm(x - (u:real^1->real^N) s) <= R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * R0 / C` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 <= C` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x - (u:real^1->real^N) s) <= R0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * norm(x - (u:real^1->real^N) s)` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (s:real^1) (x:real^N) IN D` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!x:real^(1,N)finite_sum. x IN K' /\ K' SUBSET D ==> x IN D`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^(1,N)finite_sum->real^N`; `(:real^1) PCROSS (:real^N)`;
                 `pastecart (s:real^1) (x:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
  STRIP_TAC THEN
  ABBREV_TAC `v = \t. ode_flow (g:real^(1,N)finite_sum->real^N)
                       ((:real^1) PCROSS (:real^N)) t (pastecart s x)` THEN
  SUBGOAL_THEN
   `!t. ode_flow (g:real^(1,N)finite_sum->real^N) ((:real^1) PCROSS (:real^N)) t
          (pastecart s x) = (v:real^1->real^N) t`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_solution (g:real^(1,N)finite_sum->real^N) ((:real^1) PCROSS (:real^N))
                 (interval[a,b]) u`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ode_solution (f:real^(1,N)finite_sum->real^N) D (interval[a,b]) u` THEN
    REWRITE_TAC[ode_solution; PASTECART_IN_PCROSS; IN_UNIV] THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(g:real^(1,N)finite_sum->real^N)(pastecart t ((u:real^1->real^N) t)) =
      f(pastecart t (u t))` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_solution (g:real^(1,N)finite_sum->real^N) ((:real^1) PCROSS (:real^N))
                 (interval[a,b]) v`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ODE_SOLUTION_SUBINTERVAL THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[IS_INTERVAL_INTERVAL; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^(1,N)finite_sum->real^N`; `(:real^1) PCROSS (:real^N)`;
                 `(:real^(1,N)finite_sum)`; `interval[a:real^1,b]`;
                 `v:real^1->real^N`; `u:real^1->real^N`; `s:real^1`; `L:real`]
         ODE_SOLUTION_GRONWALL) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[a,b]
        ==> norm((v:real^1->real^N) t - (u:real^1->real^N) t) <=
            C * norm(x - u s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(s:real^1) IN interval[a,b]` THEN
    UNDISCH_TAC `(t:real^1) IN interval[a,b]` THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_solution (f:real^(1,N)finite_sum->real^N) D (interval[a,b]) v`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ode_solution (g:real^(1,N)finite_sum->real^N)
                   ((:real^1) PCROSS (:real^N)) (interval[a,b]) v` THEN
    REWRITE_TAC[ode_solution; PASTECART_IN_PCROSS; IN_UNIV] THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `norm((v:real^1->real^N) t - (u:real^1->real^N) t) <= R0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * norm(x - (u:real^1->real^N) s)` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:real^(1,N)finite_sum->real^N)(pastecart t ((v:real^1->real^N) t)) =
      f(pastecart t (v t))` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!x:real^(1,N)finite_sum. x IN K' /\ K' SUBSET D ==> x IN D`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `pastecart (s:real^1) (x:real^N)`; `interval[a:real^1,b]`;
                 `v:real^1->real^N`] ODE_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real^1` th) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Openness of the flow domain and continuity of the flow map.               *)
(* ------------------------------------------------------------------------- *)

let ODE_DIST_COMPONENTS = prove
 (`!(t:real^1) t1 (z:real^(1,N)finite_sum) z0.
        dist(t,t1) <= dist(pastecart t z,pastecart t1 z0) /\
        dist(fstcart z,fstcart z0) <= dist(pastecart t z,pastecart t1 z0) /\
        dist(sndcart(z:real^(1,N)finite_sum),sndcart z0) <= dist(pastecart t z,pastecart t1 z0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`t:real^1`; `z:real^(1,N)finite_sum`; `t1:real^1`;
                 `z0:real^(1,N)finite_sum`] DIST_LE_PASTECART) THEN
  MP_TAC(ISPECL [`fstcart(z:real^(1,N)finite_sum)`; `sndcart(z:real^(1,N)finite_sum)`;
                 `fstcart(z0:real^(1,N)finite_sum)`; `sndcart(z0:real^(1,N)finite_sum)`]
         DIST_LE_PASTECART) THEN
  REWRITE_TAC[PASTECART_FST_SND] THEN REAL_ARITH_TAC);;

let ODE_IN_DOMAIN = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t z.
        pastecart t z IN ode_domain f D <=> z IN D /\ t IN ode_maxint f D z`,
  REWRITE_TAC[ode_domain; IN_ELIM_THM; PASTECART_INJ] THEN MESON_TAC[]);;

let ODE_IN_DOMAIN_ALT = prove
 (`!(f:real^(1,N)finite_sum->real^N) D w.
        w IN ode_domain f D <=>
        sndcart w IN D /\ fstcart w IN ode_maxint f D (sndcart w)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
  REWRITE_TAC[ODE_IN_DOMAIN]);;

let ODE_FLOW_LOCAL_CONTINUITY = prove
 (`!(f:real^(1,N)finite_sum->real^N) D t1 z0.
        open D /\ f continuous_on D /\ ode_locally_lipschitz f D /\
        z0 IN D /\ t1 IN ode_maxint f D z0
        ==> (?d. &0 < d /\ ball(pastecart t1 z0,d) SUBSET ode_domain f D) /\
            (\w. ode_flow f D (fstcart w) (sndcart w)) continuous
            (at (pastecart t1 z0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z0:real^(1,N)finite_sum`] ODE_FLOW_SOLUTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s0 = fstcart(z0:real^(1,N)finite_sum)` THEN
  ABBREV_TAC `M0 = ode_maxint (f:real^(1,N)finite_sum->real^N) D z0` THEN
  ABBREV_TAC `u = \t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z0` THEN
  SUBGOAL_THEN `!t. ode_flow (f:real^(1,N)finite_sum->real^N) D t z0 = u t`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN
             ASSUME_TAC th) THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(M0:real^1->bool) /\ is_interval M0 /\ (s0:real^1) IN M0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["M0"; "s0"] THEN
    ASM_SIMP_TAC[ODE_MAXINT_OPEN; ODE_MAXINT_IS_INTERVAL; ODE_MAXINT_INITIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^1->real^N) continuous_on M0` ASSUME_TAC THENL
   [ASM_MESON_TAC[ODE_SOLUTION_CONTINUOUS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:real^1->real^N) continuous (at s0) /\ u continuous (at t1)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `s0:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `t1:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min e1 e2` THEN
  SUBGOAL_THEN `&0 < e /\ e <= e1 /\ e <= e2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a = lift(min (drop s0) (drop t1) - e / &2)` THEN
  ABBREV_TAC `b = lift(max (drop s0) (drop t1) + e / &2)` THEN
  SUBGOAL_THEN `(a:real^1) IN M0 /\ (b:real^1) IN M0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_CASES_TAC `drop s0 <= drop t1` THENL
     [UNDISCH_TAC `ball(s0:real^1,e1) SUBSET M0`;
      UNDISCH_TAC `ball(t1:real^1,e2) SUBSET M0`;
      UNDISCH_TAC `ball(t1:real^1,e2) SUBSET M0`;
      UNDISCH_TAC `ball(s0:real^1,e1) SUBSET M0`] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[a:real^1,b] SUBSET M0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ODE_IS_INTERVAL_BETWEEN THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. dist(t,t1) < e / &2 \/ dist(t,s0) < e / &2 ==> t IN interval[a:real^1,b]`
  ASSUME_TAC THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[IN_INTERVAL_1; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                 `z0:real^(1,N)finite_sum`; `a:real^1`; `b:real^1`]
         ODE_FLOW_STABILITY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "stab"))))) THEN
  SUBGOAL_THEN
   `!eps. &0 < eps
          ==> ?d. &0 < d /\
                  !t z. dist(pastecart t z,pastecart t1 z0) < d
                        ==> pastecart t z IN ode_domain (f:real^(1,N)finite_sum->real^N) D /\
                            dist(ode_flow f D t z,u t1) < eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(u:real^1->real^N) continuous (at s0)` THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `min (R / &2) (eps / (&3 * C))`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)] THEN
    UNDISCH_TAC `(u:real^1->real^N) continuous (at t1)` THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `eps / &3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min (e / &2) (min d1 (min d2 (min (R / &2) (eps / (&3 * C)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `z:real^(1,N)finite_sum`] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^1`; `t1:real^1`; `z:real^(1,N)finite_sum`;
                   `z0:real^(1,N)finite_sum`] ODE_DIST_COMPONENTS) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `dist(t:real^1,t1) < e / &2 /\
      dist(fstcart(z:real^(1,N)finite_sum),s0) < e / &2 /\
      dist(fstcart z,s0) < d1 /\ dist(t,t1) < d2 /\
      dist(sndcart(z:real^(1,N)finite_sum),sndcart(z0:real^(1,N)finite_sum)) < R / &2 /\
      dist(sndcart(z:real^(1,N)finite_sum),sndcart z0) < eps / (&3 * C)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `dist((u:real^1->real^N)(fstcart(z:real^(1,N)finite_sum)),u s0) <
      min (R / &2) (eps / (&3 * C)) /\
      dist((u:real^1->real^N) t,u t1) < eps / &3`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^1->real^N) s0 = sndcart(z0:real^(1,N)finite_sum)`
    ASSUME_TAC THENL [EXPAND_TAC "s0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `fstcart(z:real^(1,N)finite_sum) IN interval[a,b] /\ t IN interval[a,b]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `norm(sndcart(z:real^(1,N)finite_sum) - (u:real^1->real^N)(fstcart z)) <=
      dist(sndcart z,sndcart(z0:real^(1,N)finite_sum)) +
      dist((u:real^1->real^N)(fstcart z),u s0)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
    SUBGOAL_THEN
     `norm(sndcart(z:real^(1,N)finite_sum) - (u:real^1->real^N)(fstcart z)) <
      &2 * min (R / &2) (eps / (&3 * C))`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "stab" (MP_TAC o SPEC `z:real^(1,N)finite_sum`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `norm(sndcart(z:real^(1,N)finite_sum) - (u:real^1->real^N)(fstcart(z:real^(1,N)finite_sum))) <
        &2 * min (R / &2) (eps / (&3 * C))` THEN
      REAL_ARITH_TAC;
      STRIP_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ODE_IN_DOMAIN] THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `C * norm(sndcart(z:real^(1,N)finite_sum) - (u:real^1->real^N)(fstcart(z:real^(1,N)finite_sum))) <
      &2 * eps / &3`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `C * &2 * eps / (&3 * C)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `&2 * min (R / &2) (eps / (&3 * C))` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < C` THEN
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`ode_flow (f:real^(1,N)finite_sum->real^N) D t z`;
                   `(u:real^1->real^N) t`; `(u:real^1->real^N) t1`]
     (NORM_ARITH `!x y z:real^N. norm(x - z) <= norm(x - y) + norm(y - z)`)) THEN
    UNDISCH_TAC `dist((u:real^1->real^N) t,u t1) < eps / &3` THEN
    UNDISCH_TAC
     `norm(ode_flow (f:real^(1,N)finite_sum->real^N) D t z - (u:real^1->real^N) t) <=
      C * norm(sndcart z - u(fstcart(z:real^(1,N)finite_sum)))` THEN
    UNDISCH_TAC
     `C * norm(sndcart(z:real^(1,N)finite_sum) - (u:real^1->real^N)(fstcart z)) <
      &2 * eps / &3` THEN
    REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    X_GEN_TAC `w:real^(1,(1,N)finite_sum)finite_sum` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`fstcart(w:real^(1,(1,N)finite_sum)finite_sum)`;
                                  `sndcart(w:real^(1,(1,N)finite_sum)finite_sum)`]) THEN
    REWRITE_TAC[PASTECART_FST_SND] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[DIST_SYM]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^(1,(1,N)finite_sum)finite_sum` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`fstcart(w:real^(1,(1,N)finite_sum)finite_sum)`;
                                `sndcart(w:real^(1,(1,N)finite_sum)finite_sum)`]) THEN
  ASM_REWRITE_TAC[PASTECART_FST_SND] THEN SIMP_TAC[]);;

let ODE_FLOW_CONTINUOUS = prove
 (`!(f:real^(1,N)finite_sum->real^N) D.
    open D /\ f continuous_on D /\ ode_locally_lipschitz f D
    ==> open(ode_domain f D) /\
        (\w. ode_flow f D (fstcart w) (sndcart w)) continuous_on
        ode_domain f D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. w IN ode_domain (f:real^(1,N)finite_sum->real^N) D
        ==> (?d. &0 < d /\ ball(w,d) SUBSET ode_domain f D) /\
            (\w. ode_flow f D (fstcart w) (sndcart w)) continuous (at w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(1,(1,N)finite_sum)finite_sum` THEN
    REWRITE_TAC[ODE_IN_DOMAIN_ALT] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^N`; `D:real^(1,N)finite_sum->bool`;
                   `fstcart(w:real^(1,(1,N)finite_sum)finite_sum)`;
                   `sndcart(w:real^(1,(1,N)finite_sum)finite_sum)`]
           ODE_FLOW_LOCAL_CONTINUITY) THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_CONTAINS_BALL] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN ASM_MESON_TAC[]]);;

