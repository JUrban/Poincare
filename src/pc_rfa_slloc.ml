(* ========================================================================= *)
(* Unit pc_rfa_slloc: the local derivative estimate in coordinates           *)
(* (CLN Thm 6.15 / 14.16 route, MT Thm 3.28): a local Ricci flow on          *)
(* ball(vec 0,rho) whose metric at the start time sg is in normal            *)
(* coordinates (the conclusions of CMP_EXP_PULLBACK, predicate rfa_expc),    *)
(* with bounds on abs(nabla^i Rm) for i < m on [sg,sg + tau], has            *)
(* abs(nabla^m Rm)^2 <= C at the centre at time sg + tau, C depending only   *)
(* on m, the bounds, rho, K and tau.  Bernstein quantity                     *)
(* (B + |nabla^(m-1) Rm|^2) |nabla^m Rm|^2, barrier RFA_LOCAL_BARRIER,       *)
(* cutoff rfa_prof (rho / 4) (rho / 2) o norm; for m = 1 the Christoffel     *)
(* change is controlled by the barrier itself (bootstrap).                   *)
(* ========================================================================= *)

needs "src/pc_rfa_slcut.ml";;

prioritize_real();;
type_invention_error := true;;

(* The properties of the exp pullback at the start time used by the local   *)
(* estimate (the conclusions of CMP_EXP_PULLBACK_STATEMENT on ball(0,rho)): *)
(* comparable to the Euclidean metric within a factor 2, the Gauss lemma,   *)
(* and the two-sided Hessian comparison of r = |w| with constant K.         *)

let rfa_expc = new_definition
 `rfa_expc (G0:real^N->real^N^N) rho K <=>
    (!w a. norm w < rho
           ==> inv(&2) * (a dot a) <= a dot (G0 w ** a) /\
               a dot (G0 w ** a) <= &2 * (a dot a)) /\
    (!w. norm w < rho ==> G0 w ** w = w) /\
    (!w a. &0 < norm w /\ norm w < rho
           ==> (inv(norm w) - K * norm w) *
               (a dot (G0 w ** a) - (w dot a) pow 2 / norm w pow 2) <=
               cmp_lhess G0 (\z. norm z) w a a /\
               cmp_lhess G0 (\z. norm z) w a a <=
               (inv(norm w) + K * norm w) *
               (a dot (G0 w ** a) - (w dot a) pow 2 / norm w pow 2))`;;

(* ========================================================================= *)
(* Consequences of the normal-coordinate data at the start                   *)
(* time: the absolute Hessian bound of |w| (RFA_CUT_LAP form) and the metric *)
(* comparisons at later times under a bound on |Rm|^2.                       *)
(* ========================================================================= *)

let RFA_EXPC_HESS_ABS = prove
 (`!U (G0:real^N->real^N^N) rho K z.
     rfa_expc G0 rho K /\ &0 <= K /\ metric_field U G0 /\ z IN U /\
     ~(z = vec 0) /\ norm z < rho
     ==> !v. abs(cmp_lhess G0 (\w. norm w) z v v) <=
             (inv(norm z) + K * norm z) * (v dot (G0 z ** v))`,
  REWRITE_TAC[rfa_expc] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2") (LABEL_TAC "c3")))
    STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `&0 < norm(z:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(G0:real^N->real^N^N) z ** z = z` ASSUME_TAC THENL
   [USE_THEN "c2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `z:real^N`; `v:real^N`]
         RFA_GAUSS_CS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "c3" (MP_TAC o SPECL [`z:real^N`; `v:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `Q = v dot ((G0:real^N->real^N^N) z ** v) -
                  (z dot v) pow 2 / norm(z:real^N) pow 2` THEN
  SUBGOAL_THEN `&0 <= Q /\ Q <= v dot ((G0:real^N->real^N^N) z ** v)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    SUBGOAL_THEN
     `&0 <= (z dot v) pow 2 / norm(z:real^N) pow 2 /\
      (z dot v) pow 2 / norm z pow 2 <= v dot ((G0:real^N->real^N^N) z ** v)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE];
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      ASM_REWRITE_TAC[NORM_POW_2];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(norm(z:real^N)) * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(inv(norm(z:real^N)) + K * norm z) * Q <=
    (inv(norm z) + K * norm z) * (v dot ((G0:real^N->real^N^N) z ** v))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; NORM_POS_LE; REAL_LE_MUL];
    ALL_TAC] THEN
  UNDISCH_TAC `(inv(norm(z:real^N)) + K * norm z) * Q <=
               (inv(norm z) + K * norm z) * (v dot ((G0:real^N->real^N^N) z ** v))` THEN
  UNDISCH_TAC `&0 <= inv(norm(z:real^N)) * Q` THEN
  UNDISCH_TAC `(inv(norm(z:real^N)) - K * norm z) * Q <=
               cmp_lhess (G0:real^N->real^N^N) (\z. norm z) z v v` THEN
  UNDISCH_TAC `cmp_lhess (G0:real^N->real^N^N) (\z. norm z) z v v <=
               (inv(norm(z:real^N)) + K * norm z) * Q` THEN
  REWRITE_TAC[ETA_AX] THEN REAL_ARITH_TAC);;

let RFA_SLOC_METRIC = prove
 (`!a b (G:real->real^N->real^N^N) sg t1 rho K A0.
     lricci_flow (ball(vec 0,rho)) a b G /\ a < sg /\ sg <= t1 /\ t1 < b /\
     rfa_expc (G sg) rho K /\ &0 <= A0 /\
     (!s z. sg <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0)
     ==> !s z. sg <= s /\ s <= t1 /\ norm z < rho
               ==> !x. x dot (G sg z ** x) <=
                     exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg)) *
                     (x dot (G s z ** x)) /\
                     norm x pow 2 <=
                     (&2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg))) *
                     (x dot (G s z ** x)) /\
                     x dot (G s z ** x) <=
                     (&2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg))) *
                     norm x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Kr = &(dimindex(:N)) * sqrt A0` THEN
  SUBGOAL_THEN `&0 <= Kr` ASSUME_TAC THENL
   [EXPAND_TAC "Kr" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `z:real^N`; `sg:real`; `s:real`;
                 `Kr:real`] RFA_LMETRIC_EQUIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s':real`; `v:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "Kr" THEN MATCH_MP_TAC RFA_LRIC_BOUND THEN
    EXISTS_TAC `ball(vec 0:real^N,rho)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `x:real^N`] o CONJUNCT1 o
    GEN_REWRITE_RULE I [rfa_expc]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `E = exp(&2 * Kr * (t1 - sg))` THEN
  ABBREV_TAC `e1 = exp(&2 * Kr * (s - sg))` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= E /\ e1 * exp(--(&2 * Kr * (s - sg))) = &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "E"] THEN
    REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LE; REAL_EXP_NEG_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `P0 = (x:real^N) dot ((G:real->real^N->real^N^N) sg z ** x)` THEN
  ABBREV_TAC `P1 = (x:real^N) dot ((G:real->real^N->real^N^N) s z ** x)` THEN
  ABBREV_TAC `em = exp(--(&2 * Kr * (s - sg)))` THEN
  SUBGOAL_THEN `&0 <= P0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2) * ((x:real^N) dot x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[DOT_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `P0 <= e1 * P1` ASSUME_TAC THENL
   [SUBGOAL_THEN `e1 * em * P0 <= e1 * P1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `em * P0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "em" THEN REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 * P1 <= E * P1 /\ e1 * P0 <= E * P0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `E * P0 <= E * (&2 * ((x:real^N) dot x))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2] THEN
  UNDISCH_TAC `E * P0 <= E * (&2 * ((x:real^N) dot x))` THEN
  UNDISCH_TAC `P1 <= e1 * P0` THEN
  UNDISCH_TAC `inv(&2) * ((x:real^N) dot x) <= P0` THEN
  UNDISCH_TAC `e1 * P1 <= E * P1` THEN UNDISCH_TAC `e1 * P0 <= E * P0` THEN
  UNDISCH_TAC `P0 <= e1 * P1` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The cutoff bounds at a point and time from the start-time                 *)
(* data, and the weighted Christoffel change when |nabla Rm|^2 is bounded   *)
(* (orders m >= 2).                                                          *)
(* ========================================================================= *)

let RFA_SLOC_CUT = prove
 (`!a b (G:real->real^N->real^N^N) sg t0 t1 rho K A0 C1 C2 Dg z.
     lricci_flow (ball(vec 0,rho)) a b G /\ a < sg /\ sg <= t0 /\ t0 <= t1 /\
     t1 < b /\ &0 < rho /\ &0 <= K /\ rfa_expc (G sg) rho K /\ &0 <= A0 /\
     (!s z. sg <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0) /\
     norm z < rho /\
     abs(real_derivative (rfa_prof (rho / &4) (rho / &2)) (norm z)) <= C1 /\
     abs(real_derivative (real_derivative (rfa_prof (rho / &4) (rho / &2)))
                         (norm z)) <= C2 /\
     &0 <= Dg /\
     (!v. rfa_prof (rho / &4) (rho / &2) (norm z) *
          norm(christoffel (G t0) z v v - christoffel (G sg) z v v) <=
          Dg * norm v pow 2)
     ==> lgrad2 (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z <=
         C1 pow 2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg)) *
         &(dimindex(:N)) /\
         --(rfa_prof (rho / &4) (rho / &2) (norm z) *
            llap (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z) <=
         ((C2 + C1 * (inv(rho / &4) + K * rho)) *
          exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg)) +
          C1 * Dg * (&2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg)))) *
         &(dimindex(:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < b
        ==> metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) sg) /\
    metric_field (ball(vec 0,rho)) (G t0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real->real^N->real^N^N) sg z ** z = z` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfa_expc]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E = exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg))` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `sg:real`; `t1:real`;
                 `rho:real`; `K:real`; `A0:real`] RFA_SLOC_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t0:real`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "met")] THEN
  SUBGOAL_THEN `&0 < rho / &4 /\ rho / &4 < rho / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_CUT_GRAD THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`;
                          `(G:real->real^N->real^N^N) sg`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_CUT_LAP THEN
  MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`;
                        `(G:real->real^N->real^N^N) sg`] THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC RFA_EXPC_HESS_ABS THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`; `rho:real`] THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let RFA_SLOC_DG_HI = prove
 (`!a b (G:real->real^N->real^N^N) sg t0 t1 rho K A0 A1 Lm z.
     lricci_flow (ball(vec 0,rho)) a b G /\ a < sg /\ sg < t0 /\ t0 <= t1 /\
     t1 < b /\ &0 < rho /\ rfa_expc (G sg) rho K /\ &0 <= A0 /\ &0 <= A1 /\
     (!s z. sg <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0) /\
     (!s z. sg <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 1 (G s) z <= A1) /\
     Lm = &2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg)) /\
     norm z < rho
     ==> !v. rfa_prof (rho / &4) (rho / &2) (norm z) *
             norm(christoffel (G t0) z v v - christoffel (G sg) z v v) <=
             ((&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) *
              sqrt(&(dimindex(:N)) * A1) * (t1 - sg)) * norm v pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lm` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `sg:real`; `t1:real`;
                 `rho:real`; `K:real`; `A0:real`] RFA_SLOC_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "met") THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `sg:real`; `t0:real`; `z:real^N`;
                 `v:real^N`; `Lm:real`; `&0`; `sqrt(&(dimindex(:N)) * A1)`]
         RFA_GAMMA_CHANGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^N`] THEN STRIP_TAC THEN
      USE_THEN "met" (MP_TAC o SPECL [`s:real`; `z:real^N`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  ABBREV_TAC `nG = norm(christoffel ((G:real->real^N->real^N^N) t0) z v v -
                        christoffel (G sg) z v v)` THEN
  ABBREV_TAC `ps = rfa_prof (rho / &4) (rho / &2) (norm(z:real^N))` THEN
  ABBREV_TAC `sA = sqrt(&(dimindex(:N)) * A1)` THEN
  ABBREV_TAC `nv = norm(v:real^N) pow 2` THEN
  DISCH_TAC THEN
  ABBREV_TAC `Cg = &3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)` THEN
  SUBGOAL_THEN `&0 <= ps /\ ps <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ps" THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Cg /\ &0 <= sA /\ &0 <= nv /\ &0 <= nG` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Cg"; "sA"; "nv"; "nG"] THEN
    REWRITE_TAC[NORM_POS_LE; REAL_LE_POW_2] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ps * nG <= nG` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Cg * nv * sA) * (t0 - sg) <= (Cg * nv * sA) * (t1 - sg)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(Cg * nv * sA) * (t0 - sg) <= (Cg * nv * sA) * (t1 - sg)` THEN
  UNDISCH_TAC `ps * nG <= nG` THEN
  UNDISCH_TAC `nG <= (Cg * nv) * sA * (t0 - sg)` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Order m = 1, the bootstrap: before the barrier is touched,                *)
(* F <= H gives sqrt(N |nabla Rm|^2) <= A / sqrt(s - sg) + B, hence the     *)
(* weighted Christoffel change; and the choice of the barrier constant.     *)
(* ========================================================================= *)

let RFA_SQRT_ADD3_LE = prove
 (`!x y z. &0 <= x /\ &0 <= y /\ &0 <= z
           ==> sqrt(x + y + z) <= sqrt x + sqrt y + sqrt z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  ASM_SIMP_TAC[REAL_LE_ADD; SQRT_POS_LE] THEN
  MP_TAC(SPEC `x:real` SQRT_POW_2) THEN MP_TAC(SPEC `y:real` SQRT_POW_2) THEN
  MP_TAC(SPEC `z:real` SQRT_POW_2) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= sqrt x * sqrt y /\ &0 <= sqrt x * sqrt z /\ &0 <= sqrt y * sqrt z`
  MP_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RFA_BOOT_RATE = prove
 (`!n B delta Bc Lam ps r0 r1 d.
     &0 <= n /\ &0 < B /\ &0 < delta /\ &0 < Bc /\ &0 <= Lam /\ &0 < ps /\ &0 < d /\
     &0 <= r0 /\ &0 <= r1 /\
     (B + r0) * r1 <= Bc * inv(ps pow 2) + inv(delta * d) + Lam
     ==> sqrt(n * r1) <=
         sqrt(n / (B * delta)) * inv(sqrt d) +
         sqrt(n / B) * (sqrt Bc * inv ps + sqrt Lam)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `H = Bc * inv(ps pow 2) + inv(delta * d) + Lam` THEN
  SUBGOAL_THEN `B * r1 <= H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B + r0) * r1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n * r1 <= n / B * H` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(n / B) * sqrt H` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt H <= sqrt Bc * inv ps + inv(sqrt delta) * inv(sqrt d) + sqrt Lam`
  ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(Bc * inv(ps pow 2)) + sqrt(inv(delta * d)) + sqrt Lam` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_SQRT_ADD3_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]];
      REWRITE_TAC[SQRT_MUL; SQRT_INV; REAL_INV_MUL] THEN
      ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(n / (B * delta)) = sqrt(n / B) * inv(sqrt delta)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL; SQRT_MUL; SQRT_INV; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(n / B) * (sqrt Bc * inv ps + inv(sqrt delta) * inv(sqrt d) + sqrt Lam)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REAL_ARITH_TAC]);;

let RFA_BOOT_ALG = prove
 (`!ps nG X nv A c1 sBc sL d0 d1 q0 q1.
     &0 < ps /\ ps <= &1 /\ &0 <= X /\ &0 <= nv /\ &0 <= A /\ &0 <= c1 /\
     &0 <= sBc /\ &0 <= sL /\ &0 <= d0 /\ d0 <= d1 /\ &0 <= q0 /\ q0 <= q1 /\
     nG <= (X * nv) * (&2 * A * q0 + (c1 * (sBc * inv ps + sL)) * d0)
     ==> ps * nG <= (X * (&2 * A * q1 + c1 * (sBc + sL) * d1)) * nv`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ps * nG <= ps * ((X * nv) * (&2 * A * q0 + (c1 * (sBc * inv ps + sL)) * d0))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ps * ((X * nv) * (&2 * A * q0 + (c1 * (sBc * inv ps + sL)) * d0)) =
    (X * nv) * (&2 * A * (ps * q0) + c1 * (sBc + ps * sL) * d0)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < ps` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  SUBGOAL_THEN
   `(X * (&2 * A * q1 + c1 * (sBc + sL) * d1)) * nv =
    (X * nv) * (&2 * A * q1 + c1 * (sBc + sL) * d1)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `q0:real` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[REAL_LE_REFL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]);;

let RFA_BC_CHOICE = prove
 (`!p q d. &0 <= p /\ &0 <= q /\ &0 < d
           ==> ?Bc. &0 < Bc /\ p + q * sqrt Bc < d * Bc`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `X = max (&1) ((p + q + &1) / d)` THEN
  SUBGOAL_THEN `&1 <= X /\ (p + q + &1) / d <= X` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `X pow 2` THEN
  SUBGOAL_THEN `sqrt(X pow 2) = X` SUBST1_TAC THENL
   [MATCH_MP_TAC POW_2_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p + q + &1 <= d * X` ASSUME_TAC THENL
   [UNDISCH_TAC `(p + q + &1) / d <= X` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p + q + &1) * X <= (d * X) * X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p <= p * X` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  UNDISCH_TAC `(p + q + &1) * X <= (d * X) * X` THEN
  UNDISCH_TAC `p <= p * X` THEN UNDISCH_TAC `&1 <= X` THEN
  REAL_ARITH_TAC);;

let RFA_SLOC_DG_BOOT = prove
 (`!a b (G:real->real^N->real^N^N) sg t0 t1 rho K A0 Lm B delta Bc Lam z.
     lricci_flow (ball(vec 0,rho)) a b G /\ a < sg /\ sg < t0 /\ t0 <= t1 /\
     t1 < b /\ &0 < rho /\ rfa_expc (G sg) rho K /\ &0 <= A0 /\
     (!s z. sg <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0) /\
     Lm = &2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg)) /\
     &0 < B /\ &0 < delta /\ &0 < Bc /\ &0 <= Lam /\ norm z < rho /\
     &0 < rfa_prof (rho / &4) (rho / &2) (norm z) /\
     (!s. sg < s /\ s <= t0
          ==> (B + lrm_deriv_norm2 0 (G s) z) * lrm_deriv_norm2 1 (G s) z <=
              Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) +
              inv(delta * (s - sg)) + Lam)
     ==> !v. rfa_prof (rho / &4) (rho / &2) (norm z) *
             norm(christoffel (G t0) z v v - christoffel (G sg) z v v) <=
             ((&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) *
              (&2 * sqrt(&(dimindex(:N)) / (B * delta)) * sqrt(t1 - sg) +
               sqrt(&(dimindex(:N)) / B) * (sqrt Bc + sqrt Lam) * (t1 - sg))) *
             norm v pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < b
        ==> metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) t)`
  (LABEL_TAC "mf") THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lm` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `sg:real`; `t1:real`;
                 `rho:real`; `K:real`; `A0:real`] RFA_SLOC_METRIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "met") THEN
  ABBREV_TAC `ps = rfa_prof (rho / &4) (rho / &2) (norm(z:real^N))` THEN
  SUBGOAL_THEN `ps <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "ps" THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `sg:real`; `t0:real`; `z:real^N`;
                 `v:real^N`; `Lm:real`; `sqrt(&(dimindex(:N)) / (B * delta))`;
                 `sqrt(&(dimindex(:N)) / B) * (sqrt Bc * inv ps + sqrt Lam)`]
         RFA_GAMMA_CHANGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^N`] THEN STRIP_TAC THEN
      USE_THEN "met" (MP_TAC o SPECL [`s:real`; `z:real^N`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) s)`
      ASSUME_TAC THENL
       [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC RFA_BOOT_RATE THEN
      EXISTS_TAC `lrm_deriv_norm2 0 ((G:real->real^N->real^N^N) s) z` THEN
      ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sqrt(&(dimindex(:N)) / (B * delta)) /\ &0 <= sqrt(&(dimindex(:N)) / B) /\
    &0 <= sqrt Bc /\ &0 <= sqrt Lam`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `Lm = &2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * (t1 - sg))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC RFA_BOOT_ALG THEN
  MAP_EVERY EXISTS_TAC [`t0 - sg:real`; `sqrt(t0 - sg)`] THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SQRT_MONO_LE) THEN
  TRY(MATCH_MP_TAC SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The barrier argument for the Bernstein quantity in the                    *)
(* normal-coordinate ball, given the cutoff bounds before the barrier is     *)
(* touched: the bound at the centre at the final time.                       *)
(* ========================================================================= *)

let RFA_BERN_QUANT_SMOOTH = prove
 (`!s (f:real^M->real) g c.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift((c + f x) * g x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN
  ASM_REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]);;

let RFA_SLOC_BARRIER_APPLY = prove
 (`!m (A:num->real) Bq D a b (G:real->real^N->real^N^N) sg tau rho delta Bc Lam
    beta2 gam.
     1 <= m /\ &0 < Bq /\ &0 < rho /\ &0 < tau /\ &0 <= A(m - 1) /\
     (!U a b (G:real->real^N->real^N^N) t y.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
        (!i. i < m ==> lrm_deriv_norm2 i (G t) y <= A i)
        ==> ?dF. ((\s. (Bq + lrm_deriv_norm2 (m - 1) (G s) y) *
                       lrm_deriv_norm2 m (G s) y) has_real_derivative dF) (atreal t) /\
                 dF <= llap (G t) (\z. (Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                                       lrm_deriv_norm2 m (G t) z) y -
                       ((Bq + lrm_deriv_norm2 (m - 1) (G t) y) *
                        lrm_deriv_norm2 m (G t) y) pow 2 /
                       (&2 * (Bq + A(m - 1)) pow 2) + D) /\
     delta = inv(&2 * (Bq + A(m - 1)) pow 2) /\
     lricci_flow (ball(vec 0,rho)) a b G /\ a < sg /\ sg + tau < b /\
     (!i s z. i < m /\ sg <= s /\ s <= sg + tau /\ norm z < rho
              ==> lrm_deriv_norm2 i (G s) z <= A i) /\
     &0 < Bc /\ &0 <= Lam /\ D <= delta * Lam pow 2 /\
     &2 * gam + &6 * beta2 < delta * Bc /\
     (!t0 z. sg < t0 /\ t0 <= sg + tau /\ z IN ball(vec 0,rho) /\
             &0 < rfa_prof (rho / &4) (rho / &2) (norm z) /\
             (!t. sg < t /\ t <= t0
                  ==> (Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                      lrm_deriv_norm2 m (G t) z <=
                      Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) +
                      inv(delta * (t - sg)) + Lam)
             ==> lgrad2 (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z <=
                 beta2 /\
                 --(rfa_prof (rho / &4) (rho / &2) (norm z) *
                    llap (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z) <=
                 gam)
     ==> lrm_deriv_norm2 m (G (sg + tau)) (vec 0) <=
         (Bc + inv(delta * tau) + Lam) / Bq`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bern")
   (CONJUNCTS_THEN2 (LABEL_TAC "deq") STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
   [USE_THEN "deq" SUBST1_TAC THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X. X pow 2 / (&2 * (Bq + (A:num->real)(m - 1)) pow 2) = delta * X pow 2`
  (LABEL_TAC "dq") THENL
   [USE_THEN "deq" SUBST1_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "deq" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < b
        ==> metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^N,rho / &2) SUBSET ball(vec 0,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sg < sg + tau` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (ball(vec 0:real^N,rho))
      (\z. lift(rfa_prof (rho / &4) (rho / &2) (norm z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_BUMP_SMOOTH_ON THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN ball(vec 0,rho) ==> &0 <= rfa_prof (rho / &4) (rho / &2) (norm z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN ball(vec 0,rho) /\ ~(z IN cball(vec 0,rho / &2))
               ==> rfa_prof (rho / &4) (rho / &2) (norm z) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_CBALL_0] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NORM] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift((Bq + lrm_deriv_norm2 (m - 1)
                  ((G:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w)) *
              lrm_deriv_norm2 m (G (drop(fstcart w))) (sndcart w)))
    continuous_on (interval[lift sg,lift(sg + tau)] PCROSS cball(vec 0,rho / &2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS ball(vec 0:real^N,rho)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN
      MATCH_MP_TAC RFA_BERN_QUANT_SMOOTH THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP LRG_FLOW_BASIC) THEN SIMP_TAC[] THEN
      DISCH_THEN(K ALL_TAC) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP RFA_LRICCI_FLOW_LSMOOTH) THEN
      ASM_SIMP_TAC[RFA_LSMOOTH_LRM_NORM2];
      MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. sg < t /\ t <= sg + tau
        ==> smooth_map_on (ball(vec 0:real^N,rho))
              (\z. lift((Bq + lrm_deriv_norm2 (m - 1)
                               ((G:real->real^N->real^N^N) t) z) *
                        lrm_deriv_norm2 m (G t) z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field (ball(vec 0:real^N,rho)) ((G:real->real^N->real^N^N) t)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RFA_BERN_QUANT_SMOOTH THEN
    ASM_SIMP_TAC[OPEN_BALL; RFA_RMD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. sg < t /\ t <= sg + tau /\ z IN ball(vec 0,rho)
          ==> ?dF. ((\s. (Bq + lrm_deriv_norm2 (m - 1)
                                 ((G:real->real^N->real^N^N) s) z) *
                         lrm_deriv_norm2 m (G s) z) has_real_derivative dF)
                   (atreal t) /\
                   dF <= llap (G t) (\z. (Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                                         lrm_deriv_norm2 m (G t) z) z -
                         delta * ((Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                                  lrm_deriv_norm2 m (G t) z) pow 2 + D`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < t /\ t < b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "dq" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "bern" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `cball(vec 0:real^N,rho / &2)`;
                 `G:real->real^N->real^N^N`;
                 `\t z. (Bq + lrm_deriv_norm2 (m - 1)
                                ((G:real->real^N->real^N^N) t) z) *
                        lrm_deriv_norm2 m (G t) z`;
                 `\w:real^N. rfa_prof (rho / &4) (rho / &2) (norm w)`;
                 `a:real`; `b:real`; `sg:real`; `sg + tau:real`; `delta:real`;
                 `D:real`; `Bc:real`; `Lam:real`; `beta2:real`; `gam:real`]
         RFA_LOCAL_BARRIER) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`sg + tau:real`; `vec 0:real^N`]) THEN
  SUBGOAL_THEN `rfa_prof (rho / &4) (rho / &2) (norm(vec 0:real^N)) = &1`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_0] THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `&0`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_0] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LE_REFL; REAL_LT_01] THEN
  REWRITE_TAC[REAL_ADD_SUB; REAL_POW_ONE; REAL_INV_1; REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `&0 <= lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) (sg + tau)) (vec 0) /\
    &0 <= lrm_deriv_norm2 m ((G:real->real^N->real^N^N) (sg + tau)) (vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_RMD_POS THEN
    EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r0 = lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) (sg + tau)) (vec 0)` THEN
  ABBREV_TAC `r1 = lrm_deriv_norm2 m ((G:real->real^N->real^N^N) (sg + tau)) (vec 0)` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= r0 * r1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(Bq + r0) * r1 < Bc + inv(delta * tau) + Lam` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The local derivative estimate of order m >= 1 at the centre               *)
(* of the normal-coordinate ball (constants depending only on m, the bounds  *)
(* A i for i < m, K, rho and tau).                                           *)
(* ========================================================================= *)

let RFA_SLOC_STEP = prove
 (`!m (A:num->real) K rho tau.
     1 <= m /\ (!i. &0 <= A i) /\ &0 < rho /\ &0 <= K /\ &0 < tau
     ==> ?C. !a b (G:real->real^N->real^N^N) sg.
               lricci_flow (ball(vec 0,rho)) a b G /\ a < sg /\ sg + tau < b /\
               rfa_expc (G sg) rho K /\
               (!i s z. i < m /\ sg <= s /\ s <= sg + tau /\ norm z < rho
                        ==> lrm_deriv_norm2 i (G s) z <= A i)
               ==> lrm_deriv_norm2 m (G (sg + tau)) (vec 0) <= C`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Bq = &8 * (A:num->real)(m - 1) + &1` THEN
  SUBGOAL_THEN `&0 < Bq /\ &8 * (A:num->real)(m - 1) <= Bq /\ &0 <= A(m - 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Bq" THEN FIRST_ASSUM(MP_TAC o SPEC `m - 1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `A:num->real`; `Bq:real`] RFA_BERN_FLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (LABEL_TAC "bern")) THEN
  ABBREV_TAC `delta = inv(&2 * (Bq + (A:num->real)(m - 1)) pow 2)` THEN
  SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = sqrt(abs D / delta)` THEN
  SUBGOAL_THEN `&0 <= Lam /\ D <= delta * Lam pow 2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= abs D / delta` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    EXPAND_TAC "Lam" THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho / &4`; `rho / &2`; `rho:real`] RFA_PROF_DBOUNDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (X_CHOOSE_THEN `C2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd"))))) THEN
  ABBREV_TAC `E = exp(&2 * (&(dimindex(:N)) * sqrt((A:num->real) 0)) * tau)` THEN
  ABBREV_TAC `Cg = &3 * &(dimindex(:N)) * (&2 * E) * ((&2 * E) * sqrt(&2 * E))` THEN
  ABBREV_TAC
   `dq0 = if m = 1
          then &2 * sqrt(&(dimindex(:N)) / (Bq * delta)) * sqrt tau +
               sqrt(&(dimindex(:N)) / Bq) * sqrt Lam * tau
          else sqrt(&(dimindex(:N)) * (A:num->real) 1) * tau` THEN
  ABBREV_TAC `dq1 = if m = 1 then sqrt(&(dimindex(:N)) / Bq) * tau else &0` THEN
  ABBREV_TAC `beta2 = C1 pow 2 * E * &(dimindex(:N))` THEN
  ABBREV_TAC `g0 = (C2 + C1 * (inv(rho / &4) + K * rho)) * E` THEN
  SUBGOAL_THEN
   `&0 <= E /\ &0 <= Cg /\ &0 <= dq0 /\ &0 <= dq1 /\ &0 <= beta2 /\ &0 <= g0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 <= sqrt(&(dimindex(:N)) / (Bq * delta)) /\
      &0 <= sqrt(&(dimindex(:N)) / Bq) /\ &0 <= sqrt tau /\ &0 <= sqrt Lam /\
      &0 <= sqrt(&(dimindex(:N)) * (A:num->real) 1) /\ &0 <= sqrt(&2 * E)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
      TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Cg" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "dq0" THEN COND_CASES_TAC THEN
      REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
             CONJ_TAC) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "dq1" THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "beta2" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      EXPAND_TAC "g0" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`&2 * (g0 + C1 * (Cg * dq0) * (&2 * E)) * &(dimindex(:N)) + &6 * beta2`;
    `&2 * (C1 * (Cg * dq1) * (&2 * E)) * &(dimindex(:N))`; `delta:real`]
   RFA_BC_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
           CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bc:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(Bc + inv(delta * tau) + Lam) / Bq` THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `sg:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `gam = (g0 + C1 * (Cg * (dq0 + dq1 * sqrt Bc)) * (&2 * E)) *
                    &(dimindex(:N))` THEN
  SUBGOAL_THEN `&2 * gam + &6 * beta2 < delta * Bc` ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN
    UNDISCH_TAC
     `(&2 * (g0 + C1 * (Cg * dq0) * (&2 * E)) * &(dimindex(:N)) + &6 * beta2) +
      (&2 * (C1 * (Cg * dq1) * (&2 * E)) * &(dimindex(:N))) * sqrt Bc < delta * Bc` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t0 z. sg < t0 /\ t0 <= sg + tau /\ z IN ball(vec 0,rho) /\
           &0 < rfa_prof (rho / &4) (rho / &2) (norm z) /\
           (!t. sg < t /\ t <= t0
                ==> (Bq + lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t) z) *
                    lrm_deriv_norm2 m (G t) z <=
                    Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) +
                    inv(delta * (t - sg)) + Lam)
           ==> lgrad2 (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z <= beta2 /\
               --(rfa_prof (rho / &4) (rho / &2) (norm z) *
                  llap (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z) <= gam`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t0:real`; `z:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FH"))))) THEN
    SUBGOAL_THEN `norm(z:real^N) < rho` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_BALL_0]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!s z. sg <= s /\ s <= sg + tau /\ norm z < rho
            ==> lrm_deriv_norm2 0 ((G:real->real^N->real^N^N) s) z <= (A:num->real) 0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!v. rfa_prof (rho / &4) (rho / &2) (norm z) *
          norm(christoffel ((G:real->real^N->real^N^N) t0) z v v -
               christoffel (G sg) z v v) <=
          (Cg * (dq0 + dq1 * sqrt Bc)) * norm v pow 2`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `m = 1` THENL
       [SUBGOAL_THEN
         `dq0 + dq1 * sqrt Bc =
          &2 * sqrt(&(dimindex(:N)) / (Bq * delta)) * sqrt tau +
          sqrt(&(dimindex(:N)) / Bq) * (sqrt Bc + sqrt Lam) * tau`
        SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["dq0"; "dq1"] THEN REWRITE_TAC[ASSUME `m = 1`] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        REMOVE_THEN "FH" MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `sg:real`;
                       `t0:real`; `sg + tau:real`; `rho:real`; `K:real`;
                       `(A:num->real) 0`; `&2 * E`; `Bq:real`; `delta:real`;
                       `Bc:real`; `Lam:real`; `z:real^N`] RFA_SLOC_DG_BOOT) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ADD_SUB]; ALL_TAC] THEN
        REWRITE_TAC[REAL_ADD_SUB] THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `dq0 + dq1 * sqrt Bc = sqrt(&(dimindex(:N)) * (A:num->real) 1) * tau`
        SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["dq0"; "dq1"] THEN REWRITE_TAC[ASSUME `~(m = 1)`] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `sg:real`;
                       `t0:real`; `sg + tau:real`; `rho:real`; `K:real`;
                       `(A:num->real) 0`; `(A:num->real) 1`; `&2 * E`; `z:real^N`]
               RFA_SLOC_DG_HI) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[REAL_ADD_SUB] THEN
          REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          REWRITE_TAC[REAL_ADD_SUB] THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(real_derivative (rfa_prof (rho / &4) (rho / &2)) (norm(z:real^N))) <= C1 /\
      abs(real_derivative (real_derivative (rfa_prof (rho / &4) (rho / &2)))
                          (norm z)) <= C2`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "pd" MATCH_MP_TAC THEN REWRITE_TAC[REAL_ABS_NORM] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Cg * (dq0 + dq1 * sqrt Bc) /\ sg <= t0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `sg:real`;
                   `t0:real`; `sg + tau:real`; `rho:real`; `K:real`;
                   `(A:num->real) 0`; `C1:real`; `C2:real`;
                   `Cg * (dq0 + dq1 * sqrt Bc)`; `z:real^N`] RFA_SLOC_CUT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_SUB] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_SLOC_BARRIER_APPLY THEN
  MAP_EVERY EXISTS_TAC [`A:num->real`; `D:real`; `a:real`; `b:real`; `rho:real`;
                        `beta2:real`; `gam:real`] THEN
  ASM_REWRITE_TAC[]);;

