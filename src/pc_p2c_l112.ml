(* ========================================================================= *)
(* Unit pc_p2c_l112 (Part 2C): MT Lemma 11.2, the core form for regular      *)
(* views (P2C_LEMMA_11_2_DB_STATEMENT of pc_p2c_iface, proved outright as    *)
(* P2C_LEMMA_11_2_DB): where R >= r0^-2 the curvature derivative bounds      *)
(* |grad R| <= C R^(3/2) and |Lap R + 2|Ric|^2| <= C R^2 hold, the scalar    *)
(* curvature is controlled on a ball of radius 1/(2 C sqrt Q) and a time     *)
(* interval of length 1/(16 C Q') around (z,t0) (Q = max(R(z), r0^-2), Q' =  *)
(* max(0,R(z)) + r0^-2).  The proof follows MT: R^-1/2 is C/2-Lipschitz      *)
(* along curves (spatial step, bound 16/9 Q) and 1/R moves at speed <= C in  *)
(* time (temporal step, dR/dt = Lap R + 2|Ric|^2 at persisting points, from  *)
(* the Ricci flow p2c_vfam of the regular view in a restricted chart of the  *)
(* last time; continuity in time up to both ends of the persistence          *)
(* interval).  Lemma 11.2 for histories follows (P2C_LEMMA_11_2_COND) from   *)
(* P2C_CANON_DERIV and P2C_HISTORY_REGULAR.                                  *)
(* ========================================================================= *)

needs "src/pc_p2c_iface.ml";;
needs "src/pc_p2a_lgeo1.ml";;
needs "src/pc_apx_scal.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The one-variable comparison behind MT Lemma 11.2: where                   *)
(* |f'| <= C f^2 above a threshold, 1/f moves at speed <= C, so from         *)
(* f(t0) <= M one gets f <= M/(1 - C d M) at distance d from t0.             *)
(* ------------------------------------------------------------------------- *)

(* The last time in [a,b] at which a continuous f is below a level M. *)

let P2C_LAST_BELOW = prove
 (`!f a b M.
     a <= b /\ f real_continuous_on real_interval[a,b] /\ f a <= M
     ==> ?c. c IN real_interval[a,b] /\ f c <= M /\ !t. c < t /\ t <= b ==> M < f t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(f:real->real) b <= M` THENL
   [EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL
   [ASM_CASES_TAC `a:real = b` THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclideanreal`; `\u. (f:real->real)(b - u * (b - a))`;
                 `{x:real | M < x}`] GRGD_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GRGD_CONTINUOUS_MAP_REAL] THEN
      SUBGOAL_THEN `(\u. (f:real->real)(b - u * (b - a))) = f o (\u. b - u * (b - a))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
        MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `real_interval[a,b]` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
        X_GEN_TAC `u:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `u * (b - a) <= &1 * (b - a) ==> a <= b - u * (b - a)`) THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `&0 <= u * (b - a) ==> b - u * (b - a) <= b`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[GSYM REAL_OPEN_IN; GSYM real_gt; REAL_OPEN_HALFSPACE_GT];
      REWRITE_TAC[IN_ELIM_THM; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `&1` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM; REAL_MUL_LID;
                  REAL_ARITH `b - (b - a) = a`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `b - t1 * (b - a)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; REAL_NOT_LT]) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `t1 * (b - a) <= &1 * (b - a) ==> a <= b - t1 * (b - a)`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 <= t1 * (b - a) ==> b - t1 * (b - a) <= b`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(b - t) / (b - a)`) THEN
    SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_LDIV_EQ; REAL_SUB_LE; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ARITH `b - (b - t) = t`]]]);;

(* The forward comparison. *)

let P2C_ODE_FORWARD = prove
 (`!f f' t0 s C L M.
     t0 <= s /\ &0 < C /\ &0 < M /\ L <= M /\ C * (s - t0) * M < &1 /\
     f real_continuous_on real_interval[t0,s] /\
     (!u. u IN real_interval(t0,s) ==> (f has_real_derivative f' u) (atreal u)) /\
     (!u. u IN real_interval(t0,s) /\ L <= f u ==> abs(f' u) <= C * f u pow 2) /\
     f t0 <= M
     ==> f s <= M / (&1 - C * (s - t0) * M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `t0:real`; `s:real`; `M:real`] P2C_LAST_BELOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  SUBGOAL_THEN `&0 < &1 - C * (s - t0) * M` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c:real = s` THENL
   [UNDISCH_TAC `(f:real->real) c <= M` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= M * x ==> M * (&1 - x) <= M`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* on [c,s], f >= M *)
  SUBGOAL_THEN `(f:real->real) c = M` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ASSUME `f real_continuous_on real_interval[t0,s]`) THEN
    REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `M - (f:real->real) c`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min s (c + d / &2)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `min s (c + d / &2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. c <= u /\ u <= s ==> M <= (f:real->real) u` ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN ASM_CASES_TAC `u:real = c` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. inv((f:real->real) u)`;
                 `\u. --((f':real->real) u) / (f:real->real) u pow 2`; `c:real`; `s:real`]
         REAL_MVT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `real_interval[t0,s]` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN REPEAT STRIP_TAC THEN
        MP_TAC(SPEC `x:real` (ASSUME `!u. c <= u /\ u <= s ==> M <= (f:real->real) u`)) THEN
        ASM_REAL_ARITH_TAC];
      X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((f:real->real) u = &0)` ASSUME_TAC THENL
       [MP_TAC(SPEC `u:real` (ASSUME `!u. c <= u /\ u <= s ==> M <= (f:real->real) u`)) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real->real`; `(f':real->real) u`; `u:real`]
             HAS_REAL_DERIVATIVE_INV_ATREAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `xi:real` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  SUBGOAL_THEN `M <= (f:real->real) xi /\ M <= f s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs((f':real->real) xi) <= C * f xi pow 2` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(--((f':real->real) xi) / (f:real->real) xi pow 2) <= C` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (f:real->real) xi pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG; REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_LE_LDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(M) - C * (s - t0) <= inv((f:real->real) s)` ASSUME_TAC THENL
   [UNDISCH_TAC `inv((f:real->real) s) - inv(f c) =
                 --((f':real->real) xi) / f xi pow 2 * (s - c)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(--((f':real->real) xi) / (f:real->real) xi pow 2 * (s - c)) <=
                  C * (s - t0)` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (f:real->real) s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv(M) - C * (s - t0) = (&1 - C * (s - t0) * M) / M` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - C * (s - t0) * M) / M <= inv((f:real->real) s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - C * (s - t0) * M) <= inv((f:real->real) s) * M` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - C * (s - t0) * M) * (f:real->real) s <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(inv((f:real->real) s) * M) * f s` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `(inv((f:real->real) s) * M) * f s = M` SUBST1_TAC THENL
       [SUBGOAL_THEN `~((f:real->real) s = &0)` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
        REWRITE_TAC[REAL_LE_REFL]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* The backward comparison, by reflection. *)

let P2C_ODE_BACKWARD = prove
 (`!f f' t0 s C L M.
     s <= t0 /\ &0 < C /\ &0 < M /\ L <= M /\ C * (t0 - s) * M < &1 /\
     f real_continuous_on real_interval[s,t0] /\
     (!u. u IN real_interval(s,t0) ==> (f has_real_derivative f' u) (atreal u)) /\
     (!u. u IN real_interval(s,t0) /\ L <= f u ==> abs(f' u) <= C * f u pow 2) /\
     f t0 <= M
     ==> f s <= M / (&1 - C * (t0 - s) * M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u. (f:real->real)(--u)`; `\u. --((f':real->real)(--u))`;
                 `--t0`; `--s`; `C:real`; `L:real`; `M:real`] P2C_ODE_FORWARD) THEN
  REWRITE_TAC[REAL_NEG_NEG; REAL_ARITH `--s - --t0 = t0 - s`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_NEG2] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\u. (f:real->real)(--u)) = f o (\u. --u)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[s,t0]` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\u:real. --u`; `f:real->real`; `--(&1)`; `(f':real->real)(--u)`;
                   `u:real`] REAL_DIFF_CHAIN_ATREAL) THEN
    REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`\u:real. u`; `&1`; `atreal u`] HAS_REAL_DERIVATIVE_NEG) THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_ID];
        FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_ABS_NEG] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of R along a C^1 curve is bounded by                       *)
(* |grad R| times the speed (Cauchy-Schwarz for the metric).                 *)
(* ------------------------------------------------------------------------- *)

let P2C_DISCRIMINANT = prove
 (`!A B C. &0 <= A /\ (!x. &0 <= x pow 2 * A + &2 * x * C + B) ==> C pow 2 <= A * B`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `A = &0` THENL
   [ASM_CASES_TAC `C = &0` THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--(abs B + &1) / (&2 * C)`) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `&2 * --(abs B + &1) / (&2 * C) * C = --(abs B + &1)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(C = &0)` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--C / A`) THEN
  SUBGOAL_THEN `(--C / A) pow 2 * A + &2 * (--C / A) * C + B = B - C pow 2 / A`
  SUBST1_TAC THENL [UNDISCH_TAC `~(A = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let P2C_METRIC_CS = prove
 (`!(G:real^N^N) u v.
     (!x y. x dot (G ** y) = y dot (G ** x)) /\ (!x. &0 <= x dot (G ** x))
     ==> (u dot (G ** v)) pow 2 <= (u dot (G ** u)) * (v dot (G ** v))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC P2C_DISCRIMINANT THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t % v + u:real^N`) THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LADD; DOT_RADD;
              DOT_LMUL; DOT_RMUL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[SPECL [`v:real^N`; `u:real^N`] th]) THEN
  REAL_ARITH_TAC);;

(* |dR(v)| <= sqrt(|grad R|^2) sqrt(v.Gv) in a chart. *)

let P2C_LGRAD2_BOUND = prove
 (`!U (G:real^N->real^N^N) (f:real^N->real) y v.
     metric_field U G /\ y IN U /\ (\z. lift(f z)) differentiable at y
     ==> abs(drop(frechet_derivative (\z. lift(f z)) (at y) v)) <=
         sqrt(lgrad2 G f y) * sqrt(v dot (G y ** v))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = frechet_derivative (\z. lift((f:real^N->real) z)) (at y)` THEN
  SUBGOAL_THEN `linear(L:real^N->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `w:real^N = lambda i. drop(L(basis i:real^N))` THEN
  SUBGOAL_THEN `drop((L:real^N->real^1) v) = w dot v` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`L:real^N->real^1`; `v:real^N`] LRG_LINEAR_DROP_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
           LRG_METRIC_INVERTIBLE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y /\
                (!x. ~(x = vec 0) ==> &0 < x dot (G y ** x))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN REWRITE_TAC[metric_field] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x z:real^N. x dot (G y ** z) = z dot ((G:real^N->real^N^N) y ** x)`
  (LABEL_TAC "sym") THENL
   [REPEAT GEN_TAC THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [GSYM(ASSUME
      `transp((G:real^N->real^N^N) y) = G y`)] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. &0 <= x dot ((G:real^N->real^N^N) y ** x)` (LABEL_TAC "pos")
  THENL
   [GEN_TAC THEN ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_SIMP_TAC[DOT_LZERO; REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `lgrad2 G f y = (w:real^N) dot (matrix_inv((G:real^N->real^N^N) y) ** w)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!k. 1 <= k /\ k <= dimindex(:N)
                      ==> drop((L:real^N->real^1)(basis k)) = (w:real^N)$k`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "w" THEN ASM_SIMP_TAC[LAMBDA_BETA]; ALL_TAC] THEN
    ASM_REWRITE_TAC[lgrad2; dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u:real^N = matrix_inv((G:real^N->real^N^N) y) ** w` THEN
  SUBGOAL_THEN `w = (G:real^N->real^N^N) y ** u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) dot u = u dot ((G:real^N->real^N^N) y ** u)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ASSUME `w = (G:real^N->real^N^N) y ** u`] THEN
    REWRITE_TAC[DOT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) dot v = u dot ((G:real^N->real^N^N) y ** v)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ASSUME `w = (G:real^N->real^N^N) y ** u`] THEN
    GEN_REWRITE_TAC LAND_CONV [DOT_SYM] THEN
    USE_THEN "sym" (fun th -> REWRITE_TAC[SPECL [`v:real^N`; `u:real^N`] th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `u:real^N`; `v:real^N`] P2C_METRIC_CS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= u dot ((G:real^N->real^N^N) y ** u) /\ &0 <= v dot (G y ** v)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  ASM_REWRITE_TAC[REAL_POW2_ABS]);;

(* ------------------------------------------------------------------------- *)
(* The derivative of R along a C^1 curve at interior times,                  *)
(* bounded by |grad R| times the speed.                                      *)
(* ------------------------------------------------------------------------- *)

(* The derivative of R along a C^1 curve at interior times. *)

let P2C_SCALAR_CURVE_DERIV = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma a b /\ a < t /\ t < b
     ==> ?D. ((\s. mfd_scalar atlas g (gamma s)) has_real_derivative D) (atreal t) /\
             abs D <= sqrt(rfs_scalar_grad2 atlas g (gamma t)) *
                      mfd_speed atlas g gamma a b t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t IN real_interval[a,b]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)`
               PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  ABBREV_TAC `G = metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (phi:A->real^N) U) G` ASSUME_TAC THENL
   [UNDISCH_TAC `riemannian_metric atlas (g:A->real^N^N)` THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) U)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:A->real^N)((gamma:real->A) t) IN IMAGE phi U` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(lscalar (G:real^N->real^N^N) z)) differentiable at ((phi:A->real^N)((gamma:real->A) t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) U` THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
    ALL_TAC] THEN
  ABBREV_TAC `L = frechet_derivative (\z. lift(lscalar (G:real^N->real^N^N) z))
                    (at ((phi:A->real^N)((gamma:real->A) t)))` THEN
  ABBREV_TAC `v = vector_derivative (\s. (phi:A->real^N)((gamma:real->A)(drop s)))
                    (at (lift t) within interval[lift a,lift b])` THEN
  SUBGOAL_THEN `((\s. (phi:A->real^N)((gamma:real->A)(drop s))) has_vector_derivative v)
                (at (lift t))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `gamma:real->A`; `a:real`; `b:real`;
                   `(U:A->bool,phi:A->real^N)`; `t:real`] GRGD_C1_CHART_HAS_VD) THEN
    ASM_REWRITE_TAC[FST; SND] THEN
    DISCH_THEN(MP_TAC o SPEC `interval(lift a,lift b)` o
               MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET)) THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
    REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_OPEN THEN
    REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `drop((L:real^N->real^1) v)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U`; `G:real^N->real^N^N`; `lscalar (G:real^N->real^N^N)`;
                   `(phi:A->real^N)((gamma:real->A) t)`; `v:real^N`] P2C_LGRAD2_BOUND) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
    REWRITE_TAC[rfs_scalar_grad2] THEN ASM_REWRITE_TAC[SND] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `a:real`; `b:real`; `t:real`;
                   `U:A->bool`; `phi:A->real^N`] MFD_SPEED_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  (* the derivative *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `gamma:real->A`; `a:real`; `b:real`; `U:A->bool`; `t:real`]
         GRGD_CURVE_TIMES_BALL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[GRGD_ATLAS_CHART; FST]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC [`\s. lscalar (G:real^N->real^N^N) ((phi:A->real^N)((gamma:real->A) s))`;
                        `min d (min (t - a) (b - t))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    EXPAND_TAC "G" THEN MATCH_MP_TAC MFD_SCALAR_CHART THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift s`) THEN REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
    REWRITE_TAC[has_vector_derivative] THEN
    MP_TAC(ISPECL [`\s. (phi:A->real^N)((gamma:real->A)(drop s))`;
                   `\z. lift(lscalar (G:real^N->real^N^N) z)`;
                   `(\h. drop h % v):real^1->real^N`; `L:real^N->real^1`; `lift t`]
           DIFF_CHAIN_AT) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_REWRITE_TAC[GSYM has_vector_derivative];
        REWRITE_TAC[LIFT_DROP] THEN EXPAND_TAC "L" THEN
        REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
    SUBGOAL_THEN `linear(L:real^N->real^1)` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_CMUL] THEN REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The spatial step of MT Lemma 11.2: along a curve of length                *)
(* at most 1/(2 C sqrt Q) from z, R stays below 16/9 Q.                      *)
(* ------------------------------------------------------------------------- *)

(* The last time at a level M crossed upwards. *)

let P2C_LAST_AT = prove
 (`!f a b M.
     a <= b /\ f real_continuous_on real_interval[a,b] /\ f a <= M /\ M < f b
     ==> ?c. a <= c /\ c < b /\ f c = M /\ !t. c < t /\ t <= b ==> M < f t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `b:real`; `M:real`] P2C_LAST_BELOW) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `c < b` ASSUME_TAC THENL
   [ASM_CASES_TAC `c:real = b` THENL
     [UNDISCH_TAC `(f:real->real) c <= M` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ASSUME `f real_continuous_on real_interval[a,b]`) THEN
  REWRITE_TAC[real_continuous_on; IN_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `c:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `M - (f:real->real) c`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min b (c + d / &2)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min b (c + d / &2)`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC);;

(* R along a C^1 curve is continuous. *)

let P2C_SCALAR_CURVE_CONT = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma a b
     ==> (\s. mfd_scalar atlas g (gamma s)) real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM GRGD_CONTINUOUS_MAP_REAL] THEN
  SUBGOAL_THEN `(\s. mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A) s)) =
                mfd_scalar atlas g o gamma` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `top:A topology` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[mfd_c1_curve];
    MATCH_MP_TAC MFD_SCALAR_CONTINUOUS THEN ASM_REWRITE_TAC[]]);;

let P2C_SCALAR_CURVE_DERIV2 = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) a b t.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_c1_curve (top,atlas) gamma a b /\ a < t /\ t < b
     ==> ((\s. mfd_scalar atlas g (gamma s)) has_real_derivative
          real_derivative (\s. mfd_scalar atlas g (gamma s)) t) (atreal t) /\
         abs(real_derivative (\s. mfd_scalar atlas g (gamma s)) t) <=
         sqrt(rfs_scalar_grad2 atlas g (gamma t)) * mfd_speed atlas g gamma a b t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2C_SCALAR_CURVE_DERIV) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `real_derivative (\s. mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A) s)) t = D`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DERIVATIVE_UNIQUE_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s. mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A) s)`;
                          `t:real`] THEN
    ASM_REWRITE_TAC[real_derivative] THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The derivative of R^(-1/2) along the curve, and its bound C/2 times the  *)
(* speed where R >= r0^-2.                                                   *)

let P2C_UINV_DERIV_BOUND = prove
 (`!top atlas (g:A->real^N^N) C r0 (gamma:real->A) s.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < C /\ &0 < r0 /\
     (!x. x IN topspace top /\ inv(r0 pow 2) <= mfd_scalar atlas g x
          ==> sqrt(rfs_scalar_grad2 atlas g x) <=
              C * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x)) /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\ &0 < s /\ s < &1 /\
     inv(r0 pow 2) <= mfd_scalar atlas g (gamma s)
     ==> ((\s. inv(sqrt(mfd_scalar atlas g (gamma s)))) has_real_derivative
          (--(real_derivative (\s. mfd_scalar atlas g (gamma s)) s) /
           (&2 * mfd_scalar atlas g (gamma s) * sqrt(mfd_scalar atlas g (gamma s)))))
         (atreal s) /\
         abs(--(real_derivative (\s. mfd_scalar atlas g (gamma s)) s) /
             (&2 * mfd_scalar atlas g (gamma s) * sqrt(mfd_scalar atlas g (gamma s)))) <=
         C / &2 * mfd_speed atlas g gamma (&0) (&1) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `&0`; `&1`; `s:real`]
         P2C_SCALAR_CURVE_DERIV2) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = real_derivative (\s. mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A) s)) s` THEN
  ABBREV_TAC `R = mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A) s)` THEN
  ABBREV_TAC `v = mfd_speed atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1) s` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < R /\ &0 < sqrt R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`\s. mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A) s)`;
                   `\x. inv(sqrt x)`; `D:real`;
                   `--inv(sqrt R pow 2) * inv(&2 * sqrt R)`; `s:real`]
           REAL_DIFF_CHAIN_ATREAL) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [MP_TAC(ISPECL [`sqrt`; `\x:real. inv x`; `inv(&2 * sqrt R)`;
                     `--inv(sqrt R pow 2)`; `R:real`] REAL_DIFF_CHAIN_ATREAL) THEN
      ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
      MP_TAC(ISPEC `sqrt R` HAS_REAL_DERIVATIVE_INV_BASIC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN REWRITE_TAC[REAL_POW_2; REAL_INV_MUL; ETA_AX];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < sqrt R` THEN UNDISCH_TAC `&0 < R` THEN
      SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs D <= C * R * sqrt R * v` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(rfs_scalar_grad2 atlas (g:A->real^N^N) ((gamma:real->A) s)) * v` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `C * R * sqrt R * v = (C * R * sqrt R) * v` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [EXPAND_TAC "R" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MFD_C1_CURVE_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `&0`; `&1`] THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "v" THEN MATCH_MP_TAC MFD_SPEED_POS_LE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * R * sqrt R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * R * sqrt R * v` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC);;

let P2C_SPATIAL_BOUND = prove
 (`!top atlas (g:A->real^N^N) C r0 (gamma:real->A).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < C /\ &0 < r0 /\
     (!x. x IN topspace top /\ inv(r0 pow 2) <= mfd_scalar atlas g x
          ==> sqrt(rfs_scalar_grad2 atlas g x) <=
              C * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x)) /\
     mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     mfd_length atlas g gamma (&0) (&1) <=
     inv(&2 * C * sqrt(max (mfd_scalar atlas g (gamma(&0))) (inv(r0 pow 2))))
     ==> mfd_scalar atlas g (gamma(&1)) <=
         &16 / &9 * max (mfd_scalar atlas g (gamma(&0))) (inv(r0 pow 2))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Q = max (mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A)(&0)))
                      (inv(r0 pow 2))` THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2) /\ inv(r0 pow 2) <= Q /\ &0 < Q /\
                mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A)(&0)) <= Q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "Q" THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `fR = \s. mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A) s)` THEN
  SUBGOAL_THEN `(fR:real->real) real_continuous_on real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "fR" THEN MATCH_MP_TAC P2C_SCALAR_CURVE_CONT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_scalar atlas (g:A->real^N^N) ((gamma:real->A)(&1)) = fR(&1) /\
                mfd_scalar atlas g (gamma(&0)) = fR(&0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "fR" THEN REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(fR:real->real)(&1) <= Q` THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`fR:real->real`; `&0`; `&1`; `Q:real`] P2C_LAST_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s. c <= s /\ s <= &1 ==> Q <= (fR:real->real) s` ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_CASES_TAC `s:real = c` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `sp = mfd_speed atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)` THEN
  ABBREV_TAC
   `du = \s. if c < s /\ s < &1
             then --(real_derivative (fR:real->real) s) /
                  (&2 * fR s * sqrt(fR s))
             else --(C / &2 * sp s)` THEN
  SUBGOAL_THEN `(du has_real_integral
                 ((\s. inv(sqrt((fR:real->real) s))) (&1) - (\s. inv(sqrt(fR s))) c))
                (real_interval[c,&1])` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN CONJ_TAC THENL
       [SUBGOAL_THEN `(\s. sqrt((fR:real->real) s)) = sqrt o fR` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval[&0,&1]` THEN
        ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        ASM_REAL_ARITH_TAC;
        X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SQRT_POS_LT THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `Q:real` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "du" THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "fR" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `C:real`; `r0:real`; `gamma:real->A`; `s:real`]
             P2C_UINV_DERIV_BOUND) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q:real` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `Q <= (fR:real->real) s` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; EXPAND_TAC "fR" THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sp:real->real) real_integrable_on real_interval[&0,&1]` ASSUME_TAC THENL
   [EXPAND_TAC "sp" THEN MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sp:real->real) real_integrable_on real_interval[c,&1]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN ASM_REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. &0 <= s /\ s <= &1 ==> &0 <= (sp:real->real) s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "sp" THEN MATCH_MP_TAC MFD_SPEED_POS_LE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--(C / &2 * real_integral (real_interval[c,&1]) sp) <=
    inv(sqrt((fR:real->real) (&1))) - inv(sqrt(fR c))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(BETA_RULE(MATCH_MP REAL_INTEGRAL_UNIQUE th))]) THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; GSYM REAL_INTEGRAL_NEG; REAL_INTEGRABLE_LMUL] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_NEG THEN MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[real_integrable_on] THEN ASM_MESON_TAC[];
      X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXPAND_TAC "du" THEN COND_CASES_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `C:real`; `r0:real`; `gamma:real->A`; `s:real`]
             P2C_UINV_DERIV_BOUND) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q:real` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `Q <= (fR:real->real) s` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
          EXPAND_TAC "fR" THEN SIMP_TAC[]];
        ALL_TAC] THEN
      EXPAND_TAC "fR" THEN EXPAND_TAC "sp" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[c,&1]) sp <=
                mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_length] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt Q /\ &0 < sqrt((fR:real->real)(&1)) /\
                sqrt Q pow 2 = Q /\ sqrt(fR(&1)) pow 2 = fR(&1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &4 * inv(sqrt Q) <= inv(sqrt((fR:real->real)(&1)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `C / &2 * mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1) <=
                  inv(&4 * sqrt Q)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C / &2 * inv(&2 * C * sqrt Q)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < C` THEN UNDISCH_TAC `&0 < sqrt Q` THEN CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(sqrt((fR:real->real) c)) = inv(sqrt Q)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `C / &2 * real_integral (real_interval[c,&1]) sp <= inv(&4 * sqrt Q)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C / &2 * mfd_length atlas (g:A->real^N^N) (gamma:real->A) (&0) (&1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&4 * sqrt Q) = &1 / &4 * inv(sqrt Q)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt((fR:real->real)(&1)) <= &4 / &3 * sqrt Q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 / &3 * sqrt Q = inv(&3 / &4 * inv(sqrt Q))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < sqrt Q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RINV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt((fR:real->real)(&1)) pow 2 <= (&4 / &3 * sqrt Q) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The pullback metric of a local diffeomorphism (mfd_diffeo                *)
(* on open sets W, W') in an arbitrary chart pair, at points of W (the      *)
(* global case is MFD_PULLBACK_METRIC_LOCAL of pc_mfd_restrict; same proof). *)
(* ------------------------------------------------------------------------- *)

let P2C_PULLBACK_METRIC_LOCAL_W = prove
 (`!top atlas W top' atlas' W' (f:A->B) f' (g':B->real^N^N) (U:A->bool)
    (phi:A->real^N) (V:B->bool) (psi:B->real^N) x.
        smooth_manifold_atlas top atlas /\ smooth_manifold_atlas top' atlas' /\
        mfd_diffeo top atlas W top' atlas' W' f f' /\
        (U,phi) IN atlas /\ (V,psi) IN atlas' /\ x IN U /\ x IN W /\ f x IN V
        ==> metric_local atlas (U,phi) (mfd_pullback_metric atlas atlas' f g')
                         (phi x) =
            mpullback (psi o f o chart_inv (U,phi))
                      (metric_local atlas' (V,psi) g') (phi x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (U:A->bool)`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (W:A->bool) /\ open_in top' (W':B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top'` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top' (W':B->bool)`)) THEN
    UNDISCH_TAC `IMAGE (f:A->B) W SUBSET W'` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [metric_local] THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN U`)]) THEN
  REWRITE_TAC[mfd_pullback_metric] THEN BETA_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `c0:(A->bool)#(A->real^N)`) THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) x`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas':((B->bool)#(B->real^N))->bool) ((f:A->B) x)`,
           `c0':(B->bool)#(B->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V0:B->bool`; `psi0:B->real^N`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`U0:A->bool`; `phi0:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`]
                MFDM_CHART) THEN
  DISCH_THEN(MP_TAC o SPEC `(U0:A->bool,phi0:A->real^N)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  (* the chart representative h0 of f at x is smooth near phi0 x *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `W:A->bool`;
                 `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                 `W':B->bool`; `f:A->B`; `f':B->A`;
                 `U0:A->bool`; `phi0:A->real^N`; `V0:B->bool`; `psi0:B->real^N`]
                MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  ABBREV_TAC `h0 = (psi0:B->real^N) o (f:A->B) o chart_inv (U0:A->bool,phi0:A->real^N)` THEN
  SUBGOAL_THEN `(h0:real^N->real^N) differentiable at ((phi0:A->real^N) x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (phi0:A->real^N)
                      {z | z IN U0 INTER W /\ (f:A->B) z IN V0}`;
                   `h0:real^N->real^N`; `(phi0:A->real^N) x`; `vec 0:real^N`]
                  LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h0:real^N->real^N) ((phi0:A->real^N) x) = (psi0:B->real^N) (f x)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h0" THEN REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the derivative identity, by locality and the chain rule *)
  SUBGOAL_THEN
   `frechet_derivative ((psi:B->real^N) o (f:A->B) o chart_inv (U,phi))
                       (at ((phi:A->real^N) x)) =
    chart_jac (V0,psi0) (V,psi) (f x) o
    frechet_derivative (h0:real^N->real^N) (at ((phi0:A->real^N) x)) o
    chart_jac (U,phi) (U0,phi0) x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`]
                  MFDM_CHART) THEN
    DISCH_THEN(MP_TAC o SPEC `(V0:B->bool,psi0:B->real^N)`) THEN
    ASM_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `frechet_derivative
        (\y. chart_trans (V0:B->bool,psi0:B->real^N) (V,psi)
               ((h0:real^N->real^N)
                  (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)))
        (at ((phi:A->real^N) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
      EXISTS_TAC `IMAGE (phi:A->real^N)
                    {z | z IN U INTER {z | z IN U0 INTER W /\ (f:A->B) z IN V0} /\
                         f z IN V}` THEN
      REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN `open_in top {z | z IN U0 INTER W /\ (f:A->B) z IN V0}` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                         `(U0:A->bool,phi0:A->real^N)`; `(V0:B->bool,psi0:B->real^N)`;
                         `W:A->bool`; `f:A->B`] MFDM_CHART_DOMAIN_OPEN) THEN
          ASM_REWRITE_TAC[FST; SND] THEN SIMP_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                       `(U:A->bool,phi:A->real^N)`; `(V:B->bool,psi:B->real^N)`;
                       `{z | z IN U0 INTER W /\ (f:A->B) z IN V0}`; `f:A->B`]
                      MFDM_CHART_DOMAIN_OPEN) THEN
        REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
          EXISTS_TAC `W:A->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
          SIMP_TAC[]];
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EXISTS_TAC `x:A` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
        X_GEN_TAC `z:A` THEN STRIP_TAC THEN EXPAND_TAC "h0" THEN
        REWRITE_TAC[o_THM] THEN
        MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                      `U:A->bool`; `phi:A->real^N`; `U0:A->bool`; `phi0:A->real^N`;
                      `z:A`] CHART_TRANS_AT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC CHART_TRANS_AT THEN
        MAP_EVERY EXISTS_TAC
         [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `w:real^N` THEN
    REWRITE_TAC[chart_jac; SND] THEN
    SUBGOAL_THEN
     `chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) differentiable at (phi x) /\
      chart_trans (U,phi) (U0,phi0) (phi x) = phi0 x`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `chart_jac (U:A->bool,phi:A->real^N) (U0,phi0) x` THEN
        MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[IN_INTER];
        MATCH_MP_TAC CHART_TRANS_AT THEN
        MAP_EVERY EXISTS_TAC
         [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `chart_trans (V0:B->bool,psi0:B->real^N) (V,psi) differentiable
      at (psi0((f:A->B) x))`
    ASSUME_TAC THENL
     [REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `chart_jac (V0:B->bool,psi0:B->real^N) (V,psi) ((f:A->B) x)` THEN
      MATCH_MP_TAC CHART_TRANS_HAS_DERIVATIVE THEN
      MAP_EVERY EXISTS_TAC
       [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y))
      differentiable at (phi x)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `(\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)) =
        h0 o chart_trans (U,phi) (U0,phi0)`
       SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`\y. (h0:real^N->real^N) (chart_trans (U:A->bool,phi:A->real^N) (U0,phi0) y)`;
      `chart_trans (V0:B->bool,psi0:B->real^N) (V,psi)`;
      `(phi:A->real^N) x`; `w:real^N`] LRG_FRECHET_DERIVATIVE_CHAIN)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL
     [`chart_trans (U:A->bool,phi:A->real^N) (U0,phi0)`; `h0:real^N->real^N`;
      `(phi:A->real^N) x`; `w:real^N`] LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LRG_MPULLBACK_EQ] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((psi:B->real^N) o (f:A->B) o chart_inv (U,phi)) ((phi:A->real^N) x) =
    psi (f x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`;
                `V0:B->bool`; `psi0:B->real^N`; `V:B->bool`; `psi:B->real^N`;
                `g':B->real^N^N`; `(f:A->B) x`] METRIC_LOCAL_JAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `linear(chart_jac (U:A->bool,phi:A->real^N) (U0,phi0) (x:A)) /\
    linear(chart_jac (V0:B->bool,psi0:B->real^N) (V,psi) ((f:A->B) x)) /\
    linear(frechet_derivative (h0:real^N->real^N) (at ((phi0:A->real^N) x)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC CHART_JAC_LINEAR THEN
      MAP_EVERY EXISTS_TAC
       [`top':B topology`; `atlas':((B->bool)#(B->real^N))->bool`] THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_COMPOSE; MATRIX_TRANSP_MUL;
               MATRIX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The pullback metric of a diffeomorphism is a riemannian                   *)
(* metric and makes f an isometry (mfd_isometry of pc_grg_dist); scalar and  *)
(* sectional curvature are natural under isometries.                         *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* R, Lap R and |Ric|^2 of two chart representatives related                *)
(* by a local diffeomorphism agree; chart independence of rfs_scalar_lap    *)
(* and rfs_ric_norm2.                                                       *)
(* ------------------------------------------------------------------------- *)

let P2C_LTNORM2_CONG = prove
 (`!k (G1:real^N->real^N^N) G2 tf1 tf2 y.
     G1 y = G2 y /\ tf1 y = tf2 y ==> ltnorm2 k G1 tf1 y = ltnorm2 k G2 tf2 y`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ltnorm2]);;

let P2C_LRIC2_ETA = prove
 (`!G:real^N->real^N^N. (\z u. lricci G z (u 1) (u 2)) = lric2 G`,
  REWRITE_TAC[FUN_EQ_THM; lric2]);;

let P2C_REP_TRANSFER = prove
 (`!t t' (h:real^N->real^N) h' (G:real^N->real^N^N) G' y.
     diffeomorphism_on t t' h h' /\ metric_field t' G' /\ y IN t /\
     (!z. z IN t ==> G z = mpullback h G' z)
     ==> lscalar G y = lscalar G' (h y) /\
         llap G (lscalar G) y = llap G' (lscalar G') (h y) /\
         ltnorm2 2 G (lric2 G) y = ltnorm2 2 G' (lric2 G') (h y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(t:real^N->bool) /\ open(t':real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN t ==> lscalar (G:real^N->real^N^N) z = lscalar G' ((h:real^N->real^N) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `lscalar (mpullback (h:real^N->real^N) (G':real^N->real^N^N)) z` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LSCALAR_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `t:real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    TRANS_TAC EQ_TRANS `llap (mpullback (h:real^N->real^N) (G':real^N->real^N^N))
                             (lscalar G' o h) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[o_THM];
      MATCH_MP_TAC LLAP_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `t:real^N->bool`; `h':real^N->real^N`] THEN
      ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]];
    TRANS_TAC EQ_TRANS
     `ltnorm2 2 (mpullback (h:real^N->real^N) (G':real^N->real^N^N))
                (ltpullback h (lric2 G')) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_LTNORM2_CONG THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FUN_EQ_THM; ltpullback; lric2] THEN BETA_TAC THEN
      X_GEN_TAC `u:num->real^N` THEN
      TRANS_TAC EQ_TRANS
       `lricci (mpullback (h:real^N->real^N) (G':real^N->real^N^N)) y (u 1) (u 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC LRICCI_PULLBACK THEN
        MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `t:real^N->bool`; `h':real^N->real^N`] THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC LTNORM2_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`t':real^N->bool`; `t:real^N->bool`; `h':real^N->real^N`] THEN
      ASM_SIMP_TAC[LRG_LRIC2_FIELD]]]);;

(* Chart independence. *)

let P2C_LAP_RIC_CHART = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) (g:A->real^N^N) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (U,phi) IN atlas /\ x IN U
     ==> rfs_scalar_lap atlas g x =
         llap (metric_local atlas (U,phi) g) (lscalar (metric_local atlas (U,phi) g))
              (phi x) /\
         rfs_ric_norm2 atlas g x =
         ltnorm2 2 (metric_local atlas (U,phi) g) (lric2 (metric_local atlas (U,phi) g))
                 (phi x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[rfs_scalar_lap; rfs_ric_norm2; P2C_LRIC2_ETA] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) x` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER V)`; `IMAGE (psi:A->real^N) (U INTER V)`;
                 `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
                 `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
                 `metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N)`;
                 `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
                 `(phi:A->real^N) x`] P2C_REP_TRANSFER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
               CHART_TRANS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* R, Lap R and |Ric|^2 of the slices of p2c_vfam in charts of              *)
(* the restricted atlas of the last time: restricted metrics and restricted *)
(* pullbacks by the identity of a diffeomorphism on W.                      *)
(* ------------------------------------------------------------------------- *)

let P2C_REP_LOCAL = prove
 (`!t (G:real^N->real^N^N) G' y.
     open t /\ y IN t /\ (!z. z IN t ==> G z = G' z)
     ==> lscalar G y = lscalar G' y /\
         llap G (lscalar G) y = llap G' (lscalar G') y /\
         ltnorm2 2 G (lric2 G) y = ltnorm2 2 G' (lric2 G') y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN t ==> lscalar (G:real^N->real^N^N) z = lscalar G' z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC P2C_LTNORM2_CONG THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[FUN_EQ_THM; lric2] THEN X_GEN_TAC `u:num->real^N` THEN
    MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let P2C_RESTRICT_CURV = prove
 (`!top atlas (W:A->bool) (g:A->real^N^N) (U:A->bool) (phi:A->real^N) x
    (G:real^N->real^N^N).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ open_in top W /\
     (U,phi) IN atlas /\ x IN U /\ x IN W /\
     (!z. z IN IMAGE phi (U INTER W)
          ==> G z = metric_local (restrict_atlas atlas W) (U INTER W,phi)
                                 (restrict_metric atlas W g) z)
     ==> lscalar G (phi x) = mfd_scalar atlas g x /\
         llap G (lscalar G) (phi x) = rfs_scalar_lap atlas g x /\
         ltnorm2 2 G (lric2 G) (phi x) = rfs_ric_norm2 atlas g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) (U INTER W)`; `G:real^N->real^N^N`;
                 `metric_local atlas (U:A->bool,phi:A->real^N) (g:A->real^N^N)`;
                 `(phi:A->real^N) x`] P2C_REP_LOCAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      TRANS_TAC EQ_TRANS
       `metric_local (restrict_atlas atlas W) (U INTER W,phi:A->real^N)
                     (restrict_metric atlas W (g:A->real^N^N)) (phi(x':A))` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
        MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[IN_INTER]]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `g:A->real^N^N`; `x:A`] P2C_LAP_RIC_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `g:A->real^N^N`; `x:A`] MFD_SCALAR_CHART) THEN
  ASM_SIMP_TAC[]);;

let P2C_PULLBACK_CURV = prove
 (`!topb atlasb topu atlasu (W:A->bool) (g:A->real^N^N) (U:A->bool) (phi:A->real^N) x
    (G:real^N->real^N^N).
     smooth_manifold_atlas topb atlasb /\ smooth_manifold_atlas topu atlasu /\
     riemannian_metric atlasu g /\
     mfd_diffeo topu atlasu W topb atlasb W (\y. y) (\y. y) /\
     (U,phi) IN atlasb /\ x IN U /\ x IN W /\
     (!z. z IN IMAGE phi (U INTER W)
          ==> G z = metric_local (restrict_atlas atlasb W) (U INTER W,phi)
                      (restrict_metric atlasb W
                         (mfd_pullback_metric atlasb atlasu (\y. y) g)) z)
     ==> lscalar G (phi x) = mfd_scalar atlasu g x /\
         llap G (lscalar G) (phi x) = rfs_scalar_lap atlasu g x /\
         ltnorm2 2 G (lric2 G) (phi x) = rfs_ric_norm2 atlasu g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_diffeo topb (atlasb:((A->bool)#(A->real^N))->bool) W
                           topu (atlasu:((A->bool)#(A->real^N))->bool) W (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_DIFFEO_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in topb (W:A->bool) /\ open_in topu W` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_diffeo]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace topu` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`topu:A topology`; `atlasu:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[rfs_scalar_lap; rfs_ric_norm2; mfd_scalar; P2C_LRIC2_ETA] THEN
  MP_TAC(ISPEC `chart_at (atlasu:((A->bool)#(A->real^N))->bool) x` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`topb:A topology`; `atlasb:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `topu:A topology`; `atlasu:((A->bool)#(A->real^N))->bool`; `W:A->bool`;
                 `\y:A. y`; `\y:A. y`; `U:A->bool`; `phi:A->real^N`; `V:A->bool`;
                 `psi:A->real^N`] MFDR_DIFFEO_CHART_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) {x | x IN U INTER W /\ (\y:A. y) x IN V}`;
                 `IMAGE (psi:A->real^N) {y | y IN V INTER W /\ (\y:A. y) y IN U}`;
                 `(psi:A->real^N) o (\y:A. y) o chart_inv (U:A->bool,phi:A->real^N)`;
                 `(phi:A->real^N) o (\y:A. y) o chart_inv (V:A->bool,psi:A->real^N)`;
                 `G:real^N->real^N^N`;
                 `metric_local atlasu (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
                 `(phi:A->real^N) x`] P2C_REP_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlasu (g:A->real^N^N)` THEN
        REWRITE_TAC[riemannian_metric] THEN
        DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
        ASM_REWRITE_TAC[FST; SND];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      TRANS_TAC EQ_TRANS
       `metric_local atlasb (U,phi:A->real^N)
                     (mfd_pullback_metric atlasb atlasu (\y:A. y) (g:A->real^N^N)) (phi(x':A))` THEN
      CONJ_TAC THENL
       [TRANS_TAC EQ_TRANS
         `metric_local (restrict_atlas atlasb W) (U INTER W,phi:A->real^N)
             (restrict_metric atlasb W
                (mfd_pullback_metric atlasb atlasu (\y:A. y) (g:A->real^N^N))) (phi(x':A))` THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
             free_in `G:real^N->real^N^N` (concl th))) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
          MATCH_MP_TAC METRIC_LOCAL_RESTRICT THEN EXISTS_TAC `topb:A topology` THEN
          ASM_REWRITE_TAC[IN_INTER]];
        MATCH_MP_TAC P2C_PULLBACK_METRIC_LOCAL_W THEN
        MAP_EVERY EXISTS_TAC [`topb:A topology`; `W:A->bool`; `topu:A topology`;
                              `W:A->bool`; `\y:A. y`] THEN
        BETA_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((psi:A->real^N) o (\y:A. y) o chart_inv (U:A->bool,phi:A->real^N)) (phi x) =
                psi x`
  SUBST1_TAC THENL
   [REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`topb:A topology`; `atlasb:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[FST; SND];
    ALL_TAC] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Slices of regular views; the evolution of R at a persisting              *)
(* point: dR/dt = Lap R + 2 |Ric|^2 (in the slice at t), from the Ricci     *)
(* flow p2c_vfam of the regular view (LSCALAR_EVOLUTION in a restricted     *)
(* chart of the last time).                                                 *)
(* ------------------------------------------------------------------------- *)

let P2C_VIEW_EXPAND = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     (!t x. rfs_vscalar V t x = mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) x) /\
     (!t x r. rfs_vball V t x r =
              mfd_ball (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) x r) /\
     (!W a b. rfs_persists V W a b <=>
              !s. a < s /\ s <= b
                  ==> smooth_manifold_atlas (rfs_vtop V s) (rfs_vatlas V s) /\
                      open_in (rfs_vtop V s) W)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_vscalar; rfs_vball; rfs_persists; rfs_vtop; rfs_vatlas;
              rfs_vmetric]);;

let P2C_REGULAR_SLICE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t x.
     p2c_regular_view V /\ x IN topspace(rfs_vtop V t)
     ==> hausdorff_space (rfs_vtop V t) /\
         smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
         riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2c_regular_view] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `t:real` o CONJUNCT1) ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let P2C_REGULAR_DIFFEO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b s.
     p2c_regular_view V /\ a < s /\ s <= b /\ rfs_persists V W a b
     ==> mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) W (rfs_vtop V b) (rfs_vatlas V b) W
                    (\y:A. y) (\y. y)`,
  REWRITE_TAC[p2c_regular_view] THEN MESON_TAC[]);;

let P2C_REGULAR_VFLOW = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b ==> p2c_vflow V W a b`,
  REWRITE_TAC[p2c_regular_view] THEN MESON_TAC[]);;

(* The slices of p2c_vfam in a restricted chart of the last time. *)

let P2C_VFAM_CURV = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b u (U:A->bool) (phi:A->real^3) x.
     p2c_regular_view V /\ rfs_persists V W a b /\ a < u /\ u <= b /\
     (U,phi) IN rfs_vatlas V b /\ x IN U /\ x IN W
     ==> lscalar (metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                               (p2c_vfam V W b u)) (phi x) = rfs_vscalar V u x /\
         llap (metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                            (p2c_vfam V W b u))
              (lscalar (metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                                     (p2c_vfam V W b u))) (phi x) =
         rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) x /\
         ltnorm2 2 (metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                                 (p2c_vfam V W b u))
                   (lric2 (metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                                        (p2c_vfam V W b u))) (phi x) =
         rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[P2C_VIEW_EXPAND] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `u:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u) /\
                x IN topspace(rfs_vtop V b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[p2c_vfam; ETA_AX] THEN
    MATCH_MP_TAC P2C_RESTRICT_CURV THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
      `W:A->bool`; `U:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[P2C_REGULAR_SLICE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2c_vfam; ETA_AX] THEN
  MATCH_MP_TAC P2C_PULLBACK_CURV THEN
  MAP_EVERY EXISTS_TAC
   [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
    `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b`;
    `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u`;
    `W:A->bool`; `U:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[P2C_REGULAR_SLICE];
    MATCH_MP_TAC P2C_REGULAR_DIFFEO THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The evolution of R at a persisting point of a regular view               *)
(* (dR/dt = Lap R + 2 |Ric|^2 on (a,b)) and continuity of R in time on      *)
(* (a,b] (P2A_UPTO_SFAMILY: the family t = b - s^2 is smooth across s = 0). *)
(* ------------------------------------------------------------------------- *)

let P2C_LSCALAR_SLICE_CONT = prove
 (`!U ta tb (G:real->real^N->real^N^N) y.
     p2a_lsmooth U ta tb G /\ y IN U
     ==> (\s. lscalar (G s) y) real_continuous_on real_interval(ta,tb)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LSMOOTH_LSCALAR) THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  SUBGOAL_THEN
   `(lift o (\s. lscalar ((G:real->real^N->real^N^N) s) y) o drop) =
    (\z. lift(lscalar (G (drop(fstcart z))) (sndcart z))) o (\s:real^1. pastecart s y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN ASM_REWRITE_TAC[]]);;

(* The chart of the last time at a persisting point. *)

let P2C_VIEW_LAST_CHART = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b x.
     a < b /\ rfs_persists V W a b /\ x IN W
     ==> smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
         open_in (rfs_vtop V b) W /\ x IN topspace(rfs_vtop V b) /\
         ?U phi. (U,phi) IN rfs_vatlas V b /\ x IN U /\
                 (U INTER W,phi) IN restrict_atlas (rfs_vatlas V b) W`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
                open_in (rfs_vtop V b) (W:A->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) a b` THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop V b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b`;
                `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                       (real->A->real^3^3)) b) (x:A)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^3`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[restrict_atlas; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^3`] THEN ASM_REWRITE_TAC[]);;

let P2C_VIEW_SCALAR_EVOL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b x s.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ x IN W /\ a < s /\ s < b
     ==> ((\u. rfs_vscalar V u x) has_real_derivative
          (rfs_scalar_lap (rfs_vatlas V s) (rfs_vmetric V s) x +
           &2 * rfs_ric_norm2 (rfs_vatlas V s) (rfs_vmetric V s) x)) (atreal s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
         P2C_REGULAR_VFLOW) THEN
  ASM_REWRITE_TAC[p2c_vflow; rfs_flow_upto] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `x:A`]
         P2C_VIEW_LAST_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`;
                 `a:real`; `b:real`; `p2c_vfam V (W:A->bool) b`;
                 `((U:A->bool) INTER (W:A->bool),phi:A->real^3)`] P2A_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER W)`; `a:real`; `b:real`;
                 `\t. metric_local (restrict_atlas (rfs_vatlas V b) W) ((U:A->bool) INTER (W:A->bool),phi:A->real^3)
                                   (p2c_vfam (V:(real->A topology)#
                                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                                     (W:A->bool) b t)`;
                 `s:real`; `(phi:A->real^3) x`] LSCALAR_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  BETA_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `s:real`;
                 `U:A->bool`; `phi:A->real^3`; `x:A`] P2C_VFAM_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  MAP_EVERY EXISTS_TAC
   [`\u. lscalar (metric_local (restrict_atlas (rfs_vatlas V b) W) ((U:A->bool) INTER (W:A->bool),phi:A->real^3)
                   (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (W:A->bool) b u)) (phi x)`;
    `min (s - a) (b - s)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `u:real` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`;
                 `U:A->bool`; `phi:A->real^3`; `x:A`] P2C_VFAM_CURV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let P2C_VIEW_SCALAR_CONT_UPTO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b x s0.
     p2c_regular_view V /\ a < s0 /\ s0 <= b /\ rfs_persists V W a b /\ x IN W
     ==> (\u. rfs_vscalar V u x) real_continuous_on real_interval[s0,b]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
         P2C_REGULAR_VFLOW) THEN
  ASM_REWRITE_TAC[p2c_vflow; GSYM P2A_FLOW_UPTO_3] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `x:A`]
         P2C_VIEW_LAST_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `d = sqrt(b - a)` THEN
  SUBGOAL_THEN `&0 < d /\ d pow 2 = b - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`;
                 `a:real`; `b:real`; `p2c_vfam V (W:A->bool) b`;
                 `((U:A->bool) INTER (W:A->bool),phi:A->real^3)`; `b:real`; `--d`; `d:real`] P2A_UPTO_SFAMILY) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs s pow 2 < d pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER W)`; `--d`; `d:real`;
                 `\s. metric_local (restrict_atlas (rfs_vatlas V b) W) ((U:A->bool) INTER (W:A->bool),phi:A->real^3)
                                   (p2c_vfam (V:(real->A topology)#
                                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                                     (W:A->bool) b (b - s pow 2))`;
                 `(phi:A->real^3) x`] P2C_LSCALAR_SLICE_CONT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `(\s. lscalar (metric_local (restrict_atlas (rfs_vatlas V b) W) ((U:A->bool) INTER (W:A->bool),phi:A->real^3)
                   (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (W:A->bool) b (b - s pow 2))) (phi x)) o
    (\u. sqrt(b - u))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `b - sqrt(b - u) pow 2 = u` SUBST1_TAC THENL
     [SUBGOAL_THEN `sqrt(b - u) pow 2 = b - u` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`;
                   `U:A->bool`; `phi:A->real^3`; `x:A`] P2C_VFAM_CURV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\u. sqrt(b - u)) = sqrt o (\u. b - u)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval(--d,d)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &0 <= x ==> --d < x`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "d" THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of R in time at the initial time of the flow of               *)
(* a regular view, when the identity is a diffeomorphism from the initial   *)
(* slice (the family t = a + s^2 is smooth across s = 0, ricci_flow_from).  *)
(* ------------------------------------------------------------------------- *)

let P2C_SMOOTH_TIME_SQ_PLUS = prove
 (`!W tt. open W
          ==> smooth_map_on W
                (\z:real^(1,N)finite_sum. pastecart (lift(tt + drop(fstcart z) pow 2))
                                                    (sndcart z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                   `\z:real^(1,N)finite_sum. lift tt`;
                   `\z:real^(1,N)finite_sum. lift(drop(fstcart z) pow 2)`]
                  SMOOTH_MAP_ON_LIFT_ADD) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                   `\z:real^(1,N)finite_sum. lift(drop(fstcart z))`; `2`]
                  SMOOTH_MAP_ON_LIFT_POW) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN
    ASM_REWRITE_TAC[ETA_AX; LINEAR_FSTCART];
    MATCH_MP_TAC LRG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[ETA_AX; LINEAR_SNDCART]]);;

let P2C_FROM_SFAMILY = prove
 (`!top atlas a b (g:real->A->real^N^N) c tt sa sb.
     ricci_flow_from (top,atlas) a b g /\ c IN atlas /\ sa < sb /\
     (!s. sa < s /\ s < sb ==> a <= tt + s pow 2 /\ tt + s pow 2 < b)
     ==> p2a_lsmooth (IMAGE (SND c) (FST c)) sa sb
                     (\s. metric_local atlas c (g(tt + s pow 2)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ricci_flow_from] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ASSUME `ricci_flow_on (top,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)`) THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_lsmooth] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFB_ATLAS_IMAGE_OPEN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N)(tt + s pow 2))` MP_TAC THENL
     [ASM_CASES_TAC `tt + s pow 2 = a` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!t. a < t /\ t < b ==> riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                                                  ((g:real->A->real^N^N) t)`) (concl th))) THEN
      SUBGOAL_THEN `a <= tt + s pow 2 /\ tt + s pow 2 < b` MP_TAC THENL
       [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `(Fx:real^(1,N)finite_sum->real^(N,N)finite_prod) o
    (\z:real^(1,N)finite_sum. pastecart (lift(tt + drop(fstcart z) pow 2)) (sndcart z))` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; o_THM; FSTCART_PASTECART; SNDCART_PASTECART;
                IN_INTERVAL_1; LIFT_DROP] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift(a - e),lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; P2C_SMOOTH_TIME_SQ_PLUS] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GEOL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a <= tt + drop(fstcart(z:real^(1,N)finite_sum)) pow 2 /\
                tt + drop(fstcart z) pow 2 < b` MP_TAC THENL
   [ASM_SIMP_TAC[]; UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC]);;

let P2C_REGULAR_VFLOW_FROM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b.
     p2c_regular_view V /\ a < b /\ open_in (rfs_vtop V a) W /\ rfs_persists V W a b
     ==> p2c_vflow_from V W a b`,
  REWRITE_TAC[p2c_regular_view] THEN MESON_TAC[]);;

let P2C_VFAM_CURV_START = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b (U:A->bool) (phi:A->real^3) x.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ open_in (rfs_vtop V a) W /\
     mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     (U,phi) IN rfs_vatlas V b /\ x IN U /\ x IN W
     ==> lscalar (metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi)
                               (p2c_vfam V W b a)) (phi x) = rfs_vscalar V a x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a:real = b)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2C_VIEW_EXPAND; p2c_vfam; ETA_AX] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
                open_in (rfs_vtop V b) (W:A->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_persists V (W:A->bool) a b` THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a)`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `a:real`; `x:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                 `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) a`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) a`;
                 `W:A->bool`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) a`;
                 `U:A->bool`; `phi:A->real^3`; `x:A`;
                 `metric_local (restrict_atlas (rfs_vatlas V b) W) (U INTER W,phi:A->real^3)
                    (restrict_metric (rfs_vatlas V b) W
                      (mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V a) (\y:A. y)
                         (rfs_vmetric (V:(real->A topology)#
                            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) a)))`]
         P2C_PULLBACK_CURV) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let P2C_VIEW_SCALAR_CONT_FROM = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b x s1.
     p2c_regular_view V /\ a < b /\ rfs_persists V W a b /\ open_in (rfs_vtop V a) W /\
     mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W (rfs_vtop V b) (rfs_vatlas V b) W
                (\y:A. y) (\y. y) /\
     x IN W /\ a <= s1 /\ s1 < b
     ==> (\u. rfs_vscalar V u x) real_continuous_on real_interval[a,s1]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
         P2C_REGULAR_VFLOW_FROM) THEN
  ASM_REWRITE_TAC[p2c_vflow_from] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `x:A`]
         P2C_VIEW_LAST_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `d = sqrt(b - a)` THEN
  SUBGOAL_THEN `&0 < d /\ d pow 2 = b - a` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) (W:A->bool)`;
                 `a:real`; `b:real`; `p2c_vfam V (W:A->bool) b`;
                 `((U:A->bool) INTER (W:A->bool),phi:A->real^3)`; `a:real`; `--d`; `d:real`]
         P2C_FROM_SFAMILY) THEN
  ASM_REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs s pow 2 < d pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER W)`; `--d`; `d:real`;
                 `\s. metric_local (restrict_atlas (rfs_vatlas V b) W)
                                   ((U:A->bool) INTER (W:A->bool),phi:A->real^3)
                                   (p2c_vfam (V:(real->A topology)#
                                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                                     (W:A->bool) b (a + s pow 2))`;
                 `(phi:A->real^3) x`] P2C_LSCALAR_SLICE_CONT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
  EXISTS_TAC
   `(\s. lscalar (metric_local (restrict_atlas (rfs_vatlas V b) W)
                   ((U:A->bool) INTER (W:A->bool),phi:A->real^3)
                   (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (W:A->bool) b (a + s pow 2))) (phi x)) o
    (\u. sqrt(u - a))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `a + sqrt(u - a) pow 2 = u` SUBST1_TAC THENL
     [SUBGOAL_THEN `sqrt(u - a) pow 2 = u - a` SUBST1_TAC THENL
       [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `u:real = a` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN MATCH_MP_TAC P2C_VFAM_CURV_START THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `u:real`;
                     `U:A->bool`; `phi:A->real^3`; `x:A`] P2C_VFAM_CURV) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\u. sqrt(u - a)) = sqrt o (\u. u - a)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `real_interval(--d,d)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &0 <= x ==> --d < x`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "d" THEN MATCH_MP_TAC SQRT_MONO_LT THEN ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* Assembly.  The spatial step at time t0 for points of the                 *)
(* ball, the temporal comparison backward and forward in time, and the      *)
(* core form of MT Lemma 11.2 for regular views.                            *)
(* ------------------------------------------------------------------------- *)

let P2C_BALL_CURVE = prove
 (`!top atlas (g:A->real^N^N) x y r.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     y IN mfd_ball (top,atlas) g x r
     ==> ?gamma. mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                 gamma(&0) = x /\ gamma(&1) = y /\
                 mfd_length atlas g gamma (&0) (&1) < r`,
  REWRITE_TAC[mfd_ball; IN_ELIM_THM; mfd_dist; mfd_joinable] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{mfd_length atlas (g:A->real^N^N) gamma (&0) (&1) | gamma |
                   mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
                   gamma(&0) = (x:A) /\ gamma(&1) = y}`; `r:real`] INF_APPROACH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; GRGD_IN_LENGTHS] THEN ASM_MESON_TAC[];
      EXISTS_TAC `&0` THEN ASM_MESON_TAC[GRGD_LENGTHS_POS_LE]];
    REWRITE_TAC[GRGD_IN_LENGTHS] THEN MESON_TAC[]]);;

let P2C_DB_SPATIAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C r0 z t0 r' y.
     p2c_regular_view V /\ &0 < C /\ &0 < r0 /\
     (!x. x IN topspace(rfs_vtop V t0) /\ inv(r0 pow 2) <= rfs_vscalar V t0 x
          ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V t0) (rfs_vmetric V t0) x) <=
              C * rfs_vscalar V t0 x * sqrt(rfs_vscalar V t0 x)) /\
     z IN topspace(rfs_vtop V t0) /\
     r' <= inv(&2 * C * sqrt(max (rfs_vscalar V t0 z) (inv(r0 pow 2)))) /\
     y IN rfs_vball V t0 z r'
     ==> rfs_vscalar V t0 y <= &16 / &9 * max (rfs_vscalar V t0 z) (inv(r0 pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t0:real`; `z:A`] P2C_REGULAR_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) t0`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t0`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t0`;
                 `z:A`; `y:A`; `r':real`] P2C_BALL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `y = (gamma:real->A)(&1) /\ z = gamma(&0)` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P2C_SPATIAL_BOUND THEN
  MAP_EVERY EXISTS_TAC [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t0`; `C:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The arithmetic of the time step: C d M <= 1/9 and M/(1 - x) <= 2 Q'. *)

let P2C_DB_ARITH1 = prove
 (`!C d Q. &0 < C /\ &0 < Q /\ &0 <= d /\ d <= inv(&16 * C * Q)
           ==> C * d * (&16 / &9 * Q) <= &1 / &9`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * inv(&16 * C * Q) * (&16 / &9 * Q)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < C` THEN UNDISCH_TAC `&0 < Q` THEN CONV_TAC REAL_FIELD]);;

let P2C_DB_ARITH2 = prove
 (`!Q x f. &0 < Q /\ x <= &1 / &9 /\ f <= (&16 / &9 * Q) / (&1 - x) ==> f <= &2 * Q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&16 / &9 * Q) / (&1 - x)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &1 - x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `Q * x <= Q * (&1 / &9)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The temporal comparison, backward in time. *)

let P2C_DB_TIME_BACK = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C r0 t0 t' B Q s y.
     p2c_regular_view V /\ &0 < C /\ &0 < r0 /\ &0 < Q /\ inv(r0 pow 2) <= Q /\
     (!x t. t' <= t /\ t <= t0 /\ x IN topspace(rfs_vtop V t) /\
            inv(r0 pow 2) <= rfs_vscalar V t x
            ==> abs(rfs_scalar_lap (rfs_vatlas V t) (rfs_vmetric V t) x +
                    &2 * rfs_ric_norm2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
                C * rfs_vscalar V t x pow 2) /\
     t0 - t' <= inv(&16 * C * Q) /\ rfs_persists V B t' t0 /\
     t' < s /\ s <= t0 /\ y IN B /\ rfs_vscalar V t0 y <= &16 / &9 * Q
     ==> rfs_vscalar V s y <= &2 * Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `C * (t0 - s) * (&16 / &9 * Q) <= &1 / &9` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_DB_ARITH1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\u. rfs_vscalar V u (y:A)) real_continuous_on real_interval[s,t0]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_VIEW_SCALAR_CONT_UPTO THEN
    MAP_EVERY EXISTS_TAC [`B:A->bool`; `t':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval(s,t0)
        ==> ((\u. rfs_vscalar V u (y:A)) has_real_derivative
             rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) y +
             &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y) (atreal u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2C_VIEW_SCALAR_EVOL THEN
    MAP_EVERY EXISTS_TAC [`B:A->bool`; `t':real`; `t0:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval(s,t0) /\ inv(r0 pow 2) <= rfs_vscalar V u (y:A)
        ==> abs(rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) y +
                &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y) <=
            C * rfs_vscalar V u y pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_lap")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_persists V (B:A->bool) t' t0` THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\u. rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) u (y:A)`;
     `\u. rfs_scalar_lap (rfs_vatlas (V:(real->A topology)#
            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
            (rfs_vmetric V u) (y:A) +
          &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y`;
     `t0:real`; `s:real`; `C:real`; `inv(r0 pow 2)`; `&16 / &9 * Q`] P2C_ODE_BACKWARD)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P2C_DB_ARITH2 THEN
  EXISTS_TAC `C * (t0 - s) * (&16 / &9 * Q)` THEN ASM_REWRITE_TAC[]);;

(* The temporal comparison, forward in time. *)

let P2C_DB_TIME_FWD = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C r0 t0 t' B Q s y.
     p2c_regular_view V /\ &0 < C /\ &0 < r0 /\ &0 < Q /\ inv(r0 pow 2) <= Q /\
     (!x t. t0 <= t /\ t <= t' /\ x IN topspace(rfs_vtop V t) /\
            inv(r0 pow 2) <= rfs_vscalar V t x
            ==> abs(rfs_scalar_lap (rfs_vatlas V t) (rfs_vmetric V t) x +
                    &2 * rfs_ric_norm2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
                C * rfs_vscalar V t x pow 2) /\
     t0 < t' /\ t' - t0 <= inv(&16 * C * Q) /\ rfs_persists V B t0 t' /\
     open_in (rfs_vtop V t0) B /\
     mfd_diffeo (rfs_vtop V t0) (rfs_vatlas V t0) B (rfs_vtop V t') (rfs_vatlas V t') B
                (\y:A. y) (\y. y) /\
     t0 < s /\ s <= t' /\ y IN B /\ rfs_vscalar V t0 y <= &16 / &9 * Q
     ==> rfs_vscalar V s y <= &2 * Q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `C * (s - t0) * (&16 / &9 * Q) <= &1 / &9` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_DB_ARITH1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\u. rfs_vscalar V u (y:A)) real_continuous_on real_interval[t0,s]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `real_interval[t0,s] = real_interval[t0,(t0 + s) / &2] UNION
                                        real_interval[(t0 + s) / &2,s]` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_UNION THEN
    REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2C_VIEW_SCALAR_CONT_FROM THEN
      MAP_EVERY EXISTS_TAC [`B:A->bool`; `t':real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `real_interval[(t0 + s) / &2,t']` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2C_VIEW_SCALAR_CONT_UPTO THEN
        MAP_EVERY EXISTS_TAC [`B:A->bool`; `t0:real`] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval(t0,s)
        ==> ((\u. rfs_vscalar V u (y:A)) has_real_derivative
             rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) y +
             &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y) (atreal u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC P2C_VIEW_SCALAR_EVOL THEN
    MAP_EVERY EXISTS_TAC [`B:A->bool`; `t0:real`; `t':real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN real_interval(t0,s) /\ inv(r0 pow 2) <= rfs_vscalar V u (y:A)
        ==> abs(rfs_scalar_lap (rfs_vatlas V u) (rfs_vmetric V u) y +
                &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y) <=
            C * rfs_vscalar V u y pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_scalar_lap")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `rfs_persists V (B:A->bool) t0 t'` THEN REWRITE_TAC[P2C_VIEW_EXPAND] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`\u. rfs_vscalar (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) u (y:A)`;
     `\u. rfs_scalar_lap (rfs_vatlas (V:(real->A topology)#
            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) u)
            (rfs_vmetric V u) (y:A) +
          &2 * rfs_ric_norm2 (rfs_vatlas V u) (rfs_vmetric V u) y`;
     `t0:real`; `s:real`; `C:real`; `inv(r0 pow 2)`; `&16 / &9 * Q`] P2C_ODE_FORWARD)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC P2C_DB_ARITH2 THEN
  EXISTS_TAC `C * (s - t0) * (&16 / &9 * Q)` THEN ASM_REWRITE_TAC[]);;

(* The core form of MT Lemma 11.2 for regular views; forward in time the    *)
(* ball at t0 must be carried to the later slices by the identity (MT: the  *)
(* embedding of B(z,t0,r') x I is compatible with time; p2c_regular_view   *)
(* gives this only for slices after the initial time).                      *)

let P2C_DB_CORE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C r0 z t0 t' r'.
     p2c_regular_view V /\ &0 < C /\ &0 < r0 /\
     (!x t. min t0 t' <= t /\ t <= max t0 t' /\ x IN topspace(rfs_vtop V t) /\
            inv(r0 pow 2) <= rfs_vscalar V t x
            ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
                C * rfs_vscalar V t x * sqrt(rfs_vscalar V t x) /\
                abs(rfs_scalar_lap (rfs_vatlas V t) (rfs_vmetric V t) x +
                    &2 * rfs_ric_norm2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
                C * rfs_vscalar V t x pow 2) /\
     z IN topspace(rfs_vtop V t0) /\ &0 < r' /\
     r' <= inv(&2 * C * sqrt(max (rfs_vscalar V t0 z) (inv(r0 pow 2)))) /\
     abs(t' - t0) <= inv(&16 * C * (max (&0) (rfs_vscalar V t0 z) + inv(r0 pow 2))) /\
     rfs_persists V (rfs_vball V t0 z r') (min t0 t') (max t0 t') /\
     (t0 < t'
      ==> mfd_diffeo (rfs_vtop V t0) (rfs_vatlas V t0) (rfs_vball V t0 z r')
                     (rfs_vtop V t') (rfs_vatlas V t') (rfs_vball V t0 z r')
                     (\y:A. y) (\y. y))
     ==> !s y. min t0 t' < s /\ s <= max t0 t' /\ y IN rfs_vball V t0 z r'
               ==> rfs_vscalar V s y <= &2 * (max (&0) (rfs_vscalar V t0 z) + inv(r0 pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`s:real`; `y:A`] THEN STRIP_TAC THEN
  ABBREV_TAC `Q = max (&0) (rfs_vscalar (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z) +
                  inv(r0 pow 2)` THEN
  SUBGOAL_THEN `&0 < inv(r0 pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Q /\ inv(r0 pow 2) <= Q /\
                max (rfs_vscalar (V:(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z)
                    (inv(r0 pow 2)) <= Q`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "Q" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_vscalar V t0 (y:A) <= &16 / &9 * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&16 / &9 * max (rfs_vscalar (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z)
                  (inv(r0 pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2C_DB_SPATIAL THEN MAP_EVERY EXISTS_TAC [`C:real`; `r':real`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `t0:real`] o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `t' <= t0:real` THENL
   [SUBGOAL_THEN `min t0 t' = t' /\ max t0 t' = t0`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `t0 - t' <= inv(&16 * C * Q)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!x t. t' <= t /\ t <= t0 /\
            x IN topspace(rfs_vtop (V:(real->A topology)#
                   (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) /\
            inv(r0 pow 2) <= rfs_vscalar V t x
            ==> abs(rfs_scalar_lap (rfs_vatlas V t) (rfs_vmetric V t) x +
                    &2 * rfs_ric_norm2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
                C * rfs_vscalar V t x pow 2`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `t:real`] o check (is_forall o concl)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC P2C_DB_TIME_BACK THEN
    MAP_EVERY EXISTS_TAC [`C:real`; `r0:real`; `t0:real`; `t':real`;
                          `rfs_vball (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z r'`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 < t'` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `min t0 t' = t0 /\ max t0 t' = t'`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t' - t0 <= inv(&16 * C * Q)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t. t0 <= t /\ t <= t' /\
          x IN topspace(rfs_vtop (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) /\
          inv(r0 pow 2) <= rfs_vscalar V t x
          ==> abs(rfs_scalar_lap (rfs_vatlas V t) (rfs_vmetric V t) x +
                  &2 * rfs_ric_norm2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
              C * rfs_vscalar V t x pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `t:real`] o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (rfs_vtop V t0)
                  (rfs_vball (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z r')`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `t0:real`; `z:A`] P2C_REGULAR_SLICE) THEN
    ASM_REWRITE_TAC[P2C_VIEW_EXPAND] THEN STRIP_TAC THEN
    MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2C_DB_TIME_FWD THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `r0:real`; `t0:real`; `t':real`;
                        `rfs_vball (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t0 z r'`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorems.  The core form P2C_LEMMA_11_2_DB_STATEMENT             *)
(* outright, and Lemma 11.2 for histories (P2C_LEMMA_11_2_STATEMENT, which   *)
(* has the body of P2_LEMMA_11_2_STATEMENT) from the bridge from canonical   *)
(* neighbourhoods to the derivative bounds and the regularity of history     *)
(* views.                                                                    *)
(* ------------------------------------------------------------------------- *)

let P2C_LEMMA_11_2_DB = prove
 (`!u:A->bool. P2C_LEMMA_11_2_DB_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT] THEN
  MATCH_ACCEPT_TAC P2C_DB_CORE);;

let P2C_LEMMA_11_2_COND = prove
 (`!u:A->bool. P2C_CANON_DERIV_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
               ==> P2C_LEMMA_11_2_STATEMENT u`,
  MESON_TAC[P2C_LEMMA_11_2_FROM_DB; P2C_LEMMA_11_2_DB]);;

