(* ========================================================================= *)
(* Unit pc_wan_sob2r: Rellich compactness.                                  *)
(*   WAN_RELLICH0: bounded open s, a sequence bounded in W^{1,2}_0(s) has a  *)
(*   subsequence converging in L^2(s) and a.e.; the limit is in W^{1,2}_0(s) *)
(*   and keeps the bound.                                                    *)
(*   WAN_RELLICH_LOC: open s, a sequence bounded in W^{1,2}(s) has a         *)
(*   subsequence converging in L^2 on compact subsets and a.e.               *)
(* Route: zero extension; the translation estimate for smooth compactly     *)
(* supported maps (segment integrals and Fubini), hence a mollification     *)
(* estimate uniform on the sequence; Arzela-Ascoli for the mollified maps   *)
(* and a diagonal subsequence give an L^2 Cauchy subsequence; the limit is  *)
(* identified with Mazur combinations (pc_wan_sob2b).                       *)
(* WAN_RELLICH_LOC: smooth cutoffs on a compact exhaustion, RELLICH0 in R^N *)
(* for the cut-off maps, a diagonal subsequence, the pointwise limit, and   *)
(* monotone convergence plus lower semicontinuity for the bound.            *)
(* ========================================================================= *)

needs "src/pc_wan_sob2b.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* The translation estimate for smooth compactly supported maps:            *)
(*   int |psi(x + y) - psi x|^2 <= |y|^2 int sum_i |d_i psi|^2.             *)
(* ------------------------------------------------------------------------- *)

let WAN_INTEGRAL_UNIV_SUPPORT = prove
 (`!(f:real^N->real^K) B.
     (!x. ~(x IN B) ==> f x = vec 0)
     ==> integral (:real^N) f = integral B f /\
         (f integrable_on (:real^N) <=> f integrable_on B)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^K) = (\x. if x IN B then f x else vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[INTEGRAL_RESTRICT_UNIV];
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV]]);;

let WAN_FULL_SEGMENT = prove
 (`!(w:real^N->real^K) x y.
     smooth_map_on (:real^N) w
     ==> norm(w y - w x) pow 2 <=
         norm(y - x) pow 2 *
         drop(integral (interval[lift(&0),lift(&1)])
                (\t. lift(sum(1..dimindex(:N))
                       (\i. norm(partial_derivative i w
                               ((&1 - drop t) % x + drop t % y)) pow 2))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`] WAN_C1_OPEN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; smooth_map_on]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. (&1 - drop t) % (x:real^N) + drop t % y) continuous_on
    interval[lift(&0),lift(&1)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
    REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (w:real^N->real^K)((&1 - drop t) % x + drop t % y)`;
                 `\t. frechet_derivative (w:real^N->real^K)
                        (at ((&1 - drop t) % x + drop t % y)) (y - x)`;
                 `lift(&0)`; `lift(&1)`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    ASM_SIMP_TAC[WAN_SEGMENT_VDERIV];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_LID;
              VECTOR_ADD_RID; VECTOR_MUL_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE) THEN
  SUBGOAL_THEN
   `(\t. frechet_derivative (w:real^N->real^K)
           (at ((&1 - drop t) % x + drop t % y)) (y - x))
    continuous_on interval[lift(&0),lift(&1)]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. (&1 - drop t) % (x:real^N) + drop t % y`;
                   `\z. frechet_derivative (w:real^N->real^K) (at z) (y - x)`;
                   `interval[lift(&0),lift(&1)]`] CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `measure(interval[lift(&0),lift(&1)]) *
    drop(integral (interval[lift(&0),lift(&1)])
          (\t. lift(norm(frechet_derivative (w:real^N->real^K)
                    (at ((&1 - drop t) % x + drop t % y)) (y - x)) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_INTEGRAL_SQ_CS THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(interval[lift(&0),lift(&1)]) = &1` SUBST1_TAC THENL
   [REWRITE_TAC[MEASURE_INTERVAL_1; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  MP_TAC(ISPECL [`interval[lift(&0),lift(&1)]`;
                 `\t. sum(1..dimindex(:N))
                       (\i. norm(partial_derivative i (w:real^N->real^K)
                               ((&1 - drop t) % x + drop t % y)) pow 2)`;
                 `norm(y - x:real^N) pow 2`] WAN_INTEGRAL_LIN1) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MP_TAC(ISPECL [`\t. (&1 - drop t) % (x:real^N) + drop t % y`;
                   `\z. lift(sum(1..dimindex(:N))
                          (\i. norm(partial_derivative i (w:real^N->real^K) z) pow 2))`;
                   `interval[lift(&0),lift(&1)]`] CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[WAN_SQGRAD_CONT; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; partial_derivative] THEN
    MATCH_MP_TAC WAN_LINEAR_SQ_BOUND THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[differentiable]]);;

let WAN_SHIFT_FUBINI = prove
 (`!(g:real^N->real) c (y:real^N) B.
     (\x. lift(g x)) continuous_on (:real^N) /\ compact c /\
     (!x. ~(x IN c) ==> g x = &0) /\ compact B /\
     (!x t. &0 <= t /\ t <= &1 /\ x + t % y IN c ==> x IN B)
     ==> (\x. integral (interval[lift(&0),lift(&1)]) (\t. lift(g(x + drop t % y))))
         integrable_on B /\
         integral B (\x. integral (interval[lift(&0),lift(&1)])
                           (\t. lift(g(x + drop t % y)))) =
         integral (:real^N) (\x. lift(g x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\z:real^(N,1)finite_sum. lift((g:real^N->real)(fstcart z + drop(sndcart z) % y))`;
    `B:real^N->bool`; `interval[lift(&0),lift(&1)]`] WAN_FUBINI_PCROSS) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; COMPACT_INTERVAL] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN
     `(\z:real^(N,1)finite_sum. lift((g:real^N->real)(fstcart z + drop(sndcart z) % y))) =
      (\x. lift(g x)) o (\z. fstcart z + drop(sndcart z) % y)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (interval[lift(&0),lift(&1)])
                (\t. integral B (\x. lift((g:real^N->real)(x + drop t % y))))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (interval[lift(&0),lift(&1)])
                (\t:real^1. integral (:real^N) (\x. lift((g:real^N->real) x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x. lift((g:real^N->real)(x + drop t % y))`; `B:real^N->bool`]
                  WAN_INTEGRAL_UNIV_SUPPORT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `x + drop t % y IN (c:real^N->bool)` THENL
       [ASM_MESON_TAC[]; ASM_SIMP_TAC[LIFT_NUM]];
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
    MP_TAC(ISPECL [`\z. lift((g:real^N->real) z)`; `(:real^N)`; `drop t % y:real^N`]
                  INTEGRAL_TRANSLATION) THEN
    REWRITE_TAC[TRANSLATION_UNIV];
    SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_INTERVAL; MEASURE_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[REAL_POS; REAL_SUB_RZERO; VECTOR_MUL_LID]]);;

let WAN_TRANSL_EST = prove
 (`!(psi:real^N->real^K) c y.
     smooth_map_on (:real^N) psi /\ compact c /\ (!x. ~(x IN c) ==> psi x = vec 0)
     ==> (\x. lift(norm(psi(x + y) - psi x) pow 2)) integrable_on (:real^N) /\
         drop(integral (:real^N) (\x. lift(norm(psi(x + y) - psi x) pow 2))) <=
         norm y pow 2 *
         drop(integral (:real^N)
                (\x. lift(sum(1..dimindex(:N))
                            (\i. norm(partial_derivative i psi x) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_vtest (:real^N) (psi:real^N->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_vtest] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i x. ~(x IN c) ==> partial_derivative i (psi:real^N->real^K) x = vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^N)`; `psi:real^N->real^K`; `c:real^N->bool`; `i:num`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `psi:real^N->real^K`; `c:real^N->bool`; `1`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `B = cball(vec 0:real^N,R + norm(y:real^N))` THEN
  SUBGOAL_THEN `compact(B:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `!x t. &0 <= t /\ t <= &1 /\ x + t % y IN c ==> (x:real^N) IN B`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_CBALL_0] THEN
    SUBGOAL_THEN `norm(x + t % y:real^N) <= R` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_CBALL_0]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(t % y:real^N) <= norm y` ASSUME_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(NORM_ARITH `!a b:real^N r n. norm(a + b) <= r /\ norm b <= n ==> norm a <= r + n`) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `t % y:real^N`; `R:real`; `norm(y:real^N)`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. norm((psi:real^N->real^K)(x + y) - psi x) pow 2 <=
        norm(y:real^N) pow 2 *
        drop(integral (interval[lift(&0),lift(&1)])
               (\t. lift(sum(1..dimindex(:N))
                      (\i. norm(partial_derivative i psi (x + drop t % y)) pow 2))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPECL [`psi:real^N->real^K`; `x:real^N`; `x + y:real^N`] WAN_FULL_SEGMENT) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x + y) - x:real^N = y`;
                    VECTOR_ARITH `(&1 - t) % x + t % (x + y):real^N = x + t % y`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((psi:real^N->real^K)(x + y) - psi x) pow 2)) continuous_on (:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    SUBGOAL_THEN `(\x. (psi:real^N->real^K)(x + y)) = psi o (\x. x + y)` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ~(x IN B) ==> lift(norm((psi:real^N->real^K)(x + y) - psi x) pow 2) = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^N) IN c) /\ ~(x + y IN c)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPECL [`x:real^N`; `&0`] o
          check (fun th -> can (find_term ((=) `B:real^N->bool`)) (concl th) &&
                           is_forall(concl th))) THEN
        REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_POS; REAL_LE_01] THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM(MP_TAC o SPECL [`x:real^N`; `&1`] o
          check (fun th -> can (find_term ((=) `B:real^N->bool`)) (concl th) &&
                           is_forall(concl th))) THEN
        REWRITE_TAC[VECTOR_MUL_LID; REAL_POS; REAL_LE_REFL] THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[VECTOR_SUB_REFL; NORM_0; LIFT_NUM] THEN
      REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; LIFT_NUM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(norm((psi:real^N->real^K)(x + y) - psi x) pow 2)`;
                 `B:real^N->bool`] WAN_INTEGRAL_UNIV_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN
   `(\x. lift(norm((psi:real^N->real^K)(x + y) - psi x) pow 2)) integrable_on B`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x. sum(1..dimindex(:N))
                       (\i. norm(partial_derivative i (psi:real^N->real^K) x) pow 2)`;
                 `c:real^N->bool`; `y:real^N`; `B:real^N->bool`] WAN_SHIFT_FUBINI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[WAN_SQGRAD_CONT];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`B:real^N->bool`;
                 `\x. drop(integral (interval[lift(&0),lift(&1)])
                        (\t. lift(sum(1..dimindex(:N))
                          (\i. norm(partial_derivative i (psi:real^N->real^K)
                                  (x + drop t % y)) pow 2))))`;
                 `norm(y:real^N) pow 2`] WAN_INTEGRAL_LIN1) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP]);;


(* ------------------------------------------------------------------------- *)
(* The mollification estimate for smooth compactly supported maps:          *)
(*   int |rho_e * psi - psi|^2 <= C e^2 int sum_i |d_i psi|^2,              *)
(* with C independent of e and psi.                                          *)
(* ------------------------------------------------------------------------- *)

let WAN_MOLL_DIFF_SHIFT = prove
 (`!e (u:real^N->real^K) x.
     &0 < e /\ wan_lloc (:real^N) u
     ==> wan_moll e u x - u x =
         integral (:real^N) (\w. wan_mke e w % (u(x + w) - u x))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_MOLL_SUB] THEN
  MP_TAC(ISPEC `e:real` (INST_TYPE [`:N`,`:M`] WAN_MKE_PROPS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. wan_mke e (x - y) % ((u:real^N->real^K) y - u x)`; `(:real^N)`;
                 `x:real^N`] INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[TRANSLATION_UNIV; VECTOR_ARITH `x - (x + w):real^N = --w`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let WAN_MKE_ABS_BOUND = prove
 (`?Bk. &0 < Bk /\
        !e (w:real^N). &0 < e ==> abs(wan_mke e w) <= Bk * inv(e) pow dimindex(:N)`,
  X_CHOOSE_THEN `Bk:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:M`] WAN_MKE_BOUND) THEN
  EXISTS_TAC `Bk:real` THEN ASM_SIMP_TAC[WAN_MKE_POS; REAL_ARITH `&0 <= x ==> abs x = x`]);;

let WAN_SQGRAD_INTEGRABLE = prove
 (`!(psi:real^N->real^K) c.
     smooth_map_on (:real^N) psi /\ compact c /\ (!x. ~(x IN c) ==> psi x = vec 0)
     ==> (\x. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i psi x) pow 2)))
         integrable_on (:real^N) /\
         &0 <= drop(integral (:real^N)
                 (\x. lift(sum(1..dimindex(:N))
                             (\i. norm(partial_derivative i psi x) pow 2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_vtest (:real^N) (psi:real^N->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_vtest] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i (psi:real^N->real^K) x)
                                         pow 2))) integrable_on (:real^N)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift(sum(1..dimindex(:N))
                       (\i. norm(partial_derivative i (psi:real^N->real^K) x) pow 2))`;
                   `c:real^N->bool`] WAN_INTEGRAL_UNIV_SUPPORT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(:real^N)`; `psi:real^N->real^K`; `c:real^N->bool`; `i:num`]
                    WAN_VTEST_PARTIAL) THEN
      ASM_SIMP_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ];
      DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[WAN_SQGRAD_CONT; SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_POW_2]);;

let WAN_MOLL_TEST_EST = prove
 (`?C. &0 < C /\
       !e (psi:real^N->real^K) c.
         &0 < e /\ smooth_map_on (:real^N) psi /\ compact c /\
         (!x. ~(x IN c) ==> psi x = vec 0)
         ==> drop(integral (:real^N) (\x. lift(norm(wan_moll e psi x - psi x) pow 2))) <=
             C * e pow 2 *
             drop(integral (:real^N)
                    (\x. lift(sum(1..dimindex(:N))
                                (\i. norm(partial_derivative i psi x) pow 2))))`,
  X_CHOOSE_THEN `Bk:real` STRIP_ASSUME_TAC WAN_MKE_ABS_BOUND THEN
  EXISTS_TAC `(Bk * measure(cball(vec 0:real^N,&1))) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[MEASURE_CBALL_POS; REAL_LT_01];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `e:real` (INST_TYPE [`:N`,`:M`] WAN_MKE_PROPS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_vtest (:real^N) (psi:real^N->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_vtest] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `psi:real^N->real^K`; `c:real^N->bool`; `1`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (psi:real^N->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_CONTINUOUS_LLOC]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED o check (fun th ->
    concl th = `compact(c:real^N->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `B = cball(vec 0:real^N,R + e)` THEN
  ABBREV_TAC `W = cball(vec 0:real^N,e)` THEN
  SUBGOAL_THEN `compact(B:real^N->bool) /\ compact(W:real^N->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN EXPAND_TAC "W" THEN REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. wan_moll e (psi:real^N->real^K) x - psi x =
        integral W (\w. wan_mke e w % (psi(x + w) - psi x))`
  (LABEL_TAC "REP") THENL
   [X_GEN_TAC `x:real^N` THEN ASM_SIMP_TAC[WAN_MOLL_DIFF_SHIFT] THEN
    MP_TAC(ISPECL [`\w. wan_mke e w % ((psi:real^N->real^K)(x + w) - psi x)`;
                   `W:real^N->bool`] WAN_INTEGRAL_UNIV_SUPPORT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `w:real^N` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN
      DISCH_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; VECTOR_MUL_LZERO];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `K0 = Bk * inv(e) pow dimindex(:N)` THEN
  SUBGOAL_THEN
   `!x. norm(wan_moll e (psi:real^N->real^K) x - psi x) pow 2 <=
        measure(W:real^N->bool) * K0 pow 2 *
        drop(integral W (\w. lift(norm(psi(x + w) - psi x) pow 2)))`
  (LABEL_TAC "PB") THENL
   [X_GEN_TAC `x:real^N` THEN USE_THEN "REP" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN
     `(\w. wan_mke e w % ((psi:real^N->real^K)(x + w) - psi x)) continuous_on W /\
      (\w. lift(norm((psi:real^N->real^K)(x + w) - psi x) pow 2)) continuous_on W`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(\w. (psi:real^N->real^K)(x + w) - psi x) continuous_on W` ASSUME_TAC
      THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        SUBGOAL_THEN `(\w. (psi:real^N->real^K)(x + w)) = psi o (\w. x + w)` SUBST1_TAC
        THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `measure(W:real^N->bool) *
      drop(integral W (\w. lift(norm(wan_mke e w %
                                     ((psi:real^N->real^K)(x + w) - psi x)) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_INTEGRAL_SQ_CS THEN
      ASM_SIMP_TAC[MEASURABLE_COMPACT; WAN_CONT_COMPACT_LSPACE2];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[MEASURE_POS_LE] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[MEASURABLE_COMPACT; MEASURE_POS_LE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^N->bool`;
                   `\w. norm((psi:real^N->real^K)(x + w) - psi x) pow 2`; `K0 pow 2`]
                  WAN_INTEGRAL_LIN1) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[LIFT_DROP; NORM_MUL; REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW2_ABS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      EXPAND_TAC "K0" THEN REWRITE_TAC[REAL_ABS_ABS] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "REP" (K ALL_TAC) THEN
  SUBGOAL_THEN `!x. ~((x:real^N) IN B) ==> ~(x IN c)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "B" THEN REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `norm(x:real^N) <= R` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_CBALL_0]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x w. ~((x:real^N) IN B) /\ w IN W ==> ~(x + w IN c)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "B" THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `norm(x + w:real^N) <= R` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_CBALL_0];
      MP_TAC(NORM_ARITH `!a b:real^N. norm a <= norm(a + b) + norm b`) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `w:real^N`]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~((x:real^N) IN B) ==> wan_moll e (psi:real^N->real^K) x = vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:real`; `psi:real^N->real^K`; `c:real^N->bool`] WAN_MOLL_SUPPORT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN REWRITE_TAC[IN_BALL_0] THEN
    STRIP_TAC THEN UNDISCH_TAC `~((x:real^N) IN B)` THEN EXPAND_TAC "B" THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN
    SUBGOAL_THEN `norm(a:real^N) <= R` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_CBALL_0]; ALL_TAC] THEN
    MP_TAC(NORM_ARITH `!a b:real^N. norm(a + b) <= norm a + norm b`) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_moll e (psi:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC WAN_MOLL_SMOOTH THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(norm(wan_moll e (psi:real^N->real^K) x - psi x) pow 2)`;
                 `B:real^N->bool`] WAN_INTEGRAL_UNIV_SUPPORT) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `wan_moll e (psi:real^N->real^K) x = vec 0 /\ psi x = vec 0`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM];
    DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN
   `(\z:real^(N,N)finite_sum.
       lift(norm((psi:real^N->real^K)(fstcart z + sndcart z) - psi(fstcart z)) pow 2))
    continuous_on (B PCROSS W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(N,N)finite_sum)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\z:real^(N,N)finite_sum. (psi:real^N->real^K)(fstcart z + sndcart z)) =
        psi o (\z. fstcart z + sndcart z)` SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_ADD; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      SUBGOAL_THEN
       `(\z:real^(N,N)finite_sum. (psi:real^N->real^K)(fstcart z)) = psi o fstcart`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real^(N,N)finite_sum.
       lift(norm((psi:real^N->real^K)(fstcart z + sndcart z) - psi(fstcart z)) pow 2)`;
    `B:real^N->bool`; `W:real^N->bool`] WAN_FUBINI_PCROSS) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`psi:real^N->real^K`; `c:real^N->bool`] WAN_SQGRAD_INTEGRABLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC
   `Gint = drop(integral (:real^N)
                  (\x. lift(sum(1..dimindex(:N))
                              (\i. norm(partial_derivative i (psi:real^N->real^K) x) pow 2))))` THEN
  SUBGOAL_THEN
   `!w. w IN W
        ==> drop(integral B (\x. lift(norm((psi:real^N->real^K)(x + w) - psi x) pow 2))) <=
            e pow 2 * Gint`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x. lift(norm((psi:real^N->real^K)(x + w) - psi x) pow 2)`;
                   `B:real^N->bool`] WAN_INTEGRAL_UNIV_SUPPORT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(psi:real^N->real^K)(x + w) = vec 0 /\ psi x = vec 0`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM];
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`psi:real^N->real^K`; `c:real^N->bool`; `w:real^N`] WAN_TRANSL_EST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    UNDISCH_TAC `(w:real^N) IN W` THEN EXPAND_TAC "W" THEN REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(wan_moll e (psi:real^N->real^K) x - psi x) pow 2)) integrable_on B`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^N->bool`;
                 `\x. drop(integral W (\w. lift(norm((psi:real^N->real^K)(x + w) - psi x)
                                                pow 2)))`;
                 `measure(W:real^N->bool) * K0 pow 2`] WAN_INTEGRAL_LIN1) THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral B (\x. lift((measure(W:real^N->bool) * K0 pow 2) *
                              drop(integral W (\w. lift(norm((psi:real^N->real^K)(x + w) -
                                                           psi x) pow 2))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; GSYM REAL_MUL_ASSOC] THEN
    USE_THEN "PB" (MATCH_ACCEPT_TAC o SPEC `x:real^N`);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `drop(integral B (\x. integral W (\w. lift(norm((psi:real^N->real^K)(x + w) - psi x)
                                             pow 2)))) <=
    measure(W:real^N->bool) * (e pow 2 * Gint)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral W (\w:real^N. lift(e pow 2 * Gint)))` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `integral B (\x. integral W (\w. lift(norm((psi:real^N->real^K)(x + w) - psi x)
                                           pow 2))) =
        integral W (\w. integral B (\x. lift(norm(psi(x + w) - psi x) pow 2)))`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[integrable_on] THEN
        EXISTS_TAC `measure(W:real^N->bool) % lift(e pow 2 * Gint)` THEN
        MATCH_MP_TAC HAS_INTEGRAL_CONST_GEN THEN ASM_SIMP_TAC[MEASURABLE_COMPACT];
        ALL_TAC] THEN
      REWRITE_TAC[LIFT_DROP] THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_COMPACT; DROP_CMUL; LIFT_DROP;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(W:real^N->bool) = e pow dimindex(:N) * measure(cball(vec 0:real^N,&1))`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    MP_TAC(ISPECL [`vec 0:real^N`; `e:real`; `&1`] MEASURE_CBALL_SCALING) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(W:real^N->bool) * K0 = Bk * measure(cball(vec 0:real^N,&1))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "K0" THEN
    SUBGOAL_THEN `e pow dimindex(:N) * inv e pow dimindex(:N) = &1` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_POW_ONE];
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= measure(W:real^N->bool) * K0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT; MEASURE_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(measure(W:real^N->bool) * K0 pow 2) * (measure W * (e pow 2 * Gint))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  UNDISCH_TAC `measure(W:real^N->bool) * K0 = Bk * measure(cball(vec 0:real^N,&1))` THEN
  CONV_TAC REAL_RING);;


(* ------------------------------------------------------------------------- *)
(* The mollification estimate for L^2 limits of smooth compactly supported  *)
(* maps, in particular for zero extensions of W^{1,2}_0 maps:               *)
(*   int |rho_e * F - F|^2 <= C e^2 wan_dir s u.                           *)
(* ------------------------------------------------------------------------- *)

let WAN_MOLL_LINEAR_SUB = prove
 (`!e (f:real^N->real^K) g x.
     &0 < e /\ wan_lloc (:real^N) f /\ wan_lloc (:real^N) g
     ==> wan_moll e f x - wan_moll e g x = wan_moll e (\y. f y - g y) x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_moll; wan_kconv; VECTOR_SUB_LDISTRIB] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST]);;

let WAN_CONT_SUPPORT_LSPACE2 = prove
 (`!(f:real^N->real^K) c.
     f continuous_on (:real^N) /\ compact c /\ (!x. ~(x IN c) ==> f x = vec 0)
     ==> f IN lspace (:real^N) (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(norm((f:real^N->real^K) x) rpow &2)`; `c:real^N->bool`]
                WAN_INTEGRAL_UNIV_SUPPORT) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[NORM_0; RPOW_ZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM];
    DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  MATCH_MP_TAC LSPACE_IMP_INTEGRABLE THEN MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let WAN_LNORM_MOLL_LE = prove
 (`!e (g:real^N->real^K).
     &0 < e /\ g IN lspace (:real^N) (&2)
     ==> wan_moll e g IN lspace (:real^N) (&2) /\
         lnorm (:real^N) (&2) (wan_moll e g) <= lnorm (:real^N) (&2) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `g:real^N->real^K`] (INST_TYPE [`:N`,`:M`] WAN_MOLL_L2)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[LNORM_POS_LE; WAN_SOB_LNORM2_SQ; ARITH]);;

let WAN_MOLL_L2_EST_GEN = prove
 (`?C. &0 < C /\
       !e (FF:real^N->real^K) (psi:num->real^N->real^K) c D.
         &0 < e /\ FF IN lspace (:real^N) (&2) /\
         (!n. smooth_map_on (:real^N) (psi n) /\ compact (c n) /\
              (!x. ~(x IN c n) ==> psi n x = vec 0)) /\
         ((\n. lnorm (:real^N) (&2) (\x. psi n x - FF x)) ---> &0) sequentially /\
         ((\n. drop(integral (:real^N)
                 (\x. lift(sum(1..dimindex(:N))
                             (\i. norm(partial_derivative i (psi n) x) pow 2)))))
          ---> D) sequentially
         ==> drop(integral (:real^N) (\x. lift(norm(wan_moll e FF x - FF x) pow 2))) <=
             C * e pow 2 * D`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC WAN_MOLL_TEST_EST THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `G = \n. drop(integral (:real^N)
                 (\x. lift(sum(1..dimindex(:N))
                             (\i. norm(partial_derivative i ((psi:num->real^N->real^K) n) x)
                                  pow 2))))` THEN
  SUBGOAL_THEN `!n. &0 <= (G:num->real) n` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(psi:num->real^N->real^K) n`; `(c:num->real^N->bool) n`]
                  WAN_SQGRAD_INTEGRABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC `G:num->real` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE] THEN
    EXPAND_TAC "G" THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (psi:num->real^N->real^K) n IN lspace (:real^N) (&2)` ASSUME_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC WAN_CONT_SUPPORT_LSPACE2 THEN
    EXISTS_TAC `(c:num->real^N->bool) n` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_moll e (FF:real^N->real^K) IN lspace (:real^N) (&2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_LNORM_MOLL_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. wan_moll e (FF:real^N->real^K) x - FF x) IN lspace (:real^N) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. lnorm (:real^N) (&2) (\x. wan_moll e (FF:real^N->real^K) x - FF x) <=
        &2 * lnorm (:real^N) (&2) (\x. (psi:num->real^N->real^K) n x - FF x) +
        sqrt(C * e pow 2 * G n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `wan_moll e ((psi:num->real^N->real^K) n) IN lspace (:real^N) (&2)`
    ASSUME_TAC THENL [ASM_MESON_TAC[WAN_LNORM_MOLL_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. wan_moll e (FF:real^N->real^K) x - wan_moll e ((psi:num->real^N->real^K) n) x)
      IN lspace (:real^N) (&2) /\
      (\x. wan_moll e (psi n) x - psi n x) IN lspace (:real^N) (&2) /\
      (\x. psi n x - FF x) IN lspace (:real^N) (&2)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\x. wan_moll e (FF:real^N->real^K) x - FF x) =
      (\x. (wan_moll e FF x - wan_moll e ((psi:num->real^N->real^K) n) x) +
           ((wan_moll e (psi n) x - psi n x) + (psi n x - FF x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `lnorm (:real^N) (&2) (\x. wan_moll e (FF:real^N->real^K) x -
                                 wan_moll e ((psi:num->real^N->real^K) n) x) +
      lnorm (:real^N) (&2) (\x. (wan_moll e (psi n) x - psi n x) + (psi n x - FF x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN
      MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= p /\ b <= y + p ==> a + b <= &2 * p + y`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`e:real`; `FF:real^N->real^K`; `(psi:num->real^N->real^K) n`]
                    WAN_MOLL_LINEAR_SUB) THEN
      ASM_SIMP_TAC[WAN_L2_LLOC; ETA_AX] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(\y. (FF:real^N->real^K) y - (psi:num->real^N->real^K) n y)
                    IN lspace (:real^N) (&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lnorm (:real^N) (&2) (\y. (FF:real^N->real^K) y - (psi:num->real^N->real^K) n y)` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`e:real`; `\y. (FF:real^N->real^K) y - (psi:num->real^N->real^K) n y`]
                      WAN_LNORM_MOLL_LE) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        GEN_REWRITE_TAC LAND_CONV [GSYM LNORM_NEG] THEN
        REWRITE_TAC[VECTOR_NEG_SUB; REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `lnorm (:real^N) (&2) (\x. wan_moll e ((psi:num->real^N->real^K) n) x - psi n x) +
      lnorm (:real^N) (&2) (\x. psi n x - (FF:real^N->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= y ==> a + p <= y + p`) THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    MP_TAC(ISPECL [`\x. wan_moll e ((psi:num->real^N->real^K) n) x - psi n x`; `(:real^N)`]
                  WAN_SOB_LNORM2_SQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
       can (find_term ((=) `wan_moll:real->(real^N->real^K)->real^N->real^K`)) (concl th))) THEN
    EXISTS_TAC `(c:num->real^N->bool) n` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm (:real^N) (&2) (\x. wan_moll e (FF:real^N->real^K) x - FF x) <=
    sqrt(C * e pow 2 * D)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LBOUND) THEN
    EXISTS_TAC `\n. &2 * lnorm (:real^N) (&2) (\x. (psi:num->real^N->real^K) n x - FF x) +
                    sqrt(C * e pow 2 * G n)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `x = &2 * &0 + x`] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
      REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT] THEN
      MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_LMUL THEN
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. wan_moll e (FF:real^N->real^K) x - FF x`; `(:real^N)`]
                WAN_SOB_LNORM2_SQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(C * e pow 2 * D) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[LNORM_POS_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SQRT_POW_2 THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

let WAN_VTEST_SQGRAD_INTEGRAL = prove
 (`!(s:real^N->bool) (psi:real^N->real^K) c.
     open s /\ smooth_map_on (:real^N) psi /\ compact c /\ c SUBSET s /\
     (!x. ~(x IN c) ==> psi x = vec 0)
     ==> drop(integral (:real^N)
               (\x. lift(sum(1..dimindex(:N))
                           (\i. norm(partial_derivative i psi x) pow 2)))) =
         wan_dir s psi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_vtest s (psi:real^N->real^K)` ASSUME_TAC THENL
   [REWRITE_TAC[wan_vtest] THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (\x. partial_derivative i (psi:real^N->real^K) x) continuous_on (:real^N) /\
        (!x. ~(x IN c) ==> partial_derivative i psi x = vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real^K`; `c:real^N->bool`; `i:num`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (\x. lift(norm(partial_derivative i (psi:real^N->real^K) x) pow 2))
        integrable_on (:real^N) /\
        integral (:real^N) (\x. lift(norm(partial_derivative i psi x) pow 2)) =
        integral s (\x. lift(norm(partial_derivative i psi x) pow 2))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `(\x. lift(norm(partial_derivative i (psi:real^N->real^K) x) pow 2))
      continuous_on (:real^N)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. ~(x IN c) ==> lift(norm(partial_derivative i (psi:real^N->real^K) x) pow 2) =
                        vec 0`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. lift(norm(partial_derivative i (psi:real^N->real^K) x) pow 2)`;
                   `c:real^N->bool`] WAN_INTEGRAL_UNIV_SUPPORT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN c` THENL
     [SUBGOAL_THEN `(x:real^N) IN s` (fun th -> ASM_REWRITE_TAC[th]) THEN ASM SET_TAC[];
      ASM_SIMP_TAC[COND_ID]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_VTEST_DIR_EQ] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MP_TAC(ISPECL [`\i x. lift(norm(partial_derivative i (psi:real^N->real^K) x) pow 2)`;
                 `(:real^N)`; `1..dimindex(:N)`] INTEGRAL_VSUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_VSUM; o_DEF] THEN ASM_REWRITE_TAC[]);;

let WAN_MOLL_W120_EST = prove
 (`?C. &0 < C /\
       !e (s:real^N->bool) (u:real^N->real^K).
         &0 < e /\ open s /\ wan_w120 s u
         ==> drop(integral (:real^N)
               (\x. lift(norm(wan_moll e (\y. if y IN s then u y else vec 0) x -
                              (if x IN s then u x else vec 0)) pow 2))) <=
             C * e pow 2 * wan_dir s u`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC WAN_MOLL_L2_EST_GEN THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[wan_w120] o check (fun th ->
    concl th = `wan_w120 s (u:real^N->real^K)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?c:num->real^N->bool.
      !n. smooth_map_on (:real^N) ((f:num->real^N->real^K) n) /\ compact (c n) /\
          c n SUBSET s /\ (!x. ~(x IN c n) ==> f n x = vec 0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM_MESON_TAC[wan_vtest];
    ALL_TAC] THEN
  ABBREV_TAC `FF = \y. if y IN s then (u:real^N->real^K) y else vec 0` THEN
  SUBGOAL_THEN `!x. (if x IN s then (u:real^N->real^K) x else vec 0) = FF x`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN EXPAND_TAC "FF" THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`f:num->real^N->real^K`; `c:num->real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "FF" THEN ASM_MESON_TAC[WAN_W120_ZERO_EXT];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. lnorm s (&2) (\x. (f:num->real^N->real^K) n x - u x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[lnorm] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\x. lift(norm((f:num->real^N->real^K) n x - FF x) rpow &2)`;
                   `s:real^N->bool`] WAN_INTEGRAL_UNIV_SUPPORT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f:num->real^N->real^K) n x = vec 0 /\ (FF:real^N->real^K) x = vec 0`
      (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "FF" THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; RPOW_ZERO] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM]];
      DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "FF" THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\n. wan_dir s ((f:num->real^N->real^K) n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_VTEST_SQGRAD_INTEGRAL THEN
      EXISTS_TAC `(c:num->real^N->bool) n` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WAN_DIR_CONT THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[WAN_VTEST_W12]]]);;


(* ------------------------------------------------------------------------- *)
(* Uniform bounds for mollified maps supported in a set of finite measure:  *)
(* |rho_e * F| <= A sqrt(|S|) ||F||, Lipschitz constant L sqrt(|S|) ||F||.  *)
(* ------------------------------------------------------------------------- *)

let WAN_BOUNDED_PAIR_L2 = prove
 (`!(q:real^N->real) (FF:real^N->real^K) S kappa.
     measurable S /\ &0 <= kappa /\ FF IN lspace (:real^N) (&2) /\
     (!y. ~(y IN S) ==> FF y = vec 0) /\
     (\y. q y % FF y) integrable_on (:real^N) /\ (!y. y IN S ==> abs(q y) <= kappa)
     ==> norm(integral (:real^N) (\y. q y % FF y)) <=
         kappa * sqrt(measure S) * lnorm (:real^N) (&2) FF`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(FF:real^N->real^K) IN lspace S (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `lnorm (:real^N) (&2) (FF:real^N->real^K) = lnorm S (&2) FF`
  SUBST1_TAC THENL
   [REWRITE_TAC[lnorm] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\x. lift(norm((FF:real^N->real^K) x) rpow &2)`; `S:real^N->bool`]
                  WAN_INTEGRAL_UNIV_SUPPORT) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[NORM_0; RPOW_ZERO] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LIFT_NUM];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. (q:real^N->real) y % (FF:real^N->real^K) y`; `S:real^N->bool`]
                WAN_INTEGRAL_UNIV_SUPPORT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `(\y. (q:real^N->real) y % (FF:real^N->real^K) y) integrable_on S`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(norm((FF:real^N->real^K) y))) integrable_on S` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`FF:real^N->real^K`; `S:real^N->bool`; `&1`] WAN_L2_L1_BOUND) THEN
    ASM_SIMP_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral S (\y. lift(kappa * norm((FF:real^N->real^K) y))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[NORM_POS_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_CMUL] THEN ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `\y. lift(norm((FF:real^N->real^K) y))`]
                WAN_INTEGRAL_SQ_CS) THEN
  ASM_SIMP_TAC[LSPACE_NORM; NORM_LIFT; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[GSYM WAN_SOB_LNORM2_SQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= drop(integral S (\y. lift(norm((FF:real^N->real^K) y))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(measure(S:real^N->bool)) * lnorm S (&2) (FF:real^N->real^K) =
    sqrt(measure S * lnorm S (&2) FF pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC POW_2_SQRT THEN MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  UNDISCH_TAC
   `norm(integral S (\y. lift(norm((FF:real^N->real^K) y)))) pow 2 <=
    measure S * lnorm S (&2) FF pow 2` THEN
  ASM_SIMP_TAC[NORM_1; REAL_ARITH `&0 <= x ==> abs x = x`]);;

let WAN_MOLL_FAMILY_BOUNDS = prove
 (`!e. &0 < e
       ==> ?A L. &0 <= A /\ &0 <= L /\
             !(FF:real^N->real^K) S x y.
               measurable S /\ FF IN lspace (:real^N) (&2) /\
               (!z. ~(z IN S) ==> FF z = vec 0)
               ==> norm(wan_moll e FF x) <= A * sqrt(measure S) * lnorm (:real^N) (&2) FF /\
                   norm(wan_moll e FF x - wan_moll e FF y) <=
                   (L * norm(x - y)) * sqrt(measure S) * lnorm (:real^N) (&2) FF`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `Bk:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WAN_MKE_ABS_BOUND) THEN
  MP_TAC(ISPEC `e:real` (INST_TYPE [`:N`,`:M`] WAN_MKE_PROPS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`wan_mke e:real^N->real`; `cball(vec 0:real^N,e)`]
                WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MAP_EVERY EXISTS_TAC [`Bk * inv(e) pow dimindex(:N)`; `abs B`] THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_lloc (:real^N) (FF:real^N->real^K)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_L2_LLOC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^N. (\z. wan_mke e (a - z) % (FF:real^N->real^K) z) integrable_on (:real^N)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST];
    ALL_TAC] THEN
  REWRITE_TAC[wan_moll; wan_kconv] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_BOUNDED_PAIR_L2 THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_POW_LE; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_SUB; GSYM VECTOR_SUB_RDISTRIB] THEN
  MATCH_MP_TAC WAN_BOUNDED_PAIR_L2 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE];
    REWRITE_TAC[VECTOR_SUB_RDISTRIB] THEN MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm((x - z) - (y - z):real^N)` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(x - z) - (y - z):real^N = x - y`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Arzela-Ascoli for uniformly bounded, uniformly Lipschitz families, in    *)
(* the form needed for SUBSEQUENCE_DIAGONALIZATION_LEMMA (uniformly Cauchy  *)
(* subsequences, stable under passing to later subsequences).                *)
(* ------------------------------------------------------------------------- *)

let WAN_AA_SUBSEQ = prove
 (`!(f:num->real^N->real^K) C Bd Lc (r:num->num).
     compact C /\ (!n x. x IN C ==> norm(f n x) <= Bd) /\
     (!n x y. x IN C /\ y IN C ==> norm(f n x - f n y) <= Lc * norm(x - y))
     ==> ?k:num->num. (!m n. m < n ==> k m < k n) /\
             !d. &0 < d ==> ?N:num. !m n x. N <= m /\ N <= n /\ x IN C
                                ==> norm(f (r(k m)) x - f (r(k n)) x) < d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. (f:num->real^N->real^K) ((r:num->num) n)`; `C:real^N->bool`;
                 `cball(vec 0:real^K,Bd)`; `Lc:real`] ARZELA_ASCOLI_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[BOUNDED_CBALL] THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
    EXISTS_TAC `(f:num->real^N->real^K) ((r:num->num) n) x` THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[IN_CBALL_0]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^K` (CONJUNCTS_THEN2 (K ALL_TAC)
    (X_CHOOSE_THEN `k:num->num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `k:num->num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `x:real^N`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[GE] THEN CONV_TAC NORM_ARITH);;

let WAN_UCAUCHY_SUBSEQ = prove
 (`!(f:num->real^N->real^K) C (r:num->num) (k1:num->num) (k2:num->num) (N:num).
     (!d. &0 < d ==> ?N:num. !m n x. N <= m /\ N <= n /\ x IN C
                          ==> norm(f ((r o k1) m) x - f ((r o k1) n) x) < d) /\
     (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
     ==> !d. &0 < d ==> ?N:num. !m n x. N <= m /\ N <= n /\ x IN C
                             ==> norm(f ((r o k2) m) x - f ((r o k2) n) x) < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N + N0:num` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
    can (find_term ((=) `k2:num->num`)) (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    can (find_term ((=) `k2:num->num`)) (concl th) && is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n':num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m':num`; `n':num`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let WAN_UNIF_TO_L2 = prove
 (`!(g:real^N->real^K) C eta.
     compact C /\ &0 <= eta /\ g continuous_on (:real^N) /\
     (!x. ~(x IN C) ==> g x = vec 0) /\ (!x. x IN C ==> norm(g x) <= eta)
     ==> g IN lspace (:real^N) (&2) /\
         lnorm (:real^N) (&2) g <= sqrt(measure C) * eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^N->real^K) IN lspace (:real^N) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_SUPPORT_LSPACE2 THEN EXISTS_TAC `C:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt(measure(C:real^N->bool)) * eta = sqrt(measure C * eta pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC POW_2_SQRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  MP_TAC(ISPECL [`\x. lift(norm((g:real^N->real^K) x) pow 2)`; `C:real^N->bool`]
                WAN_INTEGRAL_UNIV_SUPPORT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `(\x. lift(norm((g:real^N->real^K) x) pow 2)) integrable_on C` ASSUME_TAC
  THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral C (\x:real^N. lift(eta pow 2)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[integrable_on] THEN EXISTS_TAC `measure(C:real^N->bool) % lift(eta pow 2)` THEN
      MATCH_MP_TAC HAS_INTEGRAL_CONST_GEN THEN ASM_SIMP_TAC[MEASURABLE_COMPACT];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE]];
    ASM_SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_COMPACT; DROP_CMUL; LIFT_DROP;
                 REAL_LE_REFL]]);;

let WAN_MOLL_SUPPORT_BALL = prove
 (`!e (FF:real^N->real^K) S R x.
     &0 < e /\ e <= &1 /\ S SUBSET cball(vec 0,R) /\ (!z. ~(z IN S) ==> FF z = vec 0) /\
     ~(x IN cball(vec 0,R + &1))
     ==> wan_moll e FF x = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real`; `FF:real^N->real^K`; `S:real^N->bool`] WAN_MOLL_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN REWRITE_TAC[IN_BALL_0] THEN
  STRIP_TAC THEN UNDISCH_TAC `~((x:real^N) IN cball(vec 0,R + &1))` THEN
  ASM_REWRITE_TAC[IN_CBALL_0] THEN
  SUBGOAL_THEN `norm(a:real^N) <= R` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_CBALL_0]; ALL_TAC] THEN
  MP_TAC(NORM_ARITH `!a b:real^N. norm(a + b) <= norm a + norm b`) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Compactness criterion in L^2 (Kolmogorov-Riesz form): maps supported in  *)
(* a fixed bounded set, bounded in L^2, uniformly approximated by their     *)
(* mollifications, have an L^2-Cauchy subsequence.                          *)
(* ------------------------------------------------------------------------- *)

let WAN_L2_COMPACT_CRITERION = prove
 (`!(FF:num->real^N->real^K) S M0.
     bounded S /\ measurable S /\
     (!n. FF n IN lspace (:real^N) (&2)) /\ (!n z. ~(z IN S) ==> FF n z = vec 0) /\
     (!n. lnorm (:real^N) (&2) (FF n) <= M0) /\
     (!d. &0 < d ==> ?e. &0 < e /\ e <= &1 /\
             !n. lnorm (:real^N) (&2) (\x. wan_moll e (FF n) x - FF n x) <= d)
     ==> ?r:num->num. (!m n. m < n ==> r m < r n) /\
             !d. &0 < d ==> ?N:num. !m n. N <= m /\ N <= n
                     ==> lnorm (:real^N) (&2) (\x. FF (r m) x - FF (r n) x) < d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  DISCH_THEN(MP_TAC o GEN `k:num` o SPEC `inv(&k + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &k + &1`] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ee:num->real` (LABEL_TAC "EE")) THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^N` o MATCH_MP BOUNDED_SUBSET_CBALL) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `C = cball(vec 0:real^N,R + &1)` THEN
  SUBGOAL_THEN `compact(C:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[COMPACT_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?AA LL. !k. &0 <= AA k /\ &0 <= LL k /\
        (!(G:real^N->real^K) T x y.
           measurable T /\ G IN lspace (:real^N) (&2) /\ (!z. ~(z IN T) ==> G z = vec 0)
           ==> norm(wan_moll ((ee:num->real) k) G x) <=
               AA k * sqrt(measure T) * lnorm (:real^N) (&2) G /\
               norm(wan_moll (ee k) G x - wan_moll (ee k) G y) <=
               (LL k * norm(x - y)) * sqrt(measure T) * lnorm (:real^N) (&2) G)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN MATCH_MP_TAC WAN_MOLL_FAMILY_BOUNDS THEN
    USE_THEN "EE" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= lnorm (:real^N) (&2) ((FF:num->real^N->real^K) n)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M0` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPEC
   `\k (q:num->num). !d. &0 < d
        ==> ?N:num. !m n x. N <= m /\ N <= n /\ x IN C
              ==> norm(wan_moll ((ee:num->real) k) ((FF:num->real^N->real^K) (q m)) x -
                       wan_moll (ee k) (FF (q n)) x) < d`
   SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `r0:num->num`] THEN
      MP_TAC(ISPECL [`\n. wan_moll ((ee:num->real) i) ((FF:num->real^N->real^K) n)`;
                     `C:real^N->bool`;
                     `(AA:num->real) i * sqrt(measure(S:real^N->bool)) * M0`;
                     `(LL:num->real) i * sqrt(measure(S:real^N->bool)) * M0`;
                     `r0:num->num`] WAN_AA_SUBSEQ) THEN
      REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(AA:num->real) i * sqrt(measure(S:real^N->bool)) *
                    lnorm (:real^N) (&2) ((FF:num->real^N->real^K) n)` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; MEASURE_POS_LE];
        MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `((LL:num->real) i * norm(x - y:real^N)) *
                    sqrt(measure(S:real^N->bool)) *
                    lnorm (:real^N) (&2) ((FF:num->real^N->real^K) n)` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN
         `((LL:num->real) i * sqrt(measure(S:real^N->bool)) * M0) * norm(x - y:real^N) =
          (LL i * norm(x - y)) * sqrt(measure S) * M0`
        SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[NORM_POS_LE]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; MEASURE_POS_LE]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\n. wan_moll ((ee:num->real) i) ((FF:num->real^N->real^K) n)`;
                     `C:real^N->bool`; `r:num->num`; `k1:num->num`; `k2:num->num`;
                     `N:num`] WAN_UCAUCHY_SUBSEQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "UC"))) THEN
  EXISTS_TAC `k:num->num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `d / &3` REAL_ARCH_INV) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < d / &3 <=> &0 < d`] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `inv(&i + &1) < d / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&i)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = sqrt(measure(C:real^N->bool))` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[SQRT_POS_LE; MEASURE_POS_LE; MEASURABLE_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?eta. &0 < eta /\ q * eta < d / &3` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `d / (&3 * (q + &1))` THEN
    SUBGOAL_THEN `&0 < &3 * (q + &1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "UC" (fun th -> MP_TAC(MP (SPECL [`i:num`; `eta:real`] th)
                                      (ASSUME `&0 < eta`))) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. wan_moll ((ee:num->real) i) ((FF:num->real^N->real^K) j) IN lspace (:real^N) (&2) /\
        wan_moll (ee i) (FF j) continuous_on (:real^N) /\
        (!x. ~(x IN C) ==> wan_moll (ee i) (FF j) x = vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "EE" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[WAN_LNORM_MOLL_LE];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC WAN_MOLL_SMOOTH THEN
      ASM_SIMP_TAC[WAN_L2_LLOC];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC WAN_MOLL_SUPPORT_BALL THEN
      MAP_EVERY EXISTS_TAC [`S:real^N->bool`; `R:real`] THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (FF:num->real^N->real^K) ((k:num->num) m) x - wan_moll ((ee:num->real) i) (FF (k m)) x)
    IN lspace (:real^N) (&2) /\
    (\x. wan_moll (ee i) (FF (k m)) x - wan_moll (ee i) (FF (k n)) x)
    IN lspace (:real^N) (&2) /\
    (\x. wan_moll (ee i) (FF (k n)) x - FF (k n) x) IN lspace (:real^N) (&2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (FF:num->real^N->real^K) ((k:num->num) m) x - FF (k n) x) =
    (\x. (FF (k m) x - wan_moll ((ee:num->real) i) (FF (k m)) x) +
         ((wan_moll (ee i) (FF (k m)) x - wan_moll (ee i) (FF (k n)) x) +
          (wan_moll (ee i) (FF (k n)) x - FF (k n) x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC
   `lnorm (:real^N) (&2) (\x. (FF:num->real^N->real^K) ((k:num->num) m) x -
                              wan_moll ((ee:num->real) i) (FF (k m)) x) +
    lnorm (:real^N) (&2) (\x. wan_moll (ee i) (FF (k m)) x - wan_moll (ee i) (FF (k n)) x) +
    lnorm (:real^N) (&2) (\x. wan_moll (ee i) (FF (k n)) x - FF (k n) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `lnorm (:real^N) (&2) (\x. (FF:num->real^N->real^K) ((k:num->num) m) x -
                                wan_moll ((ee:num->real) i) (FF (k m)) x) +
      lnorm (:real^N) (&2) (\x. (wan_moll (ee i) (FF (k m)) x - wan_moll (ee i) (FF (k n)) x) +
                                (wan_moll (ee i) (FF (k n)) x - FF (k n) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN
      MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a + b <= a + c`) THEN
      MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a < d / &3 /\ b < d / &3 /\ c < d / &3 ==> a + b + c < d`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&i + &1)` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM LNORM_NEG] THEN REWRITE_TAC[VECTOR_NEG_SUB] THEN
    USE_THEN "EE" (fun th -> REWRITE_TAC[th]);
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `q * eta` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "q" THEN
    MP_TAC(ISPECL [`\x. wan_moll ((ee:num->real) i) ((FF:num->real^N->real^K) ((k:num->num) m)) x -
                        wan_moll (ee i) (FF (k n)) x`;
                   `C:real^N->bool`; `eta:real`] WAN_UNIF_TO_L2) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      ASM_SIMP_TAC[VECTOR_SUB_REFL]];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&i + &1)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "EE" (fun th -> REWRITE_TAC[th])]);;


(* ------------------------------------------------------------------------- *)
(* L^2 convergence gives an a.e. convergent subsequence.                     *)
(* ------------------------------------------------------------------------- *)

let WAN_L2_AE_SUBSEQ = prove
 (`!(s:real^N->bool) (f:num->real^N->real^K) g.
     (!n. f n IN lspace s (&2)) /\ g IN lspace s (&2) /\
     ((\n. lnorm s (&2) (\x. f n x - g x)) ---> &0) sequentially
     ==> ?q:num->num. (!m n. m < n ==> q m < q n) /\
           ?S. negligible S /\
               !x. x IN s DIFF S ==> ((\n. f (q n) x) --> g x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. (\x. (f:num->real^N->real^K) n x - g x) IN lspace s (&2)` ASSUME_TAC
  THENL [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
         ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. ?N. !n. N <= n
              ==> lnorm s (&2) (\x. (f:num->real^N->real^K) n x - g x) pow 2 <=
                  inv(&2) pow j`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sqrt(inv(&2) pow j)` o
      REWRITE_RULE[REALLIM_SEQUENTIALLY] o check (fun th ->
        can (find_term ((=) `(--->):(num->real)->real->(num)net->bool`)) (concl th))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `inv(&2) pow j = sqrt(inv(&2) pow j) pow 2` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_POW_2 THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[LNORM_POS_LE; REAL_LT_IMP_LE; REAL_ARITH `abs x < y ==> x <= y`];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `NN:num->num`) THEN
  EXISTS_TAC `\j. j + nsum(0..j) (NN:num->num)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG; LE_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. (NN:num->num) j <= j + nsum(0..j) NN` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE `a:num <= b ==> a <= j + b`) THEN
    MP_TAC(ISPECL [`{j:num}`; `0..j`; `NN:num->num`] NSUM_SUBSET_SIMPLE) THEN
    REWRITE_TAC[NSUM_SING; FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; LE_0; LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j x. lift(norm((f:num->real^N->real^K) (j + nsum(0..j) NN) x - g x)
                             pow 2)`; `s:real^N->bool`] WAN_SUMMABLE_AE_NULL) THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN
      MP_TAC(ISPECL [`\x. (f:num->real^N->real^K) (n + nsum(0..n) NN) x - g x`;
                     `s:real^N->bool`] WAN_SOB_LNORM2_SQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `inv(&2)`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; LIM_SEQUENTIALLY; dist; REAL_SUB_RZERO] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e pow 2`) THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;


(* ------------------------------------------------------------------------- *)
(* W^{1,2}_0 is closed under scalar multiples and finite combinations, and  *)
(* (Mazur) under L^2 limits with bounded Dirichlet integrals; the bound     *)
(* ||v||^2 + dir(v) <= M passes to L^2 limits.                              *)
(* ------------------------------------------------------------------------- *)

let WAN_VTEST_CMUL = prove
 (`!(s:real^N->bool) (f:real^N->real^K) c. wan_vtest s f ==> wan_vtest s (\x. c % f x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_vtest] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV];
    EXISTS_TAC `k:real^N->bool` THEN ASM_SIMP_TAC[VECTOR_MUL_RZERO]]);;

let WAN_DIR_CMUL = prove
 (`!(s:real^N->bool) (u:real^N->real^K) c.
     open s /\ wan_w12 s u
     ==> wan_w12 s (\x. c % u x) /\ wan_dir s (\x. c % u x) = c pow 2 * wan_dir s u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> wan_wpd s i (\x. c % (u:real^N->real^K) x) (\x. c % wan_wd s i u x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_CMUL THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (\x. c % (u:real^N->real^K) x)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_CMUL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. c % (u:real^N->real^K) x`;
                 `\i x. c % wan_wd s i (u:real^N->real^K) x`] WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dir; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_POW2_ABS; LIFT_CMUL] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `wan_wd s i (u:real^N->real^K)`]
                WAN_LSPACE2_SQNORM_INTEGRABLE) THEN
  ASM_SIMP_TAC[WAN_WD_WORKS; INTEGRAL_CMUL; DROP_CMUL]);;

let WAN_W120_CMUL = prove
 (`!(s:real^N->bool) (u:real^N->real^K) c.
     open s /\ wan_w120 s u ==> wan_w120 s (\x. c % u x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w120] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC))) THEN
  ASM_SIMP_TAC[WAN_DIR_CMUL] THEN
  EXISTS_TAC `\n x. c % (f:num->real^N->real^K) n x` THEN
  SUBGOAL_THEN
   `!n. (\x. c % (f:num->real^N->real^K) n x - c % u x) = (\x. c % (f n x - u x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!n. wan_w12 s (\x. (f:num->real^N->real^K) n x - u x)` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `(f:num->real^N->real^K) n`] WAN_VTEST_W12) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (\x. (f:num->real^N->real^K) n x - u x) IN lspace s (&2)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_VTEST_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    SUBGOAL_THEN
     `!n. lnorm s (&2) (\x. c % ((f:num->real^N->real^K) n x - u x)) =
          abs c * lnorm s (&2) (\x. f n x - u x)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC LNORM_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM(SPEC `abs c` REAL_MUL_RZERO)] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `!n. wan_dir s (\x. c % ((f:num->real^N->real^K) n x - u x)) =
          c pow 2 * wan_dir s (\x. f n x - u x)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MP_TAC(ISPECL [`s:real^N->bool`; `\x. (f:num->real^N->real^K) n x - u x`;
                                  `c:real`] WAN_DIR_CMUL) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM(SPEC `c pow 2` REAL_MUL_RZERO)] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]]);;

let WAN_W120_VSUM_CMUL = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) (c:num->real) a b.
     open s /\ (!m. a <= m /\ m <= b ==> wan_w120 s (u m))
     ==> wan_w120 s (\x. vsum(a..b) (\m. c m % u m x))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THEN STRIP_TAC THEN ASM_CASES_TAC `a = 0` THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC WAN_W120_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC WAN_VTEST_W120 THEN ASM_REWRITE_TAC[wan_vtest] THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN EXISTS_TAC `{}:real^N->bool` THEN
      REWRITE_TAC[COMPACT_EMPTY; EMPTY_SUBSET]];
    STRIP_TAC THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG] THEN ASM_CASES_TAC `a <= SUC b` THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC WAN_W120_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC WAN_W120_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let WAN_W120_WEAK_CLOSED = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) v M.
     open s /\ (!n. wan_w120 s (u n) /\ wan_dir s (u n) <= M) /\ v IN lspace s (&2) /\
     ((\n. lnorm s (&2) (\x. u n x - v x)) ---> &0) sequentially
     ==> wan_w120 s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. wan_w12 s ((u:num->real^N->real^K) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (u:num->real^N->real^K) n IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. compact k /\ k SUBSET s
        ==> ((\n. lnorm k (&2) (\x. (u:num->real^N->real^K) n x - v x)) ---> &0)
            sequentially`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LNORM2_SUBSET_CONV THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (v:real^N->real^K)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`]
                  WAN_DIR_LSC_THM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `v:real^N->real^K`; `M:real`;
                 `(:num)`] WAN_MAZUR_WPD) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[num_INFINITE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `NN:num->num` (X_CHOOSE_THEN `lam:num->num->real`
    (X_CHOOSE_THEN `h:num->real^N->real^K` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC WAN_W120_LIMIT THEN
  EXISTS_TAC `\n x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                     (u:num->real^N->real^K) m x)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. wan_w120 s (\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                           (u:num->real^N->real^K) m x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_W120_VSUM_CMUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC WAN_TCOMB_L2_CONV THEN EXISTS_TAC `(:num)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\n. sum(1..dimindex(:N))
          (\i. lnorm s (&2) (\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                     wan_wd s i ((u:num->real^N->real^K) m) x) -
                                (h:num->real^N->real^K) i x) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!i. 1 <= i /\ i <= dimindex(:N)
          ==> wan_wpd s i (\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                     (u:num->real^N->real^K) m x) - v x)
                (\x. vsum(n..NN n) (\m. lam n m % wan_wd s i (u m) x) -
                     (h:num->real^N->real^K) i x)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_WPD_SUB THEN ASM_SIMP_TAC[ETA_AX] THEN
      MATCH_MP_TAC WAN_WPD_VSUM_S THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC WAN_WPD_CMUL THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`;
                   `\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                    (u:num->real^N->real^K) m x) - v x`;
                   `\i x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                    wan_wd s i ((u:num->real^N->real^K) m) x) -
                          (h:num->real^N->real^K) i x`] WAN_DIR_EQ) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
      ASM_MESON_TAC[wan_w120];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\x. vsum(n..NN n) (\m. (lam:num->num->real) n m %
                                 wan_wd s i ((u:num->real^N->real^K) m) x) -
                        (h:num->real^N->real^K) i x`; `s:real^N->bool`]
                  WAN_SOB_LNORM2_SQ) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; ETA_AX] THEN
    MATCH_MP_TAC WAN_VSUM_CMUL_LSPACE THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV)
    [MESON[SUM_0] `&0 = sum(1..dimindex(:N)) (\i:num. &0)`] THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `&0 = &0 pow 2`] THEN
  MATCH_MP_TAC REALLIM_POW THEN ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* RELLICH0.                                                                 *)
(* ------------------------------------------------------------------------- *)

let WAN_LNORM_ZERO_EXT = prove
 (`!(s:real^N->bool) (f:real^N->real^K) p.
     &0 < p
     ==> lnorm (:real^N) p (\x. if x IN s then f x else vec 0) = lnorm s p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnorm] THEN
  SUBGOAL_THEN
   `(\x. lift(norm(if x IN s then (f:real^N->real^K) x else vec 0) rpow p)) =
    (\x. if x IN s then lift(norm(f x) rpow p) else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM];
    REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]]);;

let WAN_RELLICH_BOUND = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) v M.
     open s /\ (!n. wan_w12 s (u n)) /\
     (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M) /\
     v IN lspace s (&2) /\ ((\n. lnorm s (&2) (\x. u n x - v x)) ---> &0) sequentially
     ==> wan_w12 s v /\ lnorm s (&2) v pow 2 + wan_dir s v <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. (u:num->real^N->real^K) n IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. lnorm s (&2) ((u:num->real^N->real^K) n) pow 2) ---> lnorm s (&2) (v:real^N->real^K) pow 2)
    sequentially`
  (LABEL_TAC "LIM") THENL
   [MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC WAN_LNORM2_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> wan_w12 s (v:real^N->real^K) /\
            wan_dir s v <= M - lnorm s (&2) v pow 2 + e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "LIM" (MP_TAC o SPEC `e:real` o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\n. (u:num->real^N->real^K) (n + N)`;
                   `v:real^N->real^K`; `M - lnorm s (&2) (v:real^N->real^K) pow 2 + e`]
                  WAN_DIR_LSC_THM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n + N:num` o check (fun th ->
        can (find_term ((=) `abs:real->real`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o SPEC `n + N:num` o check (fun th ->
        can (find_term ((=) `M:real`)) (concl th) && is_forall(concl th))) THEN
      REWRITE_TAC[ARITH_RULE `N <= n + N:num`] THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LNORM2_SUBSET_CONV THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
      MP_TAC(ISPECL [`\n. lnorm s (&2) (\x. (u:num->real^N->real^K) n x - v x)`; `&0`;
                     `N:num`] REAL_SEQ_OFFSET) THEN
      ASM_REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(lnorm s (&2) (v:real^N->real^K) pow 2 + wan_dir s v - M) / &2`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < (a - b) / &2 <=> b < a`] THEN
  STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let WAN_MOLL_SQ_SMALL = prove
 (`!a t d. &0 <= a /\ &0 < t /\ t * (a + &1) <= d ==> a * t pow 2 <= d pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(t * (a + &1)) pow 2` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= t pow 2 * (a pow 2 + a + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MP_TAC(SPEC `a:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let WAN_RELLICH_MOLL_UNIF = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) M.
     open s /\ (!n. wan_w120 s (u n)) /\ (!n. wan_dir s (u n) <= M)
     ==> !d. &0 < d
             ==> ?e. &0 < e /\ e <= &1 /\
                     !n. lnorm (:real^N) (&2)
                           (\x. wan_moll e (\x. if x IN s then u n x else vec 0) x -
                                (if x IN s then u n x else vec 0)) <= d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC WAN_MOLL_W120_EST THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EST"))) THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_dir s ((u:num->real^N->real^K) 0)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WAN_DIR_POS THEN
    MP_TAC(SPEC `0` (ASSUME `!n. wan_w120 s ((u:num->real^N->real^K) n)`)) THEN
    SIMP_TAC[wan_w120];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C * M + &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d / (C * M + &1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ e <= &1 /\ e * (C * M + &1) <= d` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1) (d / (C * M + &1))` THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
   `(\x. if x IN s then (u:num->real^N->real^K) n x else vec 0) IN lspace (:real^N) (&2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `(u:num->real^N->real^K) n`] WAN_W120_ZERO_EXT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real`; `\x. if x IN s then (u:num->real^N->real^K) n x else vec 0`]
    WAN_LNORM_MOLL_LE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. wan_moll e (\x. if x IN s then (u:num->real^N->real^K) n x else vec 0) x -
         (if x IN s then u n x else vec 0)) IN lspace (:real^N) (&2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &0 <= x /\ abs x <= abs d ==> x <= d`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  MP_TAC(ISPECL
   [`\x. wan_moll e (\x. if x IN s then (u:num->real^N->real^K) n x else vec 0) x -
         (if x IN s then u n x else vec 0)`; `(:real^N)`] WAN_SOB_LNORM2_SQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * e pow 2 * wan_dir s ((u:num->real^N->real^K) n)` THEN CONJ_TAC THENL
   [USE_THEN "EST" (MP_TAC o SPECL [`e:real`; `s:real^N->bool`;
                                     `(u:num->real^N->real^K) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C * e pow 2 * M` THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `C * e pow 2 * M = (C * M) * e pow 2`] THEN
  MATCH_MP_TAC WAN_MOLL_SQ_SMALL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let WAN_RELLICH0_SUPP = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) M S.
       open s /\ bounded S /\ measurable S /\
       (!n x. x IN s /\ ~(x IN S) ==> u n x = vec 0) /\
       (!n. wan_w120 s (u n)) /\
       (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M)
       ==> ?r v. (!m n. m < n ==> r m < r n) /\ wan_w120 s v /\
                 lnorm s (&2) v pow 2 + wan_dir s v <= M /\
                 ((\n. lnorm s (&2) (\x. u (r n) x - v x)) ---> &0) sequentially /\
                 (?S. negligible S /\
                      !x. x IN s DIFF S ==> ((\n. u (r n) x) --> v x) sequentially)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD")))))) THEN
  SUBGOAL_THEN `!n. wan_w12 s ((u:num->real^N->real^K) n)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. wan_w120 s ((u:num->real^N->real^K) n)`)) THEN
    SIMP_TAC[wan_w120];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (u:num->real^N->real^K) n IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= wan_dir s ((u:num->real^N->real^K) n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_DIR_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. wan_dir s ((u:num->real^N->real^K) n) <= M` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN USE_THEN "BD" (MP_TAC o SPEC `n:num`) THEN
    MP_TAC(SPEC `lnorm s (&2) ((u:num->real^N->real^K) n)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. lnorm (:real^N) (&2) (\x. if x IN s then (u:num->real^N->real^K) n x else vec 0)
        <= sqrt M`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN SIMP_TAC[WAN_LNORM_ZERO_EXT; REAL_ARITH `&0 < &2`; ETA_AX] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN USE_THEN "BD" (MP_TAC o SPEC `n:num`) THEN
    MP_TAC(SPEC `n:num` (ASSUME `!n. &0 <= wan_dir s ((u:num->real^N->real^K) n)`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `M:real`]
    WAN_RELLICH_MOLL_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\n x. if x IN s then (u:num->real^N->real^K) n x else vec 0`;
                 `S:real^N->bool`; `sqrt M`] WAN_L2_COMPACT_CRITERION) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(u:num->real^N->real^K) n`] WAN_W120_ZERO_EXT) THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:num->num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CAU"))) THEN
  SUBGOAL_THEN
   `!m n. lnorm (:real^N) (&2)
            (\x. (if x IN s then (u:num->real^N->real^K) m x else vec 0) -
                 (if x IN s then u n x else vec 0)) =
          lnorm s (&2) (\x. u m x - u n x)`
  (LABEL_TAC "EQ") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\x. (u:num->real^N->real^K) m x - u n x`; `&2`]
      WAN_LNORM_ZERO_EXT) THEN
    REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^N` THEN
    COND_CASES_TAC THEN REWRITE_TAC[VECTOR_SUB_REFL];
    ALL_TAC] THEN
  REMOVE_THEN "CAU" MP_TAC THEN USE_THEN "EQ" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\n. (u:num->real^N->real^K) ((r1:num->num) n)`; `&2`; `s:real^N->bool`]
    RIESZ_FISCHER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`; GE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->real^K` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RF"))) THEN
  SUBGOAL_THEN
   `((\n. lnorm s (&2) (\x. (u:num->real^N->real^K) ((r1:num->num) n) x - v x)) ---> &0)
    sequentially`
  (LABEL_TAC "L2R1") THENL
   [REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "RF" (MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[GE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(TAUT `(q ==> r) ==> (p ==> q) ==> (p ==> r)`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x < e ==> abs x < e`) THEN
    MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\n. (u:num->real^N->real^K) ((r1:num->num) n)`;
                 `v:real^N->real^K`] WAN_L2_AE_SUBSEQ) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `S':real^N->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `\n. (r1:num->num) ((q:num->num) n)` THEN
  EXISTS_TAC `v:real^N->real^K` THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MATCH_MP_TAC WAN_W120_WEAK_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`\n. (u:num->real^N->real^K) ((r1:num->num) n)`; `M:real`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:real^N->bool`; `\n. (u:num->real^N->real^K) ((r1:num->num) n)`;
                   `v:real^N->real^K`; `M:real`] WAN_RELLICH_BOUND) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "L2R1" (MP_TAC o SPEC `e:real` o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `q:num->num` MONOTONE_BIGGER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN UNDISCH_TAC `N:num <= n` THEN ARITH_TAC;
    EXISTS_TAC `S':real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let WAN_RELLICH0_THM = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) M.
       open s /\ bounded s /\ (!n. wan_w120 s (u n)) /\
       (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M)
       ==> ?r v. (!m n. m < n ==> r m < r n) /\ wan_w120 s v /\
                 lnorm s (&2) v pow 2 + wan_dir s v <= M /\
                 ((\n. lnorm s (&2) (\x. u (r n) x - v x)) ---> &0) sequentially /\
                 (?S. negligible S /\
                      !x. x IN s DIFF S ==> ((\n. u (r n) x) --> v x) sequentially)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_RELLICH0_SUPP THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[MEASURABLE_OPEN] THEN MESON_TAC[]);;

let WAN_RELLICH0 = prove
 (`!(n:N->bool) (kk:K->bool). WAN_RELLICH0_STATEMENT n kk`,
  REWRITE_TAC[WAN_RELLICH0_STATEMENT; WAN_RELLICH0_THM]);;


(* ------------------------------------------------------------------------- *)
(* Tools for the local Rellich theorem: a.e. invariance of L^p, Cauchy      *)
(* sequences under sub-selection, L^2 norms along a compact exhaustion,     *)
(* lower semicontinuity of the energy under local L^2 convergence.          *)
(* ------------------------------------------------------------------------- *)

let WAN_LSPACE_SPIKE_IMP = prove
 (`!(s:real^N->bool) t (f:real^N->real^K) g p.
     negligible t /\ (!x. x IN s DIFF t ==> f x = g x) /\ f IN lspace s p
     ==> g IN lspace s p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^K`; `g:real^N->real^K`; `t:real^N->bool`;
                   `s:real^N->bool`] MEASURABLE_ON_SPIKE) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`\x. lift(norm((f:real^N->real^K) x) rpow p)`;
                   `\x. lift(norm((g:real^N->real^K) x) rpow p)`;
                   `t:real^N->bool`; `s:real^N->bool`] INTEGRABLE_SPIKE) THEN
    ASM_SIMP_TAC[]]);;

let WAN_LSPACE_LNORM_SPIKE = prove
 (`!(s:real^N->bool) t (f:real^N->real^K) g p.
     negligible t /\ (!x. x IN s DIFF t ==> f x = g x)
     ==> (f IN lspace s p <=> g IN lspace s p) /\ lnorm s p f = lnorm s p g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC WAN_LSPACE_SPIKE_IMP THENL
     [MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `f:real^N->real^K`];
      MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `g:real^N->real^K`]] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[lnorm] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `t:real^N->bool` THEN ASM_SIMP_TAC[]]);;

let WAN_CAUCHY_SUBSEL = prove
 (`!(D:num->num->real) (k1:num->num) k2 N.
     (!d. &0 < d ==> ?M. !m n. M <= m /\ M <= n ==> D (k1 m) (k1 n) < d) /\
     (!j. N <= j ==> ?j'. j <= j' /\ k2 j = k1 j')
     ==> !d. &0 < d ==> ?M. !m n. M <= m /\ M <= n ==> D (k2 m) (k2 n) < d`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEL")) THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "CA")) THEN EXISTS_TAC `MAX M N` THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= c <=> a <= c /\ b <= c`] THEN STRIP_TAC THEN
  USE_THEN "SEL" (MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':num` STRIP_ASSUME_TAC) THEN
  USE_THEN "SEL" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n':num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "CA" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let WAN_LNORM2_EXHAUST = prove
 (`!(s:real^N->bool) (f:num->real^N->bool) (v:real^N->real^K) B.
     (!j. lebesgue_measurable (f j)) /\ (!j. f j SUBSET f (SUC j)) /\
     UNIONS {f j | j IN (:num)} = s /\
     (!j. v IN lspace (f j) (&2) /\ lnorm (f j) (&2) v pow 2 <= B)
     ==> v IN lspace s (&2) /\
         ((\j. lnorm (f j) (&2) v pow 2) ---> lnorm s (&2) v pow 2) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "VB")))) THEN
  SUBGOAL_THEN `!i j. i <= j ==> (f:num->real^N->bool) i SUBSET f j` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN s <=> ?j. x IN (f:num->real^N->bool) j` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS {(f:num->real^N->bool) j | j IN (:num)} = s` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->real^K) measurable_on s` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS {(f:num->real^N->bool) j | j IN (:num)} = s` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEASURABLE_ON_COUNTABLE_UNIONS THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE] THEN X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC WAN_LSPACE_MEASURABLE THEN EXISTS_TAC `&2` THEN
    USE_THEN "VB" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\j x. if x IN (f:num->real^N->bool) j
           then lift(norm((v:real^N->real^K) x) pow 2) else vec 0`;
    `\x. if x IN s then lift(norm((v:real^N->real^K) x) pow 2) else vec 0`;
    `(:real^N)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
      USE_THEN "VB" (fun th -> REWRITE_TAC[th]);
      MAP_EVERY X_GEN_TAC [`j:num`; `x:real^N`] THEN
      REPEAT(COND_CASES_TAC THEN
             REWRITE_TAC[DROP_VEC; LIFT_DROP; REAL_LE_REFL; REAL_LE_POW_2]) THEN
      ASM_MESON_TAC[SUBSET];
      X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THENL
       [SUBGOAL_THEN `?J. x IN (f:num->real^N->bool) J` (X_CHOOSE_TAC `J:num`) THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        EXISTS_TAC `J:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `x IN (f:num->real^N->bool) j` (fun th -> REWRITE_TAC[th]) THEN
        ASM_MESON_TAC[SUBSET];
        SUBGOAL_THEN `!j. ~(x IN (f:num->real^N->bool) j)`
          (fun th -> REWRITE_TAC[th; LIM_CONST]) THEN
        ASM_MESON_TAC[]];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC; IN_UNIV; INTEGRAL_RESTRICT_UNIV] THEN
      EXISTS_TAC `abs B` THEN X_GEN_TAC `j:num` THEN
      USE_THEN "VB" (STRIP_ASSUME_TAC o SPEC `j:num`) THEN
      MP_TAC(ISPECL [`v:real^N->real^K`; `(f:num->real^N->bool) j`] WAN_SOB_LNORM2_SQ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      MP_TAC(SPEC `lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K)`
        REAL_LE_POW_2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; INTEGRAL_RESTRICT_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j. lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K) pow 2 =
        drop(integral (f j) (\x. lift(norm(v x) pow 2)))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN
    USE_THEN "VB" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  ASM_REWRITE_TAC[TENDSTO_REAL; o_DEF; LIFT_DROP; ETA_AX]);;

let WAN_RELLICH_LOC_BOUND = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) v M (f:num->real^N->bool).
     open s /\ (!n. wan_w12 s (u n)) /\
     (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M) /\
     v IN lspace s (&2) /\
     (!k. compact k /\ k SUBSET s
          ==> ((\n. lnorm k (&2) (\x. u n x - v x)) ---> &0) sequentially) /\
     (!j. compact (f j) /\ f j SUBSET s) /\
     ((\j. lnorm (f j) (&2) v pow 2) ---> lnorm s (&2) v pow 2) sequentially
     ==> wan_w12 s v /\ lnorm s (&2) v pow 2 + wan_dir s v <= M`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "BD") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "LOC") (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "EX"))))))) THEN
  SUBGOAL_THEN `!n. (u:num->real^N->real^K) n IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j e. &0 < e
          ==> wan_w12 s (v:real^N->real^K) /\
              wan_dir s v <= M - lnorm ((f:num->real^N->bool) j) (&2) v pow 2 + e`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`j:num`; `e:real`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `compact ((f:num->real^N->bool) j) /\ f j SUBSET s` STRIP_ASSUME_TAC
    THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `lebesgue_measurable ((f:num->real^N->bool) j)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((\n. lnorm ((f:num->real^N->bool) j) (&2) ((u:num->real^N->real^K) n) pow 2) --->
       lnorm (f j) (&2) (v:real^N->real^K) pow 2) sequentially`
    MP_TAC THENL
     [MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC WAN_LNORM2_CONV THEN
      REPEAT CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        USE_THEN "LOC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `\n. (u:num->real^N->real^K) (n + N)`;
                   `v:real^N->real^K`;
                   `M - lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K) pow 2 + e`]
                  WAN_DIR_LSC_THM) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n + N:num`) THEN
      REWRITE_TAC[ARITH_RULE `N <= n + N:num`] THEN
      USE_THEN "BD" (MP_TAC o SPEC `n + N:num`) THEN
      SUBGOAL_THEN
       `lnorm ((f:num->real^N->bool) j) (&2) ((u:num->real^N->real^K) (n + N)) pow 2 <=
        lnorm s (&2) (u (n + N)) pow 2`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUBSET THEN
          EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC WAN_LNORM2_SUBSET_LE THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      USE_THEN "LOC" (MP_TAC o SPEC `k:real^N->bool`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `N:num` o MATCH_MP REAL_SEQ_OFFSET) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K) pow 2 + wan_dir s v <= M`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`j:num`; `(lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K) pow 2 +
                 wan_dir s v - M) / &2`]) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < (a - b) / &2 <=> b < a`] THEN
    STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= M - d ==> a + d <= M`) THEN
  MP_TAC(ISPECL [`sequentially`;
                 `\j. lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K) pow 2`;
                 `lnorm s (&2) (v:real^N->real^K) pow 2`; `M - wan_dir s (v:real^N->real^K)`]
                REALLIM_UBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `j:num` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Cutoffs: psi u extended by zero is in W_0 of the whole space, with       *)
(* energy bounded by a constant (depending on psi) times that of u.         *)
(* ------------------------------------------------------------------------- *)

let WAN_CUTOFF_COMP_BOUND = prove
 (`!(s:real^N->bool) (a:real^N->real) (b:real^N->real) (u:real^N->real^K) g A.
     open s /\ (\x. lift(a x)) continuous_on (:real^N) /\
     (\x. lift(b x)) continuous_on (:real^N) /\
     (!x. abs(a x) <= A) /\ (!x. abs(b x) <= &1) /\
     u IN lspace s (&2) /\ g IN lspace s (&2)
     ==> (\x. a x % u x + b x % g x) IN lspace s (&2) /\
         lnorm s (&2) (\x. a x % u x + b x % g x) pow 2 <=
         &2 * A pow 2 * lnorm s (&2) u pow 2 + &2 * lnorm s (&2) g pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lebesgue_measurable (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((a:real^N->real) (vec 0))` THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (a:real^N->real) x % (u:real^N->real^K) x) IN lspace s (&2) /\
    (\x. (b:real^N->real) x % (g:real^N->real^K) x) IN lspace s (&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THENL
     [EXISTS_TAC `A:real`; EXISTS_TAC `&1`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC LSPACE_ADD THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm s (&2) (\x. (a:real^N->real) x % (u:real^N->real^K) x) <= A * lnorm s (&2) u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm s (&2) (\x. A % (u:real^N->real^K) x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^N->bool` THEN
      ASM_SIMP_TAC[LSPACE_CMUL; REAL_POS; NEGLIGIBLE_EMPTY; NORM_MUL; DIFF_EMPTY] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        can (find_term ((=) `A:real`)) (concl th) && is_forall(concl th))) THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[LNORM_MUL; REAL_ARITH `~(&2 = &0)`] THEN
      ASM_REWRITE_TAC[real_abs; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm s (&2) (\x. (b:real^N->real) x % (g:real^N->real^K) x) <= lnorm s (&2) g`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^N->bool` THEN
    ASM_SIMP_TAC[REAL_POS; NEGLIGIBLE_EMPTY; NORM_MUL; DIFF_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(A * lnorm s (&2) (u:real^N->real^K) + lnorm s (&2) (g:real^N->real^K)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_ADD THEN
      ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm s (&2) (\x. (a:real^N->real) x % (u:real^N->real^K) x) +
                lnorm s (&2) (\x. (b:real^N->real) x % (g:real^N->real^K) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_TRIANGLE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `A * lnorm s (&2) (u:real^N->real^K) - lnorm s (&2) (g:real^N->real^K)`
      REAL_LE_POW_2) THEN
    REAL_ARITH_TAC]);;

let WAN_CUTOFF_W120_BOUND = prove
 (`!(s:real^N->bool) psi.
     open s /\ wan_test s psi /\ (!x. &0 <= psi x /\ psi x <= &1)
     ==> ?C c. &0 <= C /\ compact c /\ c SUBSET s /\
               !u:real^N->real^K.
                 wan_w12 s u
                 ==> wan_w120 (:real^N) (\x. if x IN s then psi x % u x else vec 0) /\
                     (!x. ~(x IN c) ==> (if x IN s then psi x % u x else vec 0) = vec 0) /\
                     lnorm (:real^N) (&2) (\x. if x IN s then psi x % u x else vec 0) pow 2 +
                     wan_dir (:real^N) (\x. if x IN s then psi x % u x else vec 0)
                     <= C * (lnorm s (&2) u pow 2 + wan_dir s u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test] o
    check (fun th -> concl th = `wan_test (s:real^N->bool) psi`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!i. ?B. !x. abs(wan_dpart i (psi:real^N->real) x) <= B` MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real`; `i:num`] WAN_TEST_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `BB:num->real` (LABEL_TAC "BB"))] THEN
  SUBGOAL_THEN `!x. abs((psi:real^N->real) x) <= &1` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `&1`)) (concl th) && is_forall(concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(1..dimindex(:N)) (\i. (BB:num->real) i pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  EXISTS_TAC `&2 + &2 * sum(1..dimindex(:N)) (\i. (BB:num->real) i pow 2)` THEN
  EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `u:real^N->real^K` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `\i. wan_wd s i (u:real^N->real^K)`;
                 `psi:real^N->real`] WAN_CUTOFF_EXTENSION) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_WD_WORKS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kp:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DER")))))) THEN
  SUBGOAL_THEN
   `wan_w12 (:real^N)
      (\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x else vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[wan_w12] THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    EXISTS_TAC `\x. if x IN s then wan_dpart i (psi:real^N->real) x % (u:real^N->real^K) x +
                                   psi x % wan_wd s i u x else vec 0` THEN
    USE_THEN "DER" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC WAN_W12_COMPACT_SUPPORT_W120 THEN EXISTS_TAC `kp:real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; IN_UNIV];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; COND_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir (:real^N)
      (\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x else vec 0) =
    sum(1..dimindex(:N))
     (\i. lnorm s (&2) (\x. wan_dpart i psi x % u x + psi x % wan_wd s i u x) pow 2)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`;
                   `\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x
                        else vec 0`;
                   `\i x. if x IN s then wan_dpart i (psi:real^N->real) x %
                                         (u:real^N->real^K) x + psi x % wan_wd s i u x
                          else vec 0`] WAN_DIR_EQ) THEN
    REWRITE_TAC[OPEN_UNIV] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "DER" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "DER" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`\x. if x IN s then wan_dpart i (psi:real^N->real) x %
                                       (u:real^N->real^K) x + psi x % wan_wd s i u x
                        else vec 0`; `(:real^N)`] WAN_SOB_LNORM2_SQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC WAN_LNORM_ZERO_EXT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> lnorm s (&2) (\x. wan_dpart i (psi:real^N->real) x % (u:real^N->real^K) x +
                              psi x % wan_wd s i u x) pow 2 <=
            &2 * (BB:num->real) i pow 2 * lnorm s (&2) u pow 2 +
            &2 * lnorm s (&2) (wan_wd s i u) pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `wan_dpart i (psi:real^N->real)`; `psi:real^N->real`;
                   `u:real^N->real^K`; `wan_wd s i (u:real^N->real^K)`; `(BB:num->real) i`]
                  WAN_CUTOFF_COMP_BOUND) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[WAN_WD_WORKS] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real`; `i:num`] WAN_TEST_CONTINUOUS) THEN
      ASM_SIMP_TAC[ETA_AX];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir s (u:real^N->real^K) =
    sum(1..dimindex(:N)) (\i. lnorm s (&2) (wan_wd s i u) pow 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[wan_dir] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN ASM_SIMP_TAC[WAN_WD_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lnorm (:real^N) (&2)
      (\x. if x IN s then (psi:real^N->real) x % (u:real^N->real^K) x else vec 0) pow 2
    <= lnorm s (&2) u pow 2`
  ASSUME_TAC THENL
   [SIMP_TAC[WAN_LNORM_ZERO_EXT; REAL_ARITH `&0 < &2`] THEN
    SUBGOAL_THEN `(\x. (psi:real^N->real) x % (u:real^N->real^K) x) IN lspace s (&2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN EXISTS_TAC `&1` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `psi:real^N->real`; `1`] WAN_TEST_CONTINUOUS) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^N->bool` THEN
    ASM_SIMP_TAC[REAL_POS; NEGLIGIBLE_EMPTY; NORM_MUL; DIFF_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `lnorm s (&2) (u:real^N->real^K) pow 2 +
    sum(1..dimindex(:N)) (\i. &2 * (BB:num->real) i pow 2 * lnorm s (&2) u pow 2 +
                              &2 * lnorm s (&2) (wan_wd s i u) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_RMUL] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..dimindex(:N)) (\i. lnorm s (&2) (wan_wd s i (u:real^N->real^K)) pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MP_TAC(SPEC `lnorm s (&2) (u:real^N->real^K)` REAL_LE_POW_2) THEN
  MP_TAC(ISPECL [`sum(1..dimindex(:N)) (\i. (BB:num->real) i pow 2)`;
                 `sum(1..dimindex(:N)) (\i. lnorm s (&2) (wan_wd s i (u:real^N->real^K)) pow 2)`]
                REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Cauchy and limit helpers, then the diagonal subsequence for the local    *)
(* Rellich theorem (cutoffs on an exhaustion, RELLICH0_SUPP in R^N).        *)
(* ------------------------------------------------------------------------- *)

let WAN_L2_CONV_CAUCHY = prove
 (`!(s:real^N->bool) (f:num->real^N->real^K) g.
     (!n. f n IN lspace s (&2)) /\ g IN lspace s (&2) /\
     ((\n. lnorm s (&2) (\x. f n x - g x)) ---> &0) sequentially
     ==> !d. &0 < d ==> ?N. !m n. N <= m /\ N <= n
                                ==> lnorm s (&2) (\x. f m x - f n x) < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d / &2` o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_RZERO] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `lnorm s (&2) (\x. (g:real^N->real^K) x - f (n:num) x) =
    lnorm s (&2) (\x. (f:num->real^N->real^K) n x - g x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `\x. (f:num->real^N->real^K) n x - g x`]
      LNORM_NEG) THEN
    REWRITE_TAC[VECTOR_NEG_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `lnorm s (&2) (\x. (f:num->real^N->real^K) m x - g x) +
              lnorm s (&2) (\x. (g:real^N->real^K) x - f (n:num) x)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `\x. (f:num->real^N->real^K) m x - g x`;
                   `\x. (g:real^N->real^K) x - f (n:num) x`] LNORM_TRIANGLE) THEN
    REWRITE_TAC[VECTOR_ARITH `(a - b) + (b - c):real^N = a - c`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LSPACE_SUB) THEN
    ASM_REWRITE_TAC[REAL_POS; ETA_AX] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `m:num` th) THEN MP_TAC(SPEC `n:num` th)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= lnorm s (&2) (\x. (f:num->real^N->real^K) m x - g x) /\
                  &0 <= lnorm s (&2) (\x. (f:num->real^N->real^K) n x - g x)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_REWRITE_TAC[REAL_POS; ETA_AX];
      REAL_ARITH_TAC]]);;

let WAN_PT_CONV_CAUCHY = prove
 (`!(a:num->real^K) l.
     (a --> l) sequentially
     ==> !d. &0 < d ==> ?N. !m n. N <= m /\ N <= n ==> norm(a m - a n) < d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `m:num` th) THEN MP_TAC(SPEC `n:num` th)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH);;

let WAN_PT_CAUCHY_LIM = prove
 (`!(a:num->real^K).
     (!d. &0 < d ==> ?N. !m n. N <= m /\ N <= n ==> norm(a m - a n) < d)
     ==> (a --> lim sequentially a) sequentially`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?l. ((a:num->real^K) --> l) sequentially` MP_TAC THENL
   [REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy; GE; dist] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[lim]]);;

let WAN_L2_CAUCHY_AE_LIMIT = prove
 (`!(s:real^N->bool) (w:num->real^N->real^K) v S.
     (!n. w n IN lspace s (&2)) /\
     (!d. &0 < d ==> ?N. !m n. N <= m /\ N <= n ==> lnorm s (&2) (\x. w m x - w n x) < d) /\
     negligible S /\ (!x. x IN s DIFF S ==> ((\n. w n x) --> v x) sequentially)
     ==> v IN lspace s (&2) /\ ((\n. lnorm s (&2) (\x. w n x - v x)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AE")))) THEN
  MP_TAC(ISPECL [`w:num->real^N->real^K`; `&2`; `s:real^N->bool`] RIESZ_FISCHER) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`; GE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^K` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "RF"))) THEN
  SUBGOAL_THEN
   `((\n. lnorm s (&2) (\x. (w:num->real^N->real^K) n x - g x)) ---> &0) sequentially`
  (LABEL_TAC "L2") THENL
   [REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "RF" (MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[GE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(TAUT `(q ==> r) ==> (p ==> q) ==> (p ==> r)`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x < e ==> abs x < e`) THEN
    MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_REWRITE_TAC[REAL_POS; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `w:num->real^N->real^K`; `g:real^N->real^K`]
    WAN_L2_AE_SUBSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->num` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `S':real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!x. x IN s DIFF (S UNION S') ==> (g:real^N->real^K) x = v x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\n. (w:num->real^N->real^K) ((q:num->num) n) x` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF];
      MP_TAC(ISPECL [`\n. (w:num->real^N->real^K) n x`; `q:num->num`;
                     `(v:real^N->real^K) x`] LIM_SUBSEQUENCE) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "AE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `negligible (S UNION S':real^N->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `S UNION S':real^N->bool`; `g:real^N->real^K`;
                   `v:real^N->real^K`; `&2`] WAN_LSPACE_LNORM_SPIKE) THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `!n. lnorm s (&2) (\x. (w:num->real^N->real^K) n x - v x) =
          lnorm s (&2) (\x. w n x - g x)`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `S UNION S':real^N->bool`;
                   `\x. (w:num->real^N->real^K) n x - v x`;
                   `\x. (w:num->real^N->real^K) n x - g x`; `&2`]
      WAN_LSPACE_LNORM_SPIKE) THEN
    ASM_SIMP_TAC[]]);;

let WAN_RELLICH_LOC_DIAG = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) M (f:num->real^N->bool).
     open s /\ (!n. wan_w12 s (u n)) /\
     (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M) /\
     (!j. compact (f j) /\ f j SUBSET s)
     ==> ?k:num->num. (!m n. m < n ==> k m < k n) /\
             !j. (!d. &0 < d
                      ==> ?N. !m n. N <= m /\ N <= n
                              ==> lnorm (f j) (&2) (\x. u (k m) x - u (k n) x) < d) /\
                 (?S. negligible S /\
                      !x. x IN f j DIFF S
                          ==> !d. &0 < d
                                  ==> ?N. !m n. N <= m /\ N <= n
                                          ==> norm(u (k m) x - u (k n) x) < d)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "BD") (LABEL_TAC "FJ")))) THEN
  SUBGOAL_THEN
   `?psi. !j. wan_test s (psi j) /\ (!x. &0 <= psi j x /\ psi j x <= &1) /\
              (!x. x IN (f:num->real^N->bool) j ==> psi j x = &1)`
  (X_CHOOSE_THEN `psi:num->real^N->real` (LABEL_TAC "PSI")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC WAN_SMOOTH_URYSOHN THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "FJ" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?C c. !j. &0 <= C j /\ compact (c j) /\ c j SUBSET s /\
              !w:real^N->real^K.
                wan_w12 s w
                ==> wan_w120 (:real^N)
                      (\x. if x IN s then (psi:num->real^N->real) j x % w x else vec 0) /\
                    (!x. ~(x IN c j) ==> (if x IN s then psi j x % w x else vec 0) = vec 0) /\
                    lnorm (:real^N) (&2) (\x. if x IN s then psi j x % w x else vec 0) pow 2 +
                    wan_dir (:real^N) (\x. if x IN s then psi j x % w x else vec 0)
                    <= C j * (lnorm s (&2) w pow 2 + wan_dir s w)`
  (X_CHOOSE_THEN `C:num->real` (X_CHOOSE_THEN `c:num->real^N->bool` (LABEL_TAC "CUT")))
  THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC WAN_CUTOFF_W120_BOUND THEN ASM_REWRITE_TAC[ETA_AX] THEN
    USE_THEN "PSI" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `\j (q:num->num).
      (!d. &0 < d
           ==> ?N. !m n. N <= m /\ N <= n
                   ==> lnorm ((f:num->real^N->bool) j) (&2)
                         (\x. (u:num->real^N->real^K) (q m) x - u (q n) x) < d) /\
      (?S. negligible S /\
           !x. x IN f j DIFF S
               ==> !d. &0 < d ==> ?N. !m n. N <= m /\ N <= n
                                      ==> norm(u (q m) x - u (q n) x) < d)`
   SUBSEQUENCE_DIAGONALIZATION_LEMMA) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`j:num`; `r:num->num`] THEN
      USE_THEN "CUT" (MP_TAC o SPEC `j:num`) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CJ")))) THEN
      SUBGOAL_THEN
       `!n. wan_w120 (:real^N)
              (\x. if x IN s then (psi:num->real^N->real) j x %
                                  (u:num->real^N->real^K) ((r:num->num) n) x else vec 0) /\
            (!x. ~(x IN (c:num->real^N->bool) j)
                 ==> (if x IN s then psi j x % u (r n) x else vec 0) = vec 0) /\
            lnorm (:real^N) (&2) (\x. if x IN s then psi j x % u (r n) x else vec 0) pow 2 +
            wan_dir (:real^N) (\x. if x IN s then psi j x % u (r n) x else vec 0)
            <= (C:num->real) j * M`
      (LABEL_TAC "TRI") THENL
       [X_GEN_TAC `n:num` THEN
        USE_THEN "CJ" (MP_TAC o SPEC `(u:num->real^N->real^K) ((r:num->num) n)`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(C:num->real) j * (lnorm s (&2) ((u:num->real^N->real^K) ((r:num->num) n))
                      pow 2 + wan_dir s (u (r n)))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "BD" (fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!n. (\x. if x IN s then (psi:num->real^N->real) j x %
                                (u:num->real^N->real^K) ((r:num->num) n) x else vec 0)
            IN lspace (:real^N) (&2)`
      ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC WAN_W12_IMP_LSPACE THEN
        USE_THEN "TRI" (MP_TAC o CONJUNCT1 o SPEC `n:num`) THEN SIMP_TAC[wan_w120];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`(:real^N)`;
                     `\n x. if x IN s then (psi:num->real^N->real) j x %
                                (u:num->real^N->real^K) ((r:num->num) n) x else vec 0`;
                     `(C:num->real) j * M`; `(c:num->real^N->bool) j`]
                    WAN_RELLICH0_SUPP) THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; MEASURABLE_COMPACT] THEN
        USE_THEN "TRI" (fun th -> SIMP_TAC[th]);
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num->num` (X_CHOOSE_THEN `G:real^N->real^K`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `k:num->num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`(:real^N)`;
                       `\n x. if x IN s then (psi:num->real^N->real) j x %
                                  (u:num->real^N->real^K) ((r:num->num) ((k:num->num) n)) x
                              else vec 0`;
                       `G:real^N->real^K`] WAN_L2_CONV_CAUCHY) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_W12_IMP_LSPACE THEN
          UNDISCH_TAC `wan_w120 (:real^N) (G:real^N->real^K)` THEN SIMP_TAC[wan_w120];
          ALL_TAC] THEN
        DISCH_THEN(LABEL_TAC "FC") THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
        REMOVE_THEN "FC" (MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
        MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < d ==> x < d`) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC
         `lnorm ((f:num->real^N->bool) j) (&2)
            (\x. (if x IN s then (psi:num->real^N->real) j x %
                      (u:num->real^N->real^K) ((r:num->num) ((k:num->num) m)) x else vec 0) -
                 (if x IN s then psi j x % u (r (k n)) x else vec 0))` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          MP_TAC(ISPECL
           [`(f:num->real^N->bool) j`; `{}:real^N->bool`;
            `\x. (u:num->real^N->real^K) ((r:num->num) ((k:num->num) m)) x - u (r (k n)) x`;
            `\x. (if x IN s then (psi:num->real^N->real) j x %
                      (u:num->real^N->real^K) ((r:num->num) ((k:num->num) m)) x else vec 0) -
                 (if x IN s then psi j x % u (r (k n)) x else vec 0)`; `&2`]
           WAN_LSPACE_LNORM_SPIKE) THEN
          REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN ANTS_TAC THENL
           [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
            SUBGOAL_THEN `(x:real^N) IN s /\ (psi:num->real^N->real) j x = &1`
              (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
            CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
            SIMP_TAC[]];
          MATCH_MP_TAC WAN_LNORM2_SUBSET_LE THEN REWRITE_TAC[SUBSET_UNIV] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX];
            MATCH_MP_TAC LEBESGUE_MEASURABLE_COMPACT THEN ASM_MESON_TAC[]]];
        EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        MATCH_MP_TAC WAN_PT_CONV_CAUCHY THEN EXISTS_TAC `(G:real^N->real^K) x` THEN
        SUBGOAL_THEN
         `(\n. (u:num->real^N->real^K) ((r:num->num) ((k:num->num) n)) x) =
          (\n. if x IN s then (psi:num->real^N->real) j x % u (r (k n)) x else vec 0)`
        SUBST1_TAC THENL
         [SUBGOAL_THEN `(x:real^N) IN s /\ (psi:num->real^N->real) j x = &1`
            (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
          CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]]];
      MAP_EVERY X_GEN_TAC [`j:num`; `r:num->num`; `k1:num->num`; `k2:num->num`; `N:num`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `S:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "AEC"))))
        ASSUME_TAC) THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL
         [`\m n. lnorm ((f:num->real^N->bool) j) (&2)
                   (\x. (u:num->real^N->real^K) ((r:num->num) m) x - u (r n) x)`;
          `k1:num->num`; `k2:num->num`; `N:num`] WAN_CAUCHY_SUBSEL) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        REMOVE_THEN "AEC" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN
        MP_TAC(ISPECL
         [`\m n. norm((u:num->real^N->real^K) ((r:num->num) m) x - u (r n) x)`;
          `k1:num->num`; `k2:num->num`; `N:num`] WAN_CAUCHY_SUBSEL) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(MP_TAC o SPEC `\n:num. n`) THEN REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The local Rellich theorem WAN_RELLICH_LOC.                                *)
(* ------------------------------------------------------------------------- *)

let WAN_RELLICH_LOC_THM = prove
 (`!(s:real^N->bool) (u:num->real^N->real^K) M.
       open s /\ (!n. wan_w12 s (u n)) /\
       (!n. lnorm s (&2) (u n) pow 2 + wan_dir s (u n) <= M)
       ==> ?r v. (!m n. m < n ==> r m < r n) /\ wan_w12 s v /\
                 lnorm s (&2) v pow 2 + wan_dir s v <= M /\
                 (!k. compact k /\ k SUBSET s
                      ==> ((\n. lnorm k (&2) (\x. u (r n) x - v x)) ---> &0)
                          sequentially) /\
                 (?S. negligible S /\
                      !x. x IN s DIFF S ==> ((\n. u (r n) x) --> v x) sequentially)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BD"))) THEN
  SUBGOAL_THEN `!n. (u:num->real^N->real^K) n IN lspace s (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` OPEN_UNION_COMPACT_SUBSETS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "UN") (LABEL_TAC "COV")))))) THEN
  SUBGOAL_THEN `!n j. (u:num->real^N->real^K) n IN lspace ((f:num->real^N->bool) j) (&2)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:num->real^N->real^K`; `M:real`;
                 `f:num->real^N->bool`] WAN_RELLICH_LOC_DIAG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CAU") MP_TAC) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `SS:num->real^N->bool` (LABEL_TAC "SS")) THEN
  SUBGOAL_THEN `!x:real^N. x IN s <=> ?j. x IN (f:num->real^N->bool) j` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN USE_THEN "UN" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = UNIONS {(SS:num->real^N->bool) j | j IN (:num)}` THEN
  SUBGOAL_THEN `negligible (S:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
    USE_THEN "SS" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?v:real^N->real^K. !x. v x = lim sequentially (\n. (u:num->real^N->real^K) ((r:num->num) n) x)`
  (X_CHOOSE_THEN `v:real^N->real^K` (LABEL_TAC "V")) THENL
   [EXISTS_TAC `\x. lim sequentially (\n. (u:num->real^N->real^K) ((r:num->num) n) x)` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s DIFF S
        ==> ((\n. (u:num->real^N->real^K) ((r:num->num) n) x) --> v x) sequentially`
  (LABEL_TAC "AE") THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?j. x IN (f:num->real^N->bool) j` (X_CHOOSE_TAC `j:num`) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "V" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC WAN_PT_CAUCHY_LIM THEN REWRITE_TAC[] THEN
    USE_THEN "SS" (MP_TAC o CONJUNCT2 o SPEC `j:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    UNDISCH_TAC `~((x:real^N) IN S)` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "V" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!j. (v:real^N->real^K) IN lspace ((f:num->real^N->bool) j) (&2) /\
        ((\n. lnorm (f j) (&2) (\x. (u:num->real^N->real^K) ((r:num->num) n) x - v x)) --->
         &0) sequentially`
  (LABEL_TAC "LJ") THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`(f:num->real^N->bool) j`; `\n. (u:num->real^N->real^K) ((r:num->num) n)`;
                   `v:real^N->real^K`; `S:real^N->bool`] WAN_L2_CAUCHY_AE_LIMIT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      USE_THEN "CAU" (fun th -> REWRITE_TAC[th]);
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      USE_THEN "AE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K) pow 2 <= M`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`sequentially`;
                   `\n. lnorm ((f:num->real^N->bool) j) (&2)
                          ((u:num->real^N->real^K) ((r:num->num) n)) pow 2`;
                   `lnorm ((f:num->real^N->bool) j) (&2) (v:real^N->real^K) pow 2`; `M:real`]
                  REALLIM_UBOUND) THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_POW THEN
      MP_TAC(ISPECL [`(f:num->real^N->bool) j`; `\n. (u:num->real^N->real^K) ((r:num->num) n)`;
                     `v:real^N->real^K`] WAN_LNORM2_CONV) THEN
      REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "LJ" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `lnorm s (&2) ((u:num->real^N->real^K) ((r:num->num) n)) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC WAN_LNORM2_SUBSET_LE THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT]];
        MP_TAC(ISPECL [`s:real^N->bool`; `(u:num->real^N->real^K) ((r:num->num) n)`]
          WAN_DIR_POS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "BD" (MP_TAC o SPEC `(r:num->num) n`) THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:num->real^N->bool`; `v:real^N->real^K`; `M:real`]
    WAN_LNORM2_EXHAUST) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
      X_GEN_TAC `j:num` THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interior((f:num->real^N->bool) (j + 1))` THEN
      ASM_REWRITE_TAC[ADD1; INTERIOR_SUBSET];
      USE_THEN "UN" (fun th -> REWRITE_TAC[th]);
      ASM_REWRITE_TAC[] THEN USE_THEN "LJ" (fun th -> REWRITE_TAC[th])];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!k. compact k /\ k SUBSET s
        ==> ((\n. lnorm k (&2) (\x. (u:num->real^N->real^K) ((r:num->num) n) x - v x)) --->
             &0) sequentially`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "COV" (MP_TAC o SPEC `k:real^N->bool`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[GE; LE_REFL] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(f:num->real^N->bool) N`; `k:real^N->bool`;
                   `\n. (u:num->real^N->real^K) ((r:num->num) n)`; `v:real^N->real^K`]
                  WAN_LNORM2_SUBSET_CONV) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT] THEN
    USE_THEN "LJ" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\n. (u:num->real^N->real^K) ((r:num->num) n)`;
                 `v:real^N->real^K`; `M:real`; `f:num->real^N->bool`]
                WAN_RELLICH_LOC_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "BD" (fun th -> REWRITE_TAC[th]);
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:num->num`; `v:real^N->real^K`] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let WAN_RELLICH_LOC = prove
 (`!(n:N->bool) (kk:K->bool). WAN_RELLICH_LOC_STATEMENT n kk`,
  REWRITE_TAC[WAN_RELLICH_LOC_STATEMENT; WAN_RELLICH_LOC_THM]);;

