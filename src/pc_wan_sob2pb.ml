(* ========================================================================= *)
(* Unit pc_wan_sob2pb: the Poincare inequality with mean value on balls     *)
(* (WAN_POINCARE_BALL_STATEMENT of pc_wan_defs), generic dimension.         *)
(* Two-point argument: |w(x) - w(y)|^2 is bounded through the midpoint by   *)
(* segment integrals of the squared gradient over t in [1/2,1]; Fubini on   *)
(* cball x cball and on cball x [1/2,1] and the affine change of variables  *)
(* y -> (1 - t) x + t y give the smooth inequality on closed balls; local   *)
(* smooth approximation and a radius limit give W^(1,2) of the open ball.   *)
(* ========================================================================= *)

needs "src/pc_wan_sob2p.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Pointwise tools: |f v|^2 <= |v|^2 sum_i |f e_i|^2 for linear f, the     *)
(* Cauchy-Schwarz bound for integrals, and the half-segment estimate for    *)
(* smooth maps.                                                              *)
(* ------------------------------------------------------------------------- *)

let WAN_LINEAR_SQ_BOUND = prove
 (`!(f:real^N->real^K) v.
     linear f
     ==> norm(f v) pow 2 <=
         norm v pow 2 * sum(1..dimindex(:N)) (\i. norm(f(basis i)) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A:real^N = lambda i. abs((v:real^N)$i)` THEN
  ABBREV_TAC `B:real^N = lambda i. norm((f:real^N->real^K)(basis i))` THEN
  SUBGOAL_THEN `norm((f:real^N->real^K) v) <= (A:real^N) dot B` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [MATCH_MP WAN_LINEAR_BASIS_EXPAND th]) THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[dot] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    SIMP_TAC[LAMBDA_BETA; NORM_MUL; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(A:real^N) pow 2 = norm(v:real^N) pow 2 /\
                norm(B:real^N) pow 2 =
                sum(1..dimindex(:N)) (\i. norm((f:real^N->real^K)(basis i)) pow 2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_POW_2; dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      SIMP_TAC[LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_POW_2; REAL_POW2_ABS];
      GEN_REWRITE_TAC LAND_CONV [NORM_POW_2] THEN REWRITE_TAC[dot] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA; REAL_POW_2]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(norm(A:real^N) * norm(B:real^N)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(A:real^N) dot B` THEN
    ASM_REWRITE_TAC[NORM_CAUCHY_SCHWARZ];
    ASM_REWRITE_TAC[REAL_POW_MUL; REAL_LE_REFL]]);;

let WAN_VARIANCE_IDENTITY = prove
 (`!(S:real^N->bool) (g:real^N->real^K) c.
     measurable S /\ &0 < measure S /\ g IN lspace S (&2)
     ==> drop(integral S (\x. lift(norm(g x - c) pow 2))) =
         drop(integral S (\x. lift(norm(g x - inv(measure S) % integral S g) pow 2))) +
         measure S * norm(inv(measure S) % integral S g - c) pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^N->real^K) integrable_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`g:real^N->real^K`; `S:real^N->bool`; `&2`] HOELDER_BOUND) THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= &2`];
    ALL_TAC] THEN
  ABBREV_TAC `m:real^K = inv(measure(S:real^N->bool)) % integral S g` THEN
  SUBGOAL_THEN `integral S (g:real^N->real^K) = measure S % m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (g:real^N->real^K) x - m) IN lspace S (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (g:real^N->real^K) x - m) integrable_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[INTEGRABLE_ON_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((g:real^N->real^K) x - c) pow 2)) =
    (\x. (lift(norm(g x - m) pow 2) + &2 % lift((m - c) dot (g x - m))) +
         lift(norm(m - c) pow 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD; LIFT_EQ; NORM_POW_2] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((g:real^N->real^K) x - m) pow 2)) integrable_on S /\
    (\x. lift((m - c) dot ((g:real^N->real^K) x - m))) integrable_on S /\
    integral S (\x. lift((m - c) dot ((g:real^N->real^K) x - m))) = vec 0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`\x. (g:real^N->real^K) x - m`; `\v:real^K. lift((m - c) dot v)`;
                     `S:real^N->bool`] INTEGRABLE_LINEAR) THEN
      ASM_REWRITE_TAC[LINEAR_LIFT_DOT; o_DEF];
      MP_TAC(ISPECL [`\x. (g:real^N->real^K) x - m`; `S:real^N->bool`;
                     `\v:real^K. lift((m - c) dot v)`] INTEGRAL_LINEAR) THEN
      ASM_REWRITE_TAC[LINEAR_LIFT_DOT; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRAL_CONST_GEN; INTEGRABLE_ON_CONST] THEN
      REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO; LIFT_NUM]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL;
               INTEGRAL_CONST_GEN; INTEGRABLE_ON_CONST] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC);;

let WAN_CS_REAL_LEMMA = prove
 (`!m v n. &0 < m /\ &0 <= v ==> n <= m * (v + m * (inv m pow 2 * n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m * (v + m * (inv m pow 2 * n)) = m * v + n` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> n <= a + n`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let WAN_INTEGRAL_SQ_CS = prove
 (`!(S:real^N->bool) (g:real^N->real^K).
     measurable S /\ g IN lspace S (&2)
     ==> norm(integral S g) pow 2 <=
         measure S * drop(integral S (\x. lift(norm(g x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `measure(S:real^N->bool) = &0` THENL
   [SUBGOAL_THEN `negligible(S:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_MEASURE_EQ_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_ON_NEGLIGIBLE; NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < measure(S:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURE_POS_LE; REAL_LT_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `g:real^N->real^K`; `vec 0:real^K`]
                WAN_VARIANCE_IDENTITY) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`] THEN
  MATCH_MP_TAC WAN_CS_REAL_LEMMA THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN MATCH_MP_TAC LSPACE_SUB THEN
  ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX]);;

let WAN_SEGMENT_VDERIV = prove
 (`!(w:real^N->real^K) x y t.
     smooth_map_on (:real^N) w
     ==> ((\t. w((&1 - drop t) % x + drop t % y)) has_vector_derivative
          frechet_derivative w (at ((&1 - drop t) % x + drop t % y)) (y - x)) (at t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`] WAN_C1_OPEN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; smooth_map_on]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^1. (&1 - drop t) % (x:real^N) + drop t % y = x + drop t % (y - x)`
  (fun th -> REWRITE_TAC[th]) THENL [GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative] THEN
  MP_TAC(ISPECL [`\t:real^1. (x:real^N) + drop t % (y - x)`; `w:real^N->real^K`;
                 `\h:real^1. drop h % ((y:real^N) - x)`;
                 `frechet_derivative (w:real^N->real^K) (at (x + drop t % (y - x)))`;
                 `t:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`\t:real^1. (x:real^N)`; `\h:real^1. vec 0:real^N`;
                   `\t:real^1. drop t % ((y:real^N) - x)`; `\h:real^1. drop h % ((y:real^N) - x)`;
                   `at (t:real^1)`] HAS_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(INST [`at (t:real^1)`,`net:(real^1)net`]
            (ISPECL [`\t:real^1. t`; `\h:real^1. h`; `(y:real^N) - x`]
                    HAS_DERIVATIVE_VMUL_DROP)) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^1` THEN
  MATCH_MP_TAC LINEAR_CMUL THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  ASM_MESON_TAC[differentiable]);;

let WAN_SQGRAD_CONT = prove
 (`!(w:real^N->real^K).
     smooth_map_on (:real^N) w
     ==> (\z. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i w z) pow 2)))
         continuous_on (:real^N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`] WAN_C1_OPEN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; smooth_map_on]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
  ASM_REWRITE_TAC[partial_derivative]);;

let WAN_HALF_SEGMENT = prove
 (`!(w:real^N->real^K) x y.
     smooth_map_on (:real^N) w
     ==> norm(w y - w(inv(&2) % (x + y))) pow 2 <=
         inv(&2) * norm(y - x) pow 2 *
         drop(integral (interval[lift(inv(&2)),lift(&1)])
                (\t. lift(sum(1..dimindex(:N))
                       (\i. norm(partial_derivative i w
                               ((&1 - drop t) % x + drop t % y)) pow 2))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`] WAN_C1_OPEN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; smooth_map_on]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. (&1 - drop t) % (x:real^N) + drop t % y) continuous_on
    interval[lift(inv(&2)),lift(&1)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
    REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (w:real^N->real^K)((&1 - drop t) % x + drop t % y)`;
                 `\t. frechet_derivative (w:real^N->real^K)
                        (at ((&1 - drop t) % x + drop t % y)) (y - x)`;
                 `lift(inv(&2))`; `lift(&1)`] FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    ASM_SIMP_TAC[WAN_SEGMENT_VDERIV];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `(&1 - inv(&2)) % (x:real^N) + inv(&2) % y = inv(&2) % (x + y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE) THEN
  SUBGOAL_THEN
   `(\t. frechet_derivative (w:real^N->real^K)
           (at ((&1 - drop t) % x + drop t % y)) (y - x))
    continuous_on interval[lift(inv(&2)),lift(&1)]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. (&1 - drop t) % (x:real^N) + drop t % y`;
                   `\z. frechet_derivative (w:real^N->real^K) (at z) (y - x)`;
                   `interval[lift(inv(&2)),lift(&1)]`] CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `measure(interval[lift(inv(&2)),lift(&1)]) *
    drop(integral (interval[lift(inv(&2)),lift(&1)])
          (\t. lift(norm(frechet_derivative (w:real^N->real^K)
                    (at ((&1 - drop t) % x + drop t % y)) (y - x)) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WAN_INTEGRAL_SQ_CS THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(interval[lift(inv(&2)),lift(&1)]) = inv(&2)` SUBST1_TAC THENL
   [REWRITE_TAC[MEASURE_INTERVAL_1; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`interval[lift(inv(&2)),lift(&1)]`;
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
                   `interval[lift(inv(&2)),lift(&1)]`] CONTINUOUS_ON_COMPOSE) THEN
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

(* ------------------------------------------------------------------------- *)
(* Fubini for continuous functions on a product of compact sets.             *)
(* ------------------------------------------------------------------------- *)

let WAN_FUBINI_PCROSS = prove
 (`!(f:real^(M,N)finite_sum->real^K) s t.
     compact s /\ compact t /\ f continuous_on (s PCROSS t)
     ==> (\x. integral t (\y. f(pastecart x y))) integrable_on s /\
         (\y. integral s (\x. f(pastecart x y))) integrable_on t /\
         integral (s PCROSS t) f = integral s (\x. integral t (\y. f(pastecart x y))) /\
         integral (s PCROSS t) f = integral t (\y. integral s (\x. f(pastecart x y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. if z IN s PCROSS t then (f:real^(M,N)finite_sum->real^K) z else vec 0)
      absolutely_integrable_on (:real^(M,N)finite_sum)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_SIMP_TAC[COMPACT_PCROSS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. integral (:real^N)
          (\y. if pastecart x y IN s PCROSS t
               then (f:real^(M,N)finite_sum->real^K)(pastecart x y) else vec 0) =
         if x IN s then integral t (\y. f(pastecart x y)) else vec 0) /\
    (!y. integral (:real^M)
          (\x. if pastecart x y IN s PCROSS t
               then (f:real^(M,N)finite_sum->real^K)(pastecart x y) else vec 0) =
         if y IN t then integral s (\x. f(pastecart x y)) else vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; INTEGRAL_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE_ALT) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[INTEGRAL_RESTRICT_UNIV; HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[integrable_on];
    ASM_MESON_TAC[integrable_on];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]]);;

let WAN_AFFINE_IMAGE_UNIV = prove
 (`!m (c:real^N). ~(m = &0) ==> IMAGE (\x. inv m % x + --(inv m % c)) (:real^N) = (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `z:real^N` THEN EXISTS_TAC `m % (z:real^N) + c` THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

let WAN_AFFINE_INTEGRAL_BOUND = prove
 (`!(g:real^N->real) S (x:real^N) t.
     compact S /\ convex S /\ (\z. lift(g z)) continuous_on S /\
     (!z. z IN S ==> &0 <= g z) /\ x IN S /\ inv(&2) <= t /\ t <= &1
     ==> (\y. lift(g((&1 - t) % x + t % y))) integrable_on S /\
         drop(integral S (\y. lift(g((&1 - t) % x + t % y)))) <=
         &2 pow dimindex(:N) * drop(integral S (\z. lift(g z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [UNDISCH_TAC `inv(&2) <= t` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN S ==> (&1 - t) % x + t % y IN S` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CONVEX_ALT]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift((g:real^N->real)((&1 - t) % x + t % y))) integrable_on S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\y:real^N. (&1 - t) % (x:real^N) + t % y`; `\z. lift((g:real^N->real) z)`;
                   `S:real^N->bool`] CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\z. lift((g:real^N->real) z)) integrable_on S` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. if z IN S then lift((g:real^N->real) z) else vec 0`;
                 `integral S (\z. lift((g:real^N->real) z))`; `(:real^N)`; `t:real`;
                 `(&1 - t) % (x:real^N)`] HAS_INTEGRAL_AFFINITY) THEN
  ASM_SIMP_TAC[WAN_AFFINE_IMAGE_UNIV; REAL_LT_IMP_NZ; HAS_INTEGRAL_RESTRICT_UNIV;
               INTEGRABLE_INTEGRAL] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (:real^N)
                (\y. if t % y + (&1 - t) % x IN S
                     then lift((g:real^N->real)(t % y + (&1 - t) % x)) else vec 0))` THEN
  CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `drop(integral S
            (\y. if t % y + (&1 - t) % x IN S
                 then lift((g:real^N->real)(t % y + (&1 - t) % x)) else vec 0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `t % y + (&1 - t) % x = (&1 - t) % x + t % (y:real^N)` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN REWRITE_TAC[SUBSET_UNIV] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC `\y. lift((g:real^N->real)((&1 - t) % x + t % y))` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `t % y + (&1 - t) % x = (&1 - t) % x + t % (y:real^N)` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ASM_SIMP_TAC[]];
      ASM_MESON_TAC[integrable_on];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[DROP_VEC; LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[DROP_CMUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    SUBGOAL_THEN `&2 pow dimindex(:N) = inv(inv(&2) pow dimindex(:N))` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_INV; REAL_INV_INV]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[LIFT_DROP]]);;

let WAN_SEGMENT_FUBINI_BOUND = prove
 (`!(g:real^N->real) S (x:real^N).
     compact S /\ convex S /\ (\z. lift(g z)) continuous_on (:real^N) /\
     (!z. z IN S ==> &0 <= g z) /\ x IN S
     ==> (\y. integral (interval[lift(inv(&2)),lift(&1)])
                (\t. lift(g((&1 - drop t) % x + drop t % y)))) integrable_on S /\
         drop(integral S (\y. integral (interval[lift(inv(&2)),lift(&1)])
                (\t. lift(g((&1 - drop t) % x + drop t % y))))) <=
         inv(&2) * &2 pow dimindex(:N) * drop(integral S (\z. lift(g z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(N,1)finite_sum.
                    lift((g:real^N->real)((&1 - drop(sndcart z)) % x +
                                          drop(sndcart z) % fstcart z))`;
                 `S:real^N->bool`; `interval[lift(inv(&2)),lift(&1)]`] WAN_FUBINI_PCROSS) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; COMPACT_INTERVAL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\z:real^(N,1)finite_sum.
                      (&1 - drop(sndcart z)) % (x:real^N) + drop(sndcart z) % fstcart z`;
                   `\z. lift((g:real^N->real) z)`; `(S:real^N->bool) PCROSS
                     interval[lift(inv(&2)),lift(&1)]`] CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART; ETA_AX];
        MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
        CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        REWRITE_TAC[LINEAR_SNDCART; LINEAR_FSTCART; ETA_AX]];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) SUBST1_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (interval[lift(inv(&2)),lift(&1)])
                 (\t:real^1. lift(&2 pow dimindex(:N) *
                                  drop(integral S (\z. lift((g:real^N->real) z))))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[INTEGRABLE_CONST; LIFT_DROP] THEN
    X_GEN_TAC `t:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^N->real`; `S:real^N->bool`; `x:real^N`; `drop t`]
                  WAN_AFFINE_INTEGRAL_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; SIMP_TAC[]];
    REWRITE_TAC[INTEGRAL_CONST; DROP_CMUL; LIFT_DROP] THEN
    SIMP_TAC[CONTENT_1; LIFT_DROP; REAL_ARITH `inv(&2) <= &1`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The smooth Poincare inequality with mean value on closed balls.           *)
(* ------------------------------------------------------------------------- *)

let WAN_PCROSS_SWAP = prove
 (`!(f:real^(N,N)finite_sum->real^K) S.
     compact S /\ f continuous_on (S PCROSS S)
     ==> integral (S PCROSS S) (\z. f(pastecart (sndcart z) (fstcart z))) =
         integral (S PCROSS S) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^(N,N)finite_sum->real^K`; `S:real^N->bool`; `S:real^N->bool`]
                WAN_FUBINI_PCROSS) THEN
  MP_TAC(ISPECL [`\z. (f:real^(N,N)finite_sum->real^K)(pastecart (sndcart z) (fstcart z))`;
                 `S:real^N->bool`; `S:real^N->bool`] WAN_FUBINI_PCROSS) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`\z:real^(N,N)finite_sum. pastecart (sndcart z) (fstcart z)`;
                   `f:real^(N,N)finite_sum->real^K`; `(S:real^N->bool) PCROSS S`]
                  CONTINUOUS_ON_COMPOSE) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                  PASTECART_ADD; PASTECART_CMUL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(S:real^N->bool) PCROSS S` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 th1));
                CONJUNCT2(CONJUNCT2(CONJUNCT2 th2))])));;

let WAN_INNER_BOUND = prove
 (`!(w:real^N->real^K) a rho x.
     smooth_map_on (:real^N) w /\ &0 < rho /\ x IN cball(a,rho)
     ==> drop(integral (cball(a,rho)) (\y. lift(norm(w y - w(inv(&2) % (x + y))) pow 2)))
         <= &2 pow dimindex(:N) * rho pow 2 *
            drop(integral (cball(a,rho))
                   (\z. lift(sum(1..dimindex(:N))
                               (\i. norm(partial_derivative i w z) pow 2))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. sum(1..dimindex(:N))
                        (\i. norm(partial_derivative i (w:real^N->real^K) z) pow 2)`;
                 `cball(a:real^N,rho)`; `x:real^N`] WAN_SEGMENT_FUBINI_BOUND) THEN
  ASM_SIMP_TAC[COMPACT_CBALL; CONVEX_CBALL; WAN_SQGRAD_CONT; SUM_POS_LE_NUMSEG;
               REAL_LE_POW_2] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (cball(a:real^N,rho))
          (\y. (&2 * rho pow 2) %
               integral (interval[lift(inv(&2)),lift(&1)])
                 (\t. lift(sum(1..dimindex(:N))
                       (\i. norm(partial_derivative i (w:real^N->real^K)
                               ((&1 - drop t) % x + drop t % y)) pow 2)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_CMUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN REWRITE_TAC[COMPACT_CBALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      SUBGOAL_THEN `(w:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV; ETA_AX];
        MP_TAC(ISPECL [`\y:real^N. inv(&2) % ((x:real^N) + y)`; `w:real^N->real^K`;
                       `cball(a:real^N,rho)`] CONTINUOUS_ON_COMPOSE) THEN
        REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
          SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
          ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]]];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_CMUL] THEN
    MP_TAC(ISPECL [`w:real^N->real^K`; `x:real^N`; `y:real^N`] WAN_HALF_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `norm(y - x:real^N) <= &2 * rho` MP_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN cball(a,rho)` THEN
        UNDISCH_TAC `(y:real^N) IN cball(a,rho)` THEN
        REWRITE_TAC[IN_CBALL; dist] THEN NORM_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `n <= &2 * r ==> &0 <= n ==> n <= &2 * r`)) THEN
      REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `n2 <= (&2 * r) pow 2 ==> inv(&2) * n2 <= &2 * r pow 2`) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP] THEN
      SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_LE_POW_2] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MP_TAC(ISPECL [`\t. (&1 - drop t) % (x:real^N) + drop t % y`;
                     `\z. lift(sum(1..dimindex(:N))
                            (\i. norm(partial_derivative i (w:real^N->real^K) z) pow 2))`;
                     `interval[lift(inv(&2)),lift(&1)]`] CONTINUOUS_ON_COMPOSE) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
        REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
        SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        ASM_MESON_TAC[WAN_SQGRAD_CONT; CONTINUOUS_ON_SUBSET; SUBSET_UNIV]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_binary "real_le" o concl)) THEN
  SUBGOAL_THEN `&0 <= rho pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 pow dimindex(:N)` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`&2 pow dimindex(:N)`,`p:real`) THEN SPEC_TAC(`rho pow 2`,`q:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * q) * (inv(&2) * p * drop(integral (cball(a:real^N,rho))
                (\z. lift(sum(1..dimindex(:N))
                       (\i. norm(partial_derivative i (w:real^N->real^K) z) pow 2)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let WAN_COMPOSE_LINEAR_CONT = prove
 (`!(w:real^N->real^K) (L:real^M->real^N).
     w continuous_on (:real^N) /\ linear L ==> (\z. w(L z)) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:real^M->real^N`; `w:real^N->real^K`; `(:real^M)`]
                CONTINUOUS_ON_COMPOSE) THEN
  ASM_SIMP_TAC[o_DEF; LINEAR_CONTINUOUS_ON] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let WAN_SQNORM_DIFF_CONT = prove
 (`!(w:real^N->real^K) (L1:real^M->real^N) L2.
     w continuous_on (:real^N) /\ linear L1 /\ linear L2
     ==> (\z. lift(norm(w(L1 z) - w(L2 z)) pow 2)) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  ASM_SIMP_TAC[WAN_COMPOSE_LINEAR_CONT]);;

let WAN_NORM_SQ_TRIANGLE2 = prove
 (`!a b c:real^K. norm(a - b) pow 2 <= &2 * norm(a - c) pow 2 + &2 * norm(b - c) pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(NORM_ARITH `norm(a - b:real^K) <= norm(a - c) + norm(b - c)`) THEN
  MP_TAC(SPEC `norm(a - c:real^K) - norm(b - c:real^K)` REAL_LE_POW_2) THEN
  MP_TAC(ISPEC `a - b:real^K` NORM_POS_LE) THEN
  SPEC_TAC(`norm(a - b:real^K)`,`p:real`) THEN SPEC_TAC(`norm(a - c:real^K)`,`q:real`) THEN
  SPEC_TAC(`norm(b - c:real^K)`,`s:real`) THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(q + s) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `&0 <= (q - s) pow 2` THEN REAL_ARITH_TAC]);;

let WAN_POINCARE_SMOOTH_CBALL = prove
 (`!(w:real^N->real^K) a rho.
     smooth_map_on (:real^N) w /\ &0 < rho
     ==> drop(integral (cball(a,rho))
                (\x. lift(norm(w x - inv(measure(cball(a,rho))) %
                                     integral (cball(a,rho)) w) pow 2)))
         <= &2 pow (dimindex(:N) + 2) * rho pow 2 *
            drop(integral (cball(a,rho))
                   (\z. lift(sum(1..dimindex(:N))
                               (\i. norm(partial_derivative i w z) pow 2))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N->real^K) continuous_on (:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < measure(cball(a:real^N,rho))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MEASURE_CBALL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(cball(a:real^N,rho)) /\ compact((cball(a:real^N,rho)) PCROSS (cball(a:real^N,rho))) /\ measurable(cball(a:real^N,rho))`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[COMPACT_CBALL; COMPACT_PCROSS; MEASURABLE_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(fstcart z) - w(sndcart z)) pow 2)) continuous_on (:real^(N,N)finite_sum) /\
    (\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(sndcart z) - w(inv(&2) % (fstcart z + sndcart z))) pow 2)) continuous_on (:real^(N,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC WAN_SQNORM_DIFF_CONT THEN ASM_REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
      MP_TAC(ISPECL [`w:real^N->real^K`; `sndcart:real^(N,N)finite_sum->real^N`;
                     `\z:real^(N,N)finite_sum. inv(&2) % (fstcart z + sndcart z)`]
                    WAN_SQNORM_DIFF_CONT) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[LINEAR_SNDCART] THEN
      MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
      REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(fstcart z) - w(sndcart z)) pow 2))`; `cball(a:real^N,rho)`; `cball(a:real^N,rho)`] WAN_FUBINI_PCROSS) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(sndcart z) - w(inv(&2) % (fstcart z + sndcart z))) pow 2))`; `cball(a:real^N,rho)`; `cball(a:real^N,rho)`] WAN_FUBINI_PCROSS) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N->real^K) IN lspace (cball(a:real^N,rho)) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(cball(a:real^N,rho)) * drop(integral (cball(a:real^N,rho)) (\x. lift(norm((w:real^N->real^K) x - (inv(measure(cball(a:real^N,rho))) % integral (cball(a,rho)) (w:real^N->real^K))) pow 2))) <= drop(integral (cball(a:real^N,rho) PCROSS cball(a,rho)) (\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(fstcart z) - w(sndcart z)) pow 2)))` (LABEL_TAC "s1") THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cball(a:real^N,rho)`; `\x. norm((w:real^N->real^K) x - (inv(measure(cball(a:real^N,rho))) % integral (cball(a,rho)) (w:real^N->real^K))) pow 2`;
                   `measure(cball(a:real^N,rho))`] WAN_INTEGRAL_LIN1) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MP_TAC(ISPECL [`cball(a:real^N,rho)`; `w:real^N->real^K`; `(w:real^N->real^K) x`]
                  WAN_VARIANCE_IDENTITY) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `integral (cball(a:real^N,rho)) (\y. lift(norm((w:real^N->real^K) x - w y) pow 2)) =
      integral (cball(a:real^N,rho)) (\y. lift(norm(w y - w x) pow 2))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN REWRITE_TAC[] THEN MESON_TAC[NORM_SUB]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ b = c ==> b <= a + c`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX];
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MESON_TAC[NORM_SUB]];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (cball(a:real^N,rho) PCROSS cball(a,rho)) (\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(fstcart z) - w(sndcart z)) pow 2))) <= &4 * drop(integral (cball(a:real^N,rho) PCROSS cball(a,rho)) (\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(sndcart z) - w(inv(&2) % (fstcart z + sndcart z))) pow 2)))` (LABEL_TAC "s2") THENL
   [MP_TAC(ISPECL [`\z:real^(N,N)finite_sum.
                      lift(norm((w:real^N->real^K)(sndcart z) -
                                w(inv(&2) % (fstcart z + sndcart z))) pow 2)`;
                   `cball(a:real^N,rho)`] WAN_PCROSS_SWAP) THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "swap") THEN
    SUBGOAL_THEN
     `(\z:real^(N,N)finite_sum.
         lift(norm((w:real^N->real^K)(fstcart z) -
                   w(inv(&2) % (sndcart z + fstcart z))) pow 2))
      integrable_on (cball(a:real^N,rho)) PCROSS (cball(a:real^N,rho)) /\
      (\z:real^(N,N)finite_sum.
         lift(norm((w:real^N->real^K)(sndcart z) -
                   w(inv(&2) % (fstcart z + sndcart z))) pow 2))
      integrable_on (cball(a:real^N,rho)) PCROSS (cball(a:real^N,rho)) /\
      (\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(fstcart z) - w(sndcart z)) pow 2))
      integrable_on (cball(a:real^N,rho)) PCROSS (cball(a:real^N,rho))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC WAN_CONT_COMPACT_ABS_INT THEN ASM_REWRITE_TAC[] THEN
      TRY(ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]) THEN
      MP_TAC(ISPECL [`w:real^N->real^K`; `fstcart:real^(N,N)finite_sum->real^N`;
                     `\z:real^(N,N)finite_sum. inv(&2) % (sndcart z + fstcart z)`]
                    WAN_SQNORM_DIFF_CONT) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[LINEAR_FSTCART] THEN
        MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
        REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX];
        MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(cball(a:real^N,rho)) PCROSS (cball(a:real^N,rho))`;
                   `\z:real^(N,N)finite_sum. norm((w:real^N->real^K)(fstcart z) -
                         w(inv(&2) % (sndcart z + fstcart z))) pow 2`;
                   `\z:real^(N,N)finite_sum. norm((w:real^N->real^K)(sndcart z) -
                         w(inv(&2) % (fstcart z + sndcart z))) pow 2`;
                   `&2`; `&2`] WAN_INTEGRAL_LIN2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lin2")) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral ((cball(a:real^N,rho)) PCROSS (cball(a:real^N,rho)))
        (\z:real^(N,N)finite_sum.
           lift(&2 * norm((w:real^N->real^K)(fstcart z) -
                         w(inv(&2) % (sndcart z + fstcart z))) pow 2 +
                &2 * norm(w(sndcart z) - w(inv(&2) % (fstcart z + sndcart z))) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `y1:real^N`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `inv(&2) % (y1 + x1) = inv(&2) % (x1 + y1:real^N)` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_ADD_SYM]; REWRITE_TAC[WAN_NORM_SQ_TRIANGLE2]];
      REMOVE_THEN "lin2" SUBST1_TAC THEN REMOVE_THEN "swap" SUBST1_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a = c /\ b = c ==> &2 * a + &2 * b <= &4 * c`) THEN
      CONJ_TAC THEN REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (cball(a:real^N,rho) PCROSS cball(a,rho)) (\z:real^(N,N)finite_sum. lift(norm((w:real^N->real^K)(sndcart z) - w(inv(&2) % (fstcart z + sndcart z))) pow 2))) <= measure(cball(a:real^N,rho)) * (&2 pow dimindex(:N) * rho pow 2 * drop(integral (cball(a:real^N,rho)) (\z. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i (w:real^N->real^K) z) pow 2)))))`
  (LABEL_TAC "s3") THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (cball(a:real^N,rho))
                  (\x:real^N. lift(&2 pow dimindex(:N) * rho pow 2 * drop(integral (cball(a:real^N,rho)) (\z. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i (w:real^N->real^K) z) pow 2)))))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_ON_CONST; LIFT_DROP] THEN
      X_GEN_TAC `x0:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC WAN_INNER_BOUND THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[INTEGRAL_CONST_GEN; DROP_CMUL; LIFT_DROP; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `measure(cball(a:real^N,rho)) * drop(integral (cball(a:real^N,rho)) (\x. lift(norm((w:real^N->real^K) x - (inv(measure(cball(a:real^N,rho))) % integral (cball(a,rho)) (w:real^N->real^K))) pow 2))) <= measure(cball(a:real^N,rho)) * (&2 pow (dimindex(:N) + 2) * rho pow 2 * drop(integral (cball(a:real^N,rho)) (\z. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i (w:real^N->real^K) z) pow 2)))))`
  MP_TAC THENL
   [REMOVE_THEN "s1" MP_TAC THEN REMOVE_THEN "s2" MP_TAC THEN REMOVE_THEN "s3" MP_TAC THEN
    REWRITE_TAC[REAL_POW_ADD] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* From smooth maps to W^(1,2): the inequality on closed balls inside s.    *)
(* ------------------------------------------------------------------------- *)

let WAN_LSPACE2_INTEGRABLE_MEAS = prove
 (`!(S:real^N->bool) (f:real^N->real^K).
     measurable S /\ f IN lspace S (&2) ==> f integrable_on S`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MP_TAC(ISPECL [`f:real^N->real^K`; `S:real^N->bool`; `&2`] HOELDER_BOUND) THEN
  ASM_SIMP_TAC[REAL_ARITH `&1 <= &2`]);;

let WAN_MEAN_DIFF_BOUND = prove
 (`!(S:real^N->bool) (f:real^N->real^K) g.
     measurable S /\ &0 < measure S /\ f IN lspace S (&2) /\ g IN lspace S (&2)
     ==> drop(integral S (\x. lift(norm((f x - inv(measure S) % integral S f) -
                                        (g x - inv(measure S) % integral S g)) pow 2)))
         <= drop(integral S (\x. lift(norm(f x - g x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (f:real^N->real^K) x - g x) IN lspace S (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^K) integrable_on S /\ (g:real^N->real^K) integrable_on S`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_LSPACE2_INTEGRABLE_MEAS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (f x - inv(measure S) % integral S (f:real^N->real^K)) -
        (g x - inv(measure S) % integral S g) =
        (f x - g x) - inv(measure S) % integral S (\x. f x - g x)`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[INTEGRAL_SUB] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `\x. (f:real^N->real^K) x - g x`; `vec 0:real^K`]
                WAN_VARIANCE_IDENTITY) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2]);;

let WAN_L2_CONV_SQ = prove
 (`!(S:real^N->bool) (f:num->real^N->real^K) g.
     (!n. f n IN lspace S (&2)) /\ g IN lspace S (&2) /\
     ((\n. drop(integral S (\x. lift(norm(f n x - g x) pow 2)))) ---> &0) sequentially
     ==> ((\n. drop(integral S (\x. lift(norm(f n x) pow 2)))) --->
          drop(integral S (\x. lift(norm(g x) pow 2)))) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!n. drop(integral S (\x. lift(norm((f:num->real^N->real^K) n x) pow 2))) =
         lnorm S (&2) (f n) pow 2) /\
    drop(integral S (\x. lift(norm((g:real^N->real^K) x) pow 2))) = lnorm S (&2) g pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL [GEN_TAC; ALL_TAC] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC WAN_LNORM2_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC WAN_LNORM2_NULL THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]);;

let WAN_POINCARE_W12_CBALL = prove
 (`!(s:real^N->bool) (u:real^N->real^K) a rho.
     open s /\ wan_w12 s u /\ &0 < rho /\ cball(a,rho) SUBSET s
     ==> drop(integral (cball(a,rho))
                (\x. lift(norm(u x - inv(measure(cball(a,rho))) %
                                     integral (cball(a,rho)) u) pow 2)))
         <= &2 pow (dimindex(:N) + 2) * rho pow 2 *
            sum(1..dimindex(:N))
              (\i. drop(integral (cball(a,rho)) (\x. lift(norm(wan_wd s i u x) pow 2))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real^K`; `\i. wan_wd s i (u:real^N->real^K)`;
                 `cball(a:real^N,rho)`] WAN_W12_LOCAL_APPROX) THEN
  REWRITE_TAC[COMPACT_CBALL] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_LSPACE2_IMP_L2LOC; WAN_W12_IMP_LSPACE; WAN_WD_WORKS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->real^N->real^K` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < measure(cball(a:real^N,rho)) /\ measurable(cball(a:real^N,rho)) /\ compact(cball(a:real^N,rho))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURE_CBALL_POS; MEASURABLE_CBALL; COMPACT_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. smooth_map_on (:real^N) ((w:num->real^N->real^K) n) /\
        w n IN lspace (cball(a:real^N,rho)) (&2) /\
        (!i. partial_derivative i (w n) IN lspace (cball(a:real^N,rho)) (&2))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest] o SPEC `n:num`) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kn:real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      X_GEN_TAC `i:num` THEN MATCH_MP_TAC WAN_CONT_COMPACT_LSPACE2 THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `(w:num->real^N->real^K) n`; `kn:real^N->bool`;
                     `i:num`] WAN_VTEST_PARTIAL) THEN
      ASM_SIMP_TAC[ETA_AX] THEN MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace (cball(a:real^N,rho)) (&2) /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> wan_wd s i u IN lspace (cball(a:real^N,rho)) (&2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; REPEAT STRIP_TAC] THEN
    MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_W12_IMP_LSPACE; WAN_WD_WORKS];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\n. drop(integral (cball(a:real^N,rho)) (\x. lift(norm((w:num->real^N->real^K) n x - (inv(measure(cball(a:real^N,rho))) % integral (cball(a,rho)) ((w:num->real^N->real^K) n))) pow 2)))`;
    `\n. &2 pow (dimindex(:N) + 2) * rho pow 2 *
         sum(1..dimindex(:N))
           (\i. drop(integral (cball(a:real^N,rho))
                  (\x. lift(norm(partial_derivative i ((w:num->real^N->real^K) n) x) pow 2))))`] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`cball(a:real^N,rho)`; `\n x. (w:num->real^N->real^K) n x - (inv(measure(cball(a:real^N,rho))) % integral (cball(a,rho)) ((w:num->real^N->real^K) n))`;
                   `\x. (u:real^N->real^K) x - (inv(measure(cball(a:real^N,rho))) % integral (cball(a,rho)) (u:real^N->real^K))`] WAN_L2_CONV_SQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX];
      MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX];
      MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
      EXISTS_TAC `\n. drop(integral (cball(a:real^N,rho)) (\x. lift(norm((w:num->real^N->real^K) n x - u x) pow 2)))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
        MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
        MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THEN
        MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX];
        MATCH_MP_TAC WAN_MEAN_DIFF_BOUND THEN ASM_SIMP_TAC[]]];
    MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_LMUL THEN
    MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cball(a:real^N,rho)`; `\n. partial_derivative i ((w:num->real^N->real^K) n)`;
                   `wan_wd s i (u:real^N->real^K)`] WAN_L2_CONV_SQ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(w:num->real^N->real^K) n`; `a:real^N`; `rho:real`]
                  WAN_POINCARE_SMOOTH_CBALL) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cball(a:real^N,rho)`;
                   `\i x. norm(partial_derivative i ((w:num->real^N->real^K) n) x) pow 2`;
                   `dimindex(:N)`] WAN_SUM_DROP_INTEGRAL) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
      ASM_REWRITE_TAC[ETA_AX];
      REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Radius limit and WAN_POINCARE_BALL.                                       *)
(* ------------------------------------------------------------------------- *)

let WAN_RADII_FACTS = prove
 (`!r. &0 < r
       ==> (!n. inv(&2) * r <= (&1 - inv(&n + &2)) * r /\ (&1 - inv(&n + &2)) * r < r) /\
           (!t. t < r ==> ?N. !n. N <= n ==> t <= (&1 - inv(&n + &2)) * r)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= inv(&2) ==> inv(&2) <= &1 - x`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 < x * r ==> (&1 - x) * r < r`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ASM_CASES_TAC `t <= &0` THENL
     [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &0 <= &1 - x`) THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `(r - t) / r` REAL_ARCH_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv(&n + &2) <= inv(&N)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      UNDISCH_TAC `(N:num) <= n` THEN UNDISCH_TAC `~((N:num) = 0)` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_EQ] THEN
      MP_TAC(SPEC `N:num` REAL_POS) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&N) * r < r - t` MP_TAC THENL
     [UNDISCH_TAC `inv(&N) < (r - t) / r` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&n + &2) * r <= inv(&N) * r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let WAN_ANNULUS_NULL = prove
 (`!(h:real^N->real^1) a r.
     &0 < r /\ h absolutely_integrable_on ball(a,r)
     ==> ((\n. integral (ball(a,r) DIFF cball(a,(&1 - inv(&n + &2)) * r)) h) --> vec 0)
         sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_RADII_FACTS) THEN
  SUBGOAL_THEN
   `!n. integral (ball(a,r) DIFF cball(a:real^N,(&1 - inv(&n + &2)) * r)) h =
        integral (ball(a,r))
          (\x. if x IN (:real^N) DIFF cball(a,(&1 - inv(&n + &2)) * r)
               then (h:real^N->real^1) x else vec 0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; IN_DIFF; IN_UNIV] THEN GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`(x:real^N) IN ball(a,r)`;
                             `(x:real^N) IN cball(a,(&1 - inv(&n + &2)) * r)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. if x IN (:real^N) DIFF cball(a,(&1 - inv(&n + &2)) * r)
          then (h:real^N->real^1) x else vec 0`;
    `\x:real^N. vec 0:real^1`;
    `\x. lift(norm((h:real^N->real^1) x))`;
    `ball(a:real^N,r)`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[INTEGRAL_0] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_INTER] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(a:real^N,r)` THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN
    REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL; LEBESGUE_MEASURABLE_CBALL;
                LEBESGUE_MEASURABLE_BALL];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; NORM_0; NORM_POS_LE];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `dist(a:real^N,x)`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN cball(a,(&1 - inv(&n + &2)) * r)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_CBALL] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]]);;

let WAN_MEAN_SQ_BOUND = prove
 (`!(S:real^N->bool) (g:real^N->real^K).
     measurable S /\ &0 < measure S /\ g IN lspace S (&2)
     ==> norm(inv(measure S) % integral S g) pow 2 <=
         inv(measure S) * drop(integral S (\x. lift(norm(g x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `g:real^N->real^K`] WAN_INTEGRAL_SQ_CS) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_POW_MUL; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(measure(S:real^N->bool)) pow 2 *
              (measure S * drop(integral S (\x. lift(norm((g:real^N->real^K) x) pow 2))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> inv m pow 2 * (m * i) = inv m * i`; REAL_LE_REFL]]);;

let WAN_POINCARE_BALL_STEP = prove
 (`!(a:real^N) r rho (u:real^N->real^K).
     &0 < r /\ inv(&2) * r <= rho /\ rho < r /\ wan_w12 (ball(a,r)) u
     ==> drop(integral (ball(a,r))
                (\x. lift(norm(u x - inv(measure(ball(a,r))) % integral (ball(a,r)) u) pow 2)))
         <= &2 pow (dimindex(:N) + 2) * r pow 2 * wan_dir (ball(a,r)) u +
            drop(integral (ball(a,r) DIFF cball(a,rho))
                   (\x. lift(&2 * norm(u x) pow 2 +
                             &2 * (inv(measure(cball(a,inv(&2) * r))) *
                                   drop(integral (ball(a,r)) (\x. lift(norm(u x) pow 2)))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&2) * r` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(a:real^N,rho) SUBSET ball(a,r)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `measurable(ball(a:real^N,r)) /\ &0 < measure(ball(a:real^N,r)) /\
    measurable(cball(a:real^N,rho)) /\ &0 < measure(cball(a:real^N,rho)) /\
    measurable(ball(a:real^N,r) DIFF cball(a,rho)) /\
    lebesgue_measurable(cball(a:real^N,rho)) /\
    lebesgue_measurable(ball(a:real^N,r) DIFF cball(a,rho)) /\
    &0 < measure(cball(a:real^N,inv(&2) * r)) /\
    measure(cball(a:real^N,inv(&2) * r)) <= measure(cball(a:real^N,rho))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_BALL; MEASURE_BALL_POS; MEASURABLE_CBALL; MEASURE_CBALL_POS;
                 MEASURABLE_DIFF; LEBESGUE_MEASURABLE_CBALL; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_BALL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_CBALL; SUBSET_CBALL]];
    ALL_TAC] THEN
  ABBREV_TAC `m = inv(measure(cball(a:real^N,rho))) % integral (cball(a,rho)) (u:real^N->real^K)` THEN
  SUBGOAL_THEN
   `(u:real^N->real^K) IN lspace (ball(a,r)) (&2) /\
    u IN lspace (cball(a,rho)) (&2) /\
    (\x. u x - m) IN lspace (ball(a,r)) (&2) /\
    (\x. u x - m) IN lspace (cball(a,rho)) (&2) /\
    (\x. u x - m) IN lspace (ball(a,r) DIFF cball(a,rho)) (&2) /\
    u IN lspace (ball(a,r) DIFF cball(a,rho)) (&2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(u:real^N->real^K) IN lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. (u:real^N->real^K) x - m) IN lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; LSPACE_CONST; ETA_AX]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC LSPACE_SUBSET THEN
    EXISTS_TAC `ball(a:real^N,r)` THEN ASM_REWRITE_TAC[SUBSET_DIFF];
    ALL_TAC] THEN
  (* the variance step *)
  SUBGOAL_THEN
   `drop(integral (ball(a,r))
           (\x. lift(norm((u:real^N->real^K) x - inv(measure(ball(a,r))) %
                                integral (ball(a,r)) u) pow 2)))
    <= drop(integral (ball(a:real^N,r)) (\x. lift(norm(u x - m) pow 2)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^N,r)`; `u:real^N->real^K`; `m:real^K`]
                  WAN_VARIANCE_IDENTITY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a <= a + b`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  (* the splitting step *)
  SUBGOAL_THEN
   `drop(integral (ball(a:real^N,r)) (\x. lift(norm((u:real^N->real^K) x - m) pow 2))) =
    drop(integral (cball(a,rho)) (\x. lift(norm(u x - m) pow 2))) +
    drop(integral (ball(a,r) DIFF cball(a,rho)) (\x. lift(norm(u x - m) pow 2)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. lift(norm((u:real^N->real^K) x - m) pow 2)`;
                   `cball(a:real^N,rho)`; `ball(a:real^N,r) DIFF cball(a,rho)`]
                  INTEGRAL_UNION) THEN
    SUBGOAL_THEN `cball(a:real^N,rho) UNION (ball(a,r) DIFF cball(a,rho)) = ball(a,r) /\
                  cball(a:real^N,rho) INTER (ball(a,r) DIFF cball(a,rho)) = {}`
    (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_ADD]];
    ALL_TAC] THEN
  (* the Poincare inequality on the closed ball *)
  SUBGOAL_THEN
   `drop(integral (cball(a,rho)) (\x. lift(norm((u:real^N->real^K) x - m) pow 2)))
    <= &2 pow (dimindex(:N) + 2) * r pow 2 * wan_dir (ball(a:real^N,r)) u`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(a:real^N,r)`; `u:real^N->real^K`; `a:real^N`; `rho:real`]
                  WAN_POINCARE_W12_CBALL) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_POW_2; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN MATCH_MP_TAC LSPACE_SUBSET THEN
      EXISTS_TAC `ball(a:real^N,r)` THEN ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
      REWRITE_TAC[wan_dir] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN CONJ_TAC THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THENL
       [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `ball(a:real^N,r)` THEN
        ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
        ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX]]];
    ALL_TAC] THEN
  (* the mean on the smaller ball *)
  SUBGOAL_THEN
   `norm(m:real^K) pow 2 <=
    inv(measure(cball(a:real^N,inv(&2) * r))) *
    drop(integral (ball(a,r)) (\x. lift(norm((u:real^N->real^K) x) pow 2)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(measure(cball(a:real^N,rho))) *
                drop(integral (cball(a,rho)) (\x. lift(norm((u:real^N->real^K) x) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_MEAN_SQ_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN CONJ_TAC THEN
      MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the annulus *)
  SUBGOAL_THEN
   `drop(integral (ball(a:real^N,r) DIFF cball(a,rho))
           (\x. lift(norm((u:real^N->real^K) x - m) pow 2)))
    <= drop(integral (ball(a,r) DIFF cball(a,rho))
              (\x. lift(&2 * norm(u x) pow 2 +
                        &2 * (inv(measure(cball(a,inv(&2) * r))) *
                              drop(integral (ball(a,r)) (\x. lift(norm(u x) pow 2)))))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN
        MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[INTEGRABLE_ON_CONST]];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MP_TAC(ISPECL [`(u:real^N->real^K) x`; `m:real^K`; `vec 0:real^K`]
                    WAN_NORM_SQ_TRIANGLE2) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO] THEN
      UNDISCH_TAC
       `norm(m:real^K) pow 2 <=
        inv(measure(cball(a:real^N,inv(&2) * r))) *
        drop(integral (ball(a,r)) (\x. lift(norm((u:real^N->real^K) x) pow 2)))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let WAN_POINCARE_BALL_BOUND = prove
 (`!(a:real^N) r (u:real^N->real^K).
     &0 < r /\ wan_w12 (ball(a,r)) u
     ==> drop(integral (ball(a,r))
                (\x. lift(norm(u x - inv(measure(ball(a,r))) % integral (ball(a,r)) u) pow 2)))
         <= &2 pow (dimindex(:N) + 2) * r pow 2 * wan_dir (ball(a,r)) u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP WAN_RADII_FACTS) THEN
  ABBREV_TAC `K0 = inv(measure(cball(a:real^N,inv(&2) * r))) *
                   drop(integral (ball(a,r)) (\x. lift(norm((u:real^N->real^K) x) pow 2)))` THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(&2 * norm((u:real^N->real^K) x) pow 2 + &2 * K0)`;
                 `a:real^N`; `r:real`] WAN_ANNULUS_NULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC `\x. lift(&2 * norm((u:real^N->real^K) x) pow 2 + &2 * K0)` THEN
    SUBGOAL_THEN `&0 <= K0` ASSUME_TAC THENL
     [EXPAND_TAC "K0" THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [SIMP_TAC[REAL_LE_INV_EQ; MEASURE_POS_LE; MEASURABLE_CBALL];
        MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
        MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. lift(&2 * norm((u:real^N->real^K) x) pow 2 + &2 * K0)) integrable_on
                  ball(a:real^N,r)` ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_CMUL THEN
        MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[INTEGRABLE_ON_CONST; MEASURABLE_BALL]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs x <= x`) THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `drop(integral (ball(a,r))
           (\x. lift(norm((u:real^N->real^K) x - inv(measure(ball(a,r))) %
                                integral (ball(a,r)) u) pow 2))) -
    &2 pow (dimindex(:N) + 2) * r pow 2 * wan_dir (ball(a:real^N,r)) u`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M:num`)) THEN REWRITE_TAC[LE_REFL] THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`; `(&1 - inv(&M + &2)) * r`; `u:real^N->real^K`]
                WAN_POINCARE_BALL_STEP) THEN
  ASM_REWRITE_TAC[NORM_1] THEN REAL_ARITH_TAC);;

let WAN_POINCARE_BALL = prove
 (`!(n:N->bool) (kk:K->bool). WAN_POINCARE_BALL_STATEMENT n kk`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WAN_POINCARE_BALL_STATEMENT] THEN
  EXISTS_TAC `&2 pow (dimindex(:N) + 2)` THEN
  SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`; WAN_POINCARE_BALL_BOUND]);;

