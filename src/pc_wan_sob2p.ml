(* ========================================================================= *)
(* Unit pc_wan_sob2p: Poincare inequality with zero boundary values         *)
(* (POINCARE0), Hardy's inequality on balls (HARDY_BALL), and the vector    *)
(* Wirtinger inequality on [0,2 pi] (WIRTINGER_VEC).  Statement constants:  *)
(* pc_wan_defs.  The two inequalities for test maps come from one           *)
(* integration by parts of |phi|^2 against a vector field (x_1 - a_1, and   *)
(* -(x - a)/(r^2 - |x - a|^2)); W_0 limits by continuity of lnorm and of    *)
(* the Dirichlet integral.  WIRTINGER_VEC is the library                    *)
(* WIRTINGER_INEQUALITY (100/isoperimetric.ml) applied componentwise.       *)
(* ========================================================================= *)

needs "src/pc_wan_sob2v.ml";;

(* The library file invents type variables, so it is loaded with the check *)
(* off; the check is switched back on before any proof of this unit.      *)

type_invention_error := false;;
needs "100/isoperimetric.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Continuity of lnorm and of the Dirichlet integral along W^(1,2)          *)
(* approximations; the Dirichlet integral of a test map; an AM-GM bound.    *)
(* ------------------------------------------------------------------------- *)

let WAN_LNORM2_CONV = prove
 (`!(s:real^N->bool) (f:num->real^N->real^K) g.
     (!n. f n IN lspace s (&2)) /\ g IN lspace s (&2) /\
     ((\n. lnorm s (&2) (\x. f n x - g x)) ---> &0) sequentially
     ==> ((\n. lnorm s (&2) (f n)) ---> lnorm s (&2) g) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. lnorm s (&2) (\x. (f:num->real^N->real^K) n x - g x)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. (f:num->real^N->real^K) n x - g x) IN lspace s (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `g:real^N->real^K`;
                 `\x. (f:num->real^N->real^K) n x - g x`] LNORM_TRIANGLE) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&2`; `(f:num->real^N->real^K) n`;
                 `\x. --((f:num->real^N->real^K) n x - g x)`] LNORM_TRIANGLE) THEN
  ASM_SIMP_TAC[LSPACE_NEG; REAL_ARITH `&1 <= &2`; LNORM_NEG] THEN
  REWRITE_TAC[VECTOR_ARITH `(g:real^K) + (f - g) = f`;
              VECTOR_ARITH `(f:real^K) + --(f - g) = g`; ETA_AX] THEN
  REAL_ARITH_TAC);;

let WAN_WD_L2_CONV = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (f:num->real^N->real^K) i.
     open s /\ wan_w12 s u /\ (!n. wan_w12 s (f n)) /\
     ((\n. wan_dir s (\x. f n x - u x)) ---> &0) sequentially /\
     1 <= i /\ i <= dimindex(:N)
     ==> ((\n. lnorm s (&2) (\x. wan_wd s i (f n) x - wan_wd s i u x)) ---> &0)
         sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LNORM2_NULL THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_SIMP_TAC[REAL_POS; WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. wan_dir s (\x. (f:num->real^N->real^K) n x - u x)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(f:num->real^N->real^K) n`; `u:real^N->real^K`]
                WAN_W12_SUB_WD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i:num`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `i:num`; `\x. (f:num->real^N->real^K) n x - u x`;
                 `\x. wan_wd s i ((f:num->real^N->real^K) n) x - wan_wd s i u x`]
                WAN_WD_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN MATCH_MP_TAC LSPACE_SUB THEN
    ASM_SIMP_TAC[REAL_POS; WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x. lift(norm(wan_wd s i
                (\x. (f:num->real^N->real^K) n x - u x) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `{x | x IN s /\
                     ~(wan_wd s i (\x. (f:num->real^N->real^K) n x - u x) x =
                       wan_wd s i (f n) x - wan_wd s i u x)}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC WAN_WD_SQ_LE_DIR THEN ASM_REWRITE_TAC[]]);;

let WAN_DIR_CONT = prove
 (`!(s:real^N->bool) (u:real^N->real^K) (f:num->real^N->real^K).
     open s /\ wan_w12 s u /\ (!n. wan_w12 s (f n)) /\
     ((\n. wan_dir s (\x. f n x - u x)) ---> &0) sequentially
     ==> ((\n. wan_dir s (f n)) ---> wan_dir s u) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!w:real^N->real^K.
      wan_w12 s w
      ==> drop(integral s (\x. lift(norm(wan_wd s i w x) pow 2))) =
          lnorm s (&2) (wan_wd s i w) pow 2`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_SOB_LNORM2_SQ THEN
    ASM_SIMP_TAC[WAN_WD_WORKS];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC WAN_LNORM2_CONV THEN
  ASM_SIMP_TAC[WAN_WD_WORKS] THEN MATCH_MP_TAC WAN_WD_L2_CONV THEN ASM_REWRITE_TAC[]);;

let WAN_VTEST_DIR_EQ = prove
 (`!(s:real^N->bool) (phi:real^N->real^K).
     open s /\ wan_vtest s phi
     ==> wan_dir s phi =
         sum(1..dimindex(:N))
            (\i. drop(integral s (\x. lift(norm(partial_derivative i phi x) pow 2))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`] WAN_VTEST_W12) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`;
                 `\i x. partial_derivative i (phi:real^N->real^K) x`] WAN_DIR_EQ) THEN
  ASM_SIMP_TAC[]);;

let WAN_VTEST_PARTIAL_SQ_LE_DIR = prove
 (`!(s:real^N->bool) (phi:real^N->real^K) i.
     open s /\ wan_vtest s phi /\ 1 <= i /\ i <= dimindex(:N)
     ==> drop(integral s (\x. lift(norm(partial_derivative i phi x) pow 2)))
         <= wan_dir s phi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_VTEST_DIR_EQ] THEN
  MP_TAC(ISPECL [`\j. drop(integral s (\x. lift(norm(partial_derivative j
                         (phi:real^N->real^K) x) pow 2)))`;
                 `1..dimindex(:N)`; `i:num`] SUM_DELETE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= c ==> c = s - a ==> a <= s`) THEN
  MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[IN_DELETE; IN_NUMSEG; FINITE_DELETE;
                                           FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`] WAN_VTEST_W12) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`; `k:real^N->bool`; `x:num`]
                WAN_VTEST_PARTIAL) THEN
  ASM_SIMP_TAC[]);;

let WAN_AMGM_WEIGHT = prove
 (`!t R (p:real^K) q.
     abs t <= R
     ==> -- &2 * t * (p dot q) <= norm p pow 2 / &2 + &2 * R pow 2 * norm q pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `-- &2 * t * ((p:real^K) dot q) <= &2 * R * (norm p * norm q)` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(t * d) <= R * n ==> -- &2 * t * d <= &2 * R * n`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  MP_TAC(SPEC `norm(p:real^K) - &2 * R * norm(q:real^K)` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integration by parts of |phi|^2 against a C^1 scalar field V on s:      *)
(* int_s |phi|^2 d_i V = -2 int_s V (phi . d_i phi) for test maps phi.     *)
(* ------------------------------------------------------------------------- *)

let WAN_SQNORM_DERIV = prove
 (`!(phi:real^N->real^K) x.
     (phi has_derivative frechet_derivative phi (at x)) (at x)
     ==> ((\y. lift(norm(phi y) pow 2)) has_derivative
          (\h. lift(&2 * (phi x dot frechet_derivative phi (at x) h)))) (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^N->real^K`; `\y:real^K. lift(norm y pow 2)`;
                 `frechet_derivative (phi:real^N->real^K) (at x)`;
                 `\y. &2 % lift((phi:real^N->real^K) x dot y)`; `x:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT; o_DEF; LIFT_CMUL]);;

let WAN_SQNORM_IBP = prove
 (`!(s:real^N->bool) (phi:real^N->real^K) (V:real^N->real) i.
     open s /\ wan_vtest s phi /\ continuously_differentiable 1 s (\x. lift(V x))
     ==> (\x. lift(norm(phi x) pow 2 *
                   drop(frechet_derivative (\y. lift(V y)) (at x) (basis i))))
           integrable_on s /\
         (\x. lift(V x * (phi x dot partial_derivative i phi x))) integrable_on s /\
         drop(integral s (\x. lift(norm(phi x) pow 2 *
                   drop(frechet_derivative (\y. lift(V y)) (at x) (basis i))))) =
         -- &2 * drop(integral s (\x. lift(V x * (phi x dot partial_derivative i phi x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`; `k:real^N->bool`; `i:num`]
                WAN_VTEST_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `phi:real^N->real^K`] WAN_C1_OPEN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[OPEN_UNIV; smooth_map_on]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x. lift((V:real^N->real) x)`] WAN_C1_OPEN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> ((\x. norm((phi:real^N->real^K) x) pow 2 % lift((V:real^N->real) x))
             has_derivative
             (\h. norm(phi x) pow 2 % frechet_derivative (\y. lift(V y)) (at x) h +
                  (&2 * (phi x dot frechet_derivative phi (at x) h)) % lift(V x))) (at x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. norm((phi:real^N->real^K) x) pow 2`;
                   `\h. &2 * ((phi:real^N->real^K) x dot frechet_derivative phi (at x) h)`;
                   `\x. lift((V:real^N->real) x)`;
                   `frechet_derivative (\y. lift((V:real^N->real) y)) (at x)`; `x:real^N`]
                  HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[WAN_SQNORM_DERIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((phi:real^N->real^K) x) pow 2 *
              drop(frechet_derivative (\y. lift((V:real^N->real) y)) (at x) (basis i))))
      continuous_on s /\
    (\x. lift(V x * (phi x dot partial_derivative i phi x))) continuous_on s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN ASM_REWRITE_TAC[ETA_AX] THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((phi:real^N->real^K) x) pow 2 *
              drop(frechet_derivative (\y. lift((V:real^N->real) y)) (at x) (basis i))))
      integrable_on s /\
    (\x. lift(V x * (phi x dot partial_derivative i phi x))) integrable_on s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_NT_INTEGRABLE_COMPACT_SUPPORT THEN
    EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ; REAL_MUL_LZERO;
                 REAL_MUL_RZERO; LIFT_NUM; DOT_LZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\x. norm((phi:real^N->real^K) x) pow 2 % lift((V:real^N->real) x)`;
    `\x h. norm((phi:real^N->real^K) x) pow 2 %
           frechet_derivative (\y. lift((V:real^N->real) y)) (at x) h +
           (&2 * (phi x dot frechet_derivative phi (at x) h)) % lift(V x)`;
    `s:real^N->bool`; `k:real^N->bool`; `i:num`] WAN_NT_INTEGRAL_PARTIAL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_0; REAL_POW_ZERO; ARITH_EQ; VECTOR_MUL_LZERO] THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. lift(norm((phi:real^N->real^K) x) pow 2 *
                    drop(frechet_derivative (\y. lift((V:real^N->real) y)) (at x) (basis i))) +
                    &2 % lift(V x * (phi x dot partial_derivative i phi x))` THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP; partial_derivative] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  SUBGOAL_THEN
   `(\x. norm((phi:real^N->real^K) x) pow 2 %
         frechet_derivative (\y. lift((V:real^N->real) y)) (at x) (basis i) +
         (&2 * (phi x dot frechet_derivative phi (at x) (basis i))) % lift(V x)) =
    (\x. lift(norm(phi x) pow 2 *
              drop(frechet_derivative (\y. lift(V y)) (at x) (basis i))) +
         &2 % lift(V x * (phi x dot partial_derivative i phi x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; LIFT_DROP; partial_derivative] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_VEC] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* POINCARE0: int |u|^2 <= 4 R^2 int |grad u|^2 for u in W_0^(1,2)(s),     *)
(* s inside ball(a,R): integrate |phi|^2 by parts against x_1 - a_1 and use *)
(* -2 t (p.q) <= |p|^2/2 + 2 R^2 |q|^2 for |t| <= R.                        *)
(* ------------------------------------------------------------------------- *)

let WAN_COORD_FACTS = prove
 (`!(a:real^N) j (x:real^N).
     ((\y:real^N. lift(y$j - a$j)) has_derivative (\h:real^N. lift(h$j))) (at x) /\
     continuously_differentiable 1 (:real^N) (\y:real^N. lift(y$j - a$j)) /\
     frechet_derivative (\y:real^N. lift(y$j - a$j)) (at x) = (\h:real^N. lift(h$j))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. ((\y. lift(y$j - (a:real^N)$j)) has_derivative (\h. lift(h$j))) (at x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\y:real^N. lift(y$j)`; `\h:real^N. lift(h$j)`;
                   `\y:real^N. lift((a:real^N)$j)`; `\h:real^N. vec 0:real^1`;
                   `at (x:real^N)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_LIFT_COMPONENT; HAS_DERIVATIVE_CONST; LIFT_SUB;
                VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_1] THEN
    EXISTS_TAC `\x:real^N h:real^N. lift(h$j)` THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN; CONTINUOUS_ON_CONST];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]);;

let WAN_INTEGRAL_LIN2 = prove
 (`!(s:real^N->bool) f g a b.
     (\x. lift(f x)) integrable_on s /\ (\x. lift(g x)) integrable_on s
     ==> (\x. lift(a * f x + b * g x)) integrable_on s /\
         drop(integral s (\x. lift(a * f x + b * g x))) =
         a * drop(integral s (\x. lift(f x))) + b * drop(integral s (\x. lift(g x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_CMUL; INTEGRAL_ADD; INTEGRAL_CMUL;
               DROP_ADD; DROP_CMUL]);;

let WAN_INTEGRAL_LIN1 = prove
 (`!(s:real^N->bool) f a.
     (\x. lift(f x)) integrable_on s
     ==> (\x. lift(a * f x)) integrable_on s /\
         drop(integral s (\x. lift(a * f x))) = a * drop(integral s (\x. lift(f x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRAL_CMUL; DROP_CMUL]);;

let WAN_POINCARE0_TEST = prove
 (`!(s:real^N->bool) (a:real^N) R (phi:real^N->real^K).
     open s /\ s SUBSET ball(a,R) /\ wan_vtest s phi
     ==> drop(integral s (\x. lift(norm(phi x) pow 2))) <=
         &4 * R pow 2 *
         drop(integral s (\x. lift(norm(partial_derivative 1 phi x) pow 2)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `phi:real^N->real^K`; `k:real^N->bool`; `1`]
                WAN_VTEST_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_vtest (:real^N) (phi:real^N->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_VTEST_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. lift(norm((phi:real^N->real^K) x) pow 2)) =
    integral (:real^N) (\x. lift(norm(phi x) pow 2)) /\
    integral s (\x. lift(norm(partial_derivative 1 (phi:real^N->real^K) x) pow 2)) =
    integral (:real^N) (\x. lift(norm(partial_derivative 1 phi x) pow 2))`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; NORM_0; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((phi:real^N->real^K) x) pow 2)) integrable_on (:real^N) /\
    (\x. lift(norm(partial_derivative 1 (phi:real^N->real^K) x) pow 2))
      integrable_on (:real^N)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N)`; `phi:real^N->real^K`; `\x:real^N. x$1 - (a:real^N)$1`; `1`]
                WAN_SQNORM_IBP) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; WAN_COORD_FACTS] THEN
  SUBGOAL_THEN `(basis 1:real^N)$1 = &1` (fun th -> REWRITE_TAC[th; LIFT_DROP; REAL_MUL_RID])
  THENL [SIMP_TAC[BASIS_COMPONENT; LE_REFL; DIMINDEX_GE_1]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`(:real^N)`;
                 `\x. ((x:real^N)$1 - (a:real^N)$1) *
                      ((phi:real^N->real^K) x dot partial_derivative 1 phi x)`;
                 `-- &2`] WAN_INTEGRAL_LIN1) THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x. norm((phi:real^N->real^K) x) pow 2`;
                 `\x. norm(partial_derivative 1 (phi:real^N->real^K) x) pow 2`;
                 `inv(&2)`; `&2 * R pow 2`] WAN_INTEGRAL_LIN2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th2 -> DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN MP_TAC th2) THEN
  MATCH_MP_TAC(REAL_ARITH
   `l <= r ==> r = inv(&2) * A + (&2 * R pow 2) * D ==> l = -- &2 * P ==> A = -- &2 * P
    ==> A <= &4 * R pow 2 * D`) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  ASM_CASES_TAC `(x:real^N) IN k` THENL
   [SUBGOAL_THEN `abs((x:real^N)$1 - (a:real^N)$1) <= R` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
      SUBGOAL_THEN `(x:real^N) IN ball(a,R)` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(ISPECL [`a - x:real^N`; `1`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(x:real^N)$1 - (a:real^N)$1`; `R:real`; `(phi:real^N->real^K) x`;
                   `partial_derivative 1 (phi:real^N->real^K) x`] WAN_AMGM_WEIGHT) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[DOT_LZERO; REAL_MUL_RZERO; NORM_0; REAL_POW_ZERO; ARITH_EQ] THEN
    REAL_ARITH_TAC]);;

let WAN_POINCARE0 = prove
 (`!(n:N->bool) (kk:K->bool). WAN_POINCARE0_STATEMENT n kk`,
  REWRITE_TAC[WAN_POINCARE0_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_w120]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!n. wan_w12 s ((f:num->real^N->real^K) n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[WAN_VTEST_W12]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. lnorm s (&2) ((f:num->real^N->real^K) n) pow 2 <= &4 * R pow 2 * wan_dir s (f n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`(f:num->real^N->real^K) n`; `s:real^N->bool`] WAN_SOB_LNORM2_SQ) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * R pow 2 *
                drop(integral s (\x. lift(norm(partial_derivative 1
                       ((f:num->real^N->real^K) n) x) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_POINCARE0_TEST THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC WAN_VTEST_PARTIAL_SQ_LE_DIR THEN
      ASM_REWRITE_TAC[LE_REFL; DIMINDEX_GE_1]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\n. lnorm s (&2) ((f:num->real^N->real^K) n) pow 2`;
    `\n. &4 * R pow 2 * wan_dir s ((f:num->real^N->real^K) n)`] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC WAN_LNORM2_CONV THEN
    ASM_SIMP_TAC[WAN_W12_IMP_LSPACE];
    MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_LMUL THEN
    MATCH_MP_TAC WAN_DIR_CONT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* WIRTINGER_VEC: the library WIRTINGER_INEQUALITY applied componentwise.   *)
(* ------------------------------------------------------------------------- *)

let WAN_REAL_INTEGRAL_BRIDGE = prove
 (`!(g:real->real) c.
     (g real_integrable_on real_interval[&0,c] <=>
      (\t. lift(g(drop t))) integrable_on interval[vec 0,lift c]) /\
     (g real_integrable_on real_interval[&0,c]
      ==> real_integral (real_interval[&0,c]) g =
          drop(integral (interval[vec 0,lift c]) (\t. lift(g(drop t)))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; LIFT_NUM; o_DEF] THEN
  SIMP_TAC[REAL_INTEGRAL; REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; LIFT_NUM; o_DEF]);;

let WAN_SQNORM_INTEGRAL_COMPONENTS = prove
 (`!(g:real->real^K) c.
     (!k. 1 <= k /\ k <= dimindex(:K)
          ==> (\x. (g x)$k pow 2) real_integrable_on real_interval[&0,c])
     ==> (\t. lift(norm(g(drop t)) pow 2)) integrable_on interval[vec 0,lift c] /\
         drop(integral (interval[vec 0,lift c]) (\t. lift(norm(g(drop t)) pow 2))) =
         sum(1..dimindex(:K)) (\k. real_integral (real_interval[&0,c]) (\x. (g x)$k pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. lift(norm((g:real->real^K)(drop t)) pow 2)) =
    (\t. vsum(1..dimindex(:K)) (\k. lift((g(drop t))$k pow 2)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; NORM_POW_2; dot; LIFT_SUM; o_DEF; REAL_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:K)
        ==> (\t. lift(((g:real->real^K)(drop t))$k pow 2)) integrable_on
              interval[vec 0,lift c] /\
            real_integral (real_interval[&0,c]) (\x. (g x)$k pow 2) =
            drop(integral (interval[vec 0,lift c]) (\t. lift((g(drop t))$k pow 2)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x. ((g:real->real^K) x)$k pow 2`; `c:real`] WAN_REAL_INTEGRAL_BRIDGE) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    MP_TAC(ISPECL [`\k t. lift(((g:real->real^K)(drop t))$k pow 2)`;
                   `interval[vec 0:real^1,lift c]`; `1..dimindex(:K)`] INTEGRAL_VSUM) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_VSUM; o_DEF] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[]]);;

let WAN_WIRTINGER_VEC = prove
 (`!(kk:K->bool). WAN_WIRTINGER_VEC_STATEMENT kk`,
  REWRITE_TAC[WAN_WIRTINGER_VEC_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * pi IN real_interval[&0,&2 * pi]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\t. (f':real->real^K)(drop t)) measurable_on interval[vec 0,lift(&2 * pi)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `(f:real->real^K)(&2 * pi) - f(&0)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:K)
        ==> (\x. ((f':real->real^K) x)$k pow 2) real_integrable_on
              real_interval[&0,&2 * pi] /\
            (\x. ((f:real->real^K) x)$k pow 2) real_integrable_on
              real_interval[&0,&2 * pi] /\
            real_integral (real_interval[&0,&2 * pi]) (\x. (f x)$k pow 2) <=
            real_integral (real_interval[&0,&2 * pi]) (\x. (f' x)$k pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(\x. ((f':real->real^K) x)$k pow 2) real_integrable_on real_interval[&0,&2 * pi]`
    ASSUME_TAC THENL
     [REWRITE_TAC[WAN_REAL_INTEGRAL_BRIDGE] THEN
      MP_TAC(ISPECL [`interval[vec 0:real^1,lift(&2 * pi)]`; `&2`;
                     `\t. lift(((f':real->real^K)(drop t))$k)`;
                     `\t. (f':real->real^K)(drop t)`] LSPACE_BOUNDED_MEASURABLE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ARITH `&0 < &2`; NORM_LIFT; COMPONENT_LE_NORM] THEN CONJ_TAC THENL
         [UNDISCH_TAC
           `(\t. (f':real->real^K)(drop t)) measurable_on interval[vec 0,lift(&2 * pi)]` THEN
          GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_COMPONENTWISE] THEN
          DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW] THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(MP_TAC o MATCH_MP WAN_LSPACE2_SQNORM_INTEGRABLE) THEN
        REWRITE_TAC[NORM_LIFT; REAL_POW2_ABS]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. ((f:real->real^K) x)$k`; `\x. ((f':real->real^K) x)$k`]
                  WIRTINGER_INEQUALITY) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL; o_DEF; LIFT_NUM] THEN
        FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `x IN real_interval[&0,&2 * pi]`)) THEN
        GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_COMPONENTWISE] THEN
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT];
        REWRITE_TAC[HAS_REAL_INTEGRAL; o_DEF; LIFT_NUM] THEN
        UNDISCH_TAC
         `((\t. (f:real->real^K)(drop t)) has_integral vec 0)
          (interval[vec 0,lift(&2 * pi)])` THEN
        GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_COMPONENTWISE] THEN
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[VEC_COMPONENT; LIFT_NUM]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real^K`; `&2 * pi`] WAN_SQNORM_INTEGRAL_COMPONENTS) THEN
  MP_TAC(ISPECL [`f':real->real^K`; `&2 * pi`] WAN_SQNORM_INTEGRAL_COMPONENTS) THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The vector field V(x) = -(x - a)/(r^2 - |x - a|^2) on ball(a,r): its     *)
(* components are C^1 with d_i V_i = -1/D - 2 (x_i - a_i)^2/D^2,            *)
(* D = r^2 - |x - a|^2.                                                      *)
(* ------------------------------------------------------------------------- *)

let WAN_HARDY_FIELD_DERIV = prove
 (`!(a:real^N) r i x.
     x IN ball(a,r)
     ==> ((\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2)))
          has_derivative
          (\h. lift(--(h$i) * inv(r pow 2 - norm(x - a) pow 2) +
                    (a$i - x$i) * (&2 * inv((r pow 2 - norm(x - a) pow 2) pow 2) *
                                   ((x - a) dot h))))) (at x)`,
  REWRITE_TAC[IN_BALL; dist] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r pow 2 - norm(x - a:real^N) pow 2 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `b < a ==> ~(a - b = &0)`) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. lift(norm(y - a:real^N) pow 2)) has_derivative
     (\h. &2 % lift((x - a) dot h))) (at x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. y - a`; `\z:real^N. lift(norm z pow 2)`; `\h:real^N. h`;
                   `\h. &2 % lift((x - a:real^N) dot h)`; `x:real^N`] DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF; HAS_DERIVATIVE_SQNORM_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\y:real^N. y`; `\h:real^N. h`; `\y:real^N. a:real^N`;
                   `\h:real^N. vec 0:real^N`; `at (x:real^N)`] HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. lift(inv(r pow 2 - norm(y - a:real^N) pow 2))) has_derivative
     (\h. --(inv(drop(lift(r pow 2 - norm(x - a) pow 2)) pow 2)) %
          (vec 0 - &2 % lift((x - a) dot h)))) (at x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^N. lift(r pow 2 - norm(y - a) pow 2)`; `lift o inv o drop`;
                   `\h:real^N. vec 0 - &2 % lift((x - a:real^N) dot h)`;
                   `\h:real^1. --(inv(drop(lift(r pow 2 - norm(x - a:real^N) pow 2)) pow 2)) % h`;
                   `x:real^N`] DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
      ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST];
      MP_TAC(ISPEC `lift(r pow 2 - norm(x - a:real^N) pow 2)` HAS_DERIVATIVE_LIFT_INV) THEN
      ASM_REWRITE_TAC[LIFT_DROP; o_DEF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. ((a:real^N)$i - y$i) % lift(inv(r pow 2 - norm(y - a) pow 2))) has_derivative
     (\h. (a$i - x$i) %
          (--(inv(drop(lift(r pow 2 - norm(x - a) pow 2)) pow 2)) %
           (vec 0 - &2 % lift((x - a) dot h))) +
          --(h$i) % lift(inv(r pow 2 - norm(x - a) pow 2)))) (at x)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_MUL_AT THEN ASM_REWRITE_TAC[o_DEF] THEN
    REWRITE_TAC[LIFT_SUB; LIFT_NEG] THEN
    MP_TAC(ISPECL [`\y:real^N. lift((a:real^N)$i)`; `\h:real^N. vec 0:real^1`;
                   `\y:real^N. lift(y$i)`; `\h:real^N. lift(h$i)`; `at (x:real^N)`]
                  HAS_DERIVATIVE_SUB) THEN
    REWRITE_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_LIFT_COMPONENT; VECTOR_SUB_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) =
    (\y. (a$i - y$i) % lift(inv(r pow 2 - norm(y - a) pow 2)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_NEG; DROP_SUB; DROP_VEC;
              LIFT_DROP; REAL_INV_POW] THEN
  REAL_ARITH_TAC);;

let WAN_HARDY_FIELD_C1 = prove
 (`!(a:real^N) r i.
     continuously_differentiable 1 (ball(a,r))
       (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 (ball(a:real^N,r))
      (\y. lift(r pow 2 - norm(y - a) pow 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUB_OPEN THEN
    SIMP_TAC[OPEN_BALL; CONTINUOUSLY_DIFFERENTIABLE_CONST] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_NORM_POW2_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUB_OPEN THEN
    SIMP_TAC[OPEN_BALL; CONTINUOUSLY_DIFFERENTIABLE_CONST;
             CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuously_differentiable 1 (ball(a:real^N,r))
      (\y. lift(inv(drop(lift(r pow 2 - norm(y - a) pow 2)))))`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_LIFT_INV_OPEN THEN
    ASM_REWRITE_TAC[OPEN_BALL; LIFT_DROP] THEN
    REWRITE_TAC[IN_BALL; dist] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `b < a ==> ~(a - b = &0)`) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`1`; `ball(a:real^N,r)`; `\y:real^N. lift((a:real^N)$i - y$i)`;
                 `\y:real^N. lift(inv(r pow 2 - norm(y - a:real^N) pow 2))`]
                CONTINUOUSLY_DIFFERENTIABLE_MUL_LIFT_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP; OPEN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUB_OPEN THEN
  SIMP_TAC[OPEN_BALL; CONTINUOUSLY_DIFFERENTIABLE_CONST;
           CONTINUOUSLY_DIFFERENTIABLE_LINEAR_OPEN; LINEAR_LIFT_COMPONENT]);;

let WAN_HARDY_DIV_COMPONENT = prove
 (`!(a:real^N) r i x.
     x IN ball(a,r) /\ 1 <= i /\ i <= dimindex(:N)
     ==> drop(frechet_derivative
               (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2)))
               (at x) (basis i)) =
         --inv(r pow 2 - norm(x - a) pow 2) -
         &2 * (x$i - a$i) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP WAN_HARDY_FIELD_DERIV) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  ASM_SIMP_TAC[LIFT_DROP; BASIS_COMPONENT; DOT_BASIS; VECTOR_SUB_COMPONENT] THEN
  REAL_ARITH_TAC);;

let WAN_HARDY_REAL_INEQ = prove
 (`!N r t.
     &1 <= N /\ &0 <= t /\ t < r
     ==> inv((r - t) pow 2) <=
         &2 * (N * inv(r pow 2 - t pow 2) +
               &2 * t pow 2 * inv((r pow 2 - t pow 2) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r pow 2 - t pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `b < a ==> &0 < a - b`) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv((r - t) pow 2) = (r + t) pow 2 * inv((r pow 2 - t pow 2) pow 2) /\
    N * inv(r pow 2 - t pow 2) =
    (N * (r pow 2 - t pow 2)) * inv((r pow 2 - t pow 2) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC(REAL_FIELD
      `~(r - t = &0) /\ ~(r + t = &0) /\ ~(D = &0) /\ D = (r - t) * (r + t)
       ==> inv((r - t) pow 2) = (r + t) pow 2 * inv(D pow 2) /\
           N * inv(D) = (N * D) * inv(D pow 2)`) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `&2 * (a * i + &2 * b * i) = (&2 * a + &4 * b) * i`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * D <= &2 * (N * D) /\ (r + t) pow 2 <= &2 * D + &4 * t pow 2
    ==> (r + t) pow 2 <= &2 * (N * D) + &4 * t pow 2`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MP_TAC(SPEC `r - t` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let WAN_AMGM_DOT = prove
 (`!v (p:real^K) q. &2 * v * (p dot q) <= v pow 2 * norm p pow 2 + norm q pow 2`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&2 * v * ((p:real^K) dot q) <= &2 * abs v * (norm p * norm q)` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(v * d) <= w ==> &2 * v * d <= &2 * w`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS; NORM_CAUCHY_SCHWARZ_ABS];
    ALL_TAC] THEN
  MP_TAC(SPEC `abs v * norm(p:real^K) - norm(q:real^K)` REAL_LE_POW_2) THEN
  REWRITE_TAC[REAL_ARITH `(a * b - c) pow 2 = a pow 2 * b pow 2 - &2 * a * b * c + c pow 2`;
              REAL_POW2_ABS] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hardy's inequality for test maps on ball(a,r): pointwise algebra.  With  *)
(* D = r^2 - |x - a|^2 and W = N/D + 2 |x - a|^2/D^2, the divergence of the *)
(* field is -W, 2 V.(p . q) <= W |p|^2/2 + |q|^2 and 1/d^2 <= 2 W.          *)
(* ------------------------------------------------------------------------- *)

let WAN_HARDY_POINTWISE = prove
 (`!(a:real^N) r x (p:real^K) (q:num->real^K).
     x IN ball(a,r)
     ==> sum(1..dimindex(:N))
           (\i. norm p pow 2 *
                drop(frechet_derivative
                       (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2)))
                       (at x) (basis i))) =
         --(norm p pow 2 *
            (&(dimindex(:N)) * inv(r pow 2 - norm(x - a) pow 2) +
             &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))) /\
         &2 * sum(1..dimindex(:N))
                (\i. ((a$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * (p dot q i))
         <= inv(&2) * (norm p pow 2 *
                (&(dimindex(:N)) * inv(r pow 2 - norm(x - a) pow 2) +
                 &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))) +
            sum(1..dimindex(:N)) (\i. norm(q i) pow 2) /\
         norm p pow 2 / (r - norm(x - a)) pow 2 <=
         &2 * (norm p pow 2 *
                (&(dimindex(:N)) * inv(r pow 2 - norm(x - a) pow 2) +
                 &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(x - a:real^N) < r` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_MESON_TAC[IN_BALL; dist]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 2 - norm(x - a:real^N) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `b < a ==> &0 < a - b`) THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. ((a:real^N)$i - (x:real^N)$i) pow 2) = norm(x - a) pow 2`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NORM_SUB] THEN
    REWRITE_TAC[NORM_POW_2; dot; VECTOR_SUB_COMPONENT; REAL_POW_2];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS
     `sum(1..dimindex(:N))
        (\i. norm(p:real^K) pow 2 *
             (--inv(r pow 2 - norm(x - a:real^N) pow 2) -
              &2 * ((x:real^N)$i - (a:real^N)$i) pow 2 *
              inv((r pow 2 - norm(x - a) pow 2) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC WAN_HARDY_DIV_COMPONENT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL; SUM_SUB_NUMSEG; SUM_NEG; SUM_CONST_NUMSEG; SUM_RMUL] THEN
    SUBGOAL_THEN
     `sum(1..dimindex(:N)) (\i. ((x:real^N)$i - (a:real^N)$i) pow 2) = norm(x - a) pow 2`
    (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB] THEN REAL_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS
     `sum(1..dimindex(:N))
        (\i. (((a:real^N)$i - (x:real^N)$i) * inv(r pow 2 - norm(x - a) pow 2)) pow 2 *
             norm(p:real^K) pow 2 + norm((q:num->real^K) i) pow 2)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[WAN_AMGM_DOT];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; REAL_POW_MUL; SUM_RMUL] THEN
    ASM_REWRITE_TAC[REAL_INV_POW] THEN
    SUBGOAL_THEN
     `&0 <= norm(p:real^K) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      REAL_ARITH_TAC];
    MP_TAC(ISPECL [`&(dimindex(:N))`; `r:real`; `norm(x - a:real^N)`] WAN_HARDY_REAL_INEQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LE; REAL_OF_NUM_LE; DIMINDEX_GE_1]; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[real_div] THEN
    TRANS_TAC REAL_LE_TRANS `norm(p:real^K) pow 2 * (&2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; REAL_ARITH_TAC]]);;

let WAN_HARDY_TEST = prove
 (`!(a:real^N) r (phi:real^N->real^K).
     &0 < r /\ wan_vtest (ball(a,r)) phi
     ==> (\x. lift(norm(phi x) pow 2 / (r - norm(x - a)) pow 2)) integrable_on ball(a,r) /\
         drop(integral (ball(a,r)) (\x. lift(norm(phi x) pow 2 / (r - norm(x - a)) pow 2)))
         <= &4 * wan_dir (ball(a,r)) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_vtest]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!i. (\x. lift(norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i)))) integrable_on ball(a,r) /\
        (\x. lift((((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * (phi x dot partial_derivative i phi x))) integrable_on ball(a,r) /\
        drop(integral (ball(a,r)) (\x. lift(norm(phi x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i))))) =
        -- &2 * drop(integral (ball(a,r))
                       (\x. lift((((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * (phi x dot partial_derivative i phi x))))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`ball(a:real^N,r)`; `phi:real^N->real^K`;
                   `\y:real^N. ((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2)`;
                   `i:num`] WAN_SQNORM_IBP) THEN
    ASM_REWRITE_TAC[OPEN_BALL; WAN_HARDY_FIELD_C1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift(norm(partial_derivative i (phi:real^N->real^K) x) pow 2))
            integrable_on ball(a,r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    MATCH_MP_TAC WAN_LSPACE2_CONT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
    MP_TAC(ISPECL [`ball(a:real^N,r)`; `phi:real^N->real^K`; `k:real^N->bool`; `i:num`]
                  WAN_VTEST_PARTIAL) THEN
    ASM_SIMP_TAC[OPEN_BALL; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`;
                 `\i x. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i))`;
                 `dimindex(:N)`] WAN_SUM_DROP_INTEGRAL) THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`;
                 `\i x. (((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * ((phi:real^N->real^K) x dot partial_derivative i phi x)`;
                 `dimindex(:N)`] WAN_SUM_DROP_INTEGRAL) THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`;
                 `\i x. norm(partial_derivative i (phi:real^N->real^K) x) pow 2`;
                 `dimindex(:N)`] WAN_SUM_DROP_INTEGRAL) THEN
  ASM_SIMP_TAC[] THEN
  REPLICATE_TAC 3 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN
   `(\x. lift(sum(1..dimindex(:N)) (\i. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i))))) integrable_on ball(a,r) /\
    (\x. lift(sum(1..dimindex(:N)) (\i. (((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * ((phi:real^N->real^K) x dot partial_derivative i phi x)))) integrable_on ball(a,r) /\
    (\x. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i (phi:real^N->real^K) x) pow 2))) integrable_on ball(a,r)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_VSUM THEN ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (ball(a,r)) (\x. lift(sum(1..dimindex(:N)) (\i. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i)))))) =
    -- &2 * drop(integral (ball(a,r)) (\x. lift(sum(1..dimindex(:N)) (\i. (((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * ((phi:real^N->real^K) x dot partial_derivative i phi x)))))`
  (LABEL_TAC "e1") THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(a:real^N,r)
        ==> sum(1..dimindex(:N)) (\i. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i))) = --(norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))) /\
            &2 * sum(1..dimindex(:N)) (\i. (((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * ((phi:real^N->real^K) x dot partial_derivative i phi x)) <= inv(&2) * (norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))) + sum(1..dimindex(:N)) (\i. norm(partial_derivative i (phi:real^N->real^K) x) pow 2) /\
            norm((phi:real^N->real^K) x) pow 2 / (r - norm(x - a)) pow 2 <= &2 * (norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`; `x:real^N`; `(phi:real^N->real^K) x`;
                   `\i. partial_derivative i (phi:real^N->real^K) x`] WAN_HARDY_POINTWISE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2)))) integrable_on ball(a:real^N,r) /\
    drop(integral (ball(a,r)) (\x. lift(norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))))) =
    -- drop(integral (ball(a,r)) (\x. lift(sum(1..dimindex(:N)) (\i. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i))))))`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "adef")) THENL
   [SUBGOAL_THEN
     `!x. x IN ball(a:real^N,r) ==> lift(norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))) = --(lift(sum(1..dimindex(:N)) (\i. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i)))))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LIFT_NEG; VECTOR_NEG_NEG]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC `\x. --(lift(sum(1..dimindex(:N)) (\i. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i)))))` THEN
      ASM_SIMP_TAC[INTEGRABLE_NEG];
      TRANS_TAC EQ_TRANS `drop(integral (ball(a:real^N,r)) (\x. --(lift(sum(1..dimindex(:N)) (\i. norm((phi:real^N->real^K) x) pow 2 * drop(frechet_derivative (\y. lift(((a:real^N)$i - y$i) * inv(r pow 2 - norm(y - a) pow 2))) (at x) (basis i)))))))` THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[INTEGRAL_NEG; DROP_NEG]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`; `\x. sum(1..dimindex(:N)) (\i. (((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * ((phi:real^N->real^K) x dot partial_derivative i phi x))`; `&2`] WAN_INTEGRAL_LIN1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lin1") o BETA_RULE) THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`; `\x. norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))`; `\x. sum(1..dimindex(:N)) (\i. norm(partial_derivative i (phi:real^N->real^K) x) pow 2)`; `inv(&2)`; `&1`]
                WAN_INTEGRAL_LIN2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lin2") o BETA_RULE) THEN
  MP_TAC(ISPECL [`ball(a:real^N,r)`; `\x. norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))`; `&2`] WAN_INTEGRAL_LIN1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lin3") o BETA_RULE) THEN
  SUBGOAL_THEN
   `drop(integral (ball(a:real^N,r)) (\x. lift(&2 * sum(1..dimindex(:N)) (\i. (((a:real^N)$i - x$i) * inv(r pow 2 - norm(x - a) pow 2)) * ((phi:real^N->real^K) x dot partial_derivative i phi x))))) <=
    drop(integral (ball(a,r)) (\x. lift(inv(&2) * (norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))) + &1 * sum(1..dimindex(:N)) (\i. norm(partial_derivative i (phi:real^N->real^K) x) pow 2))))`
  (LABEL_TAC "ineq") THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(norm((phi:real^N->real^K) x) pow 2 / (r - norm(x - a)) pow 2))
      integrable_on ball(a:real^N,r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x. lift(&2 * (norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))))` THEN
    ASM_REWRITE_TAC[LIFT_DROP; NORM_LIFT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_BALL; real_div; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
        MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
        MP_TAC(ISPECL [`\x:real^N. (r - norm(x - a:real^N)) pow 2`; `ball(a:real^N,r)`]
                      CONTINUOUS_ON_INV) THEN
        REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN REWRITE_TAC[LIFT_SUB] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
          SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
          REWRITE_TAC[IN_BALL; dist] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
          REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ] THEN
          FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[NORM_SUB] o
                        check (is_binary "real_lt" o concl)) THEN
          REAL_ARITH_TAC]];
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (ball(a:real^N,r))
      (\x. lift(norm((phi:real^N->real^K) x) pow 2 / (r - norm(x - a)) pow 2))) <=
    drop(integral (ball(a,r)) (\x. lift(&2 * (norm((phi:real^N->real^K) x) pow 2 * (&(dimindex(:N)) * inv(r pow 2 - norm(x - a:real^N) pow 2) + &2 * norm(x - a) pow 2 * inv((r pow 2 - norm(x - a) pow 2) pow 2))))))`
  (LABEL_TAC "ineq2") THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `wan_dir (ball(a:real^N,r)) (phi:real^N->real^K) =
    drop(integral (ball(a,r)) (\x. lift(sum(1..dimindex(:N)) (\i. norm(partial_derivative i (phi:real^N->real^K) x) pow 2))))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WAN_VTEST_DIR_EQ; OPEN_BALL]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REMOVE_THEN "e1" MP_TAC THEN REMOVE_THEN "adef" MP_TAC THEN
  REMOVE_THEN "lin1" MP_TAC THEN REMOVE_THEN "lin2" MP_TAC THEN
  REMOVE_THEN "lin3" MP_TAC THEN REMOVE_THEN "ineq" MP_TAC THEN
  REMOVE_THEN "ineq2" MP_TAC THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hardy's inequality for W_0^(1,2)(ball(a,r)): truncated weights           *)
(* w_m = min(1/d, m) with d = r - |x - a|, continuity of lnorm along the    *)
(* approximating test maps, then monotone convergence in m.                 *)
(* ------------------------------------------------------------------------- *)

let WAN_HARDY_WEIGHT = prove
 (`!(a:real^N) r m.
     (\x. lift(min (inv(r - norm(x - a))) (&m))) continuous_on ball(a,r) /\
     (!x. x IN ball(a,r)
          ==> &0 < r - norm(x - a) /\
              &0 <= min (inv(r - norm(x - a))) (&m) /\
              min (inv(r - norm(x - a))) (&m) <= &m /\
              min (inv(r - norm(x - a))) (&m) <= inv(r - norm(x - a)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN ball(a,r) ==> &0 < r - norm(x - a)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist; REAL_SUB_LT] THEN MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MIN_1 THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MP_TAC(ISPECL [`\x:real^N. r - norm(x - a:real^N)`; `ball(a:real^N,r)`]
                  CONTINUOUS_ON_INV) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN REWRITE_TAC[LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_MIN; REAL_MIN_LE; REAL_LE_REFL; REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]]);;

let WAN_HARDY_TRUNC = prove
 (`!(a:real^N) r (u:real^N->real^K) m.
     &0 < r /\ wan_w120 (ball(a,r)) u
     ==> (\x. min (inv(r - norm(x - a))) (&m) % u x) IN lspace (ball(a,r)) (&2) /\
         lnorm (ball(a,r)) (&2) (\x. min (inv(r - norm(x - a))) (&m) % u x) pow 2
         <= &4 * wan_dir (ball(a,r)) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_w120]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:num->real^N->real^K` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a:real^N`; `r:real`; `m:num`] WAN_HARDY_WEIGHT) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!v:real^N->real^K.
      v IN lspace (ball(a,r)) (&2)
      ==> (\x. min (inv(r - norm(x - a))) (&m) % v x) IN lspace (ball(a,r)) (&2)`
  (LABEL_TAC "wl") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_BOUNDED_MUL THEN
    EXISTS_TAC `&m` THEN ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. wan_w12 (ball(a:real^N,r)) ((f:num->real^N->real^K) n) /\
        f n IN lspace (ball(a,r)) (&2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN
    REWRITE_TAC[WAN_W12_IMP_LSPACE] THEN ASM_MESON_TAC[WAN_VTEST_W12; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->real^K) IN lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[WAN_W12_IMP_LSPACE]; ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "wl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. lnorm (ball(a:real^N,r)) (&2)
          (\x. min (inv(r - norm(x - a))) (&m) % (f:num->real^N->real^K) n x) pow 2
        <= &4 * wan_dir (ball(a,r)) (f n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`; `(f:num->real^N->real^K) n`] WAN_HARDY_TEST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. min (inv(r - norm(x - a))) (&m) % (f:num->real^N->real^K) n x`;
                   `ball(a:real^N,r)`] WAN_SOB_LNORM2_SQ) THEN
    ANTS_TAC THENL
     [USE_THEN "wl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(a:real^N,r))
                 (\x. lift(norm((f:num->real^N->real^K) n x) pow 2 /
                           (r - norm(x - a)) pow 2)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN USE_THEN "wl" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; NORM_MUL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&m`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= w ==> abs w = w`; real_div; REAL_INV_POW;
                 REAL_POW_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\n. lnorm (ball(a:real^N,r)) (&2)
           (\x. min (inv(r - norm(x - a))) (&m) % (f:num->real^N->real^K) n x) pow 2`;
    `\n. &4 * wan_dir (ball(a:real^N,r)) ((f:num->real^N->real^K) n)`] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_POW THEN MATCH_MP_TAC WAN_LNORM2_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN USE_THEN "wl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
      USE_THEN "wl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC `\n. &m * lnorm (ball(a:real^N,r)) (&2)
                         (\x. (f:num->real^N->real^K) n x - u x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\x. (f:num->real^N->real^K) n x - u x) IN lspace (ball(a:real^N,r)) (&2)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS; ETA_AX]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(\x. min (inv(r - norm(x - a))) (&m) % (f:num->real^N->real^K) n x -
             min (inv(r - norm(x - a))) (&m) % u x) IN lspace (ball(a:real^N,r)) (&2)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THEN
        USE_THEN "wl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC LNORM_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(a:real^N,r)`; `&2`; `\x. (f:num->real^N->real^K) n x - u x`;
                     `&m`] LNORM_MUL) THEN
      ASM_REWRITE_TAC[REAL_ARITH `~(&2 = &0)`; REAL_ABS_NUM] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^N->bool` THEN
      ASM_SIMP_TAC[REAL_POS; LSPACE_CMUL; NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_NUM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&m`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REALLIM_NULL_LMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC WAN_DIR_CONT THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_REWRITE_TAC[]]);;

let WAN_HARDY_BALL = prove
 (`!(n:N->bool) (kk:K->bool). WAN_HARDY_BALL_STATEMENT n kk`,
  REWRITE_TAC[WAN_HARDY_BALL_STATEMENT] THEN REPEAT GEN_TAC THEN
  EXISTS_TAC `&4` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `r:real`; `u:real^N->real^K`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. (\x. lift(norm(min (inv(r - norm(x - a))) (&m) % (u:real^N->real^K) x) pow 2))
          integrable_on ball(a:real^N,r) /\
        drop(integral (ball(a,r))
               (\x. lift(norm(min (inv(r - norm(x - a))) (&m) % u x) pow 2)))
        <= &4 * wan_dir (ball(a,r)) u`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `r:real`; `u:real^N->real^K`; `m:num`] WAN_HARDY_TRUNC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE] THEN
    MP_TAC(ISPECL [`\x. min (inv(r - norm(x - a))) (&m) % (u:real^N->real^K) x`;
                   `ball(a:real^N,r)`] WAN_SOB_LNORM2_SQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\m x. lift(norm(min (inv(r - norm(x - a))) (&m) %
                               (u:real^N->real^K) x) pow 2)`;
                 `\x. lift(norm((u:real^N->real^K) x) pow 2 / (r - norm(x - a:real^N)) pow 2)`;
                 `ball(a:real^N,r)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`m:num`; `x:real^N`] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`a:real^N`; `r:real`; `m:num`] WAN_HARDY_WEIGHT) THEN
      MP_TAC(ISPECL [`a:real^N`; `r:real`; `SUC m`] WAN_HARDY_WEIGHT) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[LIFT_DROP; NORM_MUL; REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= w ==> abs w = w`] THEN
      MATCH_MP_TAC(REAL_ARITH `m <= m' ==> min c m <= min c m'`) THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      MP_TAC(SPEC `inv(r - norm(x - a:real^N))` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `N:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`a:real^N`; `r:real`; `m:num`] WAN_HARDY_WEIGHT) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `min (inv(r - norm(x - a:real^N))) (&m) = inv(r - norm(x - a))`
      SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ARITH `min a b = a <=> a <= b`] THEN
        TRANS_TAC REAL_LE_TRANS `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        ALL_TAC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[NORM_MUL; REAL_POW_MUL; real_div; REAL_INV_POW] THEN
      ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < d ==> abs d = d`] THEN
      REWRITE_TAC[REAL_MUL_SYM];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC; IN_UNIV] THEN
      EXISTS_TAC `&4 * wan_dir (ball(a:real^N,r)) (u:real^N->real^K) + &1` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`ball(a:real^N,r)`; `u:real^N->real^K`] WAN_DIR_POS) THEN
        ASM_MESON_TAC[wan_w120; REAL_ARITH `&0 <= d ==> &0 < &4 * d + &1`];
        X_GEN_TAC `m:num` THEN
        FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `m:num`) THEN
        REWRITE_TAC[NORM_REAL; GSYM drop] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y + &1`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
        ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2]]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_UBOUND) THEN
  EXISTS_TAC `\m. integral (ball(a:real^N,r))
                    (\x. lift(norm(min (inv(r - norm(x - a))) (&m) %
                                   (u:real^N->real^K) x) pow 2))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_REWRITE_TAC[]);;

