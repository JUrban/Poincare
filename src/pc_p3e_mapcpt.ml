(* ========================================================================= *)
(* Unit pc_p3e_mapcpt (for MT Prop 15.2): sequences of isometries between    *)
(* converging metrics on Euclidean domains.  Uniform jet bounds on compact   *)
(* sets from the near calculus; first-derivative bounds of isometries from   *)
(* two-sided bounds of the metrics; location control for isometries between  *)
(* near-cylinders (log of the norm is Lipschitz in the log-radius); higher   *)
(* jets by P2CT_ISOM_JET; a convergent subsequence by P2CS_JET_SUBSEQ;       *)
(* rescaled pullbacks of near-cylinder families by convergent maps converge  *)
(* to cylinders.                                                             *)
(* ========================================================================= *)

needs "src/pc_p3e_cylrig.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Uniform bounds.  Jet bounds of near-convergent sequences                  *)
(* hold uniformly on compact sets (sequential compactness); inverse-metric   *)
(* and first-derivative bounds of isometries from two-sided bounds of the    *)
(* quadratic forms (general constants; the Part 2C units use the constants   *)
(* 2 and 1/2).                                                               *)
(* ------------------------------------------------------------------------- *)

let P3E_NEAR_UNIF_JETN = prove
 (`!K (Fs:num->real^M->real^N) f.
     compact K /\ (!z. z IN K ==> p2ci_near z Fs f)
     ==> !m. ?B N. !n y. N <= n /\ y IN K ==> pde_jetn m (Fs n) y <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
  DISCH_THEN(MP_TAC o GEN `j:num` o SPECL [`&j:real`; `j:num`]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->num` (X_CHOOSE_THEN `yy:num->real^M`
    (LABEL_TAC "BAD"))) THEN
  UNDISCH_TAC `compact(K:real^M->bool)` THEN REWRITE_TAC[compact] THEN
  DISCH_THEN(MP_TAC o SPEC `yy:num->real^M`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M` (X_CHOOSE_THEN `rr:num->num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p2ci_near (l:real^M) (Fs:num->real^M->real^N) f` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (MP_TAC o SPEC `m:num`) (K ALL_TAC)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (X_CHOOSE_THEN `N:num` (LABEL_TAC "JB"))) THEN
  UNDISCH_TAC `(((yy:num->real^M) o rr) --> l) sequentially` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  ABBREV_TAC `i = N + N1 + N2:num` THEN
  SUBGOAL_THEN `i <= (rr:num->num) i` ASSUME_TAC THENL
   [ASM_MESON_TAC[MONOTONE_BIGGER]; ALL_TAC] THEN
  USE_THEN "BAD" (MP_TAC o SPEC `(rr:num->num) i`) THEN STRIP_TAC THEN
  USE_THEN "JB" (MP_TAC o SPECL [`(nn:num->num) (rr(i:num))`; `(yy:num->real^M) (rr(i:num))`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `N + N1 + N2 = (i:num)` THEN UNDISCH_TAC `i <= (rr:num->num) i` THEN
      UNDISCH_TAC `(rr:num->num) i <= nn(rr i)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `N + N1 + N2 = (i:num)` THEN UNDISCH_TAC `i <= (rr:num->num) i` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N2 <= &((rr:num->num) i)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `N + N1 + N2 = (i:num)` THEN UNDISCH_TAC `i <= (rr:num->num) i` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_G_GINV = prove
 (`!U (G:real^N->real^N^N) z v.
     metric_field U G /\ z IN U
     ==> G z ** (matrix_inv(G z) ** v) = v /\ matrix_inv(G z) ** (G z ** v) = v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) z)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]);;

let P3E_GINV_NORM_GEN = prove
 (`!U (G:real^N->real^N^N) z be.
     metric_field U G /\ z IN U /\ &0 < be /\
     (!a. be * (a dot a) <= a dot (G z ** a))
     ==> !b. norm(matrix_inv(G z) ** b) <= norm b / be`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `b:real^N` THEN
  ABBREV_TAC `v = matrix_inv((G:real^N->real^N^N) z) ** b` THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) z ** v = b` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN ASM_MESON_TAC[P3E_G_GINV]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`v:real^N`; `b:real^N`] NORM_CAUCHY_SCHWARZ) THEN
  REWRITE_TAC[DOT_SQUARE_NORM] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ASM_CASES_TAC `norm(v:real^N) = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN MP_TAC(ISPEC `b:real^N` NORM_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(v:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(v:real^N) * (be * norm v) <= norm v * norm(b:real^N)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC]);;

let P3E_ISOM_DT_BOUND_GEN = prove
 (`!(Tm:real^N->real^N) G H z al be.
     G z = mpullback Tm H z /\ Tm differentiable at z /\ &0 < be /\
     (!a. a dot (G z ** a) <= al * (a dot a)) /\
     (!a. be * (a dot a) <= a dot (H (Tm z) ** a))
     ==> !i. 1 <= i /\ i <= dimindex(:N)
             ==> norm(partial_derivative i Tm z) pow 2 <= al / be`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[partial_derivative] THEN
  ABBREV_TAC `v = frechet_derivative (Tm:real^N->real^N) (at z) (basis i)` THEN
  SUBGOAL_THEN `basis i dot ((G:real^N->real^N^N) z ** basis i) =
                v dot ((H:real^N->real^N^N) (Tm z) ** v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "v" THEN MATCH_MP_TAC LRG_MPULLBACK_DOT THEN
    UNDISCH_TAC `(Tm:real^N->real^N) differentiable at z` THEN
    REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[has_derivative]);
    ALL_TAC] THEN
  SUBGOAL_THEN `basis i dot basis i:real^N = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS; BASIS_COMPONENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; NORM_POW_2] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P3E_GINV_VEC_GEN = prove
 (`!U (G:real^N->real^N^N) z be.
     metric_field U G /\ z IN U /\ &0 < be /\
     (!a. be * (a dot a) <= a dot (G z ** a))
     ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (matrix_inv(G z))) <=
         &(dimindex(:(N,N)finite_prod)) / be`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[real_div] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_PROD]) THEN
  ASM_SIMP_TAC[VECTORIZE_COMPONENT] THEN
  ABBREV_TAC `a = 1 + (q - 1) DIV dimindex(:N)` THEN
  ABBREV_TAC `b = 1 + (q - 1) MOD dimindex(:N)` THEN
  SUBGOAL_THEN `1 <= a /\ a <= dimindex(:N) /\ 1 <= b /\ b <= dimindex(:N)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    SUBGOAL_THEN `~(dimindex(:N) = 0)` MP_TAC THENL [REWRITE_TAC[DIMINDEX_NONZERO]; ALL_TAC] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[ARITH_RULE `1 <= 1 + n`; ARITH_RULE `1 + a <= n <=> a < n`;
                                RDIV_LT_EQ; MOD_LT_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `be:real`]
         P3E_GINV_NORM_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `basis b:real^N`) THEN
  ASM_SIMP_TAC[NORM_BASIS; MATRIX_VECTOR_MUL_BASIS] THEN
  MP_TAC(ISPECL [`column b (matrix_inv((G:real^N->real^N^N) z))`; `a:num`] COMPONENT_LE_NORM) THEN
  ASM_SIMP_TAC[column; LAMBDA_BETA] THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Location control.  If |Df(z) v| <= C |f z| |v| / |z| on a segment staying *)
(* at norm >= m > 0, then log |f| changes by at most C |b - a| / m along it  *)
(* (DIFFERENTIABLE_BOUND for lift o log o (f dot f)).                        *)
(* ------------------------------------------------------------------------- *)

let P3E_LOGDOT_DERIV = prove
 (`!(f:real^N->real^N) z.
     f differentiable at z /\ ~(f z = vec 0)
     ==> ((\x. lift(log(f x dot f x))) has_derivative
          (\v. inv(f z dot f z) %
               (lift(f z dot frechet_derivative f (at z) v) +
                lift(frechet_derivative f (at z) v dot f z)))) (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (f:real^N->real^N) z dot f z` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. lift((f:real^N->real^N) x dot f x)) has_derivative
     (\v. lift(f z dot frechet_derivative f (at z) v) +
          lift(frechet_derivative f (at z) v dot f z))) (at z)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x y:real^N. lift(x dot y)`; `f:real^N->real^N`;
                   `f:real^N->real^N`; `frechet_derivative (f:real^N->real^N) (at z)`;
                   `frechet_derivative (f:real^N->real^N) (at z)`; `z:real^N`]
           HAS_DERIVATIVE_BILINEAR_AT) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((lift o log o drop) has_derivative (\x:real^1. inv((f:real^N->real^N) z dot f z) % x))
    (at (lift(f z dot f z)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((f:real^N->real^N) x dot f x)`; `lift o log o drop`;
                 `\v. lift((f:real^N->real^N) z dot frechet_derivative f (at z) v) +
                      lift(frechet_derivative f (at z) v dot f z)`;
                 `\x:real^1. inv((f:real^N->real^N) z dot f z) % x`; `z:real^N`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF; LIFT_DROP]);;

let P3E_LOGNORM_SEGMENT = prove
 (`!(f:real^N->real^N) a b C m.
     &0 < m /\ &0 <= C /\
     (!z. z IN segment[a,b]
          ==> m <= norm z /\ ~(f z = vec 0) /\ f differentiable at z /\
              (!v. norm(frechet_derivative f (at z) v) <= C * norm(f z) * norm v / norm z))
     ==> abs(log(norm(f b)) - log(norm(f a))) <= C / m * norm(b - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. lift(log((f:real^N->real^N) x dot f x))`;
    `\z (v:real^N). inv((f:real^N->real^N) z dot f z) %
                    (lift(f z dot frechet_derivative f (at z) v) +
                     lift(frechet_derivative f (at z) v dot f z))`;
    `segment[a:real^N,b]`; `&2 * C / m`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC P3E_LOGDOT_DERIV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `linear(frechet_derivative (f:real^N->real^N) (at z))` ASSUME_TAC THENL
     [ASM_MESON_TAC[FRECHET_DERIVATIVE_WORKS; has_derivative]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm((f:real^N->real^N) z)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(z:real^N)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC
     `\v:real^N. inv((f:real^N->real^N) z dot f z) %
                 (lift(f z dot frechet_derivative f (at z) v) +
                  lift(frechet_derivative f (at z) v dot f z))` ONORM) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[linear] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
      REWRITE_TAC[DOT_RADD; DOT_LADD; DOT_RMUL; DOT_LMUL; LIFT_ADD; LIFT_CMUL] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN X_GEN_TAC `v:real^N` THEN BETA_TAC THEN
    ABBREV_TAC `w = frechet_derivative (f:real^N->real^N) (at z) v` THEN
    SUBGOAL_THEN `lift((f:real^N->real^N) z dot w) + lift(w dot f z) = &2 % lift(w dot f z)`
    SUBST1_TAC THENL [REWRITE_TAC[DOT_SYM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL; NORM_LIFT; REAL_ABS_INV; REAL_ABS_NUM] THEN
    SUBGOAL_THEN `abs((f:real^N->real^N) z dot f z) = norm(f z) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_POW_2; REAL_ABS_REFL; DOT_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(w dot (f:real^N->real^N) z) <=
      C * norm(f z) pow 2 * norm(v:real^N) / norm(z:real^N)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(w:real^N) * norm((f:real^N->real^N) z)` THEN
      REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(C * norm((f:real^N->real^N) z) * norm(v:real^N) / norm(z:real^N)) *
                  norm(f z)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        EXPAND_TAC "w" THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(norm(z:real^N)) <= inv m` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(norm((f:real^N->real^N) z) pow 2) *
                (&2 * (C * norm(f z) pow 2 * norm(v:real^N) / norm(z:real^N)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `inv(norm((f:real^N->real^N) z) pow 2) *
      (&2 * (C * norm(f z) pow 2 * norm(v:real^N) / norm(z:real^N))) =
      (&2 * C * norm v) * inv(norm z)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < norm((f:real^N->real^N) z)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * C / m) * norm(v:real^N) = (&2 * C * norm v) * inv m` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_POS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`b:real^N`; `a:real^N`]) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT; GSYM LIFT_SUB; NORM_LIFT] THEN
  SUBGOAL_THEN `!x:real^N. x IN segment[a,b] ==> log(norm((f:real^N->real^N) x)) =
                                                  log(f x dot f x) / &2`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC LOG_SQRT THEN
    REWRITE_TAC[DOT_POS_LT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[NORM_SUB] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P3E_CHORD_NORM = prove
 (`!p q z:real^N.
     norm p = &1 /\ norm q = &1 /\ &0 <= p dot q /\ z IN segment[p,q]
     ==> inv(sqrt(&2)) <= norm z /\ norm z <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((&1 - t) % p:real^N) + norm(t % q:real^N)` THEN
    REWRITE_TAC[NORM_TRIANGLE; NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&2)) = sqrt(inv(&2))` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_INV]; ALL_TAC] THEN
  REWRITE_TAC[vector_norm] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  SUBGOAL_THEN `(p:real^N) dot p = &1 /\ (q:real^N) dot q = &1` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_SQUARE_NORM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N) dot p = p dot q` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= t * (&1 - t) * ((p:real^N) dot q)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2) <= (&1 - t) pow 2 + t pow 2` MP_TAC THENL
   [MP_TAC(SPEC `&2 * t - &1` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let P3E_RAY_NORM = prove
 (`!y z:real^N.
     ~(y = vec 0) /\ z IN segment[inv(norm y) % y,y]
     ==> min (norm y) (&1) <= norm z /\ norm z <= max (norm y) (&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB; NORM_MUL] THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((&1 - t) * inv(norm(y:real^N)) + t) * norm y = (&1 - t) + t * norm y`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 - t) * inv(norm(y:real^N)) + t` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    UNDISCH_TAC `&0 < norm(y:real^N)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `a = norm(y:real^N)` THEN
  ABBREV_TAC `mm = min a (&1)` THEN ABBREV_TAC `MM = max a (&1)` THEN
  SUBGOAL_THEN `mm <= a /\ a <= MM /\ mm <= &1 /\ &1 <= MM` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["mm"; "MM"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * mm <= t * a /\ t * a <= t * MM` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) * mm <= (&1 - t) * &1 /\ (&1 - t) * &1 <= (&1 - t) * MM`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P3E_UNIT_BETWEEN = prove
 (`!u y0:real^N.
     2 <= dimindex(:N) /\ norm u = &1 /\ norm y0 = &1
     ==> ?w. norm w = &1 /\ &0 <= u dot w /\ &0 <= w dot y0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u + y0:real^N = vec 0` THENL
   [MP_TAC(ISPEC `y0:real^N` ORTHOGONAL_TO_VECTOR_EXISTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv(norm v) % v:real^N` THEN
    SUBGOAL_THEN `u:real^N = --y0` SUBST1_TAC THENL
     [UNDISCH_TAC `u + y0:real^N = vec 0` THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(y0:real^N) dot v = &0 /\ (v:real^N) dot y0 = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `orthogonal (y0:real^N) v` THEN REWRITE_TAC[orthogonal] THEN
      MESON_TAC[DOT_SYM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NORM_MUL; DOT_LMUL; DOT_RMUL; DOT_LNEG; REAL_ABS_INV; REAL_ABS_NORM;
                    REAL_MUL_RZERO; REAL_NEG_0; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `inv(norm(u + y0)) % (u + y0:real^N)` THEN
  SUBGOAL_THEN `&0 < norm(u + y0:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((u:real^N) dot y0) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^N`; `y0:real^N`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    ASM_REWRITE_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) dot u = &1 /\ (y0:real^N) dot y0 = &1 /\ y0 dot u = u dot y0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_SQUARE_NORM; DOT_SYM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_MUL; DOT_LMUL; DOT_RMUL; DOT_LADD; DOT_RADD; REAL_ABS_INV;
                  REAL_ABS_NORM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC]);;

let P3E_LOGNORM_PATH = prove
 (`!(f:real^N->real^N) U C y0 y.
     2 <= dimindex(:N) /\ &0 <= C /\ norm y0 = &1 /\ ~(y = vec 0) /\
     {z | min (norm y) (inv(sqrt(&2))) <= norm z /\ norm z <= max (norm y) (&1)}
     SUBSET U /\
     (!z. z IN U
          ==> ~(f z = vec 0) /\ f differentiable at z /\
              (!v. norm(frechet_derivative f (at z) v) <= C * norm(f z) * norm v / norm z))
     ==> abs(log(norm(f y)) - log(norm(f y0))) <=
         C * (abs(norm y - &1) / min (norm y) (&1) + &6)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = inv(norm(y:real^N)) % y` THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(u:real^N) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N`; `y0:real^N`] P3E_UNIT_BETWEEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < inv(sqrt(&2))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(sqrt(&2)) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_LE_RSQRT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `C / inv(sqrt(&2)) * &2 <= &3 * C` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_INV] THEN
    SUBGOAL_THEN `sqrt(&2) <= &3 / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `C * sqrt(&2) <= C * &3 / &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the three segments *)
  SUBGOAL_THEN
   `abs(log(norm((f:real^N->real^N) y)) - log(norm(f u))) <=
    C / min (norm y) (&1) * abs(norm y - &1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(y - u:real^N) = abs(norm y - &1)` (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "u" THEN
      REWRITE_TAC[VECTOR_ARITH `y - c % y:real^N = (&1 - c) % y`; NORM_MUL] THEN
      SUBGOAL_THEN `abs(&1 - inv(norm(y:real^N))) * norm y =
                    abs((&1 - inv(norm y)) * norm y)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM]; ALL_TAC] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `&0 < norm(y:real^N)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC P3E_LOGNORM_SEGMENT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`y:real^N`; `z:real^N`] P3E_RAY_NORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_MESON_TAC[SEGMENT_SYM];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q:real^N. norm p = &1 /\ norm q = &1 /\ &0 <= p dot q
                 ==> abs(log(norm((f:real^N->real^N) q)) - log(norm(f p))) <= &3 * C`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C / inv(sqrt(&2)) * norm(q - p:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC P3E_LOGNORM_SEGMENT THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `z:real^N`] P3E_CHORD_NORM) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C / inv(sqrt(&2)) * &2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(q:real^N) + norm(p:real^N)` THEN
      REWRITE_TAC[NORM_ARITH `norm(q - p:real^N) <= norm q + norm p`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`u:real^N`; `w:real^N`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `y0:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `C / min (norm(y:real^N)) (&1) * abs(norm y - &1) =
                C * (abs(norm y - &1) / min (norm y) (&1))` MP_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `abs(log(norm((f:real^N->real^N) y)) - log(norm(f u))) <=
               C / min (norm y) (&1) * abs(norm y - &1)` THEN
  REAL_ARITH_TAC);;

let P3E_CONFORMAL_ISOM_DERIV = prove
 (`!(psi:real^N->real^N) (A:real^N->real^N^N) (B:real^N->real^N^N) z al be.
     A z = mpullback psi B z /\ psi differentiable at z /\
     ~(z = vec 0) /\ ~(psi z = vec 0) /\ &0 <= al /\ &0 < be /\
     (!a. a dot (A z ** a) <= al * (&2 / norm z pow 2) * (a dot a)) /\
     (!a. be * (&2 / norm(psi z) pow 2) * (a dot a) <= a dot (B (psi z) ** a))
     ==> !v. norm(frechet_derivative psi (at z) v) <=
             sqrt(al / be) * norm(psi z) * norm v / norm z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `linear(frechet_derivative (psi:real^N->real^N) (at z))` ASSUME_TAC THENL
   [ASM_MESON_TAC[FRECHET_DERIVATIVE_WORKS; has_derivative]; ALL_TAC] THEN
  ABBREV_TAC `w = frechet_derivative (psi:real^N->real^N) (at z) v` THEN
  SUBGOAL_THEN
   `(v:real^N) dot ((A:real^N->real^N^N) z ** v) =
    (w:real^N) dot ((B:real^N->real^N^N) ((psi:real^N->real^N) z) ** w)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "w" THEN MATCH_MP_TAC LRG_MPULLBACK_DOT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:real^N) pow 2 /\ &0 < norm((psi:real^N->real^N) z) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `be * (&2 / norm((psi:real^N->real^N) z) pow 2) * norm(w:real^N) pow 2 <=
    al * (&2 / norm(z:real^N) pow 2) * norm(v:real^N) pow 2`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `(v:real^N) dot ((A:real^N->real^N^N) z ** v) =
      (w:real^N) dot ((B:real^N->real^N^N) ((psi:real^N->real^N) z) ** w)` THEN
    MP_TAC(SPEC `w:real^N` (ASSUME
     `!a:real^N. be * (&2 / norm((psi:real^N->real^N) z) pow 2) * (a dot a) <=
                 a dot ((B:real^N->real^N^N) (psi z) ** a)`)) THEN
    MP_TAC(SPEC `v:real^N` (ASSUME
     `!a:real^N. a dot ((A:real^N->real^N^N) z ** a) <=
                 al * (&2 / norm(z:real^N) pow 2) * (a dot a)`)) THEN
    REWRITE_TAC[NORM_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = norm((psi:real^N->real^N) z) pow 2` THEN
  ABBREV_TAC `Z = norm(z:real^N) pow 2` THEN
  SUBGOAL_THEN `norm(w:real^N) pow 2 <= (al / be) * (P / Z) * norm(v:real^N) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(P / (&2 * be)) * (al * (&2 / Z) * norm(v:real^N) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(P / (&2 * be)) * (be * (&2 / P) * norm(w:real^N) pow 2)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        UNDISCH_TAC `&0 < be` THEN UNDISCH_TAC `&0 < P` THEN CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < be` THEN UNDISCH_TAC `&0 < Z` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN REWRITE_TAC[ARITH_EQ] THEN
  SUBGOAL_THEN `&0 <= al / be` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
  UNDISCH_TAC `norm(w:real^N) pow 2 <= (al / be) * (P / Z) * norm(v:real^N) pow 2` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A convergent subsequence of isometries.  Isometries                       *)
(* psis n : Us n -> Vs n (exact, As n = mpullback (psis n) (Bs n)) with      *)
(* uniform jet bounds of the metrics at z and at psis n z, two-sided        *)
(* quadratic-form bounds and bounded images on ball(y0,2r) have jets         *)
(* bounded uniformly there (P2CT_ISOM_JET, P2CT_JETN_SUC_BOUND), so a        *)
(* subsequence converges in the near calculus at y0 (P2CS_JET_SUBSEQ).      *)
(* ------------------------------------------------------------------------- *)

let P3E_ISOM_JET_BOUND = prove
 (`!(psis:num->real^N->real^N) psis' Us Vs (As:num->real^N->real^N^N) Bs y0 r.
     &0 < r /\
     (!n. diffeomorphism_on (Us n) (Vs n) (psis n) (psis' n) /\
          metric_field (Us n) (As n) /\ metric_field (Vs n) (Bs n) /\
          (!z. z IN Us n ==> As n z = mpullback (psis n) (Bs n) z)) /\
     (?N. !n. N <= n ==> ball(y0,&2 * r) SUBSET Us n) /\
     (!m. ?B N. !n z. N <= n /\ z IN ball(y0,&2 * r)
                      ==> pde_jetn m (vectorize o As n) z <= B /\
                          pde_jetn m (vectorize o Bs n) (psis n z) <= B) /\
     (?al be N. &0 < be /\
        !n z a. N <= n /\ z IN ball(y0,&2 * r)
                ==> a dot (As n z ** a) <= al * (a dot a) /\
                    be * (a dot a) <= a dot (As n z ** a) /\
                    be * (a dot a) <= a dot (Bs n (psis n z) ** a)) /\
     (?M N. !n z. N <= n /\ z IN ball(y0,&2 * r) ==> norm(psis n z) <= M)
     ==> !m. ?B N. !n z. N <= n /\ z IN ball(y0,&2 * r) ==> pde_jetn m (psis n) z <= B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "D")
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N1:num` (LABEL_TAC "SUB")) (CONJUNCTS_THEN2 (LABEL_TAC "JB")
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `al:real` (X_CHOOSE_THEN `be:real` (X_CHOOSE_THEN `N2:num`
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QF")))))
      (X_CHOOSE_THEN `M:real` (X_CHOOSE_THEN `N3:num` (LABEL_TAC "LOC")))))))) THEN
  INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`M:real`; `N3:num`] THEN REWRITE_TAC[P2CT_JETN_0] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "JB" (X_CHOOSE_THEN `B:real` (X_CHOOSE_THEN `N4:num` (LABEL_TAC "JBM")) o
                 SPEC `SUC m`) THEN
  SUBGOAL_THEN `&0 <= al` ASSUME_TAC THENL
   [USE_THEN "QF" (MP_TAC o SPECL [`N2:num`; `y0:real^N`; `basis 1:real^N`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LE_REFL; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    UNDISCH_TAC `&0 < be` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `B:real`; `&(dimindex(:(N,N)finite_prod)) / be`;
                 `sqrt(al / be)`] P2CT_ISOM_JET) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `M + &(CARD(pde_index_lists (SUC m) (:N))) * (&(dimindex(:N)) * C)` THEN
  EXISTS_TAC `N1 + N2 + N3 + N4:num` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((psis:num->real^N->real^N) n z) +
              &(CARD(pde_index_lists (SUC m) (:N))) *
              sum(1..dimindex(:N)) (\i. pde_jetn m (partial_derivative i (psis n)) z)` THEN
  REWRITE_TAC[P2CT_JETN_SUC_BOUND] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [USE_THEN "LOC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `z IN (Us:num->real^N->bool) n` ASSUME_TAC THENL
   [USE_THEN "SUB" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
  SUBGOAL_THEN
   `!a:real^N. a dot ((As:num->real^N->real^N^N) n z ** a) <= al * (a dot a) /\
               be * (a dot a) <= a dot (As n z ** a) /\
               be * (a dot a) <=
               a dot ((Bs:num->real^N->real^N^N) n ((psis:num->real^N->real^N) n z) ** a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN USE_THEN "QF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "JBM" (MP_TAC o SPECL [`n:num`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(psis:num->real^N->real^N) n z IN Vs n` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on; FUN_IN_IMAGE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(Us:num->real^N->bool) n`; `(Vs:num->real^N->bool) n`;
    `(psis:num->real^N->real^N) n`; `(psis':num->real^N->real^N) n`;
    `(As:num->real^N->real^N^N) n`; `(Bs:num->real^N->real^N^N) n`; `z:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P3E_GINV_VEC_GEN THEN EXISTS_TAC `(Us:num->real^N->bool) n` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC P3E_GINV_VEC_GEN THEN EXISTS_TAC `(Vs:num->real^N->bool) n` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_RSQRT THEN
      MP_TAC(ISPECL [`(psis:num->real^N->real^N) n`; `(As:num->real^N->real^N^N) n`;
                     `(Bs:num->real^N->real^N^N) n`; `z:real^N`; `al:real`; `be:real`]
             P3E_ISOM_DT_BOUND_GEN) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `(Us:num->real^N->bool) n` THEN
        ASM_MESON_TAC[diffeomorphism_on];
        DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]]);;

let P3E_ISOM_SUBSEQ = prove
 (`!(psis:num->real^N->real^N) psis' Us Vs (As:num->real^N->real^N^N) Bs y0 r.
     &0 < r /\
     (!n. diffeomorphism_on (Us n) (Vs n) (psis n) (psis' n) /\
          metric_field (Us n) (As n) /\ metric_field (Vs n) (Bs n) /\
          (!z. z IN Us n ==> As n z = mpullback (psis n) (Bs n) z)) /\
     (?N. !n. N <= n ==> ball(y0,&2 * r) SUBSET Us n) /\
     (!m. ?B N. !n z. N <= n /\ z IN ball(y0,&2 * r)
                      ==> pde_jetn m (vectorize o As n) z <= B /\
                          pde_jetn m (vectorize o Bs n) (psis n z) <= B) /\
     (?al be N. &0 < be /\
        !n z a. N <= n /\ z IN ball(y0,&2 * r)
                ==> a dot (As n z ** a) <= al * (a dot a) /\
                    be * (a dot a) <= a dot (As n z ** a) /\
                    be * (a dot a) <= a dot (Bs n (psis n z) ** a)) /\
     (?M N. !n z. N <= n /\ z IN ball(y0,&2 * r) ==> norm(psis n z) <= M)
     ==> ?sub psi. (!m n. m < n ==> sub m < sub n) /\
                   p2ci_near y0 (\n. psis (sub n)) psi`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "JET" o MATCH_MP P3E_ISOM_JET_BOUND) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "D")
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N1:num` (LABEL_TAC "SUB")) (K ALL_TAC)))) THEN
  SUBGOAL_THEN
   `!n. N1 <= n ==> smooth_map_on (ball(y0:real^N,&2 * r)) ((psis:num->real^N->real^N) n)`
  (LABEL_TAC "SM") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(Us:num->real^N->bool) n` THEN
    USE_THEN "SUB" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(i:num) n. (psis:num->real^N->real^N) n`;
                 `\i:num. ball(y0:real^N,&2 * r)`; `\i:num. (y0:real^N)`; `\i:num. (r:real)`]
                P2CS_JET_SUBSEQ) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[NUM_COUNTABLE];
      GEN_TAC THEN REWRITE_TAC[OPEN_BALL; SUBSET; IN_CBALL; IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN EXISTS_TAC `N1:num` THEN ASM_REWRITE_TAC[];
      REPEAT GEN_TAC THEN USE_THEN "JET" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sub:num->num` (X_CHOOSE_THEN `H:num->real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`sub:num->num`; `(H:num->real^N->real^N) 0`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `r:real` THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `N1:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(y0:real^N,&2 * r)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "SM" MATCH_MP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_MESON_TAC[MONOTONE_BIGGER]]);;

(* ------------------------------------------------------------------------- *)
(* Rescaled pullbacks of near-cylinder families by convergent                *)
(* maps.  Limits in the near calculus are unique; scalar multiples by        *)
(* convergent real sequences converge; if cs n psis n pulls Hs0 n back to   *)
(* Qs n -> cyl(a), with Hs0 n -> cyl(0) and psis n -> psi, then            *)
(* cs n psis n pulls Hss n -> cyl(sig) back to a sequence converging to    *)
(* cyl(a + c sig) (affine form of the cylinder flow and Ricci convergence; *)
(* no classification of the limit map).                                     *)
(* ------------------------------------------------------------------------- *)

let P3E_NEAR_UNIQUE = prove
 (`!(z0:real^M) (Fs:num->real^M->real^N) f g.
     p2ci_near z0 Fs f /\ p2ci_near z0 Fs g
     ==> ?r. &0 < r /\ !y. y IN ball(z0,r) ==> f y = g y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "U1"))))))
    (X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "U2"))))))) THEN
  EXISTS_TAC `min r1 r2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^M` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  USE_THEN "U1" (MP_TAC o SPEC `norm((f:real^M->real^N) y - g y) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "V1"))] THEN
  USE_THEN "U2" (MP_TAC o SPEC `norm((f:real^M->real^N) y - g y) / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "V2"))] THEN
  USE_THEN "V1" (MP_TAC o SPECL [`N1 + N2:num`; `y:real^M`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_BALL] THEN ARITH_TAC; DISCH_TAC] THEN
  USE_THEN "V2" (MP_TAC o SPECL [`N1 + N2:num`; `y:real^M`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_BALL] THEN ARITH_TAC; DISCH_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC NORM_ARITH);;

let P3E_NEAR_CMUL_SEQ = prove
 (`!(z0:real^M) (cs:num->real) c (Fs:num->real^M->real^N) f.
     ((\n. lift(cs n)) --> lift c) sequentially /\ p2ci_near z0 Fs f
     ==> p2ci_near z0 (\n z. cs n % Fs n z) (\z. c % f z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(a:real^1) (v:real^N). drop a % v`; `z0:real^M`;
                 `\n:num z:real^M. lift(cs n)`; `\z:real^M. lift c`;
                 `Fs:num->real^M->real^N`; `f:real^M->real^N`] P2CI_NEAR_BILINEAR2) THEN
  REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_NEAR_CONSTSEQ THEN ASM_REWRITE_TAC[]);;

let P3E_NEAR_MAT_CMUL_SEQ = prove
 (`!(z0:real^M) (cs:num->real) c (Xs:num->real^M->real^N^N) X.
     ((\n. lift(cs n)) --> lift c) sequentially /\
     p2ci_near z0 (\n. vectorize o Xs n) (vectorize o X)
     ==> p2ci_near z0 (\n. vectorize o (\z. cs n %% Xs n z)) (vectorize o (\z. c %% X z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF; VECTORIZE_CMUL] THEN
  MP_TAC(ISPECL [`z0:real^M`; `cs:num->real`; `c:real`;
                 `\n:num. (vectorize:real^N^N->real^(N,N)finite_prod) o
                          (Xs:num->real^M->real^N^N) n`;
                 `(vectorize:real^N^N->real^(N,N)finite_prod) o (X:real^M->real^N^N)`]
                P3E_NEAR_CMUL_SEQ) THEN
  ASM_REWRITE_TAC[o_DEF]);;

let P3E_NEAR_MPULLBACK_CYL = prove
 (`!(psis:num->real^3->real^3) psi (y0:real^3) sigs sig.
     p2ci_near y0 psis psi /\ ~(psi y0 = vec 0) /\
     ((\n. lift(sigs n)) --> lift sig) sequentially
     ==> p2ci_near y0 (\n. vectorize o mpullback (psis n) (cylinder_flow (sigs n)))
                      (vectorize o mpullback psi (cylinder_flow sig))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2CI_NEAR_MPULLBACK THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P3E_CYL_SEQ_NEAR THEN ASM_REWRITE_TAC[]);;

let P3E_MNEAR_RICMAT = prove
 (`!(z0:real^N) As A0.
     p2cm_mnear z0 As A0
     ==> p2ci_near z0
           (\n. vectorize o (\z. (lambda i j. lricci (As n) z (basis i) (basis j)):real^N^N))
           (vectorize o (\z. (lambda i j. lricci A0 z (basis i) (basis j)):real^N^N))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2CI_NEAR_MATRIX] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN MATCH_MP_TAC P3E_MNEAR_LRICCI THEN ASM_REWRITE_TAC[]);;

let P3E_RICCI_AFFINE_LIMIT = prove
 (`!(Ns:num->real^3->real^3^3) (Ms:num->real^3->real^3^3) (y0:real^3) a bs b r N.
     ~(y0 = vec 0) /\ a < &1 /\ p2cm_mnear y0 Ns (cylinder_flow a) /\
     ((\n. lift(bs n)) --> lift b) sequentially /\ &0 < r /\
     (!n z. N <= n /\ z IN ball(y0,r)
            ==> Ms n z = Ns n z -
                         (&2 * bs n) %% (lambda i j. lricci (Ns n) z (basis i) (basis j)))
     ==> p2ci_near y0 (\n. vectorize o Ms n) (vectorize o cylinder_flow (a + b))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n z. (vectorize:real^3^3->real^(3,3)finite_prod) ((Ns:num->real^3->real^3^3) n z) +
           --((&2 * bs n) %
              vectorize((lambda i j. lricci (Ns n) z (basis i) (basis j)):real^3^3))`;
    `\z. (vectorize:real^3^3->real^(3,3)finite_prod) (cylinder_flow a z) +
         --((&2 * b) %
            vectorize((lambda i j. lricci (cylinder_flow a) z (basis i) (basis j)):real^3^3))`;
    `min r (norm(y0:real^3))`; `N:num`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; NORM_POS_LT] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_ADD THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [p2cm_mnear]) THEN
      REWRITE_TAC[o_DEF];
      MATCH_MP_TAC P2CI_NEAR_NEG THEN
      MP_TAC(ISPECL [`y0:real^3`; `\n:num. &2 * (bs:num->real) n`; `&2 * b`;
                     `\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o
                              (\z. (lambda i j. lricci ((Ns:num->real^3->real^3^3) n) z
                                                  (basis i) (basis j)):real^3^3)`;
                     `(vectorize:real^3^3->real^(3,3)finite_prod) o
                      (\z. (lambda i j. lricci (cylinder_flow a) z
                                          (basis i) (basis j)):real^3^3)`]
             P3E_NEAR_CMUL_SEQ) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC LIM_CMUL THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`y0:real^3`; `Ns:num->real^3->real^3^3`; `cylinder_flow a`]
               P3E_MNEAR_RICMAT) THEN
        ASM_REWRITE_TAC[o_DEF]]];
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `z IN ball(y0:real^3,r)` ASSUME_TAC THENL
     [UNDISCH_TAC `z IN ball(y0:real^3,min r (norm y0))` THEN
      REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM] THEN
    REWRITE_TAC[VECTORIZE_SUB; VECTORIZE_CMUL] THEN VECTOR_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(y0:real^3,vec 0) < norm y0` THEN CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `z:real^3`] P3E_CYL_SHIFT_AFFINE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`a:real`; `z:real^3`] P3E_CYL_RICMAT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTORIZE_SUB; VECTORIZE_CMUL] THEN VECTOR_ARITH_TAC]);;

let P3E_VECTORIZE_INJ = prove
 (`!m1 m2:real^N^N. vectorize m1 = vectorize m2 ==> m1 = m2`,
  MESON_TAC[MATRIFY_VECTORIZE]);;

let P3E_CYL_PULLBACK_LIMIT = prove
 (`!(psis:num->real^3->real^3) psis' Us Vs psi (y0:real^3) (Qs:num->real^3->real^3^3)
    Hs0 Hss cs c a sigs sig.
     ~(y0 = vec 0) /\
     (!n. diffeomorphism_on (Us n) (Vs n) (psis n) (psis' n) /\
          Vs n SUBSET (:real^3) DELETE vec 0) /\
     p2ci_near y0 psis psi /\ ~(psi y0 = vec 0) /\
     (?r N. &0 < r /\
            !n. N <= n
                ==> ball(y0,r) SUBSET Us n /\
                    !z. z IN ball(y0,r) ==> Qs n z = cs n %% mpullback (psis n) (Hs0 n) z) /\
     p2cm_mnear y0 Qs (cylinder_flow a) /\ a < &1 /\
     p2ci_near (psi y0) (\n. vectorize o Hs0 n) (vectorize o cylinder_flow (&0)) /\
     p2ci_near (psi y0) (\n. vectorize o Hss n) (vectorize o cylinder_flow sig) /\
     ((\n. lift(cs n)) --> lift c) sequentially /\ (!n. &0 < cs n) /\
     ((\n. lift(sigs n)) --> lift sig) sequentially
     ==> p2ci_near y0 (\n. vectorize o (\z. cs n %% mpullback (psis n) (Hss n) z))
                      (vectorize o cylinder_flow (a + c * sig))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "D")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N0:num`
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "QS"))))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))))) THEN
  (* the limit of cs n times the pullback of a convergent metric sequence *)
  SUBGOAL_THEN
   `!(Gs:num->real^3->real^3^3) G.
      p2ci_near (psi y0) (\n. vectorize o Gs n) (vectorize o G)
      ==> p2ci_near y0 (\n. vectorize o (\z. cs n %% mpullback (psis n) (Gs n) z))
                       (vectorize o (\z. c %% mpullback psi G z))`
  (LABEL_TAC "PB") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_NEAR_MAT_CMUL_SEQ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2CI_NEAR_MPULLBACK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* c psi pullback of cyl(0) equals cyl(a) near y0 *)
  SUBGOAL_THEN
   `?r1. &0 < r1 /\
         !z. z IN ball(y0:real^3,r1)
             ==> c %% mpullback psi (cylinder_flow (&0)) z = cylinder_flow a z`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y0:real^3`;
                   `\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o
                            (Qs:num->real^3->real^3^3) n`;
                   `(vectorize:real^3^3->real^(3,3)finite_prod) o cylinder_flow a`;
                   `(vectorize:real^3^3->real^(3,3)finite_prod) o
                    (\z. c %% mpullback psi (cylinder_flow (&0)) z)`] P3E_NEAR_UNIQUE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [p2cm_mnear] o
          check (fun th -> can (find_term ((=) `p2cm_mnear:real^3->(num->real^3->real^3^3)->(real^3->real^3^3)->bool`)) (concl th))) THEN
        REWRITE_TAC[];
        MATCH_MP_TAC P2CI_NEAR_EQ THEN
        MAP_EVERY EXISTS_TAC
         [`\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o
                   (\z. cs n %% mpullback ((psis:num->real^3->real^3) n) (Hs0 n) z)`;
          `(vectorize:real^3^3->real^(3,3)finite_prod) o
           (\z. c %% mpullback psi (cylinder_flow (&0)) z)`;
          `r:real`; `N0:num`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [USE_THEN "PB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
          USE_THEN "QS" (MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3E_VECTORIZE_INJ THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(psi(y0:real^3):real^3,norm(psi y0)) SUBSET (:real^3) DELETE vec 0 /\
                ball(y0:real^3,norm y0) SUBSET (:real^3) DELETE vec 0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_DELETE; IN_UNIV] THEN CONJ_TAC THEN
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(psi(y0:real^3):real^3) /\ &0 < norm(y0:real^3)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  (* the rescaled pullbacks of cyl(0) converge to cyl(a) *)
  SUBGOAL_THEN
   `p2cm_mnear y0
      (\n z. cs n %% mpullback ((psis:num->real^3->real^3) n) (cylinder_flow (&0)) z)
      (cylinder_flow a)`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2cm_mnear] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`min r (norm(y0:real^3))`; `N0:num`] THEN
      ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; OPEN_BALL] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y0:real^3,norm y0)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
      USE_THEN "QS" (MP_TAC o SPEC `n:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `(Us:num->real^3->bool) n` THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
        MAP_EVERY EXISTS_TAC [`(Vs:num->real^3->bool) n`; `(psis':num->real^3->real^3) n`] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01] THEN
        UNDISCH_TAC `diffeomorphism_on ((Us:num->real^3->bool) n) ((Vs:num->real^3->bool) n)
                       ((psis:num->real^3->real^3) n) ((psis':num->real^3->real^3) n)` THEN
        SIMP_TAC[diffeomorphism_on];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y0:real^3,r)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o
               (\z. cs n %% mpullback ((psis:num->real^3->real^3) n) (cylinder_flow (&0)) z)`;
      `(vectorize:real^3^3->real^(3,3)finite_prod) o
       (\z. c %% mpullback psi (cylinder_flow (&0)) z)`;
      `r1:real`; `0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\n:num. cylinder_flow (&0)`; `cylinder_flow (&0)`] (ASSUME
       `!(Gs:num->real^3->real^3^3) G.
          p2ci_near (psi (y0:real^3)) (\n. vectorize o Gs n) (vectorize o G)
          ==> p2ci_near y0 (\n. vectorize o (\z. cs n %% mpullback (psis n) (Gs n) z))
                           (vectorize o (\z. c %% mpullback psi G z))`)) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `norm(psi(y0:real^3):real^3)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `&0` RFB_CYL_METRIC_FIELD) THEN REWRITE_TAC[REAL_LT_01; metric_field] THEN
      SIMP_TAC[];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM]];
    ALL_TAC] THEN
  (* the affine form *)
  MP_TAC(ISPECL
   [`\n z. cs n %% mpullback ((psis:num->real^3->real^3) n) (cylinder_flow (&0)) z`;
    `\n z. cs n %% mpullback ((psis:num->real^3->real^3) n) (cylinder_flow (sigs n)) z`;
    `y0:real^3`; `a:real`; `\n:num. cs n * sigs n`; `c * sig`; `r:real`; `N0:num`]
   P3E_RICCI_AFFINE_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN
      MP_TAC(ISPECL [`sequentially`; `\n:num. lift(sigs n)`; `lift sig`;
                     `cs:num->real`; `c:real`] LIM_MUL) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "D" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    USE_THEN "QS" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(Vs:num->real^3->bool) n`; `(Us:num->real^3->bool) n`;
                   `(psis:num->real^3->real^3) n`; `(psis':num->real^3->real^3) n`;
                   `(cs:num->real) n`; `(sigs:num->real) n`; `z:real^3`]
                  P3E_CYL_SCALED_PULLBACK_AFFINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(y0:real^3,r) SUBSET (Us:num->real^3->bool) n` THEN
      UNDISCH_TAC `z IN ball(y0:real^3,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_ASSOC];
    DISCH_THEN(ASSUME_TAC o BETA_RULE)] THEN
  (* uniqueness: c psi pullback of cyl(sig) is cyl(a + c sig) near y0 *)
  SUBGOAL_THEN
   `?r3. &0 < r3 /\
         !z. z IN ball(y0:real^3,r3)
             ==> c %% mpullback psi (cylinder_flow sig) z = cylinder_flow (a + c * sig) z`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`y0:real^3`;
                   `\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o
                     (\z. cs n %% mpullback ((psis:num->real^3->real^3) n)
                                            (cylinder_flow (sigs n)) z)`;
                   `(vectorize:real^3^3->real^(3,3)finite_prod) o cylinder_flow (a + c * sig)`;
                   `(vectorize:real^3^3->real^(3,3)finite_prod) o
                    (\z. c %% mpullback psi (cylinder_flow sig) z)`] P3E_NEAR_UNIQUE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3E_NEAR_MAT_CMUL_SEQ THEN
      ASM_REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P3E_NEAR_MPULLBACK_CYL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r3:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P3E_VECTORIZE_INJ THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\n:num. (vectorize:real^3^3->real^(3,3)finite_prod) o
             (\z. cs n %% mpullback ((psis:num->real^3->real^3) n) (Hss n) z)`;
    `(vectorize:real^3^3->real^(3,3)finite_prod) o
     (\z. c %% mpullback psi (cylinder_flow sig) z)`;
    `r3:real`; `0`] THEN
  ASM_SIMP_TAC[o_THM] THEN USE_THEN "PB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

