(* ========================================================================= *)
(* Unit pc_p2a_lric: the chart-level Riccati comparison behind MT Prop 6.81  *)
(* and Prop 7.8.  For the L-geodesic system (6.5) of pc_p2a_defs in s = sqrt *)
(* tau, the trace sigma = tr S of the shape operator S = D_s Y Y^-1 of a     *)
(* Jacobi matrix Y satisfies                                                 *)
(*   sigma' = -tr(S^2) - 4 s tr(Ric# S) - Ric(A,A) + 2 s^2 Lap R.           *)
(* This rests on the chart trace identity P2AL_TRACE_ID (spatial part, one  *)
(* metric field) and the time derivative of tr Gamma(A,.) along a local     *)
(* Ricci flow.  Dimension-generic in N.                                      *)
(*                                                                           *)
(* First: the trace of the Christoffel symbols and its linearity.            *)
(* ========================================================================= *)

needs "src/pc_p2a_bvp.ml";;
needs "src/pc_cmp_frame.ml";;

prioritize_real();;
type_invention_error := true;;

(* tr Gamma(v,.) at y: the trace of u |-> christoffel G y v u.              *)

let p2al_tg = new_definition
 `p2al_tg (G:real^N->real^N^N) (y:real^N) (v:real^N) =
    sum(1..dimindex(:N)) (\k. (christoffel G y v (basis k))$k)`;;

let P2AL_TG_MATRIX = prove
 (`!(G:real^N->real^N^N) y v. p2al_tg G y v = trace(matrix(christoffel G y v))`,
  REWRITE_TAC[p2al_tg; LRG_TRACE_MATRIX]);;

(* Linearity of the trace in v (the Christoffel symbols are bilinear).       *)

let P2AL_TG_EXPAND = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U
     ==> p2al_tg G y v = sum(1..dimindex(:N)) (\i. v$i * p2al_tg G y (basis i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2al_tg] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> (christoffel (G:real^N->real^N^N) y v (basis k))$k =
            sum(1..dimindex(:N)) (\i. v$i * (christoffel G y (basis i) (basis k))$k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `\v:real^N. christoffel (G:real^N->real^N^N) y v (basis k)`
                 LINEAR_COMPONENTWISE_EXPANSION) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                    CHRISTOFFEL_BILINEAR) THEN
      ASM_REWRITE_TAC[bilinear] THEN SIMP_TAC[];
      DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `k:num`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_EQ_NUMSEG] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[SUM_LMUL]);;

let P2AL_TG_LINEAR = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> linear (\v. lift(p2al_tg G y v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] CHRISTOFFEL_BILINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[linear; p2al_tg; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
  ASM_SIMP_TAC[BILINEAR_LADD; BILINEAR_LMUL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               SUM_ADD_NUMSEG; SUM_LMUL]);;

(* ========================================================================= *)
(* The divergence of a field G^-1 om (om a covector field) in coordinates:   *)
(* D_k (G^-1 om)^k + tr Gamma(G^-1 om,.) = G^kl (D_k om_l -                  *)
(* om.Gamma(e_k,e_l)) (P2AL_DIV_FORM), from metric compatibility in the form *)
(* LRG_GINV_MDERIV_GINV and an algebraic identity of sums.                   *)
(* ========================================================================= *)

let P2AL_GINV_MATVEC_DERIV = prove
 (`!U (G:real^N->real^N^N) (om:real^N->real^N) y.
     metric_field U G /\ y IN U /\ om differentiable (at y)
     ==> ((\z. matrix_inv(G z) ** om z) has_derivative
          (\h. --(matrix_inv(G y) ** mderiv G y h ** matrix_inv(G y)) ** om y +
               matrix_inv(G y) ** frechet_derivative om (at y) h)) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `U:real^N->bool`; `y:real^N`]
                LRG_HAS_DERIVATIVE_MATRIX_INV) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [metric_field]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`]
                  LRG_METRIC_INVERTIBLE) THEN ASM_SIMP_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`\z. matrix_inv((G:real^N->real^N^N) z)`;
                 `\h. vectorize(--(matrix_inv((G:real^N->real^N^N) y) **
                       matrify (frechet_derivative (vectorize o G) (at y) h) **
                       matrix_inv(G y)))`;
                 `om:real^N->real^N`; `frechet_derivative (om:real^N->real^N) (at y)`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_MATVEC) THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[MATRIFY_VECTORIZE; GSYM mderiv]);;

let P2AL_DIVSUM_ALG = prove
 (`!n (g:num->num->real) (C:num->num->num->real) (w:num->real) (D:num->num->real) M.
     (!k i. 1 <= k /\ k <= n /\ 1 <= i /\ i <= n
            ==> M k i = sum(1..n) (\c. g k c * C k c i) + sum(1..n) (\d. g d i * C k d k)) /\
     (!k c i. 1 <= k /\ k <= n /\ 1 <= c /\ c <= n ==> C k c i = C c k i)
     ==> sum(1..n) (\k. sum(1..n) (\i. --(M k i) * w i) + sum(1..n) (\i. g k i * D k i)) +
         sum(1..n) (\i. sum(1..n) (\l. g i l * w l) * sum(1..n) (\k. C i k k)) =
         sum(1..n) (\k. sum(1..n) (\l. g k l * (D k l - sum(1..n) (\i. w i * C k l i))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(1..n) (\k. sum(1..n) (\i. --((M:num->num->real) k i) * (w:num->real) i) +
                   sum(1..n) (\i. (g:num->num->real) k i * (D:num->num->real) k i)) =
    sum(1..n) (\k. sum(1..n) (\i. g k i * D k i)) -
    sum(1..n) (\k. sum(1..n) (\i. sum(1..n) (\c. g k c * (C:num->num->num->real) k c i * w i))) -
    sum(1..n) (\k. sum(1..n) (\i. sum(1..n) (\d. g d i * C k d k * w i)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_NEG_ADD; REAL_ADD_RDISTRIB; REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM SUM_RMUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `!a a' b b' c:real. a = a' /\ b = b' ==> (--a + --b) + c = c - a' - b'`) THEN
    CONJ_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\i. sum(1..n) (\l. (g:num->num->real) i l * (w:num->real) l) *
                   sum(1..n) (\k. (C:num->num->num->real) i k k)) =
    sum(1..n) (\k. sum(1..n) (\i. sum(1..n) (\d. g d i * C k d k * w i)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_LMUL] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV) [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `k:num`; `k:num`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\k. sum(1..n) (\l. (g:num->num->real) k l *
                    ((D:num->num->real) k l - sum(1..n) (\i. (w:num->real) i *
                                                  (C:num->num->num->real) k l i)))) =
    sum(1..n) (\k. sum(1..n) (\i. g k i * D k i)) -
    sum(1..n) (\k. sum(1..n) (\i. sum(1..n) (\c. g k c * C k c i * w i)))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB; SUM_SUB_NUMSEG; GSYM SUM_LMUL] THEN
    MATCH_MP_TAC(REAL_ARITH `!a a' b b':real. a = a' /\ b = b' ==> a - b = a' - b'`) THEN
    CONJ_TAC THENL [REFL_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2AL_DIV_FORM = prove
 (`!U (G:real^N->real^N^N) (om:real^N->real^N) y.
     metric_field U G /\ y IN U /\ om differentiable (at y)
     ==> sum(1..dimindex(:N))
          (\k. (frechet_derivative (\z. matrix_inv(G z) ** om z) (at y) (basis k))$k) +
         p2al_tg G y (matrix_inv(G y) ** om y) =
         sum(1..dimindex(:N))
          (\k. sum(1..dimindex(:N))
            (\l. matrix_inv(G y)$k$l *
                 ((frechet_derivative om (at y) (basis k))$l -
                  om y dot christoffel G y (basis k) (basis l))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT o
    MATCH_MP P2AL_GINV_MATVEC_DERIV o CONJ (ASSUME `metric_field U (G:real^N->real^N^N)`) o
    CONJ (ASSUME `(y:real^N) IN U`)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `matrix_inv((G:real^N->real^N^N) y) ** om(y:real^N)`] P2AL_TG_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[p2al_tg] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_NEG_COMPONENT; MATRIX_NEG_COMPONENT;
           MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`dimindex(:N)`; `\k l. matrix_inv((G:real^N->real^N^N) y)$k$l`;
     `\k c i. (christoffel (G:real^N->real^N^N) y (basis k) (basis c))$i`;
     `\i. (om:real^N->real^N) y$i`;
     `\k i. (frechet_derivative (om:real^N->real^N) (at y) (basis k))$i`;
     `\k i. (matrix_inv((G:real^N->real^N^N) y) ** mderiv G y (basis k) **
             matrix_inv(G y))$k$i`] P2AL_DIVSUM_ALG)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC LRG_GINV_MDERIV_GINV THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SYM THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The two divergence identities of the trace computation: div grad R = Lap  *)
(* R (P2AL_DIV_GRAD) and, by the contracted Bianchi identity, div(Ric# A) -  *)
(* tr(Ric# Gamma(A,.)) = dR(A)/2 (P2AL_DIV_RICOP).                           *)
(* ========================================================================= *)

let P2AL_LAMBDA_DERIV = prove
 (`!(ff:real^N->num->real) y.
     (!l. 1 <= l /\ l <= dimindex(:N) ==> (\z. lift(ff z l)) differentiable (at y))
     ==> (\z. (lambda l. ff z l):real^N) differentiable (at y) /\
         !h l. 1 <= l /\ l <= dimindex(:N)
               ==> (frechet_derivative (\z. (lambda l. ff z l):real^N) (at y) h)$l =
                   drop(frechet_derivative (\z. lift(ff z l)) (at y) h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\z. (lambda l. (ff:real^N->num->real) z l):real^N) differentiable (at y)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [DIFFERENTIABLE_COMPONENTWISE_AT] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LRG_HAS_DERIVATIVE_COMPONENT o
    GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  DISCH_THEN(MP_TAC o SPEC `l:num`) THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^N`) THEN BETA_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIFT_DROP]);;

let P2AL_DIV_GRAD = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N))
          (\k. (frechet_derivative (\z. p2a_lgradR G z) (at y) (basis k))$k) +
         p2al_tg G y (p2a_lgradR G y) = llap G (lscalar G) y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `om = \z. (lambda l. drop(frechet_derivative (\w. lift(lscalar (G:real^N->real^N^N) w))
                                   (at z) (basis l))):real^N` THEN
  SUBGOAL_THEN `!z:real^N. p2a_lgradR (G:real^N->real^N^N) z = matrix_inv(G z) ** om z`
  ASSUME_TAC THENL
   [EXPAND_TAC "om" THEN REWRITE_TAC[p2a_lgradR]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^N. p2a_lgradR (G:real^N->real^N^N) z) = (\z. matrix_inv(G z) ** om z)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\z l. drop(frechet_derivative (\w. lift(lscalar (G:real^N->real^N^N) w))
                                (at z) (basis l))`; `y:real^N`] P2AL_LAMBDA_DERIV) THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\w. lift(lscalar (G:real^N->real^N^N) w)`;
                   `y:real^N`; `basis l:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[metric_field]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `om:real^N->real^N`; `y:real^N`]
                P2AL_DIV_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[llap] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN
  STRIP_TAC THEN BETA_TAC THEN EXPAND_TAC "om" THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN REFL_TAC);;

let P2AL_LRICCI_RLIN = prove
 (`!U (G:real^N->real^N^N) y a w.
     metric_field U G /\ y IN U
     ==> lricci G y a w = sum(1..dimindex(:N)) (\q. w$q * lricci G y a (basis q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`w:real^N`; `1`] o MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP]);;

let P2AL_LRICCI_LLIN = prove
 (`!U (G:real^N->real^N^N) y a w.
     metric_field U G /\ y IN U
     ==> lricci G y w a = sum(1..dimindex(:N)) (\q. w$q * lricci G y (basis q) a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT1) THEN
  DISCH_THEN(MP_TAC o SPECL [`w:real^N`; `1`] o MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP]);;

let P2AL_TRACE_MATRIX_MUL = prove
 (`!(f:real^N->real^N) (g:real^N->real^N).
     trace(matrix f ** matrix g) =
     sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N)) (\j. (f(basis j))$k * (g(basis k))$j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[matrix; LAMBDA_BETA]);;

let P2AL_DIV_RICOP = prove
 (`!U (G:real^N->real^N^N) y A.
     metric_field U G /\ y IN U
     ==> (sum(1..dimindex(:N))
           (\k. (frechet_derivative (\z. p2a_lricop G z A) (at y) (basis k))$k) +
          p2al_tg G y (p2a_lricop G y A)) -
         trace(matrix(p2a_lricop G y) ** matrix(christoffel G y A)) =
         inv(&2) * drop(frechet_derivative (\z. lift(lscalar G z)) (at y) A)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `om = \z. (lambda l. lricci (G:real^N->real^N^N) z A (basis l)):real^N` THEN
  SUBGOAL_THEN `!z:real^N. p2a_lricop (G:real^N->real^N^N) z A = matrix_inv(G z) ** om z`
  ASSUME_TAC THENL
   [EXPAND_TAC "om" THEN REWRITE_TAC[p2a_lricop]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^N. p2a_lricop (G:real^N->real^N^N) z A) = (\z. matrix_inv(G z) ** om z)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z l. lricci (G:real^N->real^N^N) z A (basis l)`; `y:real^N`]
                P2AL_LAMBDA_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `\m. if m = 1 then A:real^N else basis l` o CONJUNCT2) THEN
    REWRITE_TAC[lric2; ARITH_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `om:real^N->real^N`; `y:real^N`]
                P2AL_DIV_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`]
                LRG_CONTRACTED_BIANCHI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[P2AL_TRACE_MATRIX_MUL] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\k. sum(1..dimindex(:N))
      (\l. matrix_inv((G:real^N->real^N^N) y)$k$l *
           (frechet_derivative (om:real^N->real^N) (at y) (basis k)$l -
            om y dot christoffel G y (basis k) (basis l)))) =
    sum(1..dimindex(:N))
     (\k. sum(1..dimindex(:N))
      (\l. matrix_inv(G y)$k$l *
           (drop(frechet_derivative (\z. lift(lricci G z A (basis l))) (at y) (basis k)) -
            lricci G y A (christoffel G y (basis k) (basis l)))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`;
                   `christoffel (G:real^N->real^N^N) y (basis k) (basis l)`] P2AL_LRICCI_RLIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "om" THEN REWRITE_TAC[dot] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\k. sum(1..dimindex(:N))
      (\j. p2a_lricop (G:real^N->real^N^N) y (basis j)$k * christoffel G y A (basis k)$j)) =
    sum(1..dimindex(:N))
     (\k. sum(1..dimindex(:N))
      (\l. matrix_inv(G y)$k$l * lricci G y (christoffel G y A (basis k)) (basis l)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `!l. lricci (G:real^N->real^N^N) y (christoffel G y A (basis k)) (basis l) =
          sum(1..dimindex(:N))
            (\j. (christoffel G y A (basis k))$j * lricci G y (basis j) (basis l))`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN MATCH_MP_TAC P2AL_LRICCI_LLIN THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[p2a_lricop; MATRIX_VECTOR_MUL_COMPONENT; dot; LAMBDA_BETA] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a c. lnabla 2 (G:real^N->real^N^N) (lric2 G) y
            (\m. if m = 1 then basis a else if m = 2 then A else basis c) =
          drop(frechet_derivative (\z. lift(lricci G z (basis a) A)) (at y) (basis c)) -
          lricci G y (christoffel G y (basis c) (basis a)) A -
          lricci G y (basis a) (christoffel G y (basis c) A)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[lnabla; lric2; ARITH; SUM_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `l:num`; `k:num`]
                LRG_MATRIX_INV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(lricci (G:real^N->real^N^N) z (basis l) A)) (at y) =
    frechet_derivative (\z. lift(lricci G z A (basis l))) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y (basis k) (basis l)`; `A:real^N`]
                LRICCI_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `basis l:real^N`; `christoffel (G:real^N->real^N^N) y (basis k) A`]
                LRICCI_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `basis k:real^N`; `A:real^N`] CHRISTOFFEL_SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The chart trace identity (spatial part, one metric field G,               *)
(* s a real parameter), with GamA = matrix(christoffel G y A),              *)
(* RicM = matrix(p2a_lricop G y), tg = p2al_tg G and lacc the right side of *)
(* (6.5) for the constant family (\t. G):                                   *)
(*   tr D_y lacc + tr(GamA GamA) + 4 s tr(RicM GamA) + D_A tg(A) + tg(lacc)  *)
(*     = -Ric(A,A) + 2 s^2 Lap R - 2 s dR(A)            (P2AL_TRACE_ID).     *)
(* ========================================================================= *)

let P2AL_DTG = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U
     ==> ((\z. lift(p2al_tg G z v)) has_derivative
          (\h. lift(sum(1..dimindex(:N))
                     (\k. (frechet_derivative (\z. christoffel G z v (basis k)) (at y) h)$k))))
         (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2al_tg; LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LRG_HAS_DERIVATIVE_COMPONENT THEN
  REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2AL_RIC_EXPAND = prove
 (`!U (G:real^N->real^N^N) y A.
     metric_field U G /\ y IN U
     ==> lricci G y A A =
         sum(1..dimindex(:N))
           (\k. (frechet_derivative (\z. christoffel G z A A) (at y) (basis k))$k) -
         sum(1..dimindex(:N))
           (\k. (frechet_derivative (\z. christoffel G z A (basis k)) (at y) A)$k) +
         p2al_tg G y (christoffel G y A A) -
         trace(matrix(christoffel G y A) ** matrix(christoffel G y A))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lricci; lriemann; P2AL_TRACE_MATRIX_MUL; p2al_tg] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN
  SUBGOAL_THEN
   `!k. frechet_derivative (\z. christoffel (G:real^N->real^N^N) z (basis k) A) (at y) =
        frechet_derivative (\z. christoffel G z A (basis k)) (at y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\k. christoffel (G:real^N->real^N^N) y (basis k) (christoffel G y A A)$k) =
    sum(1..dimindex(:N)) (\k. christoffel G y (christoffel G y A A) (basis k)$k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\k. christoffel (G:real^N->real^N^N) y A (christoffel G y (basis k) A)$k) =
    sum(1..dimindex(:N)) (\k. sum(1..dimindex(:N))
       (\j. christoffel G y A (basis j)$k * christoffel G y A (basis k)$j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPEC `\w:real^N. christoffel (G:real^N->real^N^N) y A w`
                 LINEAR_COMPONENTWISE_EXPANSION) THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
                    CHRISTOFFEL_BILINEAR) THEN
      ASM_REWRITE_TAC[bilinear] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`christoffel (G:real^N->real^N^N) y (basis k) A`; `k:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                   `basis k:real^N`; `A:real^N`] CHRISTOFFEL_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

let P2AL_LGRADR_DIFF = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> (\z. p2a_lgradR G z) differentiable (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lgradR] THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\h. --(matrix_inv((G:real^N->real^N^N) y) ** mderiv G y h ** matrix_inv(G y)) **
                  ((lambda l. drop(frechet_derivative (\w. lift(lscalar G w)) (at y) (basis l))):real^N) +
                  matrix_inv(G y) **
                  frechet_derivative (\z. (lambda l. drop(frechet_derivative (\w. lift(lscalar G w))
                                                       (at z) (basis l))):real^N) (at y) h` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z. (lambda l. drop(frechet_derivative (\w. lift(lscalar (G:real^N->real^N^N) w))
                                       (at z) (basis l))):real^N`; `y:real^N`]
                P2AL_GINV_MATVEC_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`\z l. drop(frechet_derivative (\w. lift(lscalar (G:real^N->real^N^N) w))
                                (at z) (basis l))`; `y:real^N`] P2AL_LAMBDA_DERIV) THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\w. lift(lscalar (G:real^N->real^N^N) w)`;
                   `y:real^N`; `basis l:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[metric_field]; SIMP_TAC[]];
    SIMP_TAC[]]);;

let P2AL_LRICOP_DIFF = prove
 (`!U (G:real^N->real^N^N) y A.
     metric_field U G /\ y IN U ==> (\z. p2a_lricop G z A) differentiable (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lricop] THEN
  REWRITE_TAC[differentiable] THEN
  EXISTS_TAC `\h. --(matrix_inv((G:real^N->real^N^N) y) ** mderiv G y h ** matrix_inv(G y)) **
                  ((lambda l. lricci G y A (basis l)):real^N) +
                  matrix_inv(G y) **
                  frechet_derivative (\z. (lambda l. lricci G z A (basis l)):real^N) (at y) h` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`;
                 `\z. (lambda l. lricci (G:real^N->real^N^N) z A (basis l)):real^N`; `y:real^N`]
                P2AL_GINV_MATVEC_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`\z l. lricci (G:real^N->real^N^N) z A (basis l)`; `y:real^N`]
                P2AL_LAMBDA_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LRIC2_FIELD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `\m. if m = 1 then A:real^N else basis l` o CONJUNCT2) THEN
    REWRITE_TAC[lric2; ARITH_EQ];
    SIMP_TAC[]]);;

let P2AL_HAS_FD = prove
 (`!(f:real^N->real^M) y.
     f differentiable (at y) ==> (f has_derivative (\h. frechet_derivative f (at y) h)) (at y)`,
  REWRITE_TAC[ETA_AX; FRECHET_DERIVATIVE_WORKS]);;

let P2AL_LACC_DTRACE = prove
 (`!U (G:real^N->real^N^N) tt s y A.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N))
          (\k. (frechet_derivative (\z. p2a_lacc (\t:real. G) tt s z A) (at y) (basis k))$k) =
         --(sum(1..dimindex(:N))
             (\k. (frechet_derivative (\z. christoffel G z A A) (at y) (basis k))$k)) +
         &2 * s pow 2 *
         sum(1..dimindex(:N))
          (\k. (frechet_derivative (\z. p2a_lgradR G z) (at y) (basis k))$k) -
         &4 * s *
         sum(1..dimindex(:N))
          (\k. (frechet_derivative (\z. p2a_lricop G z A) (at y) (basis k))$k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lacc] THEN
  SUBGOAL_THEN
   `((\z. --christoffel (G:real^N->real^N^N) z A A + (&2 * s pow 2) % p2a_lgradR G z -
          (&4 * s) % p2a_lricop G z A) has_derivative
     (\h. --(frechet_derivative (\z. christoffel G z A A) (at y) h) +
          (&2 * s pow 2) % frechet_derivative (\z. p2a_lgradR G z) (at y) h -
          (&4 * s) % frechet_derivative (\z. p2a_lricop G z A) (at y) h)) (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN MATCH_MP_TAC P2AL_HAS_FD THEN
      MATCH_MP_TAC LRG_CHRISTOFFEL_DIFF THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC P2AL_HAS_FD THENL
       [MATCH_MP_TAC P2AL_LGRADR_DIFF; MATCH_MP_TAC P2AL_LRICOP_DIFF] THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_NEG_COMPONENT;
                VECTOR_MUL_COMPONENT; SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_NEG; SUM_LMUL] THEN
    REAL_ARITH_TAC]);;

let P2AL_TG_LACC = prove
 (`!U (G:real^N->real^N^N) tt s y A.
     metric_field U G /\ y IN U
     ==> p2al_tg G y (p2a_lacc (\t:real. G) tt s y A) =
         --(p2al_tg G y (christoffel G y A A)) +
         &2 * s pow 2 * p2al_tg G y (p2a_lgradR G y) -
         &4 * s * p2al_tg G y (p2a_lricop G y A)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_TG_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[p2a_lacc] THEN
  ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC(map (BETA_RULE o C MATCH_MP th)
                [LINEAR_ADD; LINEAR_SUB; LINEAR_NEG; LINEAR_CMUL])) THEN
  REWRITE_TAC[LIFT_ADD; LIFT_SUB; LIFT_NEG; LIFT_CMUL; VECTOR_MUL_ASSOC]);;

let P2AL_TRACE_ID = prove
 (`!U (G:real^N->real^N^N) tt s y A.
     metric_field U G /\ y IN U
     ==> sum(1..dimindex(:N))
          (\k. (frechet_derivative (\z. p2a_lacc (\t:real. G) tt s z A) (at y) (basis k))$k) +
         trace(matrix(christoffel G y A) ** matrix(christoffel G y A)) +
         &4 * s * trace(matrix(p2a_lricop G y) ** matrix(christoffel G y A)) +
         drop(frechet_derivative (\z. lift(p2al_tg G z A)) (at y) A) +
         p2al_tg G y (p2a_lacc (\t:real. G) tt s y A) =
         --(lricci G y A A) + &2 * s pow 2 * llap G (lscalar G) y -
         &2 * s * drop(frechet_derivative (\z. lift(lscalar G z)) (at y) A)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `tt:real`; `s:real`; `y:real^N`;
                 `A:real^N`] P2AL_LACC_DTRACE) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `tt:real`; `s:real`; `y:real^N`;
                 `A:real^N`] P2AL_TG_LACC) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`]
                P2AL_DTG) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`]
                P2AL_RIC_EXPAND) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_DIV_GRAD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`]
                P2AL_DIV_RICOP) THEN
  ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 3 (DISCH_THEN(ASSUME_TAC)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th; LIFT_DROP]) THEN
  REPLICATE_TAC 2 (DISCH_THEN SUBST1_TAC) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  CONV_TAC REAL_RING);;

(* ========================================================================= *)
(* Time derivative of tr Gamma(A,.) along a local Ricci flow in s = sqrt(tt  *)
(* - t): d/ds tg = 2 s dR(A) (P2AL_TG_TIME, from LCHRISTOFFEL_EVOLUTION and  *)
(* LRG_DSCALAR_CONTRACT), and the chain rule for a jointly differentiable    *)
(* function along a curve s |-> (s, y(s)) (P2AL_JOINT_CURVE,                 *)
(* P2AL_JOINT_CURVE_REAL).                                                   *)
(* ========================================================================= *)

let P2AL_CHR_TIME = prove
 (`!U a b (Gt:real->real^N->real^N^N) t y u v.
     lricci_flow U a b Gt /\ a < t /\ t < b /\ y IN U
     ==> ?w. (!k. 1 <= k /\ k <= dimindex(:N)
                  ==> ((\t'. (christoffel (Gt t') y u v)$k) has_real_derivative w$k) (atreal t)) /\
             !k. 1 <= k /\ k <= dimindex(:N)
                 ==> (Gt t y ** w)$k =
                     --(lnabla 2 (Gt t) (lric2 (Gt t)) y
                          (\m. if m = 1 then v else if m = 2 then basis k else u) +
                        lnabla 2 (Gt t) (lric2 (Gt t)) y
                          (\m. if m = 1 then u else if m = 2 then basis k else v) -
                        lnabla 2 (Gt t) (lric2 (Gt t)) y
                          (\m. if m = 1 then u else if m = 2 then v else basis k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `Gt:real->real^N->real^N^N`;
                 `t:real`; `y:real^N`; `u:real^N`; `v:real^N`] LCHRISTOFFEL_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT]) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]);;

let P2AL_TG_TIME = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt s y A.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y IN U
     ==> ((\s. p2al_tg (Gt(tt - s pow 2)) y A) has_real_derivative
          (&2 * s * drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at y) A)))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t0 = tt - s pow 2` THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N) t0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?w:num->real^N.
      !j. 1 <= j /\ j <= dimindex(:N)
          ==> (!k. 1 <= k /\ k <= dimindex(:N)
                   ==> ((\t'. (christoffel ((Gt:real->real^N->real^N^N) t') y A (basis j))$k)
                        has_real_derivative (w j)$k) (atreal t0)) /\
              !k. 1 <= k /\ k <= dimindex(:N)
                  ==> (Gt t0 y ** w j)$k =
                      --(lnabla 2 (Gt t0) (lric2 (Gt t0)) y
                           (\m. if m = 1 then basis j else if m = 2 then basis k else A) +
                         lnabla 2 (Gt t0) (lric2 (Gt t0)) y
                           (\m. if m = 1 then A else if m = 2 then basis k else basis j) -
                         lnabla 2 (Gt t0) (lric2 (Gt t0)) y
                           (\m. if m = 1 then A else if m = 2 then basis j else basis k))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2AL_CHR_TIME THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2al_tg] THEN
  SUBGOAL_THEN
   `&2 * s * drop(frechet_derivative (\z. lift(lscalar ((Gt:real->real^N->real^N^N) t0) z))
                    (at y) A) =
    sum(1..dimindex(:N)) (\j. (w:num->real^N) j$j * --(&2 * s))`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN
     `(\s. (christoffel ((Gt:real->real^N->real^N^N) (tt - s pow 2)) y A (basis j))$j) =
      (\t'. (christoffel (Gt t') y A (basis j))$j) o (\s. tt - s pow 2)`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`tt:real`; `s:real`] P2A_TIME_SQ_VDERIV) THEN
      REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
      REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP];
      ASM_SIMP_TAC[]]] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\j. (w:num->real^N) j$j) =
    --drop(frechet_derivative (\z. lift(lscalar ((Gt:real->real^N->real^N^N) t0) z)) (at y) A)`
  (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
  ABBREV_TAC `N3 = \p q r. lnabla 2 ((Gt:real->real^N->real^N^N) t0) (lric2 (Gt t0)) y
                       (\m. if m = 1 then p else if m = 2 then q else r)` THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> (w:num->real^N) j$j =
            sum(1..dimindex(:N))
             (\k. matrix_inv((Gt:real->real^N->real^N^N) t0 y)$j$k *
                  --((N3:real^N->real^N->real^N->real) (basis j) (basis k) A +
                     N3 A (basis k) (basis j) - N3 A (basis j) (basis k)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(w:num->real^N) j =
                  matrix_inv((Gt:real->real^N->real^N^N) t0 y) ** (Gt t0 y ** w j)`
    SUBST1_TAC THENL
     [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N) t0`; `y:real^N`]
                    LRG_METRIC_INVERTIBLE) THEN
      ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_COMPONENT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "N3" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\j. (w:num->real^N) j$j) =
    sum(1..dimindex(:N))
     (\j. sum(1..dimindex(:N))
       (\k. matrix_inv((Gt:real->real^N->real^N^N) t0 y)$j$k *
            --((N3:real^N->real^N->real^N->real) (basis j) (basis k) A +
               N3 A (basis k) (basis j) - N3 A (basis j) (basis k))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\j. sum(1..dimindex(:N))
       (\k. matrix_inv((Gt:real->real^N->real^N^N) t0 y)$j$k *
            (N3:real^N->real^N->real^N->real) (basis j) (basis k) A)) =
    drop(frechet_derivative (\z. lift(lscalar (Gt t0) z)) (at y) A)`
  ASSUME_TAC THENL
   [EXPAND_TAC "N3" THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N) t0`; `y:real^N`;
                   `\m:num. (A:real^N)`] LRG_DSCALAR_CONTRACT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
     (\j. sum(1..dimindex(:N))
       (\k. matrix_inv((Gt:real->real^N->real^N^N) t0 y)$j$k *
            (N3:real^N->real^N->real^N->real) A (basis k) (basis j))) =
    sum(1..dimindex(:N))
     (\j. sum(1..dimindex(:N))
       (\k. matrix_inv(Gt t0 y)$j$k * N3 A (basis j) (basis k)))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRG_MATRIX_INV_SYM THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG; REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
              SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2AL_JOINT_CURVE = prove
 (`!(f:real^(1,N)finite_sum->real^M) s (y:real^1->real^N) y'.
     f differentiable (at (pastecart (lift s) (y(lift s)))) /\
     (y has_vector_derivative y') (at (lift s))
     ==> ((\v. f(pastecart v (y v))) has_vector_derivative
          (frechet_derivative f (at (pastecart (lift s) (y(lift s))))
                              (pastecart (lift(&1)) (vec 0)) +
           frechet_derivative (\x. f(pastecart (lift s) x)) (at (y(lift s))) y'))
         (at (lift s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\v:real^1. pastecart v ((y:real^1->real^N) v)) has_vector_derivative
                 pastecart (lift(&1)) y') (at (lift s))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2A_HVD_PASTECART_EQ; LIFT_NUM; HAS_VECTOR_DERIVATIVE_ID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (f:real^(1,N)finite_sum->real^M) (at (pastecart (lift s) (y(lift s))))
       (pastecart (lift(&1)) (vec 0)) +
    frechet_derivative (\x. f(pastecart (lift s) x)) (at (y(lift s))) y' =
    frechet_derivative f (at (pastecart (lift s) (y(lift s)))) (pastecart (lift(&1)) y')`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LRG_SLICE_DERIV] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. (f:real^(1,N)finite_sum->real^M) (pastecart v ((y:real^1->real^N) v))) =
                f o (\v. pastecart v (y v))` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_vector_derivative]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  MP_TAC(ISPECL [`\v:real^1. pastecart v ((y:real^1->real^N) v)`;
                 `f:real^(1,N)finite_sum->real^M`;
                 `\x:real^1. drop x % pastecart (lift(&1)) (y':real^N)`;
                 `frechet_derivative (f:real^(1,N)finite_sum->real^M)
                    (at (pastecart (lift s) ((y:real^1->real^N)(lift s))))`;
                 `lift s`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `x:real^1` THEN
  MATCH_MP_TAC LINEAR_CMUL THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
  ASM_REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[]);;

let P2AL_JOINT_CURVE_REAL = prove
 (`!(f:real^(1,N)finite_sum->real) s (y:real^1->real^N) y' ds.
     (\z. lift(f z)) differentiable (at (pastecart (lift s) (y(lift s)))) /\
     (y has_vector_derivative y') (at (lift s)) /\
     ((\s'. f(pastecart (lift s') (y(lift s)))) has_real_derivative ds) (atreal s)
     ==> ((\s'. f(pastecart (lift s') (y(lift s')))) has_real_derivative
          (ds + drop(frechet_derivative (\x. lift(f(pastecart (lift s) x))) (at (y(lift s))) y')))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. lift((f:real^(1,N)finite_sum->real) z)`; `s:real`; `y:real^1->real^N`;
                 `y':real^N`] P2AL_JOINT_CURVE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\z. lift((f:real^(1,N)finite_sum->real) z)`; `s:real`;
                 `(y:real^1->real^N)(lift s)`] LRG_TIME_CURVE_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((\v. lift((f:real^(1,N)finite_sum->real) (pastecart v ((y:real^1->real^N)(lift s)))))
     has_vector_derivative lift ds) (at (lift s))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_REAL_VECTOR_DERIVATIVE_AT]) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP];
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift((f:real^(1,N)finite_sum->real) z))
      (at (pastecart (lift s) ((y:real^1->real^N)(lift s)))) (pastecart (lift(&1)) (vec 0)) =
    lift ds`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
    MAP_EVERY EXISTS_TAC
     [`\v. lift((f:real^(1,N)finite_sum->real) (pastecart v ((y:real^1->real^N)(lift s))))`;
      `lift s`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP; LIFT_ADD]]);;

(* ========================================================================= *)
(* The chart Riccati equation.  Along a solution (y,A) of                    *)
(* (6.5) for a local Ricci flow, and a Jacobi matrix Y (Y' = B, B' = Ly Y + *)
(* LA B with Ly, LA the derivatives of p2a_lacc in position and velocity),  *)
(* sigma = tr(B Y^-1) + tr Gamma(A,.) has derivative                         *)
(*   -tr(S S) - 4 s tr(Ric# S) - Ric(A,A) + 2 s^2 Lap R,  S = B Y^-1 + GamA  *)
(* (P2AL_RICCATI_EQ), from P2AL_TRACE_ID and P2AL_TG_TIME.                   *)
(* ========================================================================= *)

let P2AL_HVD_CONT = prove
 (`!(f:real^1->real^N) f' x.
     (f has_vector_derivative f') (at x) ==> f continuous (at x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
  REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[has_vector_derivative]);;

let P2AL_HVD_NEAR = prove
 (`!(y:real^1->real^N) y' s U.
     (y has_vector_derivative y') (at (lift s)) /\ open U /\ y(lift s) IN U
     ==> ?d. &0 < d /\ !s'. abs(s' - s) < d ==> y(lift s') IN U`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AL_HVD_CONT) THEN REWRITE_TAC[continuous_at] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(y:real^1->real^N)(lift s)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s':real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIST_LIFT]);;

let P2AL_HVD_COMPONENT_REAL = prove
 (`!(A:real^1->real^N) A' s i.
     (A has_vector_derivative A') (at (lift s)) /\ 1 <= i /\ i <= dimindex(:N)
     ==> ((\s'. (A(lift s'))$i) has_real_derivative A'$i) (atreal s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT]) THEN
  ASM_SIMP_TAC[ETA_AX]);;

let P2AL_TG_SMOOTH = prove
 (`!U sa sb (Gs:real->real^N->real^N^N) v.
     p2a_lsmooth U sa sb Gs
     ==> smooth_map_on (interval(lift sa,lift sb) PCROSS U)
           (\z. lift(p2al_tg (Gs(drop(fstcart z))) (sndcart z) v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(interval(lift sa,lift sb) PCROSS (U:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
    ASM_MESON_TAC[p2a_lsmooth];
    ALL_TAC] THEN
  REWRITE_TAC[p2al_tg] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`; `Gs:real->real^N->real^N^N`;
                 `v:real^N`; `basis k:real^N`] LRG_LSMOOTH_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[GSYM P2A_LSMOOTH_ALT] THEN
  DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP SMOOTH_MAP_ON_LIFT_COMPONENT o
             CONJ (ASSUME `open(interval(lift sa,lift sb) PCROSS (U:real^N->bool))`)) THEN
  REWRITE_TAC[]);;

let P2AL_TG_CURVE = prove
 (`!U sa sb (Gs:real->real^N->real^N^N) s (y:real^1->real^N) (A:real^1->real^N) y' A'
    (d:num->real).
     p2a_lsmooth U sa sb Gs /\ sa < s /\ s < sb /\ y(lift s) IN U /\
     (y has_vector_derivative y') (at (lift s)) /\
     (A has_vector_derivative A') (at (lift s)) /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> ((\s'. p2al_tg (Gs s') (y(lift s)) (basis i)) has_real_derivative d i)
              (atreal s))
     ==> ((\s'. p2al_tg (Gs s') (y(lift s')) (A(lift s'))) has_real_derivative
          (sum(1..dimindex(:N))
            (\i. A(lift s)$i *
                 (d i + drop(frechet_derivative (\z. lift(p2al_tg (Gs s) z (basis i)))
                                                (at (y(lift s))) y'))) +
           p2al_tg (Gs s) (y(lift s)) A')) (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2a_lsmooth]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. sa < t /\ t < sb ==> metric_field U ((Gs:real->real^N->real^N^N) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2a_lsmooth]; ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^1->real^N`; `y':real^N`; `s:real`; `U:real^N->bool`]
                P2AL_HVD_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s'. sum(1..dimindex(:N))
                     (\i. (A:real^1->real^N)(lift s')$i *
                          p2al_tg ((Gs:real->real^N->real^N^N) s') (y(lift s')) (basis i))` THEN
  EXISTS_TAC `min d0 (min (s - sa) (sb - s))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s':real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2AL_TG_EXPAND THEN EXISTS_TAC `U:real^N->bool` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2al_tg ((Gs:real->real^N->real^N^N) s) (y(lift s)) A' =
    sum(1..dimindex(:N)) (\i. A'$i * p2al_tg (Gs s) ((y:real^1->real^N)(lift s)) (basis i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2AL_TG_EXPAND THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2AL_HVD_COMPONENT_REAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. p2al_tg ((Gs:real->real^N->real^N^N)(drop(fstcart z))) (sndcart z)
                         (basis i)`;
                 `s:real`; `y:real^1->real^N`; `y':real^N`; `(d:num->real) i`]
                P2AL_JOINT_CURVE_REAL) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
  EXISTS_TAC `interval(lift sa,lift sb) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[P2AL_TG_SMOOTH; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
  MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL]);;

let P2AL_TRACE_VDERIV = prove
 (`!(M:real->real^N^N) M' s.
     ((\v. vectorize(M(drop v))) has_vector_derivative vectorize M') (at (lift s))
     ==> ((\s'. trace(M s')) has_real_derivative trace M') (atreal s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[trace] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC LRG_VDERIV_MATRIX_ENTRY_REAL THEN ASM_REWRITE_TAC[]);;

let P2AL_TRACE_BYINV_DERIV = prove
 (`!(Y:real->real^N^N) (B:real->real^N^N) B' s.
     ((\v. vectorize(Y(drop v))) has_vector_derivative vectorize(B s)) (at (lift s)) /\
     ((\v. vectorize(B(drop v))) has_vector_derivative vectorize B') (at (lift s)) /\
     ~(det(Y s) = &0)
     ==> ((\s'. trace(B s' ** matrix_inv(Y s'))) has_real_derivative
          trace(B' ** matrix_inv(Y s) -
                (B s ** matrix_inv(Y s)) ** (B s ** matrix_inv(Y s)))) (atreal s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AL_TRACE_VDERIV THEN
  MP_TAC(ISPECL [`Y:real->real^N^N`; `(B:real->real^N^N) s`; `s:real`]
                CMPF_HAS_VD_MATRIX_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`B:real->real^N^N`; `\s. matrix_inv((Y:real->real^N^N) s)`;
                 `B':real^N^N`;
                 `--(matrix_inv((Y:real->real^N^N) s) ** (B:real->real^N^N) s **
                     matrix_inv(Y s))`; `s:real`] CMPF_HAS_VD_MATMUL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[MATRIX_MUL_RNEG; GSYM MATRIX_MUL_ASSOC] THEN
  REWRITE_TAC[MATRIX_SUB; MATRIX_ADD_SYM]);;

let P2AL_LRICOP_LINEAR = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> linear (p2a_lricop G y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2a_lricop (G:real^N->real^N^N) y =
                (\x. matrix_inv(G y) ** x) o (\v. (lambda k. lricci G y v (basis k)):real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; p2a_lricop; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LRICCI_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[linear] THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                                    VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `basis i:real^N`) THEN
  REWRITE_TAC[linear; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN SIMP_TAC[]);;

let P2AL_LACC_DA = prove
 (`!U (Gt:real->real^N->real^N^N) tt s y A.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U
     ==> ((\w. p2a_lacc Gt tt s y w) has_derivative
          (\h. --(&2 % christoffel (Gt(tt - s pow 2)) y A h) -
               (&4 * s) % p2a_lricop (Gt(tt - s pow 2)) y h)) (at A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lacc] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`; `y:real^N`]
                CHRISTOFFEL_BILINEAR) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`; `y:real^N`]
                P2AL_LRICOP_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\h. --(&2 % christoffel ((Gt:real->real^N->real^N^N)(tt - s pow 2)) y A h) -
         (&4 * s) % p2a_lricop (Gt(tt - s pow 2)) y h) =
    (\h. --(christoffel (Gt(tt - s pow 2)) y A h + christoffel (Gt(tt - s pow 2)) y h A) +
         vec 0 - (&4 * s) % p2a_lricop (Gt(tt - s pow 2)) y h)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N` THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - s pow 2)`; `y:real^N`;
                   `h:real^N`; `A:real^N`] CHRISTOFFEL_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN
    MP_TAC(ISPECL [`christoffel ((Gt:real->real^N->real^N^N)(tt - s pow 2)) y`;
                   `\w:real^N. w`; `\w:real^N. w`; `\w:real^N. w`; `\w:real^N. w`;
                   `A:real^N`] HAS_DERIVATIVE_BILINEAR_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID];
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN ASM_REWRITE_TAC[ETA_AX]]);;

let P2AL_LACC_DA_MATRIX = prove
 (`!U (Gt:real->real^N->real^N^N) tt s y A.
     metric_field U (Gt(tt - s pow 2)) /\ y IN U
     ==> matrix(frechet_derivative (\w. p2a_lacc Gt tt s y w) (at A)) =
         --(&2 %% matrix(christoffel (Gt(tt - s pow 2)) y A)) -
         (&4 * s) %% matrix(p2a_lricop (Gt(tt - s pow 2)) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s:real`;
                 `y:real^N`; `A:real^N`] P2AL_LACC_DA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix; MATRIX_SUB_COMPONENT; MATRIX_NEG_COMPONENT;
           MATRIX_CMUL_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_NEG_COMPONENT;
           VECTOR_MUL_COMPONENT]);;

let P2AL_DTG_EXPAND = prove
 (`!U (G:real^N->real^N^N) y A h.
     metric_field U G /\ y IN U
     ==> drop(frechet_derivative (\z. lift(p2al_tg G z A)) (at y) h) =
         sum(1..dimindex(:N))
          (\i. A$i * drop(frechet_derivative (\z. lift(p2al_tg G z (basis i))) (at y) h))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. lift(p2al_tg (G:real^N->real^N^N) z A)) (at y) =
    frechet_derivative (\z. vsum(1..dimindex(:N)) (\i. A$i % lift(p2al_tg G z (basis i))))
                       (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `z:real^N`; `A:real^N`]
                  P2AL_TG_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LIFT_SUM; o_DEF; LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. vsum(1..dimindex(:N)) (\i. (A:real^N)$i % lift(p2al_tg (G:real^N->real^N^N) z (basis i))))
     has_derivative
     (\h. vsum(1..dimindex(:N))
            (\i. A$i % frechet_derivative (\z. lift(p2al_tg G z (basis i))) (at y) h)))
    (at y)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC P2AL_HAS_FD THEN
    REWRITE_TAC[differentiable] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis i:real^N`]
                  P2AL_DTG) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL]]);;

let P2AL_DR_EXPAND = prove
 (`!U (G:real^N->real^N^N) y A.
     metric_field U G /\ y IN U
     ==> drop(frechet_derivative (\z. lift(lscalar G z)) (at y) A) =
         sum(1..dimindex(:N))
          (\i. A$i * drop(frechet_derivative (\z. lift(lscalar G z)) (at y) (basis i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (\z. lift(lscalar (G:real^N->real^N^N) z)) (at y))`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`A:real^N`; `1`] o MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop]);;

let P2AL_LACC_FROZEN = prove
 (`!(Gt:real->real^N->real^N^N) tt s z w.
     p2a_lacc Gt tt s z w = p2a_lacc (\t:real. Gt(tt - s pow 2)) tt s z w`,
  REWRITE_TAC[p2a_lacc]);;

let P2AL_RICCATI_ALG = prove
 (`!(Sc:real^N^N) GA RM (Ly:real^N^N) s.
     trace(Ly) + trace((--(&2 %% GA) - (&4 * s) %% RM) ** Sc) - trace(Sc ** Sc) =
     --trace((Sc + GA) ** (Sc + GA)) - &4 * s * trace(RM ** (Sc + GA)) +
     (trace(Ly) + trace(GA ** GA) + &4 * s * trace(RM ** GA))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MATRIX_ADD_LDISTRIB; MATRIX_ADD_RDISTRIB; MATRIX_SUB_RDISTRIB;
              MATRIX_MUL_LMUL; MATRIX_MUL_LNEG; TRACE_ADD; TRACE_SUB; TRACE_CMUL;
              TRACE_NEG] THEN
  MP_TAC(ISPECL [`Sc:real^N^N`; `GA:real^N^N`] TRACE_MUL_SYM) THEN REAL_ARITH_TAC);;

let P2AL_RICCATI_EQ = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) sa sb tt s (y:real^1->real^N) (A:real^1->real^N)
    (Y:real->real^N^N) (B:real->real^N^N).
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s /\ s < sb /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s)) /\
     ((\v. vectorize(Y(drop v))) has_vector_derivative vectorize(B s)) (at (lift s)) /\
     ((\v. vectorize(B(drop v))) has_vector_derivative
        vectorize(matrix(frechet_derivative (\z. p2a_lacc Gt tt s z (A(lift s)))
                                            (at (y(lift s)))) ** Y s +
                  matrix(frechet_derivative (\w. p2a_lacc Gt tt s (y(lift s)) w)
                                            (at (A(lift s)))) ** B s)) (at (lift s)) /\
     ~(det(Y s) = &0)
     ==> ((\s'. trace(B s' ** matrix_inv(Y s')) +
                p2al_tg (Gt(tt - s' pow 2)) (y(lift s')) (A(lift s')))
          has_real_derivative
          (--trace((B s ** matrix_inv(Y s) +
                    matrix(christoffel (Gt(tt - s pow 2)) (y(lift s)) (A(lift s)))) **
                   (B s ** matrix_inv(Y s) +
                    matrix(christoffel (Gt(tt - s pow 2)) (y(lift s)) (A(lift s))))) -
           &4 * s * trace(matrix(p2a_lricop (Gt(tt - s pow 2)) (y(lift s))) **
                          (B s ** matrix_inv(Y s) +
                           matrix(christoffel (Gt(tt - s pow 2)) (y(lift s)) (A(lift s))))) -
           lricci (Gt(tt - s pow 2)) (y(lift s)) (A(lift s)) (A(lift s)) +
           &2 * s pow 2 * llap (Gt(tt - s pow 2)) (lscalar (Gt(tt - s pow 2))) (y(lift s))))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  ABBREV_TAC `G = (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN
  ABBREV_TAC `y0 = (y:real^1->real^N)(lift s)` THEN
  ABBREV_TAC `A0 = (A:real^1->real^N)(lift s)` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Gt:real->real^N->real^N^N`; `tt:real`; `s:real`;
                 `y0:real^N`; `A0:real^N`] P2AL_LACC_DA_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "la") THEN
  MP_TAC(ISPECL [`Y:real->real^N^N`; `B:real->real^N^N`;
                 `matrix(frechet_derivative (\z. p2a_lacc (Gt:real->real^N->real^N^N) tt s z A0)
                                            (at y0)) ** (Y:real->real^N^N) s +
                  matrix(frechet_derivative (\w. p2a_lacc Gt tt s y0 w) (at A0)) **
                  (B:real->real^N^N) s`; `s:real`] P2AL_TRACE_BYINV_DERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`;
                 `\s. (Gt:real->real^N->real^N^N)(tt - s pow 2)`; `s:real`;
                 `y:real^1->real^N`; `A:real^1->real^N`; `A0:real^N`;
                 `p2a_lacc (Gt:real->real^N->real^N^N) tt s y0 A0`;
                 `\i. &2 * s * drop(frechet_derivative
                        (\z. lift(lscalar (G:real^N->real^N^N) z)) (at y0) (basis i))`]
                P2AL_TG_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN
    MATCH_MP_TAC P2AL_TG_TIME THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th2 -> FIRST_X_ASSUM(fun th1 ->
    MP_TAC(MATCH_MP HAS_REAL_DERIVATIVE_ADD (CONJ th1 th2)))) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `!f a b. a = b ==> (f has_real_derivative a) (atreal (s:real)) ==>
                                            (f has_real_derivative b) (atreal s)`) THEN
  SUBGOAL_THEN `invertible((Y:real->real^N^N) s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_DET_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(matrix(frechet_derivative (\z. p2a_lacc (Gt:real->real^N->real^N^N) tt s z A0) (at y0)) **
     (Y:real->real^N^N) s +
     (--(&2 %% matrix(christoffel G y0 A0)) - (&4 * s) %% matrix(p2a_lricop G y0)) **
     (B:real->real^N^N) s) ** matrix_inv(Y s) =
    matrix(frechet_derivative (\z. p2a_lacc Gt tt s z A0) (at y0)) +
    (--(&2 %% matrix(christoffel G y0 A0)) - (&4 * s) %% matrix(p2a_lricop G y0)) **
    (B s ** matrix_inv(Y s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_ADD_RDISTRIB; GSYM MATRIX_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_MUL_RID];
    ALL_TAC] THEN
  REWRITE_TAC[TRACE_ADD; TRACE_SUB] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_LDISTRIB; SUM_LMUL] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\i. (A0:real^N)$i * &2 * s *
       drop(frechet_derivative (\z. lift(lscalar (G:real^N->real^N^N) z)) (at y0) (basis i))) =
    &2 * s * drop(frechet_derivative (\z. lift(lscalar G z)) (at y0) A0) /\
    sum(1..dimindex(:N)) (\i. A0$i *
       drop(frechet_derivative (\z. lift(p2al_tg G z (basis i))) (at y0) A0)) =
    drop(frechet_derivative (\z. lift(p2al_tg G z A0)) (at y0) A0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`]
                    P2AL_DR_EXPAND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`;
                     `A0:real^N`] P2AL_DTG_EXPAND) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[P2AL_LACC_FROZEN] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `tt:real`; `s:real`; `y0:real^N`;
                 `A0:real^N`] P2AL_TRACE_ID) THEN
  ASM_REWRITE_TAC[LRG_TRACE_MATRIX] THEN
  MP_TAC(ISPECL [`(B:real->real^N^N) s ** matrix_inv((Y:real->real^N^N) s)`;
                 `matrix(christoffel (G:real^N->real^N^N) y0 A0)`;
                 `matrix(p2a_lricop (G:real^N->real^N^N) y0)`;
                 `matrix(frechet_derivative (\z. p2a_lacc (\t:real. (G:real^N->real^N^N)) tt s z A0)
                     (at y0))`; `s:real`] P2AL_RICCATI_ALG) THEN
  REWRITE_TAC[LRG_TRACE_MATRIX; TRACE_SUB] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Riccati inequality.  For a G-self-adjoint S                           *)
(* (symmetric_matrix (G S)) and X = I/s - 2 s Ric#, tr((S - X)^2) >= 0      *)
(* (P2AL_HS_INEQ, via a positive semidefinite square root of G^-1) gives    *)
(*   -tr(S S) - 4 s tr(Ric# S) <= -(2/s) tr S + n/s^2 - 4 R + 4 s^2 tr(Ric#^2) *)
(* (P2AL_RICCATI_BOUND).                                                     *)
(* ========================================================================= *)

let P2AL_TRACE_PSD_SQ = prove
 (`!H K:real^N^N.
     positive_semidefinite H /\ symmetric_matrix K
     ==> &0 <= trace(H ** K ** H ** K)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [POSITIVE_SEMIDEFINITE_SQRT_EQ]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  SUBGOAL_THEN `trace(((Q:real^N^N) ** Q) ** (K:real^N^N) ** (Q ** Q) ** K) =
                trace(transp(Q ** K ** Q) ** (Q ** K ** Q))`
  SUBST1_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP POSITIVE_SEMIDEFINITE_IMP_SYMMETRIC_MATRIX) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[symmetric_matrix]) THEN
    ASM_REWRITE_TAC[MATRIX_TRANSP_MUL; GSYM MATRIX_MUL_ASSOC] THEN
    MP_TAC(ISPECL [`Q:real^N^N`; `(Q:real^N^N) ** (K:real^N^N) ** Q ** Q ** K`]
                  TRACE_MUL_SYM) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM MATRIX_MUL_ASSOC];
    REWRITE_TAC[TRACE_COVARIANCE_POS_LE]]);;

let P2AL_HS_INEQ = prove
 (`!G S X:real^N^N.
     positive_definite G /\ symmetric_matrix (G ** S) /\ symmetric_matrix (G ** X)
     ==> &2 * trace(S ** X) - trace(X ** X) <= trace(S ** S)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(G:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[POSITIVE_DEFINITE_IMP_INVERTIBLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`matrix_inv(G:real^N^N)`; `(G:real^N^N) ** ((S:real^N^N) - (X:real^N^N))`]
                P2AL_TRACE_PSD_SQ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[POSITIVE_SEMIDEFINITE_INV] THEN
      ASM_SIMP_TAC[POSITIVE_DEFINITE_IMP_POSITIVE_SEMIDEFINITE];
      REWRITE_TAC[MATRIX_SUB_LDISTRIB] THEN
      ASM_MESON_TAC[SYMMETRIC_MATRIX_SUB]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `matrix_inv(G:real^N^N) ** (G ** ((S:real^N^N) - (X:real^N^N))) **
    matrix_inv G ** (G ** (S - X)) = (S - X) ** (S - X)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!M:real^N^N. matrix_inv(G:real^N^N) ** (G ** M) = M`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    SUBGOAL_THEN `!M:real^N^N. matrix_inv(G:real^N^N) ** (G ** M) = M` MP_TAC THENL
     [ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_MUL_ASSOC] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; TRACE_SUB] THEN
  MP_TAC(ISPECL [`S:real^N^N`; `X:real^N^N`] TRACE_MUL_SYM) THEN REAL_ARITH_TAC);;

let P2AL_METRIC_PD = prove
 (`!U (G:real^N->real^N^N) y. metric_field U G /\ y IN U ==> positive_definite(G y)`,
  REWRITE_TAC[metric_field; positive_definite; symmetric_matrix] THEN MESON_TAC[]);;

let P2AL_RICM_LOWER = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> G y ** matrix(p2a_lricop G y) = (lambda i j. lricci G y (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; MATRIX_COMPONENT] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\k. (G:real^N->real^N^N) y$i$k * p2a_lricop G y (basis j)$k) =
    (G y ** p2a_lricop G y (basis j))$i`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot]; ALL_TAC] THEN
  ASM_SIMP_TAC[p2a_lricop; MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID;
               LAMBDA_BETA] THEN
  MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let P2AL_RICM_TRACE = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U ==> trace(matrix(p2a_lricop G y)) = lscalar G y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_TRACE_MATRIX; lscalar] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[p2a_lricop; MATRIX_VECTOR_MUL_COMPONENT; dot; LAMBDA_BETA] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA]);;

let P2AL_RICCATI_BOUND = prove
 (`!U (G:real^N->real^N^N) y (S:real^N^N) s.
     metric_field U G /\ y IN U /\ &0 < s /\ symmetric_matrix(G y ** S)
     ==> --trace(S ** S) - &4 * s * trace(matrix(p2a_lricop G y) ** S) <=
         --(&2 / s) * trace S + &(dimindex(:N)) / s pow 2 - &4 * lscalar G y +
         &4 * s pow 2 * trace(matrix(p2a_lricop G y) ** matrix(p2a_lricop G y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `symmetric_matrix((G:real^N->real^N^N) y ** matrix(p2a_lricop G y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_RICM_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[symmetric_matrix; CART_EQ; LAMBDA_BETA; TRANSP_COMPONENT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real^N->real^N^N) y`; `S:real^N^N`;
                 `inv(s) %% mat 1 - (&2 * s) %% matrix(p2a_lricop (G:real^N->real^N^N) y)`]
                P2AL_HS_INEQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[P2AL_METRIC_PD]; ALL_TAC] THEN
    REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_MUL_RMUL; MATRIX_MUL_RID] THEN
    MATCH_MP_TAC SYMMETRIC_MATRIX_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC SYMMETRIC_MATRIX_CMUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[symmetric_matrix] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB; MATRIX_MUL_RMUL; MATRIX_MUL_LMUL;
              MATRIX_MUL_LID; MATRIX_MUL_RID; MATRIX_CMUL_ASSOC; TRACE_SUB; TRACE_CMUL;
              TRACE_I] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_RICM_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`S:real^N^N`; `matrix(p2a_lricop (G:real^N->real^N^N) y)`] TRACE_MUL_SYM) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!a b c d e. &2 * (inv s * a - (&2 * s) * b) -
                (inv s * (inv s * c - (&2 * s) * d) - (&2 * s) * (inv s * d - (&2 * s) * e)) =
                &2 * inv s * a - &4 * s * b - c * inv(s pow 2) + &4 * d - &4 * s pow 2 * e`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The comparison function.  Along a solution of (6.5) with                  *)
(* E = |A|^2 (P2AL_ENERGY_CURVE: E' = 4 s^2 dR(A) - 4 s Ric(A,A)) and R     *)
(* (P2AL_SCALAR_CURVE: R' = -2 s (Lap R + 2|Ric|^2) + dR(A)), for any Lf    *)
(* with Lf' = llag, the function                                             *)
(*   g = s^2 sigma - (n s - s^3 R + s E/4 - Lf/2)                            *)
(* has derivative <= 0 whenever S is G-self-adjoint (P2AL_GFUN_DERIV).      *)
(* ========================================================================= *)

let P2AL_GINV_DOT = prove
 (`!U (G:real^N->real^N^N) y u w.
     metric_field U G /\ y IN U
     ==> (matrix_inv(G y) ** u) dot (G y ** w) = u dot w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y /\ invertible(G y)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field; LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]);;

let P2AL_DOT_LAMBDA = prove
 (`!(x:real^N) (f:num->real). x dot ((lambda k. f k):real^N) = sum(1..dimindex(:N)) (\k. x$k * f k)`,
  SIMP_TAC[dot; LAMBDA_BETA] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[LAMBDA_BETA]);;

let P2AL_LAMBDA_DOT = prove
 (`!(x:real^N) (f:num->real). ((lambda k. f k):real^N) dot x = sum(1..dimindex(:N)) (\k. f k * x$k)`,
  SIMP_TAC[dot; LAMBDA_BETA] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[LAMBDA_BETA]);;

let P2AL_ENERGY_CURVE = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt s (y:real^1->real^N) (A:real^1->real^N).
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s))
     ==> ((\s'. A(lift s') dot (Gt(tt - s' pow 2) (y(lift s')) ** A(lift s')))
          has_real_derivative
          (&4 * s pow 2 * drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                                  (at (y(lift s))) (A(lift s))) -
           &4 * s * lricci (Gt(tt - s pow 2)) (y(lift s)) (A(lift s)) (A(lift s))))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`; `s:real`] P2A_EL_VECTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\t. (A:real^1->real^N)(lift t)`;
                 `\t. (Gt:real->real^N->real^N^N)(tt - t pow 2) ((y:real^1->real^N)(lift t)) **
                      A(lift t)`;
                 `p2a_lacc (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                           ((A:real^1->real^N)(lift s))`;
                 `(lambda k. inv(&2) * ((A:real^1->real^N)(lift s) dot
                       (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2)) ((y:real^1->real^N)(lift s))
                               (basis k) ** A(lift s))) +
                       &2 * s pow 2 *
                       drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                               (at (y(lift s))) (basis k))):real^N`;
                 `s:real`] CMPF_DOT_DERIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  MATCH_MP_TAC(MESON[] `!(f:real^1->real^1) a b. a = b ==> (f has_vector_derivative a) (at (lift s)) ==>
                                         (f has_vector_derivative b) (at (lift s))`) THEN
  AP_TERM_TAC THEN
  ABBREV_TAC `G = (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN
  ABBREV_TAC `y0 = (y:real^1->real^N)(lift s)` THEN
  ABBREV_TAC `A0 = (A:real^1->real^N)(lift s)` THEN
  SUBGOAL_THEN `metric_field U (G:real^N->real^N^N) /\ (y0:real^N) IN U` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(A0:real^N) dot
    ((lambda k. inv(&2) * (A0 dot (mderiv (G:real^N->real^N^N) y0 (basis k) ** A0)) +
                &2 * s pow 2 *
                drop(frechet_derivative (\z. lift(lscalar G z)) (at y0) (basis k))):real^N) =
    inv(&2) * (A0 dot (mderiv G y0 A0 ** A0)) +
    &2 * s pow 2 * drop(frechet_derivative (\z. lift(lscalar G z)) (at y0) A0)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`]
                  P2AL_DR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`; `A0:real^N`]
                  LRG_MDERIV_DOT_LINEAR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`A0:real^N`; `1`] o MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[P2AL_DOT_LAMBDA; REAL_ADD_LDISTRIB; SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
    BINOP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[P2AL_LACC_FROZEN] THEN ASM_REWRITE_TAC[p2a_lacc] THEN
  REWRITE_TAC[DOT_LADD; DOT_LSUB; DOT_LNEG; DOT_LMUL] THEN
  SUBGOAL_THEN
   `christoffel (G:real^N->real^N^N) y0 A0 A0 dot (G y0 ** A0) =
    inv(&2) * (A0 dot (mderiv G y0 A0 ** A0))`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`;
                   `A0:real^N`; `A0:real^N`] LRG_CHRISTOFFEL_DOT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(A0:real^N) dot ((G:real^N->real^N^N) y0 ** christoffel G y0 A0 A0) =
                  (G y0 ** A0) dot christoffel G y0 A0 A0`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_MESON_TAC[metric_field];
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`A0:real^N`; `mderiv (G:real^N->real^N^N) y0 A0 ** (A0:real^N)`] DOT_SYM) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lgradR; p2a_lricop] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] P2AL_GINV_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `((lambda k. drop(frechet_derivative (\z. lift(lscalar (G:real^N->real^N^N) z)) (at y0)
                       (basis k))):real^N) dot A0 =
    drop(frechet_derivative (\z. lift(lscalar G z)) (at y0) A0) /\
    ((lambda k. lricci G y0 A0 (basis k)):real^N) dot A0 = lricci G y0 A0 A0`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[P2AL_LAMBDA_DOT] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`]
                    P2AL_DR_EXPAND);
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`;
                     `A0:real^N`] P2AL_LRICCI_RLIN)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2AL_SCALAR_CURVE = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) sa sb tt s (y:real^1->real^N) y'.
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s /\ s < sb /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative y') (at (lift s))
     ==> ((\s'. lscalar (Gt(tt - s' pow 2)) (y(lift s'))) has_real_derivative
          (--(&2 * s) *
           (llap (Gt(tt - s pow 2)) (lscalar (Gt(tt - s pow 2))) (y(lift s)) +
            &2 * ltnorm2 2 (Gt(tt - s pow 2)) (lric2 (Gt(tt - s pow 2))) (y(lift s))) +
           drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at (y(lift s))) y')))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. lscalar ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2))
                              (sndcart z)`;
                 `s:real`; `y:real^1->real^N`; `y':real^N`;
                 `--(&2 * s) *
                  (llap ((Gt:real->real^N->real^N^N)(tt - s pow 2)) (lscalar (Gt(tt - s pow 2)))
                        ((y:real^1->real^N)(lift s)) +
                   &2 * ltnorm2 2 (Gt(tt - s pow 2)) (lric2 (Gt(tt - s pow 2))) (y(lift s)))`]
                P2AL_JOINT_CURVE_REAL) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS (U:real^N->bool)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_INTERVAL] THEN
      ASM_MESON_TAC[p2a_lsmooth];
      MP_TAC(ISPECL [`U:real^N->bool`; `sa:real`; `sb:real`;
                     `\s. (Gt:real->real^N->real^N^N)(tt - s pow 2)`] LRG_LSMOOTH_LSCALAR) THEN
      ASM_REWRITE_TAC[GSYM P2A_LSMOOTH_ALT];
      ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s'. lscalar ((Gt:real->real^N->real^N^N)(tt - s' pow 2)) ((y:real^1->real^N)(lift s))) =
    (\t. lscalar (Gt t) (y(lift s))) o (\s'. tt - s' pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`tt:real`; `s:real`] P2A_TIME_SQ_VDERIV) THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP];
    BETA_TAC THEN MATCH_MP_TAC LSCALAR_EVOLUTION THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN
    ASM_REWRITE_TAC[]]);;

let P2AL_RICM_SQ_NORM = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> trace(matrix(p2a_lricop G y) ** matrix(p2a_lricop G y)) = ltnorm2 2 G (lric2 G) y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `RL = (lambda i j. lricci (G:real^N->real^N^N) y (basis i) (basis j)):real^N^N` THEN
  SUBGOAL_THEN `matrix(p2a_lricop (G:real^N->real^N^N) y) = matrix_inv(G y) ** RL`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_RICM_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
    ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `trace((matrix_inv((G:real^N->real^N^N) y) ** RL) ** (matrix_inv(G y) ** RL)) =
    sum(1..dimindex(:N))
     (\p. sum(1..dimindex(:N))
       (\q. (matrix_inv(G y) ** RL ** matrix_inv(G y))$p$q * lricci G y (basis p) (basis q)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_MUL_ASSOC; trace] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`(matrix_inv((G:real^N->real^N^N) y) ** RL) ** matrix_inv(G y)`;
                   `RL:real^N^N`; `p:num`; `p:num`] LRG_MATRIX_MUL_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN BETA_TAC THEN
    AP_TERM_TAC THEN EXPAND_TAC "RL" THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_LTNORM2_RIC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(lambda i j. -- &2 * lricci (G:real^N->real^N^N) y (basis i) (basis j)):real^N^N =
    (-- &2) %% RL`
  SUBST1_TAC THENL
   [EXPAND_TAC "RL" THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_COMPONENT; MATRIX_NEG_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `--(-- &2 * a) * b = &2 * (a * b)`; SUM_LMUL] THEN
  REAL_ARITH_TAC);;

let P2AL_HRD_EQ = prove
 (`!f a b net. (f has_real_derivative a) net /\ a = b ==> (f has_real_derivative b) net`,
  MESON_TAC[]);;

let P2AL_GCOMB_DERIV = prove
 (`!(sg:real->real) Rf Ef Lf sg' R' E' L' n s.
     (sg has_real_derivative sg') (atreal s) /\ (Rf has_real_derivative R') (atreal s) /\
     (Ef has_real_derivative E') (atreal s) /\ (Lf has_real_derivative L') (atreal s)
     ==> ((\x. x pow 2 * sg x - (n * x - x pow 3 * Rf x + x * Ef x / &4 - Lf x / &2))
          has_real_derivative
          (s pow 2 * sg' + &2 * s * sg s -
           (n - (s pow 3 * R' + &3 * s pow 2 * Rf s) + (s * E' + Ef s) / &4 - L' / &2)))
         (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\x. x pow 2) has_real_derivative &2 * s) (atreal s) /\
                ((\x. x pow 3) has_real_derivative &3 * s pow 2) (atreal s) /\
                ((\x. x) has_real_derivative &1) (atreal s) /\
                ((\x. n * x) has_real_derivative n) (atreal s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((\x. Ef x / &4) has_real_derivative E' / &4) (atreal s) /\
                ((\x. Lf x / &2) has_real_derivative L' / &2) (atreal s)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN CONJ_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2AL_HRD_EQ THEN EXISTS_TAC
   `(s pow 2 * sg' + (&2 * s) * sg s) -
    ((n - (s pow 3 * R' + (&3 * s pow 2) * Rf s)) +
     (s * E' / &4 + &1 * Ef s / &4) - L' / &2)` THEN
  CONJ_TAC THENL [ALL_TAC; BETA_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[]);;

let P2AL_GFUN_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) sa sb tt s (y:real^1->real^N) (A:real^1->real^N)
    (Y:real->real^N^N) (B:real->real^N^N) (Lf:real->real).
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s /\ s < sb /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     &0 < s /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s)) /\
     ((\v. vectorize(Y(drop v))) has_vector_derivative vectorize(B s)) (at (lift s)) /\
     ((\v. vectorize(B(drop v))) has_vector_derivative
        vectorize(matrix(frechet_derivative (\z. p2a_lacc Gt tt s z (A(lift s)))
                                            (at (y(lift s)))) ** Y s +
                  matrix(frechet_derivative (\w. p2a_lacc Gt tt s (y(lift s)) w)
                                            (at (A(lift s)))) ** B s)) (at (lift s)) /\
     ~(det(Y s) = &0) /\
     symmetric_matrix(Gt(tt - s pow 2) (y(lift s)) **
                      (B s ** matrix_inv(Y s) +
                       matrix(christoffel (Gt(tt - s pow 2)) (y(lift s)) (A(lift s))))) /\
     (Lf has_real_derivative p2a_llag Gt tt s (y(lift s)) (A(lift s))) (atreal s)
     ==> ?g'. ((\x. x pow 2 * (trace(B x ** matrix_inv(Y x)) +
                               p2al_tg (Gt(tt - x pow 2)) (y(lift x)) (A(lift x))) -
                    (&(dimindex(:N)) * x - x pow 3 * lscalar (Gt(tt - x pow 2)) (y(lift x)) +
                     x * (A(lift x) dot (Gt(tt - x pow 2) (y(lift x)) ** A(lift x))) / &4 -
                     Lf x / &2))
               has_real_derivative g') (atreal s) /\ g' <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `sa:real`; `sb:real`; `tt:real`; `s:real`; `y:real^1->real^N`;
                 `A:real^1->real^N`; `Y:real->real^N^N`; `B:real->real^N^N`] P2AL_RICCATI_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `sa:real`; `sb:real`; `tt:real`; `s:real`; `y:real^1->real^N`;
                 `(A:real^1->real^N)(lift s)`] P2AL_SCALAR_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `s:real`; `y:real^1->real^N`; `A:real^1->real^N`]
                P2AL_ENERGY_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun thE -> FIRST_X_ASSUM(fun thR -> FIRST_X_ASSUM(fun thS ->
    FIRST_X_ASSUM(fun thL ->
      MP_TAC(BETA_RULE(MATCH_MP P2AL_GCOMB_DERIV
        (CONJ thS (CONJ thR (CONJ thE thL))))))))) THEN
  DISCH_THEN(MP_TAC o SPEC `&(dimindex(:N))`) THEN
  DISCH_THEN(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  ABBREV_TAC `G = (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN
  ABBREV_TAC `y0 = (y:real^1->real^N)(lift s)` THEN
  ABBREV_TAC `A0 = (A:real^1->real^N)(lift s)` THEN
  ABBREV_TAC `S = (B:real->real^N^N) s ** matrix_inv((Y:real->real^N^N) s) +
                  matrix(christoffel (G:real^N->real^N^N) y0 A0)` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `S:real^N^N`; `s:real`]
                P2AL_RICCATI_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] P2AL_RICM_SQ_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `trace(S:real^N^N) = trace((B:real->real^N^N) s ** matrix_inv((Y:real->real^N^N) s)) +
                                    p2al_tg (G:real^N->real^N^N) y0 A0`
  SUBST1_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[TRACE_ADD; P2AL_TG_MATRIX]; ALL_TAC] THEN
  REWRITE_TAC[p2a_llag] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sig = trace((B:real->real^N^N) s ** matrix_inv((Y:real->real^N^N) s)) +
                    p2al_tg (G:real^N->real^N^N) y0 A0` THEN
  SUBGOAL_THEN
   `s pow 2 * (--(&2 / s) * sig + &(dimindex(:N)) / s pow 2 -
               &4 * lscalar (G:real^N->real^N^N) y0 + &4 * s pow 2 * ltnorm2 2 G (lric2 G) y0) =
    --(&2 * s) * sig + &(dimindex(:N)) - &4 * s pow 2 * lscalar G y0 +
    &4 * s pow 4 * ltnorm2 2 G (lric2 G) y0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (SPEC `s:real` REAL_LE_POW_2)) THEN
  ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;
(* ========================================================================= *)
(* The Jacobian in a chart.  tr Gamma(v,.) = tr(G^-1 DG[v])/2                *)
(* (P2AL_TG_TRACE); along the curve, |det Y| sqrt(det G) has logarithmic     *)
(* derivative sigma + 2 s R (P2AL_JC_DERIV), the chart form of d/ds log J =  *)
(* sigma + 2 s R.  Teeth: in the static flat (Gaussian) case with Y = 2 s I  *)
(* the comparison function vanishes identically, i.e. the Riccati comparison *)
(* is sharp (P2AL_TEETH_GAUSSIAN).                                           *)
(* ========================================================================= *)

let P2AL_TG_TRACE = prove
 (`!U (G:real^N->real^N^N) y v.
     metric_field U G /\ y IN U
     ==> p2al_tg G y v = inv(&2) * trace(matrix_inv(G y) ** mderiv G y v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2al_tg] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> (christoffel (G:real^N->real^N^N) y v (basis k))$k =
            inv(&2) * ((matrix_inv(G y) ** basis k) dot (mderiv G y v ** basis k) +
                       (matrix_inv(G y) ** basis k) dot (mderiv G y (basis k) ** v) -
                       v dot (mderiv G y (matrix_inv(G y) ** basis k) ** basis k))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `v:real^N`;
                   `basis k:real^N`; `matrix_inv((G:real^N->real^N^N) y) ** basis k`]
                  LRG_CHRISTOFFEL_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis k:real^N`;
                   `christoffel (G:real^N->real^N^N) y v (basis k)`] P2AL_GINV_DOT) THEN
    ASM_SIMP_TAC[DOT_BASIS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_EQ_NUMSEG] THEN
  REWRITE_TAC[SUM_LMUL; SUM_ADD_NUMSEG; SUM_SUB_NUMSEG] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N)) (\k. (matrix_inv((G:real^N->real^N^N) y) ** basis k) dot
                             (mderiv G y v ** basis k)) =
    trace(matrix_inv(G y) ** mderiv G y v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[trace] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[LRG_MATRIX_MUL_COMPONENT; dot] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `m:num`; `k:num`]
                  LRG_MATRIX_INV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b = c ==> a + b - c = a`) THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= dimindex(:N)
        ==> v dot (mderiv (G:real^N->real^N^N) y (matrix_inv(G y) ** basis k) ** basis k) =
            sum(1..dimindex(:N)) (\m. matrix_inv(G y)$m$k * (mderiv G y (basis m) ** v)$k)`
  (fun th -> SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^N->real^N^N`; `y:real^N`; `v:real^N`; `basis k:real^N`]
                  LRG_MDERIV_DOT_LINEAR) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`matrix_inv((G:real^N->real^N^N) y) ** basis k`; `1`] o
               MATCH_MP LINEAR_COMPONENTWISE_EXPANSION) THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL; GSYM drop; LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(matrix_inv((G:real^N->real^N^N) y) ** basis k)$m = matrix_inv(G y)$m$k`
    SUBST1_TAC THENL [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]; ALL_TAC] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `basis m:real^N`;
                   `v:real^N`; `basis k:real^N`] LRG_MDERIV_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[DOT_BASIS];
    ALL_TAC] THEN
  REWRITE_TAC[dot] THEN
  GEN_REWRITE_TAC RAND_CONV [SUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(matrix_inv((G:real^N->real^N^N) y) ** basis k)$m = matrix_inv(G y)$m$k`
  SUBST1_TAC THENL [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_BASIS; column; LAMBDA_BETA]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `k:num`; `m:num`]
                LRG_MATRIX_INV_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P2AL_REAL_CONT_POS = prove
 (`!f s. f real_continuous (atreal s) /\ &0 < f s
         ==> ?d. &0 < d /\ !s'. abs(s' - s) < d ==> &0 < f s'`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_CONTINUOUS_ATREAL]) THEN
  REWRITE_TAC[REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->real) s`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s':real` THEN DISCH_TAC THEN ASM_CASES_TAC `s':real = s` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `s':real`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let P2AL_ABSDET_DERIV = prove
 (`!(Y:real->real^N^N) B s.
     ((\v. vectorize(Y(drop v))) has_vector_derivative vectorize B) (at (lift s)) /\
     ~(det(Y s) = &0)
     ==> ((\s'. abs(det(Y s'))) has_real_derivative
          abs(det(Y s)) * trace(matrix_inv(Y s) ** B)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:real->real^N^N`; `B:real^N^N`; `s:real`] CMPF_DET_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM o_DEF; GSYM(REWRITE_RULE[o_DEF] HAS_REAL_VECTOR_DERIVATIVE_AT)] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `((\s'. det((Y:real->real^N^N) s')) has_real_derivative
                 det(Y s) * trace(matrix_inv(Y s) ** B)) (atreal s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL) THEN
  DISJ_CASES_TAC(MATCH_MP (REAL_ARITH `!x. ~(x = &0) ==> &0 < x \/ x < &0`)
    (ASSUME `~(det((Y:real->real^N^N) s) = &0)`)) THENL
   [MP_TAC(ISPECL [`\s'. det((Y:real->real^N^N) s')`; `s:real`] P2AL_REAL_CONT_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s'. det((Y:real->real^N^N) s')`; `d:real`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
    MP_TAC(ISPECL [`\s'. --det((Y:real->real^N^N) s')`; `s:real`] P2AL_REAL_CONT_POS) THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_NEG; REAL_ARITH `x < &0 ==> &0 < --x`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s'. --det((Y:real->real^N^N) s')`; `d:real`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < --x ==> abs x = --x`] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> abs x = --x`; REAL_MUL_LNEG] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[]]);;

let P2AL_RICM_EQ = prove
 (`!U (G:real^N->real^N^N) y.
     metric_field U G /\ y IN U
     ==> matrix(p2a_lricop G y) =
         matrix_inv(G y) ** (lambda i j. lricci G y (basis i) (basis j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] P2AL_RICM_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_MUL_ASSOC; MATRIX_INV; MATRIX_MUL_LID]);;

let P2AL_SQRTDET_CURVE = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt s (y:real^1->real^N) A0.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A0) (at (lift s))
     ==> ((\s'. sqrt(det(Gt(tt - s' pow 2) (y(lift s'))))) has_real_derivative
          sqrt(det(Gt(tt - s pow 2) (y(lift s)))) *
          (&2 * s * lscalar (Gt(tt - s pow 2)) (y(lift s)) +
           p2al_tg (Gt(tt - s pow 2)) (y(lift s)) A0)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `A0:real^N`; `s:real`]
                P2A_METRIC_CURVE_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `G = (Gt:real->real^N->real^N^N)(tt - s pow 2)` THEN
  ABBREV_TAC `y0 = (y:real^1->real^N)(lift s)` THEN
  SUBGOAL_THEN `&0 < det((G:real^N->real^N^N) y0)` ASSUME_TAC THENL
   [MATCH_MP_TAC DET_POSITIVE_DEFINITE THEN MATCH_MP_TAC P2AL_METRIC_PD THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. (Gt:real->real^N->real^N^N)(tt - t pow 2) ((y:real^1->real^N)(lift t))`;
                 `(&4 * s) %% ((lambda i j. lricci (G:real^N->real^N^N) y0 (basis i) (basis j))
                              :real^N^N) + mderiv G y0 A0`; `s:real`] CMPF_DET_DERIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s'. det((Gt:real->real^N->real^N^N)(tt - s' pow 2) ((y:real^1->real^N)(lift s'))))
     has_real_derivative
     det((G:real^N->real^N^N) y0) *
     trace(matrix_inv(G y0) ** ((&4 * s) %% ((lambda i j. lricci G y0 (basis i) (basis j))
                                            :real^N^N) + mderiv G y0 A0))) (atreal s)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] REAL_DIFF_CHAIN_ATREAL)) THEN
  DISCH_THEN(MP_TAC o SPECL [`sqrt`; `inv(&2 * sqrt(det((G:real^N->real^N^N) y0)))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_SQRT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC(MESON[] `!f a b. a = b ==> (f has_real_derivative a) (atreal (s:real)) ==>
                                            (f has_real_derivative b) (atreal s)`) THEN
  REWRITE_TAC[MATRIX_ADD_LDISTRIB; MATRIX_MUL_RMUL; TRACE_ADD; TRACE_CMUL] THEN
  SUBGOAL_THEN
   `trace(matrix_inv((G:real^N->real^N^N) y0) **
          (lambda i j. lricci G y0 (basis i) (basis j))) = lscalar G y0 /\
    trace(matrix_inv(G y0) ** mderiv G y0 A0) = &2 * p2al_tg G y0 A0`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] P2AL_RICM_EQ) THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] P2AL_RICM_TRACE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `A0:real^N`]
                    P2AL_TG_TRACE) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(det((G:real^N->real^N^N) y0)) pow 2 = det(G y0) /\
                &0 < sqrt(det(G y0))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `q = sqrt(det((G:real^N->real^N^N) y0))` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
                                                     rand(concl th) = `det((G:real^N->real^N^N) y0)`)) THEN
  UNDISCH_TAC `&0 < q` THEN CONV_TAC REAL_FIELD);;
let P2AL_JC_DERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt s (y:real^1->real^N) A0 (Y:real->real^N^N) B.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A0) (at (lift s)) /\
     ((\v. vectorize(Y(drop v))) has_vector_derivative vectorize B) (at (lift s)) /\
     ~(det(Y s) = &0)
     ==> ((\s'. abs(det(Y s')) * sqrt(det(Gt(tt - s' pow 2) (y(lift s'))))) has_real_derivative
          (abs(det(Y s)) * sqrt(det(Gt(tt - s pow 2) (y(lift s))))) *
          ((trace(B ** matrix_inv(Y s)) + p2al_tg (Gt(tt - s pow 2)) (y(lift s)) A0) +
           &2 * s * lscalar (Gt(tt - s pow 2)) (y(lift s)))) (atreal s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Y:real->real^N^N`; `B:real^N^N`; `s:real`] P2AL_ABSDET_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `s:real`; `y:real^1->real^N`; `A0:real^N`] P2AL_SQRTDET_CURVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th2 -> FIRST_X_ASSUM(fun th1 ->
    MP_TAC(BETA_RULE(MATCH_MP HAS_REAL_DERIVATIVE_MUL_ATREAL (CONJ th1 th2))))) THEN
  MATCH_MP_TAC(MESON[] `!f a b. a = b ==> (f has_real_derivative a) (atreal (s:real)) ==>
                                            (f has_real_derivative b) (atreal s)`) THEN
  MP_TAC(ISPECL [`matrix_inv((Y:real->real^N^N) s)`; `B:real^N^N`] TRACE_MUL_SYM) THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P2AL_TEETH_GAUSSIAN = prove
 (`!tt (Z:real^N) y0 s (Lf:real->real).
     &0 < s /\ Lf s = &2 * (Z dot Z) * s
     ==> s pow 2 * (trace((&2 %% mat 1:real^N^N) ** matrix_inv((&2 * s) %% mat 1:real^N^N)) +
                    p2al_tg ((\t:real z:real^N. mat 1:real^N^N) (tt - s pow 2))
                            (y0 + (&2 * s) % Z) (&2 % Z)) -
         (&(dimindex(:N)) * s -
          s pow 3 * lscalar ((\t:real z:real^N. mat 1:real^N^N) (tt - s pow 2))
                            (y0 + (&2 * s) % Z) +
          s * ((&2 % Z) dot ((\t:real z:real^N. mat 1:real^N^N) (tt - s pow 2)
                               (y0 + (&2 * s) % Z) ** (&2 % Z))) / &4 -
          Lf s / &2) = &0`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p2al_tg; GEOL_CHRISTOFFEL_CONST; P2A_LSCALAR_FLAT; VEC_COMPONENT; SUM_0] THEN
  REWRITE_TAC[MATRIX_INV_CMUL; MATRIX_INV_I; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL;
              MATRIX_MUL_LID; MATRIX_CMUL_ASSOC; TRACE_CMUL; TRACE_I;
              MATRIX_VECTOR_MUL_LID; DOT_LMUL; DOT_RMUL] THEN
  UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD);;

