(* ========================================================================= *)
(* Unit pc_cmp_cgt (comparison-geometry layer CMP, fourth unit of            *)
(* CMP_T2_CGT): the counting argument and the Cheeger-Gromov-Taylor          *)
(* injectivity radius bound.  If Psi = exp_x o E is not injective on B(0,i0) *)
(* there is a deck point q <> 0 with |q| < 2 i0; the images tau_q^k(S), k <  *)
(* N, of the part S of the segment domain in B(0,r1) are disjoint            *)
(* (CMPY_NO_PERIOD), lie in B(0,2 r1), and each has pullback volume vol      *)
(* B(x,r1) (change of variables for the local isometry tau_q^k), so N vol    *)
(* B(x,r1) <= 2^(n/2) |B(0,2 r1)|; relative volume comparison bounds vol     *)
(* B(x,r1) below by v0, so N is bounded.  Choosing N too large and i0 small  *)
(* gives injectivity, and S3 gives an injective differential, so exp_x       *)
(* parametrizes the tangent ball of radius i0.                               *)
(* ========================================================================= *)

needs "src/pc_cmp_cent.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Determinant bounds for a metric field (0 < det G, and sqrt(det G) <=      *)
(* sqrt(c)^n when G <= c I) and the bound of an integral by a constant times *)
(* the measure.                                                              *)
(* ========================================================================= *)

let CMPT_DET_POS = prove
 (`!U (G:real^N->real^N^N) y. metric_field U G /\ y IN U ==> &0 < det(G y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[DET_MUL; DET_TRANSP; REAL_LT_SQUARE] THEN
  ASM_MESON_TAC[INVERTIBLE_DET_NZ]);;

let CMPT_SQRTDET_LE = prove
 (`!U (G:real^N->real^N^N) y c.
        metric_field U G /\ y IN U /\ &0 <= c /\ (!a. a dot (G y ** a) <= c * (a dot a))
        ==> sqrt(det(G y)) <= sqrt c pow dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real^N^N` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GM"))) THEN
  SUBGOAL_THEN `!a:real^N. norm((M:real^N^N) ** a) <= sqrt c * norm a` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN REWRITE_TAC[vector_norm] THEN
    ASM_SIMP_TAC[GSYM SQRT_MUL; DOT_POS_LE] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[DOT_POS_LE] THEN
    REWRITE_TAC[GSYM CMPP_DOT_TRANSP; MATRIX_VECTOR_MUL_ASSOC] THEN
    USE_THEN "GM" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `onorm(\x:real^N. (M:real^N^N) ** x) <= sqrt c` ASSUME_TAC THENL
   [MP_TAC(ISPEC `\x:real^N. (M:real^N^N) ** x` ONORM) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "GM" SUBST1_TAC THEN REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
  REWRITE_TAC[GSYM REAL_POW_2; POW_2_SQRT_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `onorm(\x:real^N. (M:real^N^N) ** x) pow dimindex(:N)` THEN
  REWRITE_TAC[DET_LE_ONORM_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ONORM_POS_LE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);;

let CMPT_INTEGRAL_LE_MEASURE = prove
 (`!(f:real^N->real) S c.
        measurable S /\ (\w. lift(f w)) integrable_on S /\ (!w. w IN S ==> f w <= c)
        ==> drop(integral S (\w. lift(f w))) <= c * measure S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `lift c`] INTEGRAL_CONST_GEN) THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `lift c`] HAS_INTEGRAL_CONST_GEN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral S (\w:real^N. lift c))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* A deck map preserves the pullback volume density, so the integral of      *)
(* sqrt(det G) over an injective image of S equals that over S (change of    *)
(* variables).                                                               *)
(* ========================================================================= *)

let CMPT_DECK_JAC = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W sigma a.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W sigma /\ a IN W
        ==> sqrt(det(cmp_expmetric (top,atlas) g x E a)) =
            abs(det(matrix(frechet_derivative sigma (at a)))) *
            sqrt(det(cmp_expmetric (top,atlas) g x E (sigma a)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  SUBGOAL_THEN `(sigma:real^N->real^N) a IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmp_deck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `W:real^N->bool`; `sigma:real^N->real^N`; `a:real^N`] CMPK_DECK_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DET_MUL; DET_TRANSP] THEN
  SUBGOAL_THEN `&0 < det(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)
                           ((sigma:real^N->real^N) a))`
  MP_TAC THENL
   [MATCH_MP_TAC CMPT_DET_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SPEC_TAC(`det(cmp_expmetric (top,atlas) (g:A->real^N^N) x (E:real^N^N)
                  ((sigma:real^N->real^N) a))`,`u:real`) THEN
  SPEC_TAC(`det(matrix(frechet_derivative (sigma:real^N->real^N) (at a)))`,`d:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `d * u * d = d pow 2 * u` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE; POW_2_SQRT_ABS]);;

let CMPT_DECK_INTEGRAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho W sigma S.
        cmp_pullsetup (top,atlas) g x E K rho /\
        cmp_deck (top,atlas) g x E rho W sigma /\ S SUBSET W /\ lebesgue_measurable S /\
        (!a b. a IN S /\ b IN S /\ sigma a = sigma b ==> a = b) /\
        (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w)))) absolutely_integrable_on S
        ==> (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))
            absolutely_integrable_on (IMAGE sigma S) /\
            integral (IMAGE sigma S) (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w)))) =
            integral S (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `f = \w:real^N. lift(sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N)
                                             x (E:real^N^N) w)))` THEN
  MP_TAC(ISPECL [`f:real^N->real^1`; `sigma:real^N->real^N`;
                 `\a:real^N. frechet_derivative (sigma:real^N->real^N) (at a)`;
                 `S:real^N->bool`; `integral S (f:real^N->real^1)`]
    HAS_ABSOLUTE_INTEGRAL_CHANGE_OF_VARIABLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                   `W:real^N->bool`; `sigma:real^N->real^N`; `a:real^N`] CMPK_DECK_DERIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  SUBGOAL_THEN
   `!a. a IN S
        ==> abs(det(matrix((\a:real^N. frechet_derivative (sigma:real^N->real^N) (at a)) a))) %
            (f:real^N->real^1) (sigma a) = f a`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CMPT_DECK_JAC THEN
    MAP_EVERY EXISTS_TAC [`K:real`; `rho:real`; `W:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN EXISTS_TAC `f:real^N->real^1` THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The images tau_q^k(S), k < N, are pairwise disjoint when Psi is injective *)
(* on S (a common point gives tau^j = tau^k near 0 by rigidity, so tau^(k-j) *)
(* fixes tau^j 0, against CMPY_NO_PERIOD).                                   *)
(* ========================================================================= *)

let CMPT_PARAM_MONO = prove
 (`!K l b1 R m N.
        &0 <= K /\ &0 <= l /\ &0 < b1 /\ m <= N /\
        &16 * &N pow 3 * l pow 2 < b1 pow 2 /\ &2 * b1 + &(N + 1) * l <= R /\
        K * (&N * l + &2 * b1) pow 2 <= inv(&2)
        ==> &16 * &m pow 3 * l pow 2 < b1 pow 2 /\ &2 * b1 + &(m + 1) * l <= R /\
            K * (&m * l + &2 * b1) pow 2 <= inv(&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&m <= &N` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&16 * &N pow 3 * l pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * b1 + &(N + 1) * l` THEN
    ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * (&N * l + &2 * b1) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_LE_RADD] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]]]);;

let CMPT_DISJOINT = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R q N b1 r1 S a b j k.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm q < R /\
        cmp_psi (top,atlas) g x E q = x /\ ~(q = vec 0) /\ &0 < b1 /\ &0 < r1 /\
        &16 * &N pow 3 * norm q pow 2 < b1 pow 2 /\ &4 * norm q <= b1 /\
        &2 * b1 + &(N + 1) * norm q <= R /\
        K * (&N * norm q + &2 * b1) pow 2 <= inv(&2) /\
        &N * norm q < b1 /\ r1 + &N * norm q <= R /\
        S SUBSET ball(vec 0,r1) /\
        (!a b. a IN S /\ b IN S /\
               cmp_psi (top,atlas) g x E a = cmp_psi (top,atlas) g x E b
               ==> a = b) /\
        a IN S /\ b IN S /\ j < k /\ k < N /\
        ITER j (cmp_tau (top,atlas) g x E rho q) a =
        ITER k (cmp_tau (top,atlas) g x E rho q) b
        ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `q:real^N`] CMPK_TAU) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tau = cmp_tau (top,atlas) (g:A->real^N^N) (x:A) (E:real^N^N) rho q` THEN
  ABBREV_TAC `l = norm(q:real^N)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `rho:real`; `R - l`; `l:real`;
                 `tau:real^N->real^N`] CMPY_ITER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "it") THEN
  SUBGOAL_THEN `&j * l + l <= &N * l /\ &k * l + l <= &N * l /\ &j * l <= &k * l`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(REAL_ARITH `(a + &1) * l = a * l + l`); REAL_OF_NUM_ADD] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "it" (STRIP_ASSUME_TAC o SPEC `j:num`) THEN
  USE_THEN "it" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
  SUBGOAL_THEN `(a:real^N) IN ball(vec 0,R - l - &k * l) /\
                (b:real^N) IN ball(vec 0,R - l - &k * l) /\
                (a:real^N) IN ball(vec 0,R - l - &j * l) /\
                (b:real^N) IN ball(vec 0,R - l - &j * l) /\
                vec 0 IN ball(vec 0:real^N,R - l - &k * l) /\
                vec 0 IN ball(vec 0:real^N,R - l - &j * l)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `norm(a:real^N) < r1 /\ norm(b:real^N) < r1` MP_TAC THENL
     [REWRITE_TAC[GSYM IN_BALL_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_BALL_0; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) = b` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `S:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cmp_deck (top,atlas) (g:A->real^N^N) x (E:real^N^N) rho
                   (ball(vec 0,R - l - &k * l)) (ITER k (tau:real^N->real^N))` THEN
    UNDISCH_TAC `cmp_deck (top,atlas) (g:A->real^N^N) x (E:real^N^N) rho
                   (ball(vec 0,R - l - &j * l)) (ITER j (tau:real^N->real^N))` THEN
    REWRITE_TAC[cmp_deck] THEN REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmp_deck (top,atlas) (g:A->real^N^N) x (E:real^N^N) rho
                  (ball(vec 0,R - l - &k * l)) (ITER j (tau:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPY_DECK_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^N,R - l - &j * l)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; SUBSET; IN_BALL_0] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                 `ball(vec 0:real^N,R - l - &k * l)`; `ITER j (tau:real^N->real^N)`;
                 `ITER k (tau:real^N->real^N)`; `b:real^N`] CMPK_DECK_RIGID) THEN
  ASM_REWRITE_TAC[CONNECTED_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ITER (k - j) (tau:real^N->real^N) (ITER j tau (vec 0)) = ITER j tau (vec 0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ITER_ADD] THEN SUBGOAL_THEN `(k:num) - j + j = k` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_THEN `ITER j (tau:real^N->real^N) (vec 0) = ITER k tau (vec 0)` (K ALL_TAC) THEN
  MP_TAC(ISPECL [`K:real`; `l:real`; `b1:real`; `R:real`; `(k:num) - j`; `N:num`]
    CMPT_PARAM_MONO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `q:real^N`; `(k:num) - j`; `b1:real`; `ITER j (tau:real^N->real^N) (vec 0)`]
    CMPY_NO_PERIOD) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&j * l + norm(vec 0:real^N)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ITER j (tau:real^N->real^N) w`)) (concl th) &&
      can (find_term ((=) `norm(w:real^N)`)) (concl th))) THEN
    REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The counting bound.  The N disjoint images tau_q^k(S), k < N, lie in      *)
(* B(0,2 r1), each has pullback volume V1 = int_S sqrt(det G), and sqrt(det  *)
(* G) <= sqrt(2)^n there, so N V1 <= sqrt(2)^n |B(0,2 r1)|.                  *)
(* ========================================================================= *)

let CMPT_COUNT = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K rho R q N b1 r1 S.
        cmp_pullsetup (top,atlas) g x E K rho /\ R < rho /\ norm q < R /\
        cmp_psi (top,atlas) g x E q = x /\ ~(q = vec 0) /\ &0 < b1 /\ &0 < r1 /\
        &16 * &N pow 3 * norm q pow 2 < b1 pow 2 /\ &4 * norm q <= b1 /\
        &2 * b1 + &(N + 1) * norm q <= R /\
        K * (&N * norm q + &2 * b1) pow 2 <= inv(&2) /\
        &N * norm q < b1 /\ r1 + &N * norm q <= R /\ &N * norm q <= r1 /\
        &2 * r1 <= rho /\
        S SUBSET ball(vec 0,r1) /\ lebesgue_measurable S /\
        (!a b. a IN S /\ b IN S /\
               cmp_psi (top,atlas) g x E a = cmp_psi (top,atlas) g x E b
               ==> a = b) /\
        (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w)))) absolutely_integrable_on S
        ==> &N * drop(integral S (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))) <=
            sqrt(&2) pow dimindex(:N) * measure(ball(vec 0:real^N,&2 * r1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CMPW_SETUP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cmp_pullsetup]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                 `q:real^N`] CMPK_TAU) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `tau = cmp_tau (top,atlas) (g:A->real^N^N) (x:A) (E:real^N^N) rho q` THEN
  ABBREV_TAC `l = norm(q:real^N)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `rho:real`; `R - l`; `l:real`;
                 `tau:real^N->real^N`] CMPY_ITER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "it") THEN
  ABBREV_TAC `f = \w:real^N. lift(sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N)
                                             x (E:real^N^N) w)))` THEN
  ABBREV_TAC `V1 = drop(integral S (f:real^N->real^1))` THEN
  ABBREV_TAC `c = sqrt(&2) pow dimindex(:N)` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < N
        ==> IMAGE (ITER k (tau:real^N->real^N)) S SUBSET ball(vec 0,&2 * r1) /\
            measurable(IMAGE (ITER k tau) S) /\
            V1 <= c * measure(IMAGE (ITER k tau) S)`
  (LABEL_TAC "per") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "it" (STRIP_ASSUME_TAC o SPEC `k:num`) THEN
    SUBGOAL_THEN `&k * l + l <= &N * l` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(REAL_ARITH `(a + &1) * l = a * l + l`); REAL_OF_NUM_ADD] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `S SUBSET ball(vec 0:real^N,R - l - &k * l)` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^N,r1)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_BALL_0] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (ITER k (tau:real^N->real^N)) S SUBSET ball(vec 0,&2 * r1)`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `a:real^N` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `norm(a:real^N) < r1` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM IN_BALL_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&k * l + norm(a:real^N)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `ITER k (tau:real^N->real^N) w`)) (concl th) &&
          can (find_term ((=) `norm(w:real^N)`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `!a b. a IN S /\ b IN S /\ ITER k (tau:real^N->real^N) a = ITER k tau b
                        ==> a = b`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) a`))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cmp_deck (top,atlas) (g:A->real^N^N) x (E:real^N^N) rho
                     (ball(vec 0,R - l - &k * l)) (ITER k (tau:real^N->real^N))` THEN
      REWRITE_TAC[cmp_deck] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(a:real^N) IN ball(vec 0,R - l - &k * l) /\
                    (b:real^N) IN ball(vec 0,R - l - &k * l)` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`;
                   `ball(vec 0:real^N,R - l - &k * l)`; `ITER k (tau:real^N->real^N)`;
                   `S:real^N->bool`] CMPT_DECK_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `measurable(IMAGE (ITER k (tau:real^N->real^N)) S)` ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^N,&2 * r1)` THEN ASM_REWRITE_TAC[MEASURABLE_BALL] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
      ASM_REWRITE_TAC[LE_REFL; differentiable_on] THEN
      X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_AT_WITHIN THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(vec 0:real^N,R - l - &k * l)` THEN
      REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[cmp_deck]; ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "V1" THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      can (find_term ((=) `IMAGE (ITER k (tau:real^N->real^N)) S`)) (concl th)
      then REWRITE_TAC[GSYM th] else failwith "") THEN
    MP_TAC(ISPECL [`\w:real^N. sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N)
                                             x (E:real^N^N) w))`;
                   `IMAGE (ITER k (tau:real^N->real^N)) S`; `c:real`]
      CMPT_INTEGRAL_LE_MEASURE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC CMPT_SQRTDET_LE THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
    SUBGOAL_THEN `norm(y:real^N) < rho` ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN ball(vec 0,&2 * r1)` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_BALL_0; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j k. j IN {n | n < N} /\ k IN {n | n < N} /\ ~(j = k)
          ==> DISJOINT (IMAGE (ITER j (tau:real^N->real^N)) S) (IMAGE (ITER k tau) S)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `k:num`] THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(j:num) < k \/ k < j` MP_TAC THENL
     [UNDISCH_TAC `~(j:num = k)` THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                     `q:real^N`; `N:num`; `b1:real`; `r1:real`; `S:real^N->bool`;
                     `a:real^N`; `b:real^N`; `j:num`; `k:num`] CMPT_DISJOINT);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `rho:real`; `R:real`;
                     `q:real^N`; `N:num`; `b1:real`; `r1:real`; `S:real^N->bool`;
                     `b:real^N`; `a:real^N`; `k:num`; `j:num`] CMPT_DISJOINT)] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. IMAGE (ITER k (tau:real^N->real^N)) S`; `{n:num | n < N}`]
    HAS_MEASURE_DISJOINT_UNIONS_IMAGE) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      USE_THEN "per" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k:num < N`))) THEN SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE (\k. IMAGE (ITER k (tau:real^N->real^N)) S) {n | n < N}) SUBSET
    ball(vec 0,&2 * r1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "per" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k:num < N`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c * measure(UNIONS (IMAGE (\k. IMAGE (ITER k (tau:real^N->real^N)) S)
                                       {n | n < N}))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM SUM_LMUL] THEN
    MP_TAC(ISPECL [`V1:real`; `{n:num | n < N}`] SUM_CONST) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    USE_THEN "per" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k:num < N`))) THEN SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURE_SUBSET THEN ASM_REWRITE_TAC[MEASURABLE_BALL]]]);;

(* ========================================================================= *)
(* The segment-domain part S = D0 cap B(0,r1) of the tangent ball:           *)
(* measurable, Psi injective on S, sqrt(det G) absolutely integrable on S,   *)
(* and by relative volume comparison (S1, Ric >= -(n-1) K from |Rm| <= K)    *)
(* its pullback volume V1 = vol B(x,r1) satisfies v Vm(r1) <= V1 Vm(r) for   *)
(* vol B(x,r) = v.                                                           *)
(* ========================================================================= *)

let CMPT_SEG_SET = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K r v r1.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 <= K /\ &0 < r1 /\ r1 < r /\
        compact_in top (top closure_of mfd_ball (top,atlas) g x r) /\
        (!y. y IN mfd_ball (top,atlas) g x r ==> mfd_rm_norm atlas g y <= K) /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v
        ==> ?S. S SUBSET ball(vec 0,r1) /\ lebesgue_measurable S /\
                (!a b. a IN S /\ b IN S /\
                       cmp_psi (top,atlas) g x E a = cmp_psi (top,atlas) g x E b
                       ==> a = b) /\
                (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))
                absolutely_integrable_on S /\
                v * cmp_vmodel (:N) (--K) r1 <=
                drop(integral S (\w. lift(sqrt(det(cmp_expmetric (top,atlas) g x E w))))) *
                cmp_vmodel (:N) (--K) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x r SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPQ_COMPACT_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `D0 = {w:real^N | ?s. &1 < s /\ norm(s % w) < r /\
                         mfd_dist (top,atlas) (g:A->real^N^N) x
                           (mfd_exp (top,atlas) g x ((E:real^N^N) ** (s % w))) =
                         norm(s % w)}` THEN
  ABBREV_TAC `f = \w:real^N. lift(sqrt(det(cmp_expmetric (top,atlas) (g:A->real^N^N)
                                             x (E:real^N^N) w)))` THEN
  EXISTS_TAC `D0 INTER ball(vec 0:real^N,r1)` THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  SUBGOAL_THEN `lebesgue_measurable (D0 INTER ball(vec 0:real^N,r1))` ASSUME_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN REWRITE_TAC[LEBESGUE_MEASURABLE_BALL] THEN
    EXPAND_TAC "D0" THEN MATCH_MP_TAC CMPQ_SEG0_MEAS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a b. a IN D0 INTER ball(vec 0:real^N,r1) /\ b IN D0 INTER ball(vec 0,r1) /\
          cmp_psi (top,atlas) (g:A->real^N^N) x (E:real^N^N) a = cmp_psi (top,atlas) g x E b
          ==> a = b`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN EXPAND_TAC "D0" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; cmp_psi] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:real`) ASSUME_TAC)
      (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (X_CHOOSE_TAC `s':real`) ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`; `b:real^N`; `s':real`]
      CMPQ_SEG0_SUB) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`; `a:real^N`; `b:real^N`;
                   `s:real`] CMPQ_SEG_INJ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:real^N->real^1) continuous_on ball(vec 0,r)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC CMPB_SQRTDET_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?B. !w. w IN cball(vec 0:real^N,r1) ==> norm((f:real^N->real^1) w) <= B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^1`; `cball(vec 0:real^N,r1)`] COMPACT_CONTINUOUS_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^N,r)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `measurable(D0 INTER ball(vec 0:real^N,r1))` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^N,r1)` THEN ASM_REWRITE_TAC[MEASURABLE_BALL; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^1) absolutely_integrable_on (D0 INTER ball(vec 0,r1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\w:real^N. lift B` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^N,r)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL_0] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[integrable_on] THEN
      EXISTS_TAC `measure(D0 INTER ball(vec 0:real^N,r1)) % lift B` THEN
      MATCH_MP_TAC HAS_INTEGRAL_CONST_GEN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_DROP; IN_INTER; IN_BALL_0] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `r:real`; `r1:real`]
    CMPQ_BALL_VOLUME) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:N)`] CMP_RELVOL) THEN REWRITE_TAC[CMP_RELVOL_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`; `x:A`;
    `K:real`; `r:real`; `r1:real`; `r:real`;
    `drop(integral (D0 INTER ball(vec 0:real^N,r1)) (f:real^N->real^1))`; `v:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `w:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^N^N) x r` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `--K`; `w:real^N`] CMPZ_MFD_RICCI_SEC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:real^N`; `u':real^N`] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `y:A`; `u:real^N`; `u':real^N`]
        MFD_SECTIONAL_LE_RM_NORM) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "mfd_rm_norm" with Failure _ -> false))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Injectivity of Psi on B(0,i0).  With b = r1 = b1, rho = 8 b, R = 4 b, 256 *)
(* K b^2 <= 1 and 64 N^2 i0 <= b, a failure of injectivity gives a deck      *)
(* point q <> 0 with |q| < 2 i0 (CMPK_LOOP), and the counting bound with the *)
(* volume comparison contradicts the choice of N.                            *)
(* ========================================================================= *)

let CMPT_ARITH = prove
 (`!K b n l.
        &0 <= K /\ &0 < b /\ &256 * K * b pow 2 <= &1 /\ &1 <= n /\ &0 <= l /\
        &32 * n pow 2 * l < b
        ==> &16 * n pow 3 * l pow 2 < b pow 2 /\ &4 * l <= b /\
            &2 * b + (n + &1) * l <= &4 * b /\ K * (n * l + &2 * b) pow 2 <= inv(&2) /\
            n * l < b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= n pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= n * l /\ n * l <= n pow 2 * l /\ l <= n * l /\ l <= n pow 2 * l`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `n * l < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= n pow 3 * l pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 * n pow 3 * l pow 2 <= (&32 * n pow 2 * l) pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&32 * n pow 2 * l) pow 2 = (&1024 * n) * (n pow 3 * l pow 2) /\
                  &16 * n pow 3 * l pow 2 = &16 * (n pow 3 * l pow 2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&32 * n pow 2 * l) pow 2 < b pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * (&3 * b) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `K * (&3 * b) pow 2 = &9 * (K * b pow 2)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ASM_REAL_ARITH_TAC]]);;

let CMPT_VMODEL_POS = prove
 (`!K t. &0 <= K /\ &0 < t ==> &0 < cmp_vmodel (:N) (--K) t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--K`; `t:real`] (INST_TYPE [`:N`,`:N`] CMPV_VMODEL_FACTS)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CMP_SN_POS THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `t:real`]) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let CMPT_INJ = prove
 (`!top atlas (g:A->real^N^N) (x:A) (E:real^N^N) K r v0 v b N i0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ x IN topspace top /\
        mfd_orthonormal_frame g x E /\ &0 < K /\ &0 < b /\ &16 * b <= r /\
        &256 * K * b pow 2 <= &1 /\ 1 <= N /\ &0 < i0 /\ &64 * &N pow 2 * i0 <= b /\
        compact_in top (top closure_of mfd_ball (top,atlas) g x r) /\
        (!y. y IN mfd_ball (top,atlas) g x r ==> mfd_rm_norm atlas g y <= K) /\
        mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\ v0 <= v /\
        sqrt(&2) pow dimindex(:N) * measure(ball(vec 0:real^N,&2 * b)) *
        cmp_vmodel (:N) (--K) r < &N * v0 * cmp_vmodel (:N) (--K) b
        ==> !w1 w2. norm w1 < i0 /\ norm w2 < i0 /\
                    cmp_psi (top,atlas) g x E w1 = cmp_psi (top,atlas) g x E w2
                    ==> w1 = w2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`w1:real^N`; `w2:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &N /\ &1 <= &N pow 2 /\ i0 <= &N pow 2 * i0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ (b ==> c) ==> a /\ b /\ c`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x r SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPQ_COMPACT_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cmp_pullsetup (top,atlas) (g:A->real^N^N) x (E:real^N^N) K (&8 * b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[cmp_pullsetup] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `K * (&8 * b) pow 2 = &64 * (K * b pow 2) /\ &0 <= K * b pow 2`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [CONV_TAC REAL_RING;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE]];
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `mfd_tball (g:A->real^N^N) x r` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[mfd_tball; SUBSET; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:A` THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `&8 * b`; `&4 * b`;
                 `i0:real`; `w1:real^N`; `w2:real^N`] CMPK_LOOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `r:real`; `v:real`;
                 `b:real`] CMPT_SEG_SET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&N pow 2 * norm(q:real^N) < &N pow 2 * (&2 * i0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real`; `b:real`; `&N`; `norm(q:real^N)`] CMPT_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `&8 * b`; `&4 * b`;
                 `q:real^N`; `N:num`; `b:real`; `b:real`; `S:real^N->bool`] CMPT_COUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `V1 = drop(integral S (\w. lift(sqrt(det(cmp_expmetric (top,atlas)
                     (g:A->real^N^N) x (E:real^N^N) w)))))` THEN
  ABBREV_TAC `Vb = cmp_vmodel (:N) (--K) b` THEN
  ABBREV_TAC `Vr = cmp_vmodel (:N) (--K) r` THEN
  SUBGOAL_THEN `&0 < Vb /\ &0 < Vr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Vb" THEN EXPAND_TAC "Vr" THEN CONJ_TAC THEN
    MATCH_MP_TAC CMPT_VMODEL_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N * v0 * Vb <= &N * v * Vb` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N * v * Vb <= &N * V1 * Vr` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `(&N * V1) * Vr <=
                (sqrt(&2) pow dimindex(:N) * measure(ball(vec 0:real^N,&2 * b))) * Vr`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Cheeger-Gromov-Taylor bound in dimension n: the choice of b (16 b <=  *)
(* r, 256 K b^2 <= 1), of K' >= K with pi / sqrt K' <= r (for S3), of N      *)
(* (counting) and of i0; then exp_x is injective on the tangent ball of      *)
(* radius i0 (CMPT_INJ in an orthonormal frame) with injective differential  *)
(* (S3), so it parametrizes that ball (GEOS_INJECTIVE_PARAM).                *)
(* ========================================================================= *)

let CMPT_B_CHOICE = prove
 (`!K r. &0 < K /\ &0 < r ==> ?b. &0 < b /\ &16 * b <= r /\ &256 * K * b pow 2 <= &1`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `min r (inv(sqrt K)) / &16` THEN
  ABBREV_TAC `m = min r (inv(sqrt K))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= r /\ m <= inv(sqrt K)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&256 * K * (m / &16) pow 2 = K * m pow 2` SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * inv(sqrt K) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_MUL_RINV;
                 REAL_LT_IMP_NZ; REAL_LE_REFL]]);;

let CMPT_KP_CHOICE = prove
 (`!K r. &0 < K /\ &0 < r
         ==> ?K'. &0 < K' /\ K <= K' /\ &0 < pi / sqrt K' /\ pi / sqrt K' <= r`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `max K ((pi / r) pow 2)` THEN
  ABBREV_TAC `K' = max K ((pi / r) pow 2)` THEN
  SUBGOAL_THEN `K <= K' /\ (pi / r) pow 2 <= K'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K'" THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K' /\ &0 < sqrt K' /\ &0 < pi / r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ c ==> a /\ b /\ c`) THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; DISCH_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[PI_POS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[PI_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `pi / r <= sqrt K'` MP_TAC THENL
   [MP_TAC(ISPECL [`(pi / r) pow 2`; `K':real`] SQRT_MONO_LE) THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r * (pi / r) <= r * sqrt K'` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * (pi / r) = pi` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;

let CMPT_CGT_GEN = prove
 (`!K r v0. &0 < K /\ &0 < r /\ &0 < v0
      ==> ?i0. &0 < i0 /\ i0 < r /\
            !top atlas (g:A->real^N^N) x.
               hausdorff_space top /\ smooth_manifold_atlas top atlas /\
               riemannian_metric atlas g /\ x IN topspace top /\
               compact_in top (top closure_of mfd_ball (top,atlas) g x r) /\
               (!y. y IN mfd_ball (top,atlas) g x r ==> mfd_rm_norm atlas g y <= K) /\
               (?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\ v0 <= v)
               ==> mfd_inj_ball (top,atlas) g x i0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`K:real`; `r:real`] CMPT_B_CHOICE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`K:real`; `r:real`] CMPT_KP_CHOICE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < cmp_vmodel (:N) (--K) b /\ &0 < cmp_vmodel (:N) (--K) r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CMPT_VMODEL_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sqrt(&2) pow dimindex(:N) * measure(ball(vec 0:real^N,&2 * b)) *
          cmp_vmodel (:N) (--K) r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL;
                                                  REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v0 * cmp_vmodel (:N) (--K) b` REAL_ARCH) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num` o SPEC
   `sqrt(&2) pow dimindex(:N) * measure(ball(vec 0:real^N,&2 * b)) *
    cmp_vmodel (:N) (--K) r`) THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT; ARITH_RULE `n < 1 <=> n = 0`] THEN DISCH_TAC THEN
    UNDISCH_TAC
     `sqrt(&2) pow dimindex(:N) * measure(ball(vec 0:real^N,&2 * b)) *
      cmp_vmodel (:N) (--K) r < &N * v0 * cmp_vmodel (:N) (--K) b` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &64 * &N pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (b / (&64 * &N pow 2)) (pi / sqrt K' / &2)` THEN
  ABBREV_TAC `i0 = min (b / (&64 * &N pow 2)) (pi / sqrt K' / &2)` THEN
  SUBGOAL_THEN `&0 < i0 /\ i0 < pi / sqrt K' /\ &64 * &N pow 2 * i0 <= b`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "i0" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_MIN_LT] THEN DISJ2_TAC THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `min (b / (&64 * &N pow 2)) (pi / sqrt K' / &2) <= b / (&64 * &N pow 2)`
      MP_TAC THENL [REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `x:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x r SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPQ_COMPACT_DOM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`; `E:real^N^N`; `K:real`; `r:real`; `v0:real`;
                 `v:real`; `b:real`; `N:num`; `i0:real`] CMPT_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x i0 SUBSET mfd_tball g x r /\
                mfd_tball (g:A->real^N^N) x i0 SUBSET mfd_tball g x (pi / sqrt K') /\
                mfd_tball (g:A->real^N^N) x (pi / sqrt K') SUBSET mfd_tball g x r`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mfd_tball; SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_inj_ball] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x:A`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tball (g:A->real^N^N) x i0 SUBSET mfd_exp_dom (top,atlas) g x`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC GEOS_INJECTIVE_PARAM THEN ASM_REWRITE_TAC[GEOI_TBALL_OPEN] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
    EXISTS_TAC `mfd_exp_dom (top,atlas) (g:A->real^N^N) x` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`v1:real^N`; `v2:real^N`] THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
    SUBGOAL_THEN `!u:real^N. (E:real^N^N) ** (matrix_inv E ** u) = u` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `!u:real^N. norm(matrix_inv(E:real^N^N) ** u) = mfd_tnorm (g:A->real^N^N) x u`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:real^N` THEN
      MP_TAC(ISPECL [`g:A->real^N^N`; `x:A`; `E:real^N^N`; `matrix_inv(E:real^N^N) ** u`]
        CMPP_TNORM_FRAME) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `matrix_inv(E:real^N^N) ** v1 = matrix_inv E ** v2` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `i0:real`)) (concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "cmp_psi" with Failure _ -> false))
          (concl th))) THEN
      ASM_REWRITE_TAC[cmp_psi];
      DISCH_THEN(MP_TAC o AP_TERM `\u:real^N. (E:real^N^N) ** u`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:A)`; `(:N)`] CMP_CONJUGATE_RADIUS) THEN
  REWRITE_TAC[CMP_CONJUGATE_RADIUS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                             `g:A->real^N^N`; `x:A`; `K':real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `e1:real^N`; `e2:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:A) IN mfd_ball (top,atlas) (g:A->real^N^N) x r /\ y IN topspace top`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) (g:A->real^N^N) x (pi / sqrt K')` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[MFD_JOINABLE_IN_TOPSPACE]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `y:A`; `e1:real^N`; `e2:real^N`]
      MFD_SECTIONAL_LE_RM_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "mfd_rm_norm" with Failure _ -> false))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`v1:real^N`; `h:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v1:real^N` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `pi / sqrt K'`)) (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The headline CMP_T2_CGT (Cheeger-Gromov-Taylor, MT Thm 1.36 local form):  *)
(* the statement constant, with the text of P2C_REQ_CGT_STATEMENT, and its   *)
(* proof from CMPT_CGT_GEN at dimension 3.                                   *)
(* ========================================================================= *)

let CMP_T2_CGT_STATEMENT = new_definition
 `CMP_T2_CGT_STATEMENT (u:A->bool) <=>
    !K r v0. &0 < K /\ &0 < r /\ &0 < v0
      ==> ?i0. &0 < i0 /\ i0 < r /\
            !top atlas g x.
               hausdorff_space (top:A topology) /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ x IN topspace top /\
               compact_in top (top closure_of mfd_ball (top,atlas) g x r) /\
               (!y. y IN mfd_ball (top,atlas) g x r ==> mfd_rm_norm atlas g y <= K) /\
               (?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\ v0 <= v)
               ==> mfd_inj_ball (top,atlas) g x i0`;;

let CMP_T2_CGT = prove
 (`!u:A->bool. CMP_T2_CGT_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[CMP_T2_CGT_STATEMENT] THEN MATCH_ACCEPT_TAC CMPT_CGT_GEN);;

