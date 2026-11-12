(* ========================================================================= *)
(* Unit pc_pde_torus: analysis on the torus T^N = R^N / Z^N for smooth       *)
(* Z^N-periodic maps on real^N.  In order: generic layers copied from the    *)
(* Navier_Stokes development (periodic integrals, smooth parameter           *)
(* integrals); periodic maps; cube integrals and integration by parts; the   *)
(* norms pde_hs2 (recursion PDE_HS2_SUC); line means and iterated means; the *)
(* Sobolev embedding PDE_TORUS_SOBOLEV; interpolation PDE_TORUS_INTERP;      *)
(* Leibniz and commutator bounds.                                            *)
(* ========================================================================= *)

(* Lines 1-555 of the file src/ns_periodic_uniq.ml of the Navier_Stokes      *)
(* development (github.com/hol-light-family/Navier_Stokes): the generic      *)
(* layer (differentiation under the integral sign, unit-cube splitting and   *)
(* shift invariance of periodic integrals, periodic integration by parts     *)
(* along a coordinate, Gronwall with zero initial value, integer periods),   *)
(* with its needs line adapted.                                              *)

needs "src/ns_spacetime.ml";;
needs "src/pc_pde_tdefs.ml";;
needs "src/pc_pde_seeley.ml";;
prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* In the Navier_Stokes development, ns_periodic_uniq.ml proves the          *)
(* uniqueness of periodic classical solutions of the Navier-Stokes system on *)
(* R^3 x [0,tmax] by the energy method; only its generic first part is used  *)
(* here.                                                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Differentiation under the integral sign (Leibniz integral rule).          *)
(* Adapted from earlier HOL Light work; only library lemmas are used.       *)
(* ------------------------------------------------------------------------- *)

let SLICE_CONTINUOUS_FST = prove
 (`!(k:real^M->real^P->real^N) a b c d t.
     (\z. k (fstcart z) (sndcart z)) continuous_on
       interval[pastecart a c,pastecart b d] /\
     t IN interval[c,d]
     ==> (\s. k s t) continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\s. (k:real^M->real^P->real^N) s t) =
                (\z. k (fstcart z) (sndcart z)) o (\s. pastecart s t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[pastecart (a:real^M) (c:real^P),pastecart b d]` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GSYM PCROSS_INTERVAL;
                    PASTECART_IN_PCROSS] THEN
    ASM_SIMP_TAC[]]);;

let ONORM_DROP_CMUL_LE = prove
 (`!v:real^N B. norm v <= B ==> onorm(\h:real^1. drop h % v) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\h:real^1. drop h % (v:real^N)` ONORM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
  X_GEN_TAC `h:real^1` THEN REWRITE_TAC[NORM_MUL] THEN
  SIMP_TAC[NORM_REAL; GSYM drop] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

let LEIBNIZ_ARITH = prove
 (`!e n C. &0 < e /\ &0 <= n /\ &0 <= C ==> (e / (C + &1) * n) * C <= e * n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e / (C + &1) * n) * C = e * n - (e * n) / (C + &1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 <= C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let PARAMETRIC_MVT_BOUND = prove
 (`!(g:real^1->real^N) g' v t0 t B.
     (!tau. tau IN segment[t0,t]
            ==> (g has_vector_derivative g' tau) (at tau within segment[t0,t])) /\
     (!tau. tau IN segment[t0,t] ==> norm(g' tau - v) <= B)
     ==> norm(g t - g t0 - drop(t - t0) % v) <= B * norm(t - t0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\tau. (g:real^1->real^N) tau - drop tau % v`;
                 `\tau h. drop h % ((g':real^1->real^N) tau - v)`;
                 `segment[t0:real^1,t]`; `B:real`] DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_SEGMENT] THEN CONJ_TAC THEN
    X_GEN_TAC `tau:real^1` THEN DISCH_TAC THENL
     [REWRITE_TAC[GSYM has_vector_derivative] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[has_vector_derivative] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC ONORM_DROP_CMUL_LE THEN ASM_SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `t0:real^1`]) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT; DROP_SUB] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    VECTOR_ARITH_TAC]);;

let HAS_VECTOR_DERIVATIVE_PARAMETRIC_INTEGRAL = prove
 (`!(f:real^M->real^1->real^N) ft a b c d t0.
     (!s t. s IN interval[a,b] /\ t IN interval[c,d]
            ==> ((\t. f s t) has_vector_derivative ft s t)
                (at t within interval[c,d])) /\
     (\z. ft (fstcart z) (sndcart z)) continuous_on
        interval[pastecart a c,pastecart b d] /\
     (!t. t IN interval[c,d] ==> (\s. f s t) integrable_on interval[a,b]) /\
     t0 IN interval[c,d]
     ==> ((\t. integral (interval[a,b]) (\s. f s t)) has_vector_derivative
          integral (interval[a,b]) (\s. ft s t0))
         (at t0 within interval[c,d])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN interval[c,d]
        ==> (\s. (ft:real^M->real^1->real^N) s t) integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC SLICE_CONTINUOUS_FST THEN
    MAP_EVERY EXISTS_TAC [`c:real^1`; `d:real^1`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN_ALT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `C = content(interval[a:real^M,b])` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[CONTENT_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. (ft:real^M->real^1->real^N) (fstcart z) (sndcart z)`;
                 `interval[pastecart (a:real^M) (c:real^1),pastecart b d]`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (C + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 <= C ==> &0 < C + &1`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `del:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[t0:real^1,t] SUBSET interval[c,d]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:real^1`; `d:real^1`] CONVEX_INTERVAL) THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN interval[a,b]
        ==> norm((f:real^M->real^1->real^N) s t - f s t0 -
                 drop(t - t0) % ft s t0) <= e / (C + &1) * norm(t - t0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC PARAMETRIC_MVT_BOUND THEN
    EXISTS_TAC `(ft:real^M->real^1->real^N) s` THEN CONJ_TAC THEN
    X_GEN_TAC `tau:real^1` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[c:real^1,d]` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "has_vector_derivative"
                                 with Failure _ -> false)) (concl th))) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (s:real^M) (t0:real^1)`;
                                    `pastecart (s:real^M) (tau:real^1)`]) THEN
      REWRITE_TAC[GSYM PCROSS_INTERVAL; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART; DIST_PASTECART_CANCEL] THEN
      REWRITE_TAC[dist] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`t0:real^1`; `t:real^1`; `tau:real^1`]
        DIST_IN_CLOSED_SEGMENT) THEN
      ASM_REWRITE_TAC[dist] THEN
      MP_TAC(ISPECL [`t0:real^1`; `t:real^1`] NORM_SUB) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. (f:real^M->real^1->real^N) s t - f s t0 - drop(t - t0) % ft s t0`;
    `a:real^M`; `b:real^M`;
    `integral (interval[a,b]) (\s. (f:real^M->real^1->real^N) s t) -
     integral (interval[a,b]) (\s. f s t0) -
     drop(t - t0) % integral (interval[a,b]) (\s. ft s t0)`;
    `e / (C + &1) * norm(t - t0:real^1)`] HAS_INTEGRAL_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
        MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_SIMP_TAC[]];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC LEIBNIZ_ARITH THEN ASM_REWRITE_TAC[NORM_POS_LE]);;


(* Real-valued form of the Leibniz rule, parameter in a real interval.     *)

let NSPU_REAL_PARAMETRIC_INTEGRAL = prove
 (`!(h:real^M->real->real) h' a b c d t0.
     (!x s. x IN interval[a,b] /\ s IN real_interval[c,d]
            ==> ((\s. h x s) has_real_derivative h' x s)
                (atreal s within real_interval[c,d])) /\
     (\z. lift(h' (fstcart z) (drop(sndcart z)))) continuous_on
        (interval[a,b] PCROSS interval[lift c,lift d]) /\
     (!s. s IN real_interval[c,d]
          ==> (\x. lift(h x s)) integrable_on interval[a,b]) /\
     t0 IN real_interval[c,d]
     ==> ((\s. drop(integral (interval[a,b]) (\x. lift(h x s))))
          has_real_derivative
          drop(integral (interval[a,b]) (\x. lift(h' x t0))))
         (atreal t0 within real_interval[c,d])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  MP_TAC(ISPECL [`\x:real^M t:real^1. lift((h:real^M->real->real) x (drop t))`;
                 `\x:real^M t:real^1. lift((h':real^M->real->real) x (drop t))`;
                 `a:real^M`; `b:real^M`; `lift c`; `lift d`; `lift t0`]
         HAS_VECTOR_DERIVATIVE_PARAMETRIC_INTEGRAL) THEN
  REWRITE_TAC[LIFT_DROP; GSYM PCROSS_INTERVAL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_REAL_VECTOR_DERIVATIVE_WITHIN;
                              IMAGE_LIFT_REAL_INTERVAL; o_DEF]) THEN
  ASM_REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
  ASM_SIMP_TAC[]);;

(* Continuity everywhere of a real-valued function on R^N gives continuity *)
(* of its lift on any set, hence integrability on boxes.                   *)

let NSPU_RCONT_CONTINUOUS_ON = prove
 (`!(g:real^N->real) s. (!x. g real_continuous (at x))
                        ==> (\x. lift(g x)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF]);;

let NSPU_RCONT_INTEGRABLE = prove
 (`!(g:real^N->real) a b. (!x. g real_continuous (at x))
                          ==> (\x. lift(g x)) integrable_on interval[a,b]`,
  SIMP_TAC[INTEGRABLE_CONTINUOUS; NSPU_RCONT_CONTINUOUS_ON]);;


(* ========================================================================= *)
(* Periodic functions on the unit cube: translation invariance of the       *)
(* integral and periodic integration by parts along a coordinate.           *)
(* ========================================================================= *)

let NSPU_UNIT_CUBE_SPLIT = prove
 (`!j h. 1 <= j /\ j <= dimindex(:N) /\ &0 <= h /\ h <= &1
         ==> interval[vec 0,vec 1] INTER {x:real^N | x$j <= h} =
             interval[vec 0,(lambda i. if i = j then h else &1)] /\
             interval[vec 0,vec 1] INTER {x:real^N | x$j >= h} =
             interval[h % basis j,vec 1] /\
             interval[h % basis j,h % basis j + vec 1] INTER
               {x:real^N | x$j <= &1} =
             interval[h % basis j,vec 1] /\
             interval[h % basis j,h % basis j + vec 1] INTER
               {x:real^N | x$j >= &1} =
             interval[basis j,h % basis j + vec 1] /\
             interval[basis j:real^N,h % basis j + vec 1] =
             IMAGE (\x. basis j + x)
                   (interval[vec 0,(lambda i. if i = j then h else &1)])`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION; VECTOR_ADD_RID] THEN
  REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ; CONS_11] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VEC_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_ADD_COMPONENT; BASIS_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let NSPU_PERIODIC_INTEGRAL_SHIFT = prove
 (`!(g:real^N->real) j h.
     1 <= j /\ j <= dimindex(:N) /\ &0 <= h /\ h <= &1 /\
     (!x. g real_continuous (at x)) /\
     (!x. g(x + basis j) = g x)
     ==> integral (interval[vec 0,vec 1]) (\x. lift(g(x + h % basis j))) =
         integral (interval[vec 0,vec 1]) (\x. lift(g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`j:num`; `h:real`] NSPU_UNIT_CUBE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c:real^N = lambda i. if i = j then h else &1` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!a b:real^N. (\x. lift((g:real^N->real) x)) integrable_on interval[a,b]`
  ASSUME_TAC THENL [ASM_SIMP_TAC[NSPU_RCONT_INTEGRABLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. lift((g:real^N->real) x)) has_integral
     (integral (interval[vec 0,c]) (\x. lift(g x)) +
      integral (interval[h % basis j,vec 1]) (\x. lift(g x))))
    (interval[vec 0,vec 1])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPLIT THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `h:real`] THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. lift((g:real^N->real) x)) has_integral
     (integral (interval[h % basis j,vec 1]) (\x. lift(g x)) +
      integral (interval[vec 0,c]) (\x. lift(g x))))
    (interval[h % basis j,h % basis j + vec 1])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPLIT THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `&1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]; ALL_TAC] THEN
    REWRITE_TAC[GSYM HAS_INTEGRAL_TRANSLATION] THEN
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. lift((g:real^N->real) x)`;
                 `interval[vec 0:real^N,vec 1]`;
                 `h % basis j:real^N`] INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\x. lift((g:real^N->real)(x + h % basis j))) =
                (\x. lift(g(h % basis j + x)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[VECTOR_ADD_SYM]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION; VECTOR_ADD_RID] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  MATCH_ACCEPT_TAC VECTOR_ADD_SYM);;

let NSPU_LINE_DERIV_SHIFT = prove
 (`!(g:real^N->real) g' e x s.
     (!y. ((\r. g(y + r % e)) has_real_derivative g' y) (atreal (&0)))
     ==> ((\r. g(x + r % e)) has_real_derivative g'(x + s % e)) (atreal s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + s % e:real^N`) THEN DISCH_TAC THEN
  MP_TAC(INST [`\y:real. (g':real^N->real)(x + s % e)`,`g':real->real`;
               `&1`,`f':real`]
    (ISPECL [`\y:real. y = &0`; `\r:real. r - s`;
             `\r. (g:real^N->real)((x + s % e) + r % e)`]
         HAS_REAL_DERIVATIVE_CHAIN)) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT2) THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LID] THEN
  ANTS_TAC THENL [REAL_DIFF_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:real` THEN AP_TERM_TAC THEN
  VECTOR_ARITH_TAC);;

let NSPU_RCONT_COMPOSE = prove
 (`!(g:real^N->real) (k:real^M->real^N) s.
     (!x. g real_continuous (at x)) /\ k continuous_on s
     ==> (\z. lift(g(k z))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((g:real^N->real)((k:real^M->real^N) z))) =
                (\y. lift(g y)) o k`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[NSPU_RCONT_CONTINUOUS_ON]);;

let NSPU_PERIODIC_INTEGRAL_DERIVATIVE = prove
 (`!(g:real^N->real) g' j.
     1 <= j /\ j <= dimindex(:N) /\
     (!x. g real_continuous (at x)) /\ (!x. g' real_continuous (at x)) /\
     (!x. ((\s. g(x + s % basis j)) has_real_derivative g' x) (atreal (&0))) /\
     (!x. g(x + basis j) = g x)
     ==> integral (interval[vec 0,vec 1]) (\x. lift(g' x)) = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N s. (g:real^N->real)(x + s % basis j)`;
                 `\x:real^N s. (g':real^N->real)(x + s % basis j)`;
                 `vec 0:real^N`; `vec 1:real^N`; `&0`; `&1`; `&0`]
         NSPU_REAL_PARAMETRIC_INTEGRAL) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC NSPU_LINE_DERIV_SHIFT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC NSPU_RCONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[linear; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                  DROP_ADD; DROP_CMUL] THEN
      VECTOR_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC NSPU_RCONT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `((\s. drop(integral (interval[vec 0,vec 1])
                 (\x. lift((g:real^N->real)(x + s % basis j)))))
     has_real_derivative &0) (atreal (&0) within real_interval[&0,&1])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_WITHIN THEN
    MAP_EVERY EXISTS_TAC
     [`\s:real. drop(integral (interval[vec 0,vec 1])
                       (\x. lift((g:real^N->real) x)))`; `&1`] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_LT_01; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NSPU_PERIODIC_INTEGRAL_SHIFT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. drop(integral (interval[vec 0,vec 1])
                (\x. lift((g:real^N->real)(x + s % basis j))))`;
    `real_interval[&0,&1]`; `&0`;
    `drop(integral (interval[vec 0,vec 1]) (\x. lift((g':real^N->real) x)))`;
    `&0`] NS_REAL_DERIVATIVE_UNIQUE_WITHIN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[TRIVIAL_LIMIT_WITHIN_REALINTERVAL; IS_REALINTERVAL_INTERVAL;
             IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN
    REWRITE_TAC[EXTENSION; IN_REAL_INTERVAL; IN_SING] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM DROP_EQ; DROP_VEC]]);;

(* ========================================================================= *)
(* A derivative tactic, the Gronwall-type lemma, vanishing of a continuous  *)
(* nonnegative function with zero integral, and periodic extension.        *)
(* ========================================================================= *)

(* A variant of REAL_DIFF_CONV and REAL_DIFF_TAC from realanalysis.ml that  *)
(* also uses a list of local derivative facts about abstract functions.     *)
let NSPU_ETA_EXPAND th =
  let th = SPEC_ALL th in
  let tm = concl th in
  let f = lhand(rator tm) in
  if is_abs f then th else
  let ty = fst(dest_fun_ty(type_of f)) in
  let x = variant (frees tm) (mk_var("x",ty)) in
  let eth = ETA_CONV(mk_abs(x,mk_comb(f,x))) in
  CONV_RULE (RATOR_CONV(RATOR_CONV(RAND_CONV(K(SYM eth))))) th;;

let NSPU_DIFF_CONV ths =
  let ths = map NSPU_ETA_EXPAND ths in
  let partfn tm = let l,r = dest_comb tm in mk_pair(lhand l,r)
  and is_deriv = can (term_match [] `(f has_real_derivative f') net`) in
  let rec DIFF_CONV tm =
    try tryfind (fun th -> PART_MATCH partfn th (partfn tm))
                (ths @ !real_differentiation_theorems)
    with Failure _ ->
        let ith = tryfind (fun th ->
         PART_MATCH (partfn o repeat (snd o dest_imp)) th (partfn tm))
                    (!real_differentiation_theorems) in
        DIFF_ELIM ith
  and DIFF_ELIM th =
    let tm = concl th in
    if not(is_imp tm) then th else
    let t = lhand tm in
    if not(is_deriv t) then UNDISCH th
    else DIFF_ELIM (MATCH_MP th (DIFF_CONV t)) in
  DIFF_CONV;;

let NSPU_DIFF_TAC ths =
  let pth = MESON[]
   `(f has_real_derivative f') net
    ==> f' = g'
        ==> (f has_real_derivative g') net` in
  W(fun (asl,w) ->
    let th = MATCH_MP pth (NSPU_DIFF_CONV ths w) in
    let asms = map (concl o snd) asl in
    let hs = filter (fun h -> not (mem h asms)) (hyp th) in
    MATCH_MP_TAC(repeat (GEN_REWRITE_RULE I [IMP_IMP]) (itlist DISCH hs th)));;


let NSPU_GRONWALL_ZERO = prove
 (`!(e:real->real) e' c tmax.
     e(&0) = &0 /\
     (!t. t IN real_interval[&0,tmax]
          ==> &0 <= e t /\
              (e has_real_derivative e' t)
              (atreal t within real_interval[&0,tmax]) /\
              e' t <= c * e t)
     ==> !t. t IN real_interval[&0,tmax] ==> e t = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. --(exp(--(c * x)) * (e:real->real) x)`;
                 `\x. --(exp(--(c * x)) * ((e':real->real) x - c * e x))`;
                 `real_interval[&0,tmax]`; `&0`; `t:real`]
         HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      NSPU_DIFF_TAC [ASSUME `((e:real->real) has_real_derivative e' x)
                             (atreal x within real_interval[&0,tmax])`] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= a * (c * y - x) ==> &0 <= --(a * (x - c * y))`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `--(c * t)` REAL_EXP_POS_LT) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= exp(--(c * t)) * (e:real->real) t` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `exp(--(c * t)) * (e:real->real) t = &0` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; REAL_EXP_NZ]);;

let NSPU_INTEGRAL_EQ_0_CONTINUOUS = prove
 (`!(g:real^N->real).
     (!x. g real_continuous (at x)) /\
     (!x. x IN interval[vec 0,vec 1] ==> &0 <= g x) /\
     integral (interval[vec 0,vec 1]) (\x. lift(g x)) = vec 0
     ==> !x. x IN interval[vec 0,vec 1] ==> g x = &0`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((\x. lift((g:real^N->real) x)) has_integral vec 0)
                (interval[vec 0,vec 1])` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real`; `vec 0:real^N`; `vec 1:real^N`]
      NSPU_RCONT_INTEGRABLE) THEN
    ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((g:real^N->real) x)`;
                 `interval[vec 0:real^N,vec 1]`] HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_1] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i = 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP] THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `{x:real^N | x IN interval(vec 0,vec 1) /\
                            lift(g x) IN (:real^1) DIFF {vec 0}} = {}`
  MP_TAC THENL
   [MATCH_MP_TAC(MESON[OPEN_NOT_NEGLIGIBLE]
      `open (s:real^N->bool) /\ negligible s ==> s = {}`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[NSPU_RCONT_CONTINUOUS_ON; OPEN_INTERVAL; OPEN_DIFF;
                   OPEN_UNIV; CLOSED_SING];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{x:real^N | x IN interval[vec 0,vec 1] /\
                              ~(lift(g x) = vec 0)}` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
      MESON_TAC[SUBSET; INTERVAL_OPEN_SUBSET_CLOSED]];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; IN_DIFF; IN_UNIV;
                IN_SING] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `~(interval(vec 0:real^N,vec 1) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((g:real^N->real) x)`; `interval(vec 0:real^N,vec 1)`;
                 `vec 0:real^1`] CONTINUOUS_CONSTANT_ON_CLOSURE) THEN
  ASM_SIMP_TAC[NSPU_RCONT_CONTINUOUS_ON; CLOSURE_INTERVAL] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]);;

let NSPU_PERIODIC_NUM = prove
 (`!(g:real^N->A) v.
     (!x. g(x + v) = g x)
     ==> !n x. g(x + &n % v) = g x /\ g(x - &n % v) = g x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_SUB_RZERO] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `x + &n % v:real^N`
      (ASSUME `!x:real^N. (g:real^N->A)(x + v) = g x`)) THEN
    REWRITE_TAC[VECTOR_ARITH `(x + &n % v) + v = x + (&n + &1) % v:real^N`] THEN
    ASM_MESON_TAC[];
    MP_TAC(SPEC `x - (&n + &1) % v:real^N`
      (ASSUME `!x:real^N. (g:real^N->A)(x + v) = g x`)) THEN
    REWRITE_TAC[VECTOR_ARITH `(x - (&n + &1) % v) + v = x - &n % v:real^N`] THEN
    ASM_MESON_TAC[]]);;

let NSPU_PERIODIC_INTEGER = prove
 (`!(g:real^N->A) v k x.
     (!x. g(x + v) = g x) /\ integer k ==> g(x + k % v) = g x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INTEGER_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LNEG; GSYM VECTOR_SUB] THEN
  ASM_MESON_TAC[NSPU_PERIODIC_NUM]);;


(* Lines 1-575 (Part 0) of the file src/ns_param_avg.ml of the Navier_Stokes *)
(* development: differentiation under the integral sign for a parameter in   *)
(* real^M (tube argument, mean value inequality), smoothness of parameter    *)
(* integrals with partials under the integral                                *)
(* (NS_PARAM_INTEGRAL_SMOOTH, NS_PARAM_REAL_INTEGRAL_SMOOTH).  The needs     *)
(* line of that file (src/ns_profiles.ml, not used by Part 0) is dropped;    *)
(* the calculus it needs is loaded above.                                    *)
(* ========================================================================= *)
(* Smooth parameter integrals.  The radial average                          *)
(*   A_X(U)(X, eta) = int_0^1 U(s X, eta) ds        (ns_avg of ns_profiles)  *)
(* and the oriented moment integrals X A_X(U) = int_0^X U(x, eta) dx are    *)
(* smooth in (X, eta), including across the axis X = 0, and their partial   *)
(* derivatives are integrals of partial derivatives.                         *)
(*                                                                           *)
(* Part 0: differentiation under the integral sign for a parameter w in     *)
(* real^M and an integrand G jointly C^1 on an open set W of                *)
(* real^(M,P)finite_sum containing (cball w0 r) x [a,b]  (a tube argument,  *)
(* the mean value inequality and uniform continuity of the Jacobian).       *)
(* ========================================================================= *)


prioritize_real();;

type_invention_error := true;;

(* A compact fibre over w0 inside an open set W has a tube around it.       *)
let NSPA_TUBE = prove
 (`!(W:real^(M,P)finite_sum->bool) (w0:real^M) (k:real^P->bool).
     open W /\ compact k /\ (!t. t IN k ==> pastecart w0 t IN W)
     ==> ?r. &0 < r /\
             !w t. w IN cball(w0,r) /\ t IN k ==> pastecart w t IN W`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (\t:real^P. pastecart (w0:real^M) t) k`;
                 `(:real^(M,P)finite_sum) DIFF W`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; NOT_IN_EMPTY;
                  IN_IMAGE] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MAP_EVERY X_GEN_TAC [`w:real^M`; `t:real^P`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`pastecart (w0:real^M) (t:real^P)`;
                                `pastecart (w:real^M) (t:real^P)`]) THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; DIST_PASTECART_CANCEL; IN_IMAGE] THEN
  SUBGOAL_THEN `dist(w0:real^M,w) < d` MP_TAC THENL
   [UNDISCH_TAC `(w:real^M) IN cball(w0,d / &2)` THEN
    REWRITE_TAC[IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[REAL_NOT_LT]]);;

(* Continuity of the slices t |-> H(w, t).                                  *)
let NSPA_SLICE_CONTINUOUS_ON = prove
 (`!(H:real^(M,P)finite_sum->real^N) W (w:real^M) k.
     H continuous_on W /\ (!t. t IN k ==> pastecart w t IN W)
     ==> (\t. H(pastecart w t)) continuous_on k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t:real^P. (H:real^(M,P)finite_sum->real^N)(pastecart w t)) =
                H o (\t. pastecart w t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `W:real^(M,P)finite_sum->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

(* The derivative of a slice w |-> G(w, t) in the parameter w.              *)
let NSPA_SLICE_HAS_DERIVATIVE = prove
 (`!(G:real^(M,P)finite_sum->real^N) G' (x:real^M) (t:real^P).
     (G has_derivative G') (at (pastecart x t))
     ==> ((\x. G(pastecart x t)) has_derivative
          (\h. G'(pastecart h (vec 0)))) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^M. (G:real^(M,P)finite_sum->real^N)(pastecart x t)) =
                G o (\x. pastecart x t)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:real^M. (G':real^(M,P)finite_sum->real^N)
                               (pastecart h (vec 0))) =
                G' o (\h. pastecart h (vec 0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST]);;

let NSPA_LINEAR_PASTECART_0 = prove
 (`!(A:real^(M,P)finite_sum->real^N).
     linear A ==> linear (\h:real^M. A(pastecart h (vec 0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\h:real^M. (A:real^(M,P)finite_sum->real^N)(pastecart h (vec 0))) =
                A o (\h. pastecart h (vec 0))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINEAR_PASTECART THEN REWRITE_TAC[LINEAR_ID; LINEAR_ZERO]);;

(* Operator bound through the vectorized matrices.                          *)
let NSPA_VECTORIZE_BOUND = prove
 (`!(A:real^(M,P)finite_sum->real^N) B (h:real^M).
     linear A /\ linear B
     ==> norm(A(pastecart h (vec 0)) - B(pastecart h (vec 0))) <=
         norm(vectorize(matrix A) - vectorize(matrix B)) * norm h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`matrix(A:real^(M,P)finite_sum->real^N) -
                  matrix(B:real^(M,P)finite_sum->real^N)`;
                 `pastecart (h:real^M) (vec 0:real^P)`]
         COMPATIBLE_NORM_VECTORIZE) THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_SUB_RDISTRIB; MATRIX_WORKS; VECTORIZE_SUB;
               NORM_PASTECART_0]);;

(* Mean value step for one slice.                                            *)
let NSPA_MVT_STEP = prove
 (`!(G:real^(M,P)finite_sum->real^N) G' (w0:real^M) y (t:real^P) e.
     (!x. x IN segment[w0,y]
          ==> (G has_derivative G'(pastecart x t)) (at (pastecart x t))) /\
     (!x h. x IN segment[w0,y]
            ==> norm(G'(pastecart x t) (pastecart h (vec 0)) -
                     G'(pastecart w0 t) (pastecart h (vec 0))) <= e * norm h)
     ==> norm(G(pastecart y t) - G(pastecart w0 t) -
              G'(pastecart w0 t) (pastecart (y - w0) (vec 0)))
         <= e * norm(y - w0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN segment[w0:real^M,y]
        ==> linear((G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
                   (pastecart x t))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN
   `linear((G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
           (pastecart w0 t))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x:real^M. (G:real^(M,P)finite_sum->real^N)(pastecart x t) -
                (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
                (pastecart w0 t) (pastecart x (vec 0))`;
    `\x:real^M h:real^M.
        (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
        (pastecart x t) (pastecart h (vec 0)) -
        G'(pastecart w0 t) (pastecart h (vec 0))`;
    `segment[w0:real^M,y]`; `e:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC NSPA_SLICE_HAS_DERIVATIVE THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        MATCH_MP_TAC NSPA_LINEAR_PASTECART_0 THEN ASM_REWRITE_TAC[ETA_AX]];
      MP_TAC(ISPEC
       `\h:real^M. (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
                   (pastecart x t) (pastecart h (vec 0)) -
                   G'(pastecart w0 t) (pastecart h (vec 0))` ONORM) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC NSPA_LINEAR_PASTECART_0 THEN ASM_SIMP_TAC[ETA_AX];
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
        X_GEN_TAC `h:real^M` THEN BETA_TAC THEN ASM_SIMP_TAC[]]];
    DISCH_THEN(MP_TAC o SPECL [`y:real^M`; `w0:real^M`]) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    SUBGOAL_THEN `pastecart (y - w0:real^M) (vec 0:real^P) =
                  pastecart y (vec 0) - pastecart w0 (vec 0)` SUBST1_TAC THENL
     [REWRITE_TAC[PASTECART_SUB; VECTOR_SUB_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC]);;

(* Linearity of an integral of linear maps.                                 *)
let NSPA_LINEAR_INTEGRAL = prove
 (`!(A:real^P->real^M->real^N) s.
     (!t. t IN s ==> linear(A t)) /\ (!h. (\t. A t h) integrable_on s)
     ==> linear (\h. integral s (\t. A t h))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral s (\t. (A:real^P->real^M->real^N) t x + A t y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[LINEAR_ADD];
      MATCH_MP_TAC INTEGRAL_ADD THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral s (\t. c % (A:real^P->real^M->real^N) t x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[LINEAR_CMUL];
      MATCH_MP_TAC INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]]]);;

(* Provenance: LEIBNIZ_ARITH of ns_periodic_uniq.ml.                        *)
let NSPA_ARITH = prove
 (`!e n C. &0 < e /\ &0 <= n /\ &0 <= C ==> (e / (C + &1) * n) * C <= e * n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e / (C + &1) * n) * C = e * n - (e * n) / (C + &1)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 <= C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Differentiation under the integral sign, parameter w in real^M:          *)
(* d/dw int_[a,b] G(w, t) dt = int_[a,b] G'(w, t)(h, 0) dt.                  *)
(* ------------------------------------------------------------------------- *)

let NSPA_HAS_DERIVATIVE_PARAM_INTEGRAL = prove
 (`!(G:real^(M,P)finite_sum->real^N) G' W (w0:real^M) a b.
     open W /\
     (!z. z IN W ==> (G has_derivative G' z) (at z)) /\
     (!k. (\z. G' z k) continuous_on W) /\
     (!t. t IN interval[a,b] ==> pastecart w0 t IN W)
     ==> ((\w. integral (interval[a,b]) (\t. G(pastecart w t))) has_derivative
          (\h. integral (interval[a,b])
                 (\t. G' (pastecart w0 t) (pastecart h (vec 0))))) (at w0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^(M,P)finite_sum->bool`; `w0:real^M`;
                 `interval[a:real^P,b]`] NSPA_TUBE) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!z. z IN W
        ==> linear((G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N) z)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^(M,P)finite_sum->real^N) continuous_on W`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    ASM_MESON_TAC[differentiable; DIFFERENTIABLE_IMP_CONTINUOUS_AT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN cball(w0,r)
        ==> (\t. (G:real^(M,P)finite_sum->real^N)(pastecart w t))
            integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC NSPA_SLICE_CONTINUOUS_ON THEN
    EXISTS_TAC `W:real^(M,P)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. (\t. (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
              (pastecart w0 t) k) integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MP_TAC(ISPECL
     [`\z. (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N) z k`;
      `W:real^(M,P)finite_sum->bool`; `w0:real^M`;
      `interval[a:real^P,b]`] NSPA_SLICE_CONTINUOUS_ON) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. vectorize(matrix
           ((G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N) z)))
    continuous_on W`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CONTINUOUS_ON_MATRIX_VECTORIZE] THEN
    X_GEN_TAC `v:real^(M,P)finite_sum` THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC
     `\z. (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N) z v` THEN
    ASM_SIMP_TAC[MATRIX_WORKS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z. vectorize(matrix
           ((G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N) z))`;
    `cball(w0:real^M,r) PCROSS interval[a:real^P,b]`]
   COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `W:real^(M,P)finite_sum->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(LABEL_TAC "uc")] THEN
  REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\t:real^P h:real^M.
         (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
         (pastecart w0 t) (pastecart h (vec 0))`;
      `interval[a:real^P,b]`] NSPA_LINEAR_INTEGRAL) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NSPA_LINEAR_PASTECART_0 THEN
    ASM_SIMP_TAC[ETA_AX];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `C = content(interval[a:real^P,b])` THEN
  SUBGOAL_THEN `&0 <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[CONTENT_POS_LE]; ALL_TAC] THEN
  REMOVE_THEN "uc" (MP_TAC o SPEC `e / (C + &1)`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ucd"))) THEN
  EXISTS_TAC `min d r` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^M) IN cball(w0,r) /\ w0 IN cball(w0,r)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL; dist] THEN
    UNDISCH_TAC `norm(y - w0:real^M) < r` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN segment[w0:real^M,y] ==> dist(x,w0) < d /\ x IN cball(w0,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w0:real^M`; `y:real^M`; `x:real^M`]
      DIST_IN_CLOSED_SEGMENT) THEN
    ASM_REWRITE_TAC[IN_CBALL] THEN
    UNDISCH_TAC `norm(y - w0:real^M) < d` THEN
    UNDISCH_TAC `norm(y - w0:real^M) < r` THEN
    REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN interval[a,b]
        ==> norm((G:real^(M,P)finite_sum->real^N)(pastecart y t) -
                 G(pastecart w0 t) -
                 (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
                 (pastecart w0 t) (pastecart (y - w0) (vec 0)))
            <= e / (C + &1) * norm(y - w0:real^M)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^P` THEN DISCH_TAC THEN
    MATCH_MP_TAC NSPA_MVT_STEP THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `pastecart (x:real^M) (t:real^P) IN W` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`x:real^M`; `h:real^M`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `dist(x:real^M,w0) < d /\ x IN cball(w0,r)`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `pastecart (x:real^M) (t:real^P) IN W /\
                    pastecart (w0:real^M) (t:real^P) IN W`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `norm(vectorize(matrix
               ((G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
                (pastecart x t))) -
             vectorize(matrix(G'(pastecart w0 t)))) * norm(h:real^M)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NSPA_VECTORIZE_BOUND THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[GSYM dist] THEN
        USE_THEN "ucd" (MP_TAC o SPECL [`pastecart (w0:real^M) (t:real^P)`;
                                         `pastecart (x:real^M) (t:real^P)`]) THEN
        REWRITE_TAC[PASTECART_IN_PCROSS; DIST_PASTECART_CANCEL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. (G:real^(M,P)finite_sum->real^N)(pastecart y t) - G(pastecart w0 t) -
         (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
         (pastecart w0 t) (pastecart (y - w0:real^M) (vec 0))`;
    `a:real^P`; `b:real^P`;
    `integral (interval[a,b])
       (\t. (G:real^(M,P)finite_sum->real^N)(pastecart y t)) -
     integral (interval[a,b]) (\t. G(pastecart w0 t)) -
     integral (interval[a,b])
       (\t. (G':real^(M,P)finite_sum->real^(M,P)finite_sum->real^N)
            (pastecart w0 t) (pastecart (y - w0:real^M) (vec 0)))`;
    `e / (C + &1) * norm(y - w0:real^M)`] HAS_INTEGRAL_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC NSPA_ARITH THEN ASM_REWRITE_TAC[NORM_POS_LE]);;


(* ------------------------------------------------------------------------- *)
(* Smoothness of parameter integrals of smooth integrands (all orders), and  *)
(* partial derivatives as integrals of the partials of the slices.          *)
(* ------------------------------------------------------------------------- *)

let NSPA_SMOOTH_HAS_DERIVATIVE_PARAM = prove
 (`!V W (a:real^P) b (G:real^(M,P)finite_sum->real^N) (w0:real^M).
     open W /\ smooth_map_on W G /\
     (!w t. w IN V /\ t IN interval[a,b] ==> pastecart w t IN W) /\ w0 IN V
     ==> ((\w. integral (interval[a,b]) (\t. G(pastecart w t))) has_derivative
          (\h. integral (interval[a,b])
                 (\t. frechet_derivative G (at (pastecart w0 t))
                        (pastecart h (vec 0)))))
         (at w0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^(M,P)finite_sum->real^N`;
                 `\z. frechet_derivative (G:real^(M,P)finite_sum->real^N) (at z)`;
                 `W:real^(M,P)finite_sum->bool`; `w0:real^M`;
                 `a:real^P`; `b:real^P`]
         NSPA_HAS_DERIVATIVE_PARAM_INTEGRAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_HAS_DERIVATIVE THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let NSPA_PARAM_INTEGRAL_CD = prove
 (`!n (V:real^M->bool) (W:real^(M,P)finite_sum->bool) (a:real^P) b
     (G:real^(M,P)finite_sum->real^N).
     open V /\ open W /\ smooth_map_on W G /\
     (!w t. w IN V /\ t IN interval[a,b] ==> pastecart w t IN W)
     ==> continuously_differentiable n V
           (\w. integral (interval[a,b]) (\t. G(pastecart w t)))`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_0] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `w0:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h. integral (interval[a:real^P,b])
                 (\t. frechet_derivative (G:real^(M,P)finite_sum->real^N)
                        (at (pastecart w0 t)) (pastecart (h:real^M) (vec 0)))` THEN
    MATCH_MP_TAC NSPA_SMOOTH_HAS_DERIVATIVE_PARAM THEN
    EXISTS_TAC `V:real^M->bool` THEN
    EXISTS_TAC `W:real^(M,P)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_WITHIN_OPEN] THEN
    EXISTS_TAC `\w:real^M h:real^M. integral (interval[a:real^P,b])
                 (\t. frechet_derivative (G:real^(M,P)finite_sum->real^N)
                        (at (pastecart w t)) (pastecart h (vec 0)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `w0:real^M` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC NSPA_SMOOTH_HAS_DERIVATIVE_PARAM THEN
      EXISTS_TAC `V:real^M->bool` THEN
      EXISTS_TAC `W:real^(M,P)finite_sum->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `h:real^M` THEN BETA_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`V:real^M->bool`; `W:real^(M,P)finite_sum->bool`;
         `a:real^P`; `b:real^P`;
         `\z. frechet_derivative (G:real^(M,P)finite_sum->real^N) (at z)
                (pastecart (h:real^M) (vec 0:real^P))`]) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE]]]);;

let NSPA_SLICE_FRECHET = prove
 (`!W (G:real^(M,P)finite_sum->real^N) (w:real^M) (t:real^P).
     open W /\ smooth_map_on W G /\ pastecart w t IN W
     ==> frechet_derivative (\w. G(pastecart w t)) (at w) =
         (\h. frechet_derivative G (at (pastecart w t)) (pastecart h (vec 0)))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC NSPA_SLICE_HAS_DERIVATIVE THEN
  ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]);;

(* The generic result: smooth parameter integrals over a box [a,b] in       *)
(* real^P.                                                                  *)
let NS_PARAM_INTEGRAL_SMOOTH = prove
 (`!V W (a:real^P) b (G:real^(M,P)finite_sum->real^N).
     open V /\ open W /\ smooth_map_on W G /\
     (!w t. w IN V /\ t IN interval[a,b] ==> pastecart w t IN W)
     ==> smooth_map_on V (\w. integral (interval[a,b]) (\t. G(pastecart w t))) /\
         !w i. w IN V
               ==> partial_derivative i
                     (\w. integral (interval[a,b]) (\t. G(pastecart w t))) w =
                   integral (interval[a,b])
                     (\t. partial_derivative i (\w. G(pastecart w t)) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[smooth_map_on] THEN GEN_TAC THEN
    MATCH_MP_TAC NSPA_PARAM_INTEGRAL_CD THEN
    EXISTS_TAC `W:real^(M,P)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`w:real^M`; `i:num`] THEN DISCH_TAC THEN
    REWRITE_TAC[partial_derivative] THEN
    MP_TAC(ISPECL [`V:real^M->bool`; `W:real^(M,P)finite_sum->bool`;
                   `a:real^P`; `b:real^P`;
                   `G:real^(M,P)finite_sum->real^N`; `w:real^M`]
           NSPA_SMOOTH_HAS_DERIVATIVE_PARAM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `t:real^P` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`W:real^(M,P)finite_sum->bool`;
                   `G:real^(M,P)finite_sum->real^N`;
                   `w:real^M`; `t:real^P`] NSPA_SLICE_FRECHET) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]]);;

(* real_integral over real_interval[a,b] versus integral over interval.    *)
let NSPA_REAL_INTEGRAL_LIFT = prove
 (`!(g:real^1->real^1) a b.
     g continuous_on interval[lift a,lift b]
     ==> lift(real_integral (real_interval[a,b]) (\s. drop(g(lift s)))) =
         integral (interval[lift a,lift b]) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\s. drop((g:real^1->real^1)(lift s))) real_integrable_on real_interval[a,b]`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF;
                LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_INTEGRAL; LIFT_DROP; IMAGE_LIFT_REAL_INTERVAL; o_DEF;
                 ETA_AX]]);;

(* The real-valued form, integration variable s in real_interval[a,b].     *)
let NS_PARAM_REAL_INTEGRAL_SMOOTH = prove
 (`!V W a b (G:real^(M,1)finite_sum->real^1).
     open V /\ open W /\ smooth_map_on W G /\
     (!w s. w IN V /\ s IN real_interval[a,b] ==> pastecart w (lift s) IN W)
     ==> smooth_map_on V
           (\w. lift(real_integral (real_interval[a,b])
                       (\s. drop(G(pastecart w (lift s)))))) /\
         !w i. w IN V
               ==> partial_derivative i
                     (\w. lift(real_integral (real_interval[a,b])
                                (\s. drop(G(pastecart w (lift s)))))) w =
                   lift(real_integral (real_interval[a,b])
                          (\s. drop(partial_derivative i
                                      (\w. G(pastecart w (lift s))) w)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!w t. w IN V /\ t IN interval[lift a,lift b]
          ==> pastecart (w:real^M) t IN (W:real^(M,1)finite_sum->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^M->bool`; `W:real^(M,1)finite_sum->bool`;
                 `lift a`; `lift b`; `G:real^(M,1)finite_sum->real^1`]
         NS_PARAM_INTEGRAL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(G:real^(M,1)finite_sum->real^1) continuous_on W` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN V
        ==> lift(real_integral (real_interval[a,b])
                   (\s. drop((G:real^(M,1)finite_sum->real^1)
                               (pastecart (w:real^M) (lift s))))) =
            integral (interval[lift a,lift b]) (\t. G(pastecart w t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\t. (G:real^(M,1)finite_sum->real^1) (pastecart (w:real^M) t)`;
                   `a:real`; `b:real`] NSPA_REAL_INTEGRAL_LIFT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC NSPA_SLICE_CONTINUOUS_ON THEN
    EXISTS_TAC `W:real^(M,1)finite_sum->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\w. integral (interval[lift a,lift b])
                      (\t. (G:real^(M,1)finite_sum->real^1)
                             (pastecart (w:real^M) t))` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^M`; `i:num`] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `partial_derivative i
      (\w. integral (interval[lift a,lift b])
             (\t. (G:real^(M,1)finite_sum->real^1)
                    (pastecart (w:real^M) t))) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN
    EXISTS_TAC `V:real^M->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`\t. partial_derivative i
                        (\w. (G:real^(M,1)finite_sum->real^1)
                               (pastecart (w:real^M) t)) w`;
                 `a:real`; `b:real`] NSPA_REAL_INTEGRAL_LIFT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
  EXISTS_TAC `\t. frechet_derivative (G:real^(M,1)finite_sum->real^1)
                    (at (pastecart (w:real^M) t)) (pastecart (basis i) (vec 0))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[partial_derivative] THEN
    MP_TAC(ISPECL [`W:real^(M,1)finite_sum->bool`;
                   `G:real^(M,1)finite_sum->real^1`;
                   `w:real^M`; `t:real^1`] NSPA_SLICE_FRECHET) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]];
    MP_TAC(ISPECL [`\z. frechet_derivative (G:real^(M,1)finite_sum->real^1) (at z)
                          (pastecart (basis i) (vec 0))`;
                   `W:real^(M,1)finite_sum->bool`; `w:real^M`;
                   `interval[lift a,lift b]`] NSPA_SLICE_CONTINUOUS_ON) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Periodic maps.  Integer periods, the unit cube as a fundamental domain,   *)
(* boundedness, translates and their iterated partials, periodicity of       *)
(* iterated partials of smooth periodic maps.                                *)
(* ========================================================================= *)

let PDE_ZPER_INTEGER = prove
 (`!(u:real^N->B) x k.
        pde_zper u /\ (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(k$i))
        ==> u(x + k) = u x`,
  REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. FINITE s
        ==> s SUBSET 1..dimindex(:N)
            ==> !y. (u:real^N->B)(y + vsum s (\i. (k:real^N)$i % basis i)) = u y`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[VSUM_CLAUSES; VECTOR_ADD_RID] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `s:num->bool`] THEN
    REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
    STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN ASM_SIMP_TAC[VSUM_CLAUSES] THEN
    REWRITE_TAC[VECTOR_ARITH `y + a + b:real^N = (y + b) + a`] THEN
    MP_TAC(ISPECL [`u:real^N->B`; `basis j:real^N`; `(k:real^N)$j`;
                   `(y:real^N) + vsum s (\i. (k:real^N)$i % basis i)`] NSPU_PERIODIC_INTEGER) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "ih" (fun th -> ASM_SIMP_TAC[th]);
    DISCH_THEN(MP_TAC o SPEC `1..dimindex(:N)`) THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET_REFL; BASIS_EXPANSION] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[]]);;

(* Every value of a periodic map is taken on the unit cube. *)

let PDE_ZPER_CUBE = prove
 (`!(u:real^N->B) x.
        pde_zper u ==> ?y. y IN interval[vec 0,vec 1] /\ u x = u y`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `x - (lambda i. floor((x:real^N)$i)):real^N` THEN CONJ_TAC THENL
   [SIMP_TAC[IN_INTERVAL; VECTOR_SUB_COMPONENT; LAMBDA_BETA; VEC_COMPONENT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `(x:real^N)$i` FLOOR) THEN REAL_ARITH_TAC;
    CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`u:real^N->B`; `x - (lambda i. floor((x:real^N)$i)):real^N`;
                   `(lambda i. floor((x:real^N)$i)):real^N`] PDE_ZPER_INTEGER) THEN
    ASM_SIMP_TAC[LAMBDA_BETA; FLOOR; VECTOR_SUB_ADD]]);;

let PDE_ZPER_BOUNDED = prove
 (`!u:real^N->real^K.
        u continuous_on (:real^N) /\ pde_zper u ==> ?B. !x. norm(u x) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `interval[vec 0:real^N,vec 1]`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `x:real^N`] PDE_ZPER_CUBE) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Translates and their partial derivatives. *)

let PDE_PARTIAL_TRANSLATE = prove
 (`!(f:real^N->real^K) c i x.
        f differentiable (at (x + c))
        ==> partial_derivative i (\y. f(y + c)) x = partial_derivative i f (x + c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  SUBGOAL_THEN
   `((\y. (f:real^N->real^K)(y + c)) has_derivative frechet_derivative f (at (x + c))) (at x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (f:real^N->real^K)(y + c)) = f o (\y. y + c)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (f:real^N->real^K) (at (x + c)) =
                  frechet_derivative f (at (x + c)) o (\h. h + vec 0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID; HAS_DERIVATIVE_CONST];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN REFL_TAC]);;

let PDE_SMOOTH_TRANSLATE = prove
 (`!(f:real^N->real^K) c.
        smooth_map_on (:real^N) f ==> smooth_map_on (:real^N) (\y. f(y + c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (f:real^N->real^K)(y + c)) = f o (\y. y + c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let PDE_ITERATED_PARTIAL_TRANSLATE = prove
 (`!l (f:real^N->real^K) c.
        smooth_map_on (:real^N) f
        ==> !x. iterated_partial l (\y. f(y + c)) x = iterated_partial l f (x + c)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[iterated_partial] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `iterated_partial t (\y. (f:real^N->real^K)(y + c)) =
    (\y. iterated_partial t f (y + c))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_PARTIAL_TRANSLATE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_ITERATED_PARTIAL]);;

let PDE_ZPER_ITERATED_PARTIAL = prove
 (`!l (u:real^N->real^K).
        smooth_map_on (:real^N) u /\ pde_zper u ==> pde_zper (iterated_partial l u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_zper] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num list`; `u:real^N->real^K`; `basis i:real^N`]
                PDE_ITERATED_PARTIAL_TRANSLATE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o SPEC `x:real^N`) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `y:real^N` THEN RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN
  ASM_SIMP_TAC[]);;

let PDE_ZPER_PARTIAL = prove
 (`!i (u:real^N->real^K).
        smooth_map_on (:real^N) u /\ pde_zper u ==> pde_zper (partial_derivative i u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`[i:num]`; `u:real^N->real^K`] PDE_ZPER_ITERATED_PARTIAL) THEN
  ASM_REWRITE_TAC[iterated_partial; ETA_AX]);;

(* ========================================================================= *)
(* Unit-cube integrals of periodic maps.  Line derivatives, the cube         *)
(* integral of a partial of a smooth periodic map vanishes (from             *)
(* NSPU_PERIODIC_INTEGRAL_DERIVATIVE, componentwise), the product rule for   *)
(* dot products and periodic integration by parts.                           *)
(* ========================================================================= *)

let PDE_LINE_DERIV = prove
 (`!(u:real^N->real^K) x j s.
        u differentiable (at (x + s % basis j))
        ==> ((\r. u(x + drop r % basis j)) has_vector_derivative
             partial_derivative j u (x + s % basis j)) (at (lift s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP LINEAR_FRECHET_DERIVATIVE th) THEN
                       ASSUME_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS] th)) THEN
  REWRITE_TAC[has_vector_derivative; partial_derivative] THEN
  SUBGOAL_THEN `(\r:real^1. (u:real^N->real^K)(x + drop r % basis j)) =
                u o (\r. x + drop r % basis j)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^1. drop h % frechet_derivative (u:real^N->real^K) (at (x + s % basis j))
                                            (basis j)) =
    frechet_derivative u (at (x + s % basis j)) o (\h. drop h % basis j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_CMUL);
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\h:real^1. drop h % basis j:real^N) = (\h. vec 0 + drop h % basis j)`
    SUBST1_TAC THENL [REWRITE_TAC[VECTOR_ADD_LID]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN MATCH_MP_TAC LINEAR_VMUL_DROP THEN
    REWRITE_TAC[LINEAR_ID];
    ASM_REWRITE_TAC[LIFT_DROP]]);;

let PDE_LINE_REAL_DERIV = prove
 (`!(u:real^N->real^K) x j k.
        u differentiable (at x) /\ 1 <= k /\ k <= dimindex(:K)
        ==> ((\s. (u(x + s % basis j))$k) has_real_derivative
             (partial_derivative j u x)$k) (atreal (&0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF] THEN
  MP_TAC(ISPECL [`u:real^N->real^K`; `x:real^N`; `j:num`; `&0`] PDE_LINE_DERIV) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r:real^1. (u:real^N->real^K)(x + drop r % basis j)`;
                 `partial_derivative j (u:real^N->real^K) x`; `lift(&0)`; `k:num`]
                HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT) THEN
  ASM_REWRITE_TAC[]);;

let PDE_SMOOTH_CONTINUOUS_AT = prove
 (`!(f:real^M->real^N) x. smooth_map_on (:real^M) f ==> f continuous (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

(* The cube integral of a partial of a smooth periodic map vanishes. *)

let PDE_CUBE_INTEGRAL_PARTIAL = prove
 (`!(u:real^N->real^K) j.
        smooth_map_on (:real^N) u /\ pde_zper u /\ 1 <= j /\ j <= dimindex(:N)
        ==> integral (interval[vec 0,vec 1]) (partial_derivative j u) = vec 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ; VEC_COMPONENT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (partial_derivative j (u:real^N->real^K))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(partial_derivative j (u:real^N->real^K)) integrable_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`partial_derivative j (u:real^N->real^K)`; `interval[vec 0:real^N,vec 1]`;
                 `\v:real^K. lift(v$k)`] INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT; o_DEF] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`\x:real^N. (u:real^N->real^K) x$k`;
                 `\x:real^N. (partial_derivative j (u:real^N->real^K) x)$k`; `j:num`]
                NSPU_PERIODIC_INTEGRAL_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_LIFT_COMPONENT_COMPOSE THEN
      MATCH_MP_TAC PDE_SMOOTH_CONTINUOUS_AT THEN ASM_REWRITE_TAC[ETA_AX];
      GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_LIFT_COMPONENT_COMPOSE THEN
      MATCH_MP_TAC PDE_SMOOTH_CONTINUOUS_AT THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC PDE_LINE_REAL_DERIV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN ASM_SIMP_TAC[]];
    SIMP_TAC[DROP_VEC]]);;

(* Product rule for dot products, and periodic integration by parts. *)

let PDE_PARTIAL_DOT = prove
 (`!(u:real^N->real^K) v j x.
        u differentiable (at x) /\ v differentiable (at x)
        ==> partial_derivative j (\x. lift(u x dot v x)) x =
            lift(partial_derivative j u x dot v x) + lift(u x dot partial_derivative j v x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  MP_TAC(ISPECL [`\x y:real^K. lift(x dot y)`; `u:real^N->real^K`; `v:real^N->real^K`;
                 `frechet_derivative (u:real^N->real^K) (at x)`;
                 `frechet_derivative (v:real^N->real^K) (at x)`; `x:real^N`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);;

let PDE_CUBE_IBP = prove
 (`!(u:real^N->real^K) v j.
        smooth_map_on (:real^N) u /\ smooth_map_on (:real^N) v /\
        pde_zper u /\ pde_zper v /\ 1 <= j /\ j <= dimindex(:N)
        ==> integral (interval[vec 0,vec 1]) (\x. lift(partial_derivative j u x dot v x)) =
            --(integral (interval[vec 0,vec 1])
                        (\x. lift(u x dot partial_derivative j v x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift((u:real^N->real^K) x dot v x))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N)`; `\x y:real^K. lift(x dot y)`; `u:real^N->real^K`;
                   `v:real^N->real^K`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
    ASM_REWRITE_TAC[BILINEAR_DOT; OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((u:real^N->real^K) x dot v x)`; `j:num`]
                PDE_CUBE_INTEGRAL_PARTIAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN REWRITE_TAC[pde_zper] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative j (\x. lift((u:real^N->real^K) x dot v x)) =
    (\x. lift(partial_derivative j u x dot v x) + lift(u x dot partial_derivative j v x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN MATCH_MP_TAC PDE_PARTIAL_DOT THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N->real^K. smooth_map_on (:real^N) w
        ==> (partial_derivative j w) integrable_on interval[vec 0,vec 1] /\
            w integrable_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. lift(partial_derivative j (u:real^N->real^K) x dot v x)) integrable_on
      interval[vec 0,vec 1] /\
    (\x. lift((u:real^N->real^K) x dot partial_derivative j v x)) integrable_on
      interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THENL
     [MP_TAC(ISPECL [`(:real^N)`; `\x y:real^K. lift(x dot y)`;
                     `partial_derivative j (u:real^N->real^K)`; `v:real^N->real^K`]
                    SMOOTH_MAP_ON_BILINEAR_OPEN);
      MP_TAC(ISPECL [`(:real^N)`; `\x y:real^K. lift(x dot y)`;
                     `u:real^N->real^K`; `partial_derivative j (v:real^N->real^K)`]
                    SMOOTH_MAP_ON_BILINEAR_OPEN)] THEN
    ASM_SIMP_TAC[BILINEAR_DOT; OPEN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD] THEN VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Calculus of the cube norms pde_hs2.  The recursion pde_hs2                *)
(* (SUC s) u = pde_hs2 0 u + sum_i pde_hs2 s (D_i u) (index lists split by   *)
(* their last entry), positivity and monotonicity.                           *)
(* ========================================================================= *)

let PDE_APPEND_SING_INJ = prove
 (`!(l:A list) l' i i'. APPEND l [i] = APPEND l' [i'] <=> l = l' /\ i = i'`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_THEN(MP_TAC o AP_TERM `REVERSE:A list->A list`) THEN
  REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND; CONS_11] THEN
  MESON_TAC[REVERSE_REVERSE]);;

let PDE_INDEX_LISTS_SUC = prove
 (`!s. pde_index_lists (SUC s) (:N) =
       [] INSERT IMAGE (\p. APPEND (SND p) [FST p])
                       ((1..dimindex(:N)) CROSS pde_index_lists s (:N))`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
  X_GEN_TAC `l:num list` THEN
  REWRITE_TAC[pde_index_lists; IN_ELIM_THM; IN_NUMSEG; FST; SND] THEN EQ_TAC THENL
   [ASM_CASES_TAC `l:num list = []` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `l:num list` APPEND_BUTLAST_LAST) THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `m = BUTLAST(l:num list)` THEN ABBREV_TAC `i = LAST(l:num list)` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `m:num list`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_APPEND; ALL_APPEND; ALL; LENGTH]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN
    ASM_REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL; LENGTH_APPEND; ALL_APPEND; ALL; LENGTH] THEN
    ASM_ARITH_TAC]);;

let PDE_HS2_SUC = prove
 (`!s (u:real^N->real^K).
        pde_hs2 (SUC s) u =
        pde_hs2 0 u + sum (1..dimindex(:N)) (\i. pde_hs2 s (partial_derivative i u))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [pde_hs2] THEN
  ABBREV_TAC
   `tm = \l. drop(integral (interval[vec 0,vec 1])
                           (\x. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2)))` THEN
  REWRITE_TAC[PDE_INDEX_LISTS_SUC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_IMAGE; FINITE_CROSS; FINITE_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN
  REWRITE_TAC[IN_IMAGE; prove(`!(l:num list) i. ~([] = APPEND l [i])`,
                               MESON_TAC[APPEND_EQ_NIL; NOT_CONS_NIL])] THEN
  SUBGOAL_THEN
   `sum (IMAGE (\p. APPEND (SND p) [FST p]) ((1..dimindex(:N)) CROSS pde_index_lists s (:N)))
        tm =
    sum (1..dimindex(:N)) (\i. sum (pde_index_lists s (:N)) (\l. tm (APPEND l [i])))`
  SUBST1_TAC THENL
   [W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) SUM_IMAGE (lhand w))) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; FST; SND; PDE_APPEND_SING_INJ; PAIR_EQ] THEN MESON_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG; PDE_INDEX_LISTS_FINITE] THEN
    REWRITE_TAC[GSYM CROSS] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM; FST; SND] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "tm" THEN REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX] THEN
  REWRITE_TAC[PDE_HS2_0] THEN REWRITE_TAC[pde_hs2]);;

let PDE_SQNORM_CONTINUOUS = prove
 (`!(f:real^M->real^N) s.
        f continuous_on s ==> (\x. lift(norm(f x) pow 2)) continuous_on s`,
  REWRITE_TAC[NORM_POW_2] THEN SIMP_TAC[CONTINUOUS_ON_LIFT_DOT2]);;

let PDE_SQNORM_INTEGRABLE = prove
 (`!(u:real^N->real^K) l.
        smooth_map_on (:real^N) u
        ==> (\x. lift(norm(iterated_partial l u x) pow 2)) integrable_on
            interval[vec 0,vec 1]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC PDE_SQNORM_CONTINUOUS THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

let PDE_HS2_TERM_POS = prove
 (`!(u:real^N->real^K) l.
        smooth_map_on (:real^N) u
        ==> &0 <= drop(integral (interval[vec 0,vec 1])
                                (\x. lift(norm(iterated_partial l u x) pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[LIFT_DROP; REAL_LE_POW_2; PDE_SQNORM_INTEGRABLE]);;

let PDE_HS2_POS = prove
 (`!s (u:real^N->real^K). smooth_map_on (:real^N) u ==> &0 <= pde_hs2 s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hs2] THEN MATCH_MP_TAC SUM_POS_LE THEN
  ASM_SIMP_TAC[PDE_HS2_TERM_POS]);;

let PDE_HS2_TERM_LE = prove
 (`!s (u:real^N->real^K) l.
        smooth_map_on (:real^N) u /\ l IN pde_index_lists s (:N)
        ==> drop(integral (interval[vec 0,vec 1])
                          (\x. lift(norm(iterated_partial l u x) pow 2)))
            <= pde_hs2 s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hs2] THEN
  ABBREV_TAC `tm = \l. drop(integral (interval[vec 0,vec 1])
                       (\x. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2)))` THEN
  SUBGOAL_THEN `!l:num list. &0 <= tm l` ASSUME_TAC THENL
   [EXPAND_TAC "tm" THEN ASM_SIMP_TAC[PDE_HS2_TERM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (interval[vec 0,vec 1])
                  (\x. lift(norm(iterated_partial l (u:real^N->real^K) x) pow 2))) =
    tm l`
  SUBST1_TAC THENL [EXPAND_TAC "tm" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum {l:num list} tm` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_SING; REAL_LE_REFL];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; SING_SUBSET]]);;

let PDE_HS2_MONO = prove
 (`!s s' (u:real^N->real^K).
        smooth_map_on (:real^N) u /\ s <= s' ==> pde_hs2 s u <= pde_hs2 s' u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_hs2] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; PDE_INDEX_LISTS_MONO; PDE_HS2_TERM_POS]);;

let PDE_HS2_PARTIAL_SUM_LE = prove
 (`!s (u:real^N->real^K).
        smooth_map_on (:real^N) u
        ==> sum (1..dimindex(:N)) (\i. pde_hs2 s (partial_derivative i u)) <=
            pde_hs2 (SUC s) u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_HS2_SUC; REAL_LE_ADDL] THEN
  ASM_SIMP_TAC[PDE_HS2_POS]);;

let PDE_HS2_PARTIAL_LE = prove
 (`!s i (u:real^N->real^K).
        smooth_map_on (:real^N) u /\ 1 <= i /\ i <= dimindex(:N)
        ==> pde_hs2 s (partial_derivative i u) <= pde_hs2 (SUC s) u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..dimindex(:N)) (\i. pde_hs2 s (partial_derivative i (u:real^N->real^K)))` THEN
  ASM_SIMP_TAC[PDE_HS2_PARTIAL_SUM_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {i:num} (\i. pde_hs2 s (partial_derivative i (u:real^N->real^K)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_SING; REAL_LE_REFL];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG; PDE_HS2_POS;
                 SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV]]);;

(* ========================================================================= *)
(* Averages along coordinate lines.  pde_lavg j G x is the mean of the       *)
(* real^1-valued map G over the unit segment from x in direction j.  For     *)
(* smooth periodic G it is smooth and periodic, commutes with partials, does *)
(* not depend on x$j, has the same cube integral as G, and bounds G from     *)
(* above together with the mean of |D_j G| (the one-dimensional Sobolev      *)
(* inequality).                                                              *)
(* ========================================================================= *)

let pde_lavg = new_definition
 `pde_lavg (j:num) (G:real^N->real^1) =
    \x. integral (interval[vec 0,vec 1]) (\r:real^1. G(x + drop r % basis j))`;;

let PDE_LAVG_SMOOTH = prove
 (`!j (G:real^N->real^1).
        smooth_map_on (:real^N) G
        ==> smooth_map_on (:real^N) (pde_lavg j G) /\
            !i x. partial_derivative i (pde_lavg j G) x =
                  pde_lavg j (partial_derivative i G) x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `(:real^(N,1)finite_sum)`; `vec 0:real^1`; `vec 1:real^1`;
                 `\z:real^(N,1)finite_sum.
                    (G:real^N->real^1)(fstcart z + drop(sndcart z) % basis j)`]
                NS_PARAM_INTEGRAL_SMOOTH) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^(N,1)finite_sum. (G:real^N->real^1)(fstcart z + drop(sndcart z) % basis j)) =
      G o (\z. fstcart z + drop(sndcart z) % basis j)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    SUBGOAL_THEN
     `(\z:real^(N,1)finite_sum. fstcart z + drop(sndcart z) % basis j:real^N) =
      (\z. fstcart z + drop(sndcart z) % basis j) o (\z. z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LINEAR_FSTCART] THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  REWRITE_TAC[pde_lavg] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:real^N`] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:real^1` THEN
  MATCH_MP_TAC PDE_PARTIAL_TRANSLATE THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV]);;

let PDE_LAVG_ZPER = prove
 (`!j (G:real^N->real^1). pde_zper G ==> pde_zper (pde_lavg j G)`,
  REWRITE_TAC[pde_zper; pde_lavg] THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `(x + b) + c:real^N = (x + c) + b`] THEN ASM_SIMP_TAC[]);;

(* Continuity of a line function of a continuous map. *)

let PDE_LINE_CONTINUOUS = prove
 (`!(G:real^N->real^K) x j.
        G continuous_on (:real^N)
        ==> (\r:real^1. G(x + drop r % basis j)) continuous_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\r:real^1. (G:real^N->real^K)(x + drop r % basis j)) =
                G o (\r. x + drop r % basis j)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

(* The mean along direction j does not depend on the j-th coordinate. *)

let PDE_LAVG_INDEP = prove
 (`!j (G:real^N->real^1) x c.
        1 <= j /\ j <= dimindex(:N) /\ G continuous_on (:real^N) /\ pde_zper G
        ==> pde_lavg j G (x + c % basis j) = pde_lavg j G x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lavg] THEN
  ABBREV_TAC `h = \r:real^1. (G:real^N->real^1)(x + drop r % basis j)` THEN
  SUBGOAL_THEN `(h:real^1->real^1) continuous_on (:real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC PDE_LINE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. (h:real^1->real^1)(r + basis 1) = h r` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[DROP_ADD; PDE_BASIS1_REAL1; LIFT_DROP] THEN
    REWRITE_TAC[VECTOR_ARITH `x + (a + &1) % b:real^N = (x + a % b) + b`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\r:real^1. (G:real^N->real^1)((x + c % basis j) + drop r % basis j)) =
    (\r. h(r + (c - floor c) % basis 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `r:real^1` THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; PDE_BASIS1_REAL1; LIFT_DROP; REAL_MUL_RID] THEN
    SUBGOAL_THEN
     `(x + c % basis j) + drop r % basis j:real^N =
      (x + (drop r + (c - floor c)) % basis j) + floor c % basis j`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^N->real^1`; `basis j:real^N`; `floor c`;
                   `x + (drop r + (c - floor c)) % basis j:real^N`] NSPU_PERIODIC_INTEGER) THEN
    REWRITE_TAC[FLOOR] THEN ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN ASM_SIMP_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r:real^1. drop((h:real^1->real^1) r)`; `1`; `c - floor c`]
                NSPU_PERIODIC_INTEGRAL_SHIFT) THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX; DIMINDEX_1; LE_REFL] THEN
  ANTS_TAC THENL
   [MP_TAC(SPEC `c:real` FLOOR) THEN REPEAT STRIP_TAC THEN
    TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF; LIFT_DROP; ETA_AX] THEN
    MP_TAC(ISPECL [`h:real^1->real^1`; `(:real^1)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
    SIMP_TAC[]]);;

(* Integrability of line functions, and the pointwise calculus of means. *)

let PDE_LINE_INTEGRABLE = prove
 (`!(G:real^N->real^K) x j a b.
        G continuous_on (:real^N)
        ==> (\r:real^1. G(x + drop r % basis j)) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
  ASM_SIMP_TAC[SUBSET_UNIV; PDE_LINE_CONTINUOUS]);;

let PDE_LAVG_LE = prove
 (`!j (G1:real^N->real^1) G2 x.
        G1 continuous_on (:real^N) /\ G2 continuous_on (:real^N) /\
        (!y. drop(G1 y) <= drop(G2 y))
        ==> drop(pde_lavg j G1 x) <= drop(pde_lavg j G2 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lavg] THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[PDE_LINE_INTEGRABLE]);;

let PDE_LAVG_NORM_LE = prove
 (`!j (G1:real^N->real^1) G2 x.
        G1 continuous_on (:real^N) /\ G2 continuous_on (:real^N) /\
        (!y. norm(G1 y) <= drop(G2 y))
        ==> norm(pde_lavg j G1 x) <= drop(pde_lavg j G2 x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lavg] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_SIMP_TAC[PDE_LINE_INTEGRABLE]);;

let PDE_LAVG_ADD = prove
 (`!j (G1:real^N->real^1) G2 x.
        G1 continuous_on (:real^N) /\ G2 continuous_on (:real^N)
        ==> pde_lavg j (\y. G1 y + G2 y) x = pde_lavg j G1 x + pde_lavg j G2 x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lavg] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN ASM_SIMP_TAC[PDE_LINE_INTEGRABLE]);;

let PDE_LAVG_CMUL = prove
 (`!j (G:real^N->real^1) c x.
        G continuous_on (:real^N)
        ==> pde_lavg j (\y. c % G y) x = c % pde_lavg j G x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lavg] THEN
  MATCH_MP_TAC INTEGRAL_CMUL THEN ASM_SIMP_TAC[PDE_LINE_INTEGRABLE]);;

(* The cube integral of a mean is the cube integral (Fubini on the product   *)
(* of the cube with the averaging segment, and shift invariance).            *)

let PDE_LAVG_CUBE = prove
 (`!j (G:real^N->real^1).
        1 <= j /\ j <= dimindex(:N) /\ G continuous_on (:real^N) /\ pde_zper G
        ==> integral (interval[vec 0,vec 1]) (pde_lavg j G) =
            integral (interval[vec 0,vec 1]) G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lavg] THEN
  ABBREV_TAC `F2 = \z:real^(N,1)finite_sum.
                     (G:real^N->real^1)(fstcart z + drop(sndcart z) % basis j)` THEN
  SUBGOAL_THEN `(F2:real^(N,1)finite_sum->real^1) continuous_on (:real^(N,1)finite_sum)`
  ASSUME_TAC THENL
   [EXPAND_TAC "F2" THEN
    SUBGOAL_THEN
     `(\z:real^(N,1)finite_sum. (G:real^N->real^1)(fstcart z + drop(sndcart z) % basis j)) =
      G o (\z. fstcart z + drop(sndcart z) % basis j)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LINEAR_FSTCART] THEN
      MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_SNDCART];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(F2:real^(N,1)finite_sum->real^1) absolutely_integrable_on
      interval[pastecart (vec 0) (vec 0),pastecart (vec 1) (vec 1)]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`F2:real^(N,1)finite_sum->real^1`; `vec 0:real^N`; `vec 1:real^N`;
                 `vec 0:real^1`; `vec 1:real^1`] FUBINI_INTEGRAL_INTERVAL) THEN
  MP_TAC(ISPECL [`F2:real^(N,1)finite_sum->real^1`; `vec 0:real^N`; `vec 1:real^N`;
                 `vec 0:real^1`; `vec 1:real^1`] FUBINI_INTEGRAL_INTERVAL_ALT) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "F2" THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (interval[vec 0:real^1,vec 1])
                       (\r. integral (interval[vec 0:real^N,vec 1]) (G:real^N->real^1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `r:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\y:real^N. drop((G:real^N->real^1) y)`; `j:num`; `drop r`]
                  NSPU_PERIODIC_INTEGRAL_SHIFT) THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS1; o_DEF; LIFT_DROP; ETA_AX] THEN
      MP_TAC(ISPECL [`G:real^N->real^1`; `(:real^N)`] CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN SIMP_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[pde_zper]) THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[INTEGRAL_CONST; CONTENT_UNIT; VECTOR_MUL_LID]]);;

(* The one-dimensional Sobolev inequality along direction j. *)

let PDE_LAVG_1D = prove
 (`!j (G:real^N->real^1) x.
        smooth_map_on (:real^N) G
        ==> drop(G x) <=
            drop(pde_lavg j G x) +
            drop(pde_lavg j (\y. lift(abs(drop(partial_derivative j G y)))) x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_lavg] THEN
  ABBREV_TAC `phi = \r:real^1. (G:real^N->real^1)(x + drop r % basis j)` THEN
  ABBREV_TAC `dphi = \r:real^1. partial_derivative j (G:real^N->real^1)
                                 (x + drop r % basis j)` THEN
  SUBGOAL_THEN `!r. ((phi:real^1->real^1) has_vector_derivative dphi r) (at r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN MAP_EVERY EXPAND_TAC ["phi"; "dphi"] THEN
    MP_TAC(ISPECL [`G:real^N->real^1`; `x:real^N`; `j:num`; `drop r`] PDE_LINE_DERIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^1->real^1) continuous_on (:real^1) /\
                (dphi:real^1->real^1) continuous_on (:real^1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["phi"; "dphi"] THEN CONJ_TAC THEN
    MATCH_MP_TAC PDE_LINE_CONTINUOUS THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. (\r:real^1. lift(abs(drop((dphi:real^1->real^1) r)))) integrable_on interval[a,b] /\
          dphi integrable_on interval[a,b] /\
          (phi:real^1->real^1) integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `M = drop(integral (interval[vec 0,vec 1])
                               (\r:real^1. lift(abs(drop((dphi:real^1->real^1) r)))))` THEN
  SUBGOAL_THEN
   `!r. r IN interval[vec 0,vec 1]
        ==> drop((G:real^N->real^1) x) <= drop((phi:real^1->real^1) r) + M`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`phi:real^1->real^1`; `dphi:real^1->real^1`; `vec 0:real^1`; `r:real^1`]
                  FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    ASM_SIMP_TAC[DROP_VEC; HAS_VECTOR_DERIVATIVE_AT_WITHIN] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(G:real^N->real^1) x = phi(vec 0:real^1)` SUBST1_TAC THENL
     [EXPAND_TAC "phi" THEN REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((phi:real^1->real^1) r - phi(vec 0)) <= M` MP_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE) THEN
      EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(integral (interval[vec 0,r])
                                (\r:real^1. lift(abs(drop((dphi:real^1->real^1) r)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
        ASM_REWRITE_TAC[LIFT_DROP; NORM_1; REAL_LE_REFL];
        MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
        ASM_REWRITE_TAC[LIFT_DROP; REAL_ABS_POS; SUBSET_INTERVAL_1; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[NORM_1; DROP_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\r:real^1. (G:real^N->real^1) x`;
                 `\r:real^1. (phi:real^1->real^1) r + lift M`;
                 `interval[vec 0:real^1,vec 1]`] INTEGRAL_DROP_LE) THEN
  ASM_SIMP_TAC[INTEGRABLE_CONST; INTEGRABLE_ADD; DROP_ADD; LIFT_DROP] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CONST; INTEGRAL_CONST; CONTENT_UNIT;
               VECTOR_MUL_LID; DROP_ADD; LIFT_DROP] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  MAP_EVERY EXPAND_TAC ["M"; "dphi"] THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* Iterated means over the coordinates 1..m and the Sobolev embedding on the *)
(* torus (PDE_TORUS_SOBOLEV): the one-dimensional inequality is applied in   *)
(* the coordinates one at a time; after all N of them the iterated mean is   *)
(* constant, equal to the cube integral.                                     *)
(* ========================================================================= *)

let pde_cavg = define
 `(!G:real^N->real^1. pde_cavg 0 G = G) /\
  (!m (G:real^N->real^1). pde_cavg (SUC m) G = pde_lavg (SUC m) (pde_cavg m G))`;;

let PDE_CAVG_SMOOTH = prove
 (`!m (G:real^N->real^1).
        smooth_map_on (:real^N) G
        ==> smooth_map_on (:real^N) (pde_cavg m G) /\
            !i x. partial_derivative i (pde_cavg m G) x =
                  pde_cavg m (partial_derivative i G) x`,
  INDUCT_TAC THEN REWRITE_TAC[pde_cavg] THEN SIMP_TAC[] THEN
  X_GEN_TAC `G:real^N->real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `G:real^N->real^1`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC m`; `pde_cavg m (G:real^N->real^1)`] PDE_LAVG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]);;

let PDE_CAVG_ZPER = prove
 (`!m (G:real^N->real^1). pde_zper G ==> pde_zper (pde_cavg m G)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[pde_cavg; PDE_LAVG_ZPER]);;

let PDE_CAVG_CONTINUOUS = prove
 (`!m (G:real^N->real^1).
        smooth_map_on (:real^N) G ==> (pde_cavg m G) continuous_on (:real^N)`,
  MESON_TAC[PDE_CAVG_SMOOTH; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let PDE_CAVG_NORM_LE = prove
 (`!m (G1:real^N->real^1) G2 x.
        smooth_map_on (:real^N) G1 /\ smooth_map_on (:real^N) G2 /\
        (!y. norm(G1 y) <= drop(G2 y))
        ==> norm(pde_cavg m G1 x) <= drop(pde_cavg m G2 x)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[pde_cavg] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDE_LAVG_NORM_LE THEN ASM_SIMP_TAC[PDE_CAVG_CONTINUOUS]);;

let PDE_CAVG_LE = prove
 (`!m (G1:real^N->real^1) G2 x.
        smooth_map_on (:real^N) G1 /\ smooth_map_on (:real^N) G2 /\
        (!y. drop(G1 y) <= drop(G2 y))
        ==> drop(pde_cavg m G1 x) <= drop(pde_cavg m G2 x)`,
  INDUCT_TAC THEN ASM_SIMP_TAC[pde_cavg] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC PDE_LAVG_LE THEN ASM_SIMP_TAC[PDE_CAVG_CONTINUOUS]);;

let PDE_CAVG_ADD = prove
 (`!m (G1:real^N->real^1) G2 x.
        smooth_map_on (:real^N) G1 /\ smooth_map_on (:real^N) G2
        ==> pde_cavg m (\y. G1 y + G2 y) x = pde_cavg m G1 x + pde_cavg m G2 x`,
  INDUCT_TAC THEN REWRITE_TAC[pde_cavg] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pde_cavg m (\y. (G1:real^N->real^1) y + G2 y) =
                (\y. pde_cavg m G1 y + pde_cavg m G2 y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PDE_LAVG_ADD THEN ASM_SIMP_TAC[PDE_CAVG_CONTINUOUS]);;

let PDE_CAVG_ZERO = prove
 (`!m x. pde_cavg m (\y:real^N. vec 0:real^1) x = vec 0`,
  INDUCT_TAC THEN REWRITE_TAC[pde_cavg] THEN GEN_TAC THEN
  SUBGOAL_THEN `pde_cavg m (\y:real^N. vec 0:real^1) = (\y. vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pde_lavg; INTEGRAL_0]);;

let PDE_CAVG_POS = prove
 (`!m (G:real^N->real^1) x.
        smooth_map_on (:real^N) G /\ (!y. &0 <= drop(G y))
        ==> &0 <= drop(pde_cavg m G x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `\y:real^N. vec 0:real^1`; `G:real^N->real^1`; `x:real^N`]
                PDE_CAVG_LE) THEN
  ASM_REWRITE_TAC[PDE_CAVG_ZERO; SMOOTH_MAP_ON_CONST; DROP_VEC]);;

(* Independence of the coordinates already averaged. *)

let PDE_CAVG_INDEP = prove
 (`!m (G:real^N->real^1) j x c.
        smooth_map_on (:real^N) G /\ pde_zper G /\ 1 <= j /\ j <= m /\ m <= dimindex(:N)
        ==> pde_cavg m G (x + c % basis j) = pde_cavg m G x`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pde_cavg] THEN ASM_CASES_TAC `j = SUC m` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC PDE_LAVG_INDEP THEN
    ASM_SIMP_TAC[PDE_CAVG_CONTINUOUS; PDE_CAVG_ZPER] THEN ARITH_TAC;
    REWRITE_TAC[pde_lavg] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `r:real^1` THEN
    SUBGOAL_THEN `(x + c % basis j) + drop r % basis (SUC m):real^N =
                  (x + drop r % basis (SUC m)) + c % basis j` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* A map independent of every coordinate is constant. *)

let PDE_INDEP_CONST = prove
 (`!(H:real^N->B).
        (!j x c. 1 <= j /\ j <= dimindex(:N) ==> H(x + c % basis j) = H x)
        ==> !x. H x = H(vec 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. FINITE s
        ==> s SUBSET 1..dimindex(:N)
            ==> !y. (H:real^N->B)(y + vsum s (\i. (x:real^N)$i % basis i)) = H y`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[VSUM_CLAUSES; VECTOR_ADD_RID] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `s:num->bool`] THEN
    REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
    STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN ASM_SIMP_TAC[VSUM_CLAUSES] THEN
    REWRITE_TAC[VECTOR_ARITH `y + a + b:real^N = (y + b) + a`] THEN
    ASM_SIMP_TAC[] THEN USE_THEN "ih" (fun th -> ASM_SIMP_TAC[th]);
    DISCH_THEN(MP_TAC o SPEC `1..dimindex(:N)`) THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET_REFL; BASIS_EXPANSION] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN REWRITE_TAC[VECTOR_ADD_LID]]);;

let PDE_CAVG_CUBE = prove
 (`!m (G:real^N->real^1).
        smooth_map_on (:real^N) G /\ pde_zper G /\ m <= dimindex(:N)
        ==> integral (interval[vec 0,vec 1]) (pde_cavg m G) =
            integral (interval[vec 0,vec 1]) G`,
  INDUCT_TAC THEN REWRITE_TAC[pde_cavg] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC m`; `pde_cavg m (G:real^N->real^1)`] PDE_LAVG_CUBE) THEN
  ASM_SIMP_TAC[PDE_CAVG_CONTINUOUS; PDE_CAVG_ZPER] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let PDE_CAVG_FULL = prove
 (`!(G:real^N->real^1) x.
        smooth_map_on (:real^N) G /\ pde_zper G
        ==> pde_cavg (dimindex(:N)) G x = integral (interval[vec 0,vec 1]) G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `G:real^N->real^1`] PDE_CAVG_CUBE) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `!y. pde_cavg (dimindex(:N)) (G:real^N->real^1) y = pde_cavg (dimindex(:N)) G (vec 0)`
  MP_TAC THENL
   [MATCH_MP_TAC PDE_INDEP_CONST THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC PDE_CAVG_INDEP THEN ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(fun cth ->
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral (interval[vec 0:real^N,vec 1])
                         (\y. pde_cavg (dimindex(:N)) (G:real^N->real^1) (vec 0))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTEGRAL_CONST; CONTENT_UNIT; VECTOR_MUL_LID] THEN MATCH_ACCEPT_TAC cth;
      MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      BETA_TAC THEN CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC cth]));;

(* ========================================================================= *)
(* The Sobolev embedding.  One averaging step costs a factor 3 and one more  *)
(* derivative; after N steps the means are cube integrals:                   *)
(* |u(x)|^2 <= 3^N pde_hs2 N u (PDE_TORUS_SOBOLEV), and for iterated         *)
(* partials |D^l u(x)|^2 <= 3^N pde_hs2 (N + |l|) u.                         *)
(* ========================================================================= *)

let PDE_INDEX_LISTS_0 = prove
 (`pde_index_lists 0 (:N) = {[]}`,
  REWRITE_TAC[pde_index_lists; EXTENSION; IN_ELIM_THM; IN_SING; LE; LENGTH_EQ_NIL] THEN
  MESON_TAC[ALL]);;

let PDE_SQNORM_SMOOTH = prove
 (`!(w:real^N->real^K).
        smooth_map_on (:real^N) w ==> smooth_map_on (:real^N) (\y. lift(norm(w y) pow 2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
  MP_TAC(ISPECL [`(:real^N)`; `\x y:real^K. lift(x dot y)`; `w:real^N->real^K`;
                 `w:real^N->real^K`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT; OPEN_UNIV]);;

let PDE_DOT_TWICE_BOUND = prove
 (`!a b:real^K. abs(a dot b + b dot a) <= a dot a + b dot b`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `a - b:real^K` DOT_POS_LE) THEN MP_TAC(ISPEC `a + b:real^K` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN REAL_ARITH_TAC);;

let PDE_SQNORM_PARTIAL_BOUND = prove
 (`!(w:real^N->real^K) j x.
        smooth_map_on (:real^N) w
        ==> norm(partial_derivative j (\y. lift(norm(w y) pow 2)) x) <=
            norm(w x) pow 2 + norm(partial_derivative j w x) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
  MP_TAC(ISPECL [`w:real^N->real^K`; `w:real^N->real^K`; `j:num`; `x:real^N`]
                PDE_PARTIAL_DOT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM LIFT_ADD; NORM_LIFT] THEN
  MP_TAC(ISPECL [`partial_derivative j (w:real^N->real^K) x`; `(w:real^N->real^K) x`]
                PDE_DOT_TWICE_BOUND) THEN
  REAL_ARITH_TAC);;

let PDE_SOBOLEV_STEP = prove
 (`!m (h:real^N->real^K) l x.
        smooth_map_on (:real^N) h /\ pde_zper h
        ==> drop(pde_cavg m (\y. lift(norm(iterated_partial l h y) pow 2)) x) <=
            &2 * drop(pde_cavg (SUC m) (\y. lift(norm(iterated_partial l h y) pow 2)) x) +
            drop(pde_cavg (SUC m)
                   (\y. lift(norm(iterated_partial (CONS (SUC m) l) h y) pow 2)) x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `w = iterated_partial l (h:real^N->real^K)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (w:real^N->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[iterated_partial] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `G = \y. lift(norm((w:real^N->real^K) y) pow 2)` THEN
  ABBREV_TAC `Gd = \y. lift(norm(partial_derivative (SUC m) (w:real^N->real^K) y) pow 2)` THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (G:real^N->real^1) /\
                smooth_map_on (:real^N) (Gd:real^N->real^1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G"; "Gd"] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_SQNORM_SMOOTH THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (partial_derivative (SUC m) (G:real^N->real^1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `G:real^N->real^1`] PDE_CAVG_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`SUC m`; `pde_cavg m (G:real^N->real^1)`; `x:real^N`] PDE_LAVG_1D) THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 pde_cavg)] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c + d ==> a <= c + b ==> a <= &2 * c + d`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(pde_lavg (SUC m)
                     (\y. pde_cavg m (G:real^N->real^1) y + pde_cavg m Gd y) x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PDE_LAVG_LE THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_1] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      ASM_SIMP_TAC[PDE_CAVG_CONTINUOUS; ETA_AX];
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN ASM_SIMP_TAC[PDE_CAVG_CONTINUOUS; ETA_AX];
      X_GEN_TAC `y:real^N` THEN REWRITE_TAC[LIFT_DROP; GSYM NORM_1] THEN
      ASM_SIMP_TAC[GSYM PDE_CAVG_ADD] THEN
      MATCH_MP_TAC PDE_CAVG_NORM_LE THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_ADD_OPEN; OPEN_UNIV] THEN
      X_GEN_TAC `z:real^N` THEN MAP_EVERY EXPAND_TAC ["G"; "Gd"] THEN
      REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN MATCH_MP_TAC PDE_SQNORM_PARTIAL_BOUND THEN
      ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[PDE_LAVG_ADD; PDE_CAVG_CONTINUOUS; DROP_ADD; pde_cavg; REAL_LE_REFL;
                 ETA_AX]]);;

let PDE_SOBOLEV_ITER = prove
 (`!m (h:real^N->real^K) x.
        smooth_map_on (:real^N) h /\ pde_zper h /\ m <= dimindex(:N)
        ==> norm(h x) pow 2 <=
            &3 pow m *
            sum (pde_index_lists m (:N))
                (\l. drop(pde_cavg m (\y. lift(norm(iterated_partial l h y) pow 2)) x))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[PDE_INDEX_LISTS_0; SUM_SING; pde_cavg; iterated_partial; LIFT_DROP;
                real_pow; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`h:real^N->real^K`; `x:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  ABBREV_TAC
   `bb = \l. drop(pde_cavg (SUC m)
                    (\y. lift(norm(iterated_partial l (h:real^N->real^K) y) pow 2)) x)` THEN
  SUBGOAL_THEN `!l:num list. &0 <= bb l` ASSUME_TAC THENL
   [X_GEN_TAC `l:num list` THEN EXPAND_TAC "bb" THEN MATCH_MP_TAC PDE_CAVG_POS THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN MATCH_MP_TAC PDE_SQNORM_SMOOTH THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  ABBREV_TAC `S = sum (pde_index_lists (SUC m) (:N)) (bb:num list->real)` THEN
  SUBGOAL_THEN `sum (pde_index_lists m (:N)) (bb:num list->real) <= S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; PDE_INDEX_LISTS_MONO; ARITH_RULE `m <= SUC m`];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum (pde_index_lists m (:N)) (\l. (bb:num list->real) (CONS (SUC m) l)) <= S`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`CONS (SUC m):num list->num list`; `bb:num list->real`;
                   `pde_index_lists m (:N)`] SUM_IMAGE) THEN
    ANTS_TAC THENL [SIMP_TAC[CONS_11]; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; pde_index_lists; IN_ELIM_THM; LENGTH; ALL] THEN
    REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_pow; REAL_ARITH `(&3 * a) * s = a * (&3 * s)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (pde_index_lists m (:N))
                  (\l. &2 * (bb:num list->real) l + bb (CONS (SUC m) l))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN EXPAND_TAC "bb" THEN
    MATCH_MP_TAC PDE_SOBOLEV_STEP THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; PDE_INDEX_LISTS_FINITE] THEN ASM_REAL_ARITH_TAC]);;

let PDE_TORUS_SOBOLEV = prove
 (`?C. &0 < C /\
       !(u:real^N->real^K) x.
          smooth_map_on (:real^N) u /\ pde_zper u
          ==> norm(u x) pow 2 <= C * pde_hs2 (dimindex(:N)) u`,
  EXISTS_TAC `&3 pow dimindex(:N)` THEN
  SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &3`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`dimindex(:N)`; `u:real^N->real^K`; `x:real^N`] PDE_SOBOLEV_ITER) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[pde_hs2] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PDE_CAVG_FULL THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_SQNORM_SMOOTH THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
    MP_TAC(ISPECL [`iterated_partial l (u:real^N->real^K)`; `\v:real^K. lift(norm v pow 2)`]
                  PDE_ZPER_COMPOSE) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC PDE_ZPER_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]]);;

let PDE_HS2_ITERATED_PARTIAL_LE = prove
 (`!l s (u:real^N->real^K).
        smooth_map_on (:real^N) u /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
        ==> pde_hs2 s (iterated_partial l u) <= pde_hs2 (s + LENGTH l) u`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[iterated_partial; LENGTH; ADD_CLAUSES; REAL_LE_REFL; ALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_hs2 (SUC s) (iterated_partial t (u:real^N->real^K))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PDE_HS2_PARTIAL_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
    REWRITE_TAC[ARITH_RULE `SUC(s + n) = SUC s + n`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let PDE_TORUS_SOBOLEV_PARTIAL = prove
 (`?C. &0 < C /\
       !(u:real^N->real^K) l x.
          smooth_map_on (:real^N) u /\ pde_zper u /\
          ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
          ==> norm(iterated_partial l u x) pow 2 <=
              C * pde_hs2 (dimindex(:N) + LENGTH l) u`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC PDE_TORUS_SOBOLEV THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * pde_hs2 (dimindex(:N)) (iterated_partial l (u:real^N->real^K))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC PDE_ZPER_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC PDE_HS2_ITERATED_PARTIAL_LE THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Interpolation (PDE_TORUS_INTERP).  The integration by parts bound         *)
(* |D_i w|^2 <= d |D_i D_i w|^2 + |w|^2 / (4 d) in L^2, the case s = 0, and  *)
(* induction on s through the recursion PDE_HS2_SUC.                         *)
(* ========================================================================= *)

let PDE_DOT_AMGM = prove
 (`!(w:real^K) v d. &0 < d ==> --(w dot v) <= d * norm v pow 2 + inv(&4 * d) * norm w pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
  MP_TAC(ISPEC `(&2 * d) % v + w:real^K` DOT_POS_LE) THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &4 * d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `&4 * d` THEN
  ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
               REAL_MUL_LID] THEN
  ASM_REAL_ARITH_TAC);;

let PDE_IBP_GRAD_BOUND = prove
 (`!(w:real^N->real^K) i d.
        smooth_map_on (:real^N) w /\ pde_zper w /\ 1 <= i /\ i <= dimindex(:N) /\ &0 < d
        ==> pde_hs2 0 (partial_derivative i w) <=
            d * pde_hs2 0 (partial_derivative i (partial_derivative i w)) +
            inv(&4 * d) * pde_hs2 0 w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PDE_HS2_0] THEN
  ABBREV_TAC `v = partial_derivative i (partial_derivative i (w:real^N->real^K))` THEN
  SUBGOAL_THEN
   `smooth_map_on (:real^N) (partial_derivative i (w:real^N->real^K)) /\
    smooth_map_on (:real^N) (v:real^N->real^K) /\
    pde_zper (partial_derivative i (w:real^N->real^K))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; PDE_ZPER_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^N->real^K. smooth_map_on (:real^N) f
        ==> (\x. lift(norm(f x) pow 2)) integrable_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^K`; `[]:num list`] PDE_SQNORM_INTEGRABLE) THEN
    ASM_REWRITE_TAC[iterated_partial];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N->real^K`; `partial_derivative i (w:real^N->real^K)`; `i:num`]
                PDE_CUBE_IBP) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM NORM_POW_2] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(\x. lift((w:real^N->real^K) x dot v x)) integrable_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_NEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (interval[vec 0,vec 1])
                 (\x. d % lift(norm((v:real^N->real^K) x) pow 2) +
                      inv(&4 * d) % lift(norm((w:real^N->real^K) x) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_NEG; INTEGRABLE_ADD; INTEGRABLE_CMUL] THEN
    REWRITE_TAC[DROP_NEG; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    ASM_SIMP_TAC[PDE_DOT_AMGM];
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_CMUL; INTEGRABLE_CMUL; DROP_ADD; DROP_CMUL;
                 REAL_LE_REFL]]);;

(* The case s = 0. *)

let PDE_TORUS_INTERP_BASE = prove
 (`!e (u:real^N->real^K).
        &0 < e /\ smooth_map_on (:real^N) u /\ pde_zper u
        ==> pde_hs2 1 u <=
            e * pde_hs2 2 u + (&1 + &(dimindex(:N)) * inv(&4 * e)) * pde_hs2 0 u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pde_hs2 1 (u:real^N->real^K) =
    pde_hs2 0 u + sum (1..dimindex(:N)) (\i. pde_hs2 0 (partial_derivative i u))`
  SUBST1_TAC THENL [REWRITE_TAC[ONE; PDE_HS2_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (1..dimindex(:N)) (\i. pde_hs2 1 (partial_derivative i (u:real^N->real^K))) <=
    pde_hs2 2 u`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `u:real^N->real^K`] PDE_HS2_PARTIAL_SUM_LE) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 1 = 2`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_hs2 0 (u:real^N->real^K) +
              (e * sum (1..dimindex(:N)) (\i. pde_hs2 1 (partial_derivative i u)) +
               &(dimindex(:N)) * inv(&4 * e) * pde_hs2 0 u)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (1..dimindex(:N))
                    (\i. e * pde_hs2 1 (partial_derivative i (u:real^N->real^K)) +
                         inv(&4 * e) * pde_hs2 0 u)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e * pde_hs2 0 (partial_derivative i (partial_derivative i
                                   (u:real^N->real^K))) +
                  inv(&4 * e) * pde_hs2 0 u` THEN
      ASM_SIMP_TAC[PDE_IBP_GRAD_BOUND; REAL_LE_RADD] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MP_TAC(ISPECL [`0`; `i:num`; `partial_derivative i (u:real^N->real^K)`]
                    PDE_HS2_PARTIAL_LE) THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; ARITH_RULE `SUC 0 = 1`];
      REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG;
                  ARITH_RULE `(n + 1) - 1 = n`] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH
     `e * t <= e * t2 ==> h + (e * t + n * c * h) <= e * t2 + (&1 + n * c) * h`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let PDE_TORUS_INTERP_POS = prove
 (`!s e. &0 < e
         ==> ?C. &0 <= C /\
                 !(u:real^N->real^K).
                   smooth_map_on (:real^N) u /\ pde_zper u
                   ==> pde_hs2 (s + 1) u <= e * pde_hs2 (s + 2) u + C * pde_hs2 0 u`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `&1 + &(dimindex(:N)) * inv(&4 * e)` THEN
    ASM_SIMP_TAC[PDE_TORUS_INTERP_BASE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
  SUBGOAL_THEN `&0 < e / (&2 * (C1 + &1)) /\ C1 * e / (&2 * (C1 + &1)) <= e / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < C1 + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `C1 * e / (&2 * (C1 + &1)) = (e / &2) * (C1 / (C1 + &1))` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < C1 + &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e2 = e / (&2 * (C1 + &1))` THEN
  ABBREV_TAC `C2 = &1 + &(dimindex(:N)) * inv(&4 * e2)` THEN
  SUBGOAL_THEN `&0 <= C2` ASSUME_TAC THENL
   [EXPAND_TAC "C2" THEN MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `&1 + C1 * C2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL]; ALL_TAC] THEN
  X_GEN_TAC `u:real^N->real^K` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC s + 1 = SUC(s + 1)`; PDE_HS2_SUC] THEN
  ABBREV_TAC `H = pde_hs2 (SUC s + 2) (u:real^N->real^K)` THEN
  ABBREV_TAC `h0 = pde_hs2 0 (u:real^N->real^K)` THEN
  ABBREV_TAC `h1 = pde_hs2 1 (u:real^N->real^K)` THEN
  ABBREV_TAC `A = sum (1..dimindex(:N)) (\i. pde_hs2 (s + 1) (partial_derivative i (u:real^N->real^K)))` THEN
  ABBREV_TAC `B = sum (1..dimindex(:N)) (\i. pde_hs2 (s + 2) (partial_derivative i (u:real^N->real^K)))` THEN
  ABBREV_TAC `D = sum (1..dimindex(:N)) (\i. pde_hs2 0 (partial_derivative i (u:real^N->real^K)))` THEN
  SUBGOAL_THEN `A <= e / &2 * B + C1 * D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"; "D"] THEN
    REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN USE_THEN "ih" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV; PDE_ZPER_PARTIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `B <= H` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B"; "H"] THEN
    REWRITE_TAC[ARITH_RULE `SUC s + 2 = SUC(s + 2)`] THEN
    MATCH_MP_TAC PDE_HS2_PARTIAL_SUM_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `D <= h1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "h1"] THEN
    MP_TAC(ISPECL [`0`; `u:real^N->real^K`] PDE_HS2_PARTIAL_SUM_LE) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC 0 = 1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `h1 <= e2 * H + C2 * h0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "H"; "h0"; "C2"] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e2 * pde_hs2 2 (u:real^N->real^K) +
                (&1 + &(dimindex(:N)) * inv(&4 * e2)) * pde_hs2 0 u` THEN
    ASM_SIMP_TAC[PDE_TORUS_INTERP_BASE; REAL_LE_RADD] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    EXPAND_TAC "H" THEN
    MATCH_MP_TAC PDE_HS2_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= H /\ &0 <= h0 /\ &0 <= B /\ &0 <= D /\ &0 <= h1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H"; "h0"; "B"; "D"; "h1"] THEN
    REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC PDE_HS2_POS THEN FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PDE_HS2_POS THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `e / &2 * B <= e / &2 * H /\ C1 * D <= C1 * h1 /\
                C1 * h1 <= C1 * (e2 * H + C2 * h0) /\ (C1 * e2) * H <= e / &2 * H`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let PDE_TORUS_INTERP = prove
 (`!s e. &0 < e
         ==> ?C. !(u:real^N->real^K).
                   smooth_map_on (:real^N) u /\ pde_zper u
                   ==> pde_hs2 (s + 1) u <= e * pde_hs2 (s + 2) u + C * pde_hs2 0 u`,
  MESON_TAC[PDE_TORUS_INTERP_POS]);;

(* ========================================================================= *)
(* Leibniz and commutator bounds.  For a bilinear bb with                    *)
(* |bb x y| <= M |x| |y| and f with all derivatives up to order |l| bounded  *)
(* by A, the iterated partial D^l bb(f,g) is bounded by 2^|l| M A times the  *)
(* jet norm of g of order |l| (PDE_LEIBNIZ_BOUND), and                       *)
(* D^l bb(f,g) - bb(f,D^l g) by the jet norm of order                        *)
(* |l| - 1 (PDE_COMMUTATOR_BOUND).                                           *)
(* ========================================================================= *)

(* The pointwise jet norm of order m. *)

let pde_jetn = new_definition
 `pde_jetn m (g:real^N->real^Q) x =
    sum (pde_index_lists m (:N)) (\l. norm(iterated_partial l g x))`;;

let PDE_JETN_POS = prove
 (`!m (g:real^N->real^Q) x. &0 <= pde_jetn m g x`,
  REWRITE_TAC[pde_jetn] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[NORM_POS_LE]);;

let PDE_JETN_MONO = prove
 (`!m m' (g:real^N->real^Q) x. m <= m' ==> pde_jetn m g x <= pde_jetn m' g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE; PDE_INDEX_LISTS_MONO; NORM_POS_LE]);;

let PDE_JETN_PARTIAL = prove
 (`!m i (g:real^N->real^Q) x.
        1 <= i /\ i <= dimindex(:N)
        ==> pde_jetn m (partial_derivative i g) x <= pde_jetn (SUC m) g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_jetn] THEN
  SUBGOAL_THEN
   `!l. iterated_partial l (partial_derivative i (g:real^N->real^Q)) =
        iterated_partial (APPEND l [i]) g`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\l:num list. APPEND l [i:num]`;
                 `\l:num list. norm(iterated_partial l (g:real^N->real^Q) x)`;
                 `pde_index_lists m (:N)`] SUM_IMAGE) THEN
  ANTS_TAC THENL [SIMP_TAC[PDE_APPEND_SING_INJ]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE; NORM_POS_LE] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; pde_index_lists; IN_ELIM_THM;
              LENGTH_APPEND; ALL_APPEND; ALL; LENGTH] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Partials of bilinear products. *)

let PDE_PARTIAL_BILINEAR = prove
 (`!(bb:real^P->real^Q->real^K) (f:real^N->real^P) g i x.
        bilinear bb /\ f differentiable (at x) /\ g differentiable (at x)
        ==> partial_derivative i (\x. bb (f x) (g x)) x =
            bb (partial_derivative i f x) (g x) + bb (f x) (partial_derivative i g x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[partial_derivative] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `f:real^N->real^P`; `g:real^N->real^Q`;
                 `frechet_derivative (f:real^N->real^P) (at x)`;
                 `frechet_derivative (g:real^N->real^Q) (at x)`; `x:real^N`]
                HAS_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);;

let PDE_ITERATED_PARTIAL_BILINEAR_STEP = prove
 (`!(bb:real^P->real^Q->real^K) (f:real^N->real^P) g l i x.
        bilinear bb /\ smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g
        ==> iterated_partial (APPEND l [i]) (\x. bb (f x) (g x)) x =
            iterated_partial l (\x. bb (partial_derivative i f x) (g x)) x +
            iterated_partial l (\x. bb (f x) (partial_derivative i g x)) x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial] THEN
  SUBGOAL_THEN
   `partial_derivative i (\x:real^N. (bb:real^P->real^Q->real^K) ((f:real^N->real^P) x)
                                                                   ((g:real^N->real^Q) x)) =
    (\x. bb (partial_derivative i f x) (g x) + bb (f x) (partial_derivative i g x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC PDE_PARTIAL_BILINEAR THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:num list`; `(:real^N)`;
                 `\x:real^N. (bb:real^P->real^Q->real^K)
                        (partial_derivative i (f:real^N->real^P) x) ((g:real^N->real^Q) x)`;
                 `\x:real^N. (bb:real^P->real^Q->real^K)
                        ((f:real^N->real^P) x) (partial_derivative i (g:real^N->real^Q) x)`]
                PDE_ITERATED_PARTIAL_ADD_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^N)`; `bb:real^P->real^Q->real^K`;
                     `partial_derivative i (f:real^N->real^P)`; `g:real^N->real^Q`]
                    SMOOTH_MAP_ON_BILINEAR_OPEN);
      MP_TAC(ISPECL [`(:real^N)`; `bb:real^P->real^Q->real^K`;
                     `f:real^N->real^P`; `partial_derivative i (g:real^N->real^Q)`]
                    SMOOTH_MAP_ON_BILINEAR_OPEN)] THEN
    ASM_SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN REWRITE_TAC[]]);;

let PDE_LEIBNIZ_BOUND = prove
 (`!(bb:real^P->real^Q->real^K) M A.
        bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M /\ &0 <= A
        ==> !l (f:real^N->real^P) (g:real^N->real^Q) x.
              smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g /\
              (!l' y. LENGTH l' <= LENGTH l /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l'
                      ==> norm(iterated_partial l' f y) <= A) /\
              ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
              ==> norm(iterated_partial l (\x. bb (f x) (g x)) x) <=
                  &2 pow (LENGTH l) * M * A * pde_jetn (LENGTH l) g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!l (f:real^N->real^P) (g:real^N->real^Q) x.
        smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g /\
        (!l' y. LENGTH l' <= LENGTH (REVERSE l) /\
                ALL (\i. 1 <= i /\ i <= dimindex(:N)) l'
                ==> norm(iterated_partial l' f y) <= A) /\
        ALL (\i. 1 <= i /\ i <= dimindex(:N)) (REVERSE l)
        ==> norm(iterated_partial (REVERSE l)
                       (\x. (bb:real^P->real^Q->real^K) (f x) (g x)) x) <=
            &2 pow (LENGTH (REVERSE l)) * M * A * pde_jetn (LENGTH (REVERSE l)) g x`
  (LABEL_TAC "main") THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "main" (MP_TAC o SPEC `REVERSE l:num list`) THEN
    REWRITE_TAC[REVERSE_REVERSE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[REVERSE; LENGTH; iterated_partial; real_pow; REAL_MUL_LID] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[pde_jetn; PDE_INDEX_LISTS_0; SUM_SING; iterated_partial] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * norm((f:real^N->real^P) x) * norm((g:real^N->real^Q) x)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[]:num list`; `x:real^N`]) THEN
    REWRITE_TAC[LENGTH; LE_REFL; ALL; iterated_partial];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  REWRITE_TAC[REVERSE; LENGTH_APPEND; LENGTH; ALL_APPEND; ALL; ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^P`; `g:real^N->real^Q`; `x:real^N`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[PDE_ITERATED_PARTIAL_BILINEAR_STEP] THEN
  ABBREV_TAC `c = &2 pow (LENGTH (REVERSE (t:num list))) * M * A` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) (partial_derivative h (f:real^N->real^P) x)
                                             ((g:real^N->real^Q) x)) x) <=
    c * pde_jetn (LENGTH (REVERSE (t:num list))) g x`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    USE_THEN "ih" (MP_TAC o SPECL [`partial_derivative h (f:real^N->real^P)`;
                                   `g:real^N->real^Q`; `x:real^N`]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`l':num list`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `iterated_partial l' (partial_derivative h (f:real^N->real^P)) =
                  iterated_partial (APPEND l' [h]) f` SUBST1_TAC THENL
     [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; ALL_APPEND; ALL; LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) ((f:real^N->real^P) x)
                                             (partial_derivative h (g:real^N->real^Q) x)) x) <=
    c * pde_jetn (LENGTH (REVERSE (t:num list))) (partial_derivative h g) x`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    USE_THEN "ih" (MP_TAC o SPECL [`f:real^N->real^P`;
                                   `partial_derivative h (g:real^N->real^Q)`; `x:real^N`]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `n = LENGTH (REVERSE (t:num list))` THEN
  SUBGOAL_THEN
   `c * pde_jetn n (g:real^N->real^Q) x <= c * pde_jetn (SUC n) g x /\
    c * pde_jetn n (partial_derivative h g) x <= c * pde_jetn (SUC n) g x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PDE_JETN_PARTIAL; PDE_JETN_MONO; ARITH_RULE `n <= SUC n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow SUC n * M * A * pde_jetn (SUC n) (g:real^N->real^Q) x =
                &2 * (c * pde_jetn (SUC n) g x)` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) (partial_derivative h (f:real^N->real^P) x)
                                             ((g:real^N->real^Q) x)) x) +
    norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) ((f:real^N->real^P) x)
                                             (partial_derivative h (g:real^N->real^Q) x)) x)` THEN
  REWRITE_TAC[NORM_TRIANGLE] THEN ASM_REAL_ARITH_TAC);;

let PDE_COMMUTATOR_BOUND = prove
 (`!(bb:real^P->real^Q->real^K) M A.
        bilinear bb /\ (!x y. norm(bb x y) <= M * norm x * norm y) /\ &0 <= M /\ &0 <= A
        ==> !l (f:real^N->real^P) (g:real^N->real^Q) x.
              smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g /\
              (!l' y. LENGTH l' <= LENGTH l /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l'
                      ==> norm(iterated_partial l' f y) <= A) /\
              ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
              ==> norm(iterated_partial l (\x. bb (f x) (g x)) x -
                       bb (f x) (iterated_partial l g x)) <=
                  &2 pow (LENGTH l) * M * A * pde_jetn (PRE(LENGTH l)) g x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bb:real^P->real^Q->real^K`; `M:real`; `A:real`] PDE_LEIBNIZ_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "leib") THEN
  SUBGOAL_THEN
   `!l (f:real^N->real^P) (g:real^N->real^Q) x.
        smooth_map_on (:real^N) f /\ smooth_map_on (:real^N) g /\
        (!l' y. LENGTH l' <= LENGTH (REVERSE l) /\
                ALL (\i. 1 <= i /\ i <= dimindex(:N)) l'
                ==> norm(iterated_partial l' f y) <= A) /\
        ALL (\i. 1 <= i /\ i <= dimindex(:N)) (REVERSE l)
        ==> norm(iterated_partial (REVERSE l)
                   (\x. (bb:real^P->real^Q->real^K) (f x) (g x)) x -
                 bb (f x) (iterated_partial (REVERSE l) g x)) <=
            &2 pow (LENGTH (REVERSE l)) * M * A * pde_jetn (PRE(LENGTH (REVERSE l))) g x`
  (LABEL_TAC "main") THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "main" (MP_TAC o SPEC `REVERSE l:num list`) THEN
    REWRITE_TAC[REVERSE_REVERSE] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[REVERSE; LENGTH; iterated_partial; VECTOR_SUB_REFL; NORM_0] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS; PDE_JETN_POS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(LABEL_TAC "ih") THEN
  REWRITE_TAC[REVERSE; LENGTH_APPEND; LENGTH; ALL_APPEND; ALL; ADD_CLAUSES; PRE] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^P`; `g:real^N->real^Q`; `x:real^N`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[PDE_ITERATED_PARTIAL_BILINEAR_STEP] THEN
  REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX] THEN
  ABBREV_TAC `c = &2 pow (LENGTH (REVERSE (t:num list))) * M * A` THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) (partial_derivative h (f:real^N->real^P) x)
                                             ((g:real^N->real^Q) x)) x) <=
    c * pde_jetn (LENGTH (REVERSE (t:num list))) g x`
  ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    USE_THEN "leib" (MP_TAC o SPECL [`REVERSE t:num list`;
                                     `partial_derivative h (f:real^N->real^P)`;
                                     `g:real^N->real^Q`; `x:real^N`]) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`l':num list`; `y:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `iterated_partial l' (partial_derivative h (f:real^N->real^P)) =
                  iterated_partial (APPEND l' [h]) f` SUBST1_TAC THENL
     [REWRITE_TAC[ITERATED_PARTIAL_APPEND; iterated_partial; ETA_AX]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; ALL_APPEND; ALL; LENGTH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `n = LENGTH (REVERSE (t:num list))` THEN
  SUBGOAL_THEN
   `norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) ((f:real^N->real^P) x)
                                             (partial_derivative h (g:real^N->real^Q) x)) x -
         bb (f x) (iterated_partial (REVERSE t) (partial_derivative h g) x)) <=
    c * pde_jetn n g x`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [SUBGOAL_THEN `REVERSE (t:num list) = []` SUBST1_TAC THENL
       [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
      REWRITE_TAC[iterated_partial; VECTOR_SUB_REFL; NORM_0] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; PDE_JETN_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * pde_jetn (PRE n) (partial_derivative h (g:real^N->real^Q)) x` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      USE_THEN "ih" (MP_TAC o SPECL [`f:real^N->real^P`;
                                     `partial_derivative h (g:real^N->real^Q)`; `x:real^N`]) THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; OPEN_UNIV] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_jetn (SUC(PRE n)) (g:real^N->real^Q) x` THEN
      ASM_SIMP_TAC[PDE_JETN_PARTIAL] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> SUC(PRE n) = n`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow SUC n * M * A * pde_jetn n (g:real^N->real^Q) x =
                &2 * (c * pde_jetn n g x)` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) (partial_derivative h (f:real^N->real^P) x)
                                             ((g:real^N->real^Q) x)) x) +
    norm(iterated_partial (REVERSE t)
           (\x. (bb:real^P->real^Q->real^K) ((f:real^N->real^P) x)
                                             (partial_derivative h (g:real^N->real^Q) x)) x -
         bb (f x) (iterated_partial (REVERSE t) (partial_derivative h g) x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `(a + b) - c:real^K = a + (b - c)`; NORM_TRIANGLE];
    ASM_REAL_ARITH_TAC]);;

(* Smooth periodic maps have bounded derivatives of every order (the        *)
(* constant A of the Leibniz and commutator bounds).                         *)

let PDE_ZPER_JET_BOUNDED = prove
 (`!(f:real^N->real^P) k.
        smooth_map_on (:real^N) f /\ pde_zper f
        ==> ?A. &0 <= A /\
                !l y. LENGTH l <= k /\ ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
                      ==> norm(iterated_partial l f y) <= A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?B. !l y. norm(iterated_partial l (f:real^N->real^P) y) <= B l`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `l:num list` THEN
    MATCH_MP_TAC PDE_ZPER_BOUNDED THEN REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC PDE_ZPER_ITERATED_PARTIAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `sum (pde_index_lists k (:N)) (\l. abs((B:num list->real) l))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((B:num list->real) l)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_ARITH `x <= b ==> x <= abs b`]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {l:num list} (\l. abs((B:num list->real) l))` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_SING; REAL_LE_REFL];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[PDE_INDEX_LISTS_FINITE; REAL_ABS_POS; SING_SUBSET] THEN
    ASM_REWRITE_TAC[pde_index_lists; IN_ELIM_THM]]);;

