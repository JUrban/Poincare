(* ========================================================================= *)
(* pc_p2a_pconv: local convexity of the L-length and the local boundary      *)
(* value problem for piecewise C^1 competitors (used for the regularity of   *)
(* minimizers, L2).  A competitor is continuous on the s-interval and        *)
(* differentiable off a finite set K, with a bounded derivative; the         *)
(* fundamental theorem of calculus with a countable exceptional set          *)
(* (FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) and measurability       *)
(* replace the C^1 arguments of pc_p2a_bvp and pc_p2a_lbvp.                  *)
(*                                                                           *)
(* First: integrals of such derivatives, the weak Euler-Lagrange equation    *)
(* and the Wirtinger bounds.                                                 *)
(* ========================================================================= *)

needs "src/pc_p2a_lbvp.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Derivatives off a finite set: integral and measurability.                *)
(* ------------------------------------------------------------------------- *)

let P2A_PW_HAS_INTEGRAL = prove
 (`!(z:real^1->real^N) z' K a b.
     a <= b /\ FINITE K /\ z continuous_on interval[lift a,lift b] /\
     (!s. a < s /\ s < b /\ ~(s IN K)
          ==> (z has_vector_derivative z'(lift s)) (at (lift s)))
     ==> (z' has_integral (z(lift b) - z(lift a))) (interval[lift a,lift b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `IMAGE lift K` THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; FINITE_IMP_COUNTABLE; LIFT_DROP] THEN
  REWRITE_TAC[FORALL_LIFT; IN_DIFF; IN_INTERVAL_1; LIFT_DROP; IN_IMAGE_LIFT_DROP] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let P2A_PW_MEASURABLE = prove
 (`!(z:real^1->real^N) z' K a b.
     a <= b /\ FINITE K /\ z continuous_on interval[lift a,lift b] /\
     (!s. a < s /\ s < b /\ ~(s IN K)
          ==> (z has_vector_derivative z'(lift s)) (at (lift s)))
     ==> z' measurable_on interval[lift a,lift b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
  REWRITE_TAC[integrable_on] THEN
  EXISTS_TAC `(z:real^1->real^N)(lift b) - z(lift a)` THEN
  MATCH_MP_TAC P2A_PW_HAS_INTEGRAL THEN EXISTS_TAC `K:real->bool` THEN
  ASM_REWRITE_TAC[]);;

let P2A_REAL_INTEGRABLE_MEASURABLE_BOUNDED = prove
 (`!f a b M.
     (\x. lift(f(drop x))) measurable_on interval[lift a,lift b] /\
     (!t. a <= t /\ t <= b ==> abs(f t) <= M)
     ==> f real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. lift M):real^1->real^1` THEN
  ASM_REWRITE_TAC[o_DEF; INTEGRABLE_CONST] THEN
  REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP; NORM_LIFT] THEN
  ASM_SIMP_TAC[]);;

let P2A_CONT_BOUNDED = prove
 (`!(f:real^1->real^N) a b.
     f continuous_on interval[lift a,lift b]
     ==> ?B. &0 <= B /\ !t. a <= t /\ t <= b ==> norm(f(lift t)) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `interval[lift a,lift b]`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The weak Euler-Lagrange equation (P2A_WEAK_EL) for variations that are   *)
(* differentiable off a finite set.                                          *)
(* ------------------------------------------------------------------------- *)

let P2A_WEAK_EL_PW = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A (eta:real^1->real^N)
    eta' s1 s2 K.
     lricci_flow U ta tb Gt /\ s1 <= s2 /\ FINITE K /\
     (!s. s1 <= s /\ s <= s2
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
              (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                (at (lift s))) /\
     eta continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (eta has_vector_derivative eta'(lift s)) (at (lift s))) /\
     eta(lift s1) = vec 0 /\ eta(lift s2) = vec 0
     ==> ((\s. inv(&2) * (A(lift s) dot
                          (mderiv (Gt(tt - s pow 2)) (y(lift s)) (eta(lift s)) ** A(lift s))) +
               &2 * s pow 2 *
               drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                       (at (y(lift s))) (eta(lift s))) +
               eta'(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))
          has_real_integral &0) (real_interval[s1,s2])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Y")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "D") STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> ((\v. (Gt:real->real^N->real^N^N)(tt - drop v pow 2) ((y:real^1->real^N) v) **
                  (A:real^1->real^N) v) has_vector_derivative
             ((lambda k. inv(&2) * (A(lift s) dot
                                    (mderiv (Gt(tt - s pow 2)) (y(lift s)) (basis k) **
                                     A(lift s))) +
                         &2 * s pow 2 *
                         drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                                 (at (y(lift s))) (basis k))):real^N))
            (at (lift s))`
  (LABEL_TAC "GA") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "Y" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P2A_EL_VECTOR THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `ta:real`; `tb:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. (eta:real^1->real^N)(lift s) dot
         ((Gt:real->real^N->real^N^N)(tt - s pow 2) ((y:real^1->real^N)(lift s)) **
          (A:real^1->real^N)(lift s))`;
    `\s. inv(&2) * ((A:real^1->real^N)(lift s) dot
                    (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2)) ((y:real^1->real^N)(lift s))
                            ((eta:real^1->real^N)(lift s)) ** A(lift s))) +
         &2 * s pow 2 *
         drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                 (at (y(lift s))) (eta(lift s))) +
         (eta':real^1->real^N)(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s))`;
    `K:real->bool`; `s1:real`; `s2:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG) THEN
  ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; DOT_LZERO; REAL_SUB_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN
    USE_THEN "GA" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  USE_THEN "Y" (MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "D" (MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "GA" (MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF; LIFT_DROP] THEN
  MP_TAC(ISPECL [`\u v:real^N. lift(u dot v)`; `eta:real^1->real^N`;
                 `\v. (Gt:real->real^N->real^N^N)(tt - drop v pow 2) ((y:real^1->real^N) v) **
                      (A:real^1->real^N) v`;
                 `(eta':real^1->real^N)(lift x)`;
                 `((lambda k. inv(&2) * ((A:real^1->real^N)(lift x) dot
                                  (mderiv ((Gt:real->real^N->real^N^N)(tt - x pow 2))
                                          ((y:real^1->real^N)(lift x)) (basis k) **
                                   A(lift x))) +
                      &2 * x pow 2 *
                      drop(frechet_derivative (\z. lift(lscalar (Gt(tt - x pow 2)) z))
                                              (at (y(lift x))) (basis k))):real^N)`;
                 `lift x`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[BILINEAR_DOT] THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - x pow 2))` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(Gt:real->real^N->real^N^N)(tt - x pow 2)`;
                 `(y:real^1->real^N)(lift x)`; `(A:real^1->real^N)(lift x)`; `x pow 2`]
                P2A_LLAG_DY_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\w:real^N. lift(inv(&2) * ((A:real^1->real^N)(lift x) dot
                       (mderiv ((Gt:real->real^N->real^N^N)(tt - x pow 2)) ((y:real^1->real^N)(lift x))
                               w ** A(lift x))) +
                      &2 * x pow 2 *
                      drop(frechet_derivative (\z. lift(lscalar (Gt(tt - x pow 2)) z))
                                              (at (y(lift x))) w))`;
                 `(eta:real^1->real^N)(lift x)`] P2A_DOT_LAMBDA_LINEAR) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM LIFT_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Wirtinger bounds (P2A_WIRTINGER) for such variations.                    *)
(* ------------------------------------------------------------------------- *)

let P2A_PW_INTEGRABLES = prove
 (`!(eta:real^1->real^N) eta' K s1 s2 M a b.
     FINITE K /\ eta continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (eta has_vector_derivative eta'(lift s)) (at (lift s))) /\
     (!s. s1 <= s /\ s <= s2 ==> norm(eta'(lift s)) <= M) /\
     s1 <= a /\ a <= b /\ b <= s2
     ==> (\t. norm(eta(lift t)) pow 2) real_integrable_on real_interval[a,b] /\
         (\t. norm(eta'(lift t)) pow 2) real_integrable_on real_interval[a,b] /\
         (\t. norm(eta'(lift t))) real_integrable_on real_interval[a,b] /\
         (\t. norm(eta(lift t)) * norm(eta'(lift t))) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `interval[lift a,lift b] SUBSET interval[lift s1,lift s2]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(eta:real^1->real^N) continuous_on interval[lift a,lift b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(eta':real^1->real^N) measurable_on interval[lift a,lift b]` ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_PW_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`eta:real^1->real^N`; `K:real->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(eta:real^1->real^N) measurable_on interval[lift a,lift b]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eta:real^1->real^N`; `a:real`; `b:real`] P2A_CONT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> norm((eta':real^1->real^N)(lift t)) <= M`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(norm((eta':real^1->real^N) x))) measurable_on interval[lift a,lift b] /\
                (\x. lift(norm((eta:real^1->real^N) x))) measurable_on interval[lift a,lift b]`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MEASURABLE_ON_NORM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC P2A_REAL_INTEGRABLE_MEASURABLE_BOUNDED THEN REWRITE_TAC[LIFT_DROP] THENL
   [EXISTS_TAC `B pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN ASM_REWRITE_TAC[ARITH_EQ];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE]];
    EXISTS_TAC `M pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIFT_POW THEN ASM_REWRITE_TAC[ARITH_EQ];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE]];
    EXISTS_TAC `M:real` THEN ASM_SIMP_TAC[REAL_ABS_NORM];
    EXISTS_TAC `B * M` THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC MEASURABLE_ON_MUL THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE]]]);;

let P2A_VNORM_FTC_BOUND_PW = prove
 (`!(eta:real^1->real^N) eta' K s1 s2 M s.
     s1 <= s /\ s <= s2 /\ FINITE K /\ eta continuous_on interval[lift s1,lift s2] /\
     (!t. s1 < t /\ t < s2 /\ ~(t IN K)
          ==> (eta has_vector_derivative eta'(lift t)) (at (lift t))) /\
     (!t. s1 <= t /\ t <= s2 ==> norm(eta'(lift t)) <= M) /\
     eta(lift s1) = vec 0
     ==> norm(eta(lift s)) <= real_integral (real_interval[s1,s]) (\t. norm(eta'(lift t)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `interval[lift s1,lift s] SUBSET interval[lift s1,lift s2]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `K:real->bool`;
                 `s1:real`; `s:real`] P2A_PW_HAS_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `K:real->bool`;
                 `s1:real`; `s2:real`; `M:real`; `s1:real`; `s:real`] P2A_PW_INTEGRABLES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; STRIP_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP] THEN
  SUBGOAL_THEN `(eta:real^1->real^N)(lift s) =
                integral (interval[lift s1,lift s]) (eta':real^1->real^N)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(\t. norm((eta':real^1->real^N)(lift t))) real_integrable_on real_interval[s1,s]` THEN
  REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP]);;

let P2A_WIRTINGER_PW = prove
 (`!(eta:real^1->real^N) eta' K s1 s2 M.
     s1 <= s2 /\ FINITE K /\ eta continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (eta has_vector_derivative eta'(lift s)) (at (lift s))) /\
     (!s. s1 <= s /\ s <= s2 ==> norm(eta'(lift s)) <= M) /\
     eta(lift s1) = vec 0
     ==> (!s. s1 <= s /\ s <= s2
              ==> norm(eta(lift s)) pow 2 <=
                  (s2 - s1) *
                  real_integral (real_interval[s1,s2]) (\t. norm(eta'(lift t)) pow 2)) /\
         real_integral (real_interval[s1,s2]) (\t. norm(eta(lift t)) pow 2) <=
         (s2 - s1) pow 2 *
         real_integral (real_interval[s1,s2]) (\t. norm(eta'(lift t)) pow 2) /\
         real_integral (real_interval[s1,s2]) (\t. norm(eta(lift t)) * norm(eta'(lift t))) <=
         (s2 - s1) * real_integral (real_interval[s1,s2]) (\t. norm(eta'(lift t)) pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. s1 <= a /\ a <= b /\ b <= s2
          ==> (\t. norm((eta:real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[a,b] /\
              (\t. norm((eta':real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[a,b] /\
              (\t. norm((eta':real^1->real^N)(lift t))) real_integrable_on real_interval[a,b] /\
              (\t. norm((eta:real^1->real^N)(lift t)) * norm((eta':real^1->real^N)(lift t)))
                real_integrable_on real_interval[a,b]`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2A_PW_INTEGRABLES THEN
    MAP_EVERY EXISTS_TAC [`K:real->bool`; `s1:real`; `s2:real`; `M:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = real_integral (real_interval[s1,s2])
                    (\t. norm((eta':real^1->real^N)(lift t)) pow 2)` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> norm((eta:real^1->real^N)(lift s)) pow 2 <= (s2 - s1) * Q`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `K:real->bool`;
                   `s1:real`; `s2:real`; `M:real`; `s:real`] P2A_VNORM_FTC_BOUND_PW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[s1,s])
                  (\t. norm((eta':real^1->real^N)(lift t))) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(s - s1) * real_integral (real_interval[s1,s])
                             (\t. norm((eta':real^1->real^N)(lift t)) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2A_REAL_CS THEN ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_REFL];
      EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LE_REFL; SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s1,s2]) (\t. norm((eta:real^1->real^N)(lift t)) pow 2) <=
    (s2 - s1) pow 2 * Q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[s1,s2]) (\t. (s2 - s1) * Q)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `s2:real = s1` THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL; REAL_SUB_REFL; REAL_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s2 - s1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[s1,s2])
                (\t. inv(&2 * (s2 - s1)) * norm((eta:real^1->real^N)(lift t)) pow 2 +
                     (s2 - s1) / &2 * norm((eta':real^1->real^N)(lift t)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_LMUL; REAL_LE_REFL] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2A_AMGM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRABLE_LMUL; REAL_LE_REFL; REAL_INTEGRAL_LMUL] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&2 * (s2 - s1)) * ((s2 - s1) pow 2 * Q) + (s2 - s1) / &2 * Q` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a + c <= b + c`) THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_ARITH `&0 < h ==> &0 <= &2 * h`];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < s2 - s1` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* Integrability of the Lagrangian of a piecewise C^1 competitor and the     *)
(* local convexity estimate (P2A_LOCAL_CONVEXITY) for such competitors.      *)
(* ========================================================================= *)

let P2A_LLAG_PW_INTEGRABLE = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (z:real^1->real^N) z' K s1 s2 M.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s1 <= s2 /\ s2 < sb /\
     FINITE K /\ z continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (z has_vector_derivative z'(lift s)) (at (lift s))) /\
     (!s. s1 <= s /\ s <= s2 ==> norm(z'(lift s)) <= M) /\
     (!s. s1 <= s /\ s <= s2 ==> z(lift s) IN U)
     ==> (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s))) real_integrable_on
         real_interval[s1,s2]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                  ((z':real^1->real^N)(lift s))) =
    (\s. inv(&2) * (z'(lift s) dot (Gt(tt - s pow 2) (z(lift s)) ** z'(lift s))) +
         p2a_llag Gt tt s (z(lift s)) ((\x:real^1. vec 0:real^N) (lift s)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2a_llag; DOT_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`] THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `(\x:real^1. vectorize((Gt:real->real^N->real^N^N)(tt - drop x pow 2)
                            ((z:real^1->real^N) x))) continuous_on interval[lift s1,lift s2]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\x:real^1. vectorize((Gt:real->real^N->real^N^N)(tt - drop x pow 2)
                              ((z:real^1->real^N) x))) =
      (\w. vectorize((\s. Gt(tt - s pow 2)) (drop(fstcart w)) (sndcart w))) o
      (\x. pastecart x (z x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval(lift sa,lift sb) PCROSS (U:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      UNDISCH_TAC `p2a_lsmooth U sa sb (\s. (Gt:real->real^N->real^N^N)(tt - s pow 2))` THEN
      SIMP_TAC[p2a_lsmooth];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; FORALL_LIFT;
                IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1. vectorize((Gt:real->real^N->real^N^N)(tt - drop x pow 2)
                                        ((z:real^1->real^N) x))`; `s1:real`; `s2:real`]
                P2A_CONT_BOUNDED) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2A_REAL_INTEGRABLE_MEASURABLE_BOUNDED THEN
  EXISTS_TAC `M * B * M` THEN REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(z':real^1->real^N) measurable_on interval[lift s1,lift s2]` ASSUME_TAC THENL
     [MATCH_MP_TAC P2A_PW_MEASURABLE THEN
      MAP_EVERY EXISTS_TAC [`z:real^1->real^N`; `K:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\u v:real^N. lift(u dot v)`; `z':real^1->real^N`;
                   `\x:real^1. (Gt:real->real^N->real^N^N)(tt - drop x pow 2)
                                  ((z:real^1->real^N) x) ** (z':real^1->real^N) x`;
                   `interval[lift s1,lift s2]`] MEASURABLE_ON_BILINEAR) THEN
    REWRITE_TAC[BILINEAR_DOT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\(m:real^(N,N)finite_prod) (x:real^N). matrify m ** x`;
                   `\x:real^1. vectorize((Gt:real->real^N->real^N^N)(tt - drop x pow 2)
                                            ((z:real^1->real^N) x))`;
                   `z':real^1->real^N`; `interval[lift s1,lift s2]`]
                  MEASURABLE_ON_BILINEAR) THEN
    REWRITE_TAC[BILINEAR_MATRIX_VECTOR_MUL; MATRIFY_VECTORIZE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((z':real^1->real^N)(lift t)) *
              norm((Gt:real->real^N->real^N^N)(tt - t pow 2) ((z:real^1->real^N)(lift t)) **
                   z'(lift t))` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(vectorize((Gt:real->real^N->real^N^N)(tt - t pow 2)
                                ((z:real^1->real^N)(lift t)))) *
              norm((z':real^1->real^N)(lift t))` THEN
  REWRITE_TAC[COMPATIBLE_NORM_VECTORIZE] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[NORM_POS_LE]);;

let P2A_LOCAL_CONVEXITY_PW = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt sa sb (y:real^1->real^N) A (z:real^1->real^N) z'
    s1 s2 C lam B0 B1 BR a0 r0 smax K M.
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s1 /\ s1 < s2 /\ s2 < sb /\ convex C /\ C SUBSET U /\
     (!s. s1 <= s /\ s <= s2
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ s pow 2 <= smax /\
              y(lift s) IN C /\ z(lift s) IN C /\
              (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                (at (lift s)) /\
              norm(A(lift s)) <= a0 /\ norm(z(lift s) - y(lift s)) <= r0) /\
     FINITE K /\ z continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (z has_vector_derivative z'(lift s)) (at (lift s))) /\
     (!s. s1 <= s /\ s <= s2 ==> norm(z'(lift s)) <= M) /\
     z(lift s1) = y(lift s1) /\ z(lift s2) = y(lift s2) /\
     &0 < lam /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\ &0 <= a0 /\ &0 <= r0 /\ &0 <= smax /\
     (!s v w u. s1 <= s /\ s <= s2 /\ v IN C /\ w IN C
                ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) w ** u) /\
                    norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                   mderiv (Gt(tt - s pow 2)) v (w - v))) <=
                    B1 * norm(w - v) pow 2 /\
                    norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                    abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                        drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                                (at v) (w - v))) <=
                    BR * norm(w - v) pow 2) /\
     lam / &4 <= lam / &2 - (B1 * r0 + B0) * a0 * (s2 - s1) -
                 inv(&2) * B1 * a0 pow 2 * (s2 - s1) pow 2 -
                 &2 * smax * BR * (s2 - s1) pow 2
     ==> (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s)))
           real_integrable_on real_interval[s1,s2] /\
         (\s. norm(z'(lift s) - A(lift s)) pow 2) real_integrable_on real_interval[s1,s2] /\
         real_integral (real_interval[s1,s2])
           (\s. p2a_llag Gt tt s (y(lift s)) (A(lift s))) +
         lam / &4 *
         real_integral (real_interval[s1,s2]) (\s. norm(z'(lift s) - A(lift s)) pow 2)
         <= real_integral (real_interval[s1,s2])
              (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^1->real^N) continuous_on interval[lift s1,lift s2] /\
                (A:real^1->real^N) continuous_on interval[lift s1,lift s2]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `eta = \x:real^1. (z:real^1->real^N) x - (y:real^1->real^N) x` THEN
  ABBREV_TAC `eta' = \x:real^1. (z':real^1->real^N) x - (A:real^1->real^N) x` THEN
  SUBGOAL_THEN
   `!s. s1 < s /\ s < s2 /\ ~(s IN K)
        ==> ((eta:real^1->real^N) has_vector_derivative eta'(lift s)) (at (lift s))`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["eta"; "eta'"] THEN REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(eta:real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> norm((eta':real^1->real^N)(lift s)) <= M + a0`
  ASSUME_TAC THENL
   [EXPAND_TAC "eta'" THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(u:real^N) <= M /\ norm(v:real^N) <= a0 ==> norm(u - v) <= M + a0`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(eta:real^1->real^N)(lift s1) = vec 0 /\ eta(lift s2) = vec 0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  (* the weak Euler-Lagrange equation *)
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`; `eta:real^1->real^N`;
                 `eta':real^1->real^N`; `s1:real`; `s2:real`; `K:real->bool`] P2A_WEAK_EL_PW) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `smax:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `E = \s. inv(&2) * ((A:real^1->real^N)(lift s) dot
                       (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                               ((y:real^1->real^N)(lift s))
                               ((eta:real^1->real^N)(lift s)) ** A(lift s))) +
            &2 * s pow 2 *
            drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                    (at (y(lift s))) (eta(lift s))) +
            (eta':real^1->real^N)(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `E real_integrable_on real_interval[s1,s2] /\
                real_integral (real_interval[s1,s2]) E = &0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[real_integrable_on; REAL_INTEGRAL_UNIQUE]; ALL_TAC] THEN
  (* integrability of the Lagrangians and of the norms *)
  SUBGOAL_THEN
   `(\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                  ((A:real^1->real^N)(lift s))) real_integrable_on real_interval[s1,s2] /\
    (\s. p2a_llag Gt tt s ((z:real^1->real^N)(lift s))
                  ((z':real^1->real^N)(lift s))) real_integrable_on real_interval[s1,s2]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC P2A_LLAG_PW_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`; `K:real->bool`;
                            `M:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `K:real->bool`;
                 `s1:real`; `s2:real`; `M + a0`] P2A_WIRTINGER_PW) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. norm((eta:real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[s1,s2] /\
    (\t. norm((eta':real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[s1,s2] /\
    (\t. norm((eta:real^1->real^N)(lift t)) * norm((eta':real^1->real^N)(lift t)))
      real_integrable_on real_interval[s1,s2]`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `K:real->bool`;
                   `s1:real`; `s2:real`; `M + a0`; `s1:real`; `s2:real`]
                  P2A_PW_INTEGRABLES) THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (B1 * r0 + B0) * a0 /\ &0 <= inv(&2) * B1 * a0 pow 2 + &2 * smax * BR /\
    lam / &4 <= lam / &2 - ((B1 * r0 + B0) * a0) * (s2 - s1) -
                (inv(&2) * B1 * a0 pow 2 + &2 * smax * BR) * (s2 - s1) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD; REAL_LE_POW_2; REAL_LE_INV_EQ; REAL_POS];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      try lhand(concl th) = `lam / &4` with Failure _ -> false)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `K1 = (B1 * r0 + B0) * a0` THEN
  ABBREV_TAC `K2 = inv(&2) * B1 * a0 pow 2 + &2 * smax * BR` THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[s1,s2]
        ==> lam / &2 * norm((eta':real^1->real^N)(lift s)) pow 2 -
            K1 * (norm((eta:real^1->real^N)(lift s)) * norm(eta'(lift s))) -
            K2 * norm(eta(lift s)) pow 2
            <= p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                        ((z':real^1->real^N)(lift s)) -
               p2a_llag Gt tt s ((y:real^1->real^N)(lift s)) ((A:real^1->real^N)(lift s)) -
               E s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MP (CONJ (ASSUME `s1 <= s`) (ASSUME `s <= s2`)) o
      SPEC `s:real` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `smax:real`)) (concl th) &&
      can (find_term ((=) `a0:real`)) (concl th))) THEN
    FIRST_ASSUM(fun th ->
      let th' = check (fun th -> is_forall (concl th) &&
                  can (find_term ((=) `B1:real`)) (concl th) &&
                  can (find_term ((=) `lam:real`)) (concl th) &&
                  not (can (find_term ((=) `K1:real`)) (concl th))) th in
      ASSUME_TAC(GEN `u:real^N`
        (MP (SPECL [`s:real`; `(y:real^1->real^N)(lift s)`; `(z:real^1->real^N)(lift s)`;
                    `u:real^N`] th')
            (CONJ (ASSUME `s1 <= s`) (CONJ (ASSUME `s <= s2`)
              (CONJ (ASSUME `(y:real^1->real^N)(lift s) IN C`)
                    (ASSUME `(z:real^1->real^N)(lift s) IN C`))))))) THEN
    SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N)(tt - s pow 2))` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^1->real^N)(lift s) IN U /\ (y:real^1->real^N)(lift s) IN U`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(eta:real^1->real^N)(lift s) = z(lift s) - y(lift s) /\
                  (eta':real^1->real^N)(lift s) = z'(lift s) - A(lift s)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["eta"; "eta'"] THEN REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `E s = inv(&2) * ((A:real^1->real^N)(lift s) dot
                       (mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2))
                               ((y:real^1->real^N)(lift s))
                               ((eta:real^1->real^N)(lift s)) ** A(lift s))) +
            &2 * s pow 2 *
            drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                    (at (y(lift s))) (eta(lift s))) +
            (eta':real^1->real^N)(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s))`
    SUBST1_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^1->real^N)(lift s) = y(lift s) + eta(lift s) /\
                  (z':real^1->real^N)(lift s) = A(lift s) + eta'(lift s)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ASSUME `(eta:real^1->real^N)(lift s) = z(lift s) - y(lift s)`;
                  ASSUME `(eta':real^1->real^N)(lift s) = z'(lift s) - A(lift s)`] THEN
      CONV_TAC VECTOR_ARITH;
      ALL_TAC] THEN
    POP_ASSUM(fun th ->
      RULE_ASSUM_TAC(REWRITE_RULE[th; VECTOR_ARITH `!y e:real^N. (y + e) - y = e`]) THEN
      REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && fst(dest_var(fst(dest_forall(concl th)))) = "u"
      then MP_TAC(CONJ (SPEC `(eta':real^1->real^N)(lift s)` th)
                       (SPEC `(eta:real^1->real^N)(lift s)` th))
      else failwith "no u") THEN
    STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["K1"; "K2"] THEN
    MATCH_MP_TAC P2A_CONVEX_POINTWISE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\s. norm((z':real^1->real^N)(lift s) - A(lift s)) pow 2) =
                (\t. norm((eta':real^1->real^N)(lift t)) pow 2)` SUBST1_TAC THENL
   [EXPAND_TAC "eta'" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
  MP_TAC(ISPECL
   [`\s. lam / &2 * norm((eta':real^1->real^N)(lift s)) pow 2 -
         K1 * (norm((eta:real^1->real^N)(lift s)) * norm(eta'(lift s))) -
         K2 * norm(eta(lift s)) pow 2`;
    `\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                  ((z':real^1->real^N)(lift s)) -
         p2a_llag Gt tt s ((y:real^1->real^N)(lift s)) ((A:real^1->real^N)(lift s)) - E s`;
    `real_interval[s1,s2]`;
    `lam / &2 * real_integral (real_interval[s1,s2])
                  (\t. norm((eta':real^1->real^N)(lift t)) pow 2) -
     K1 * real_integral (real_interval[s1,s2])
            (\t. norm((eta:real^1->real^N)(lift t)) * norm((eta':real^1->real^N)(lift t))) -
     K2 * real_integral (real_interval[s1,s2]) (\t. norm((eta:real^1->real^N)(lift t)) pow 2)`;
    `real_integral (real_interval[s1,s2])
       (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                     ((z':real^1->real^N)(lift s))) -
     real_integral (real_interval[s1,s2])
       (\s. p2a_llag Gt tt s ((y:real^1->real^N)(lift s)) ((A:real^1->real^N)(lift s))) -
     &0`] HAS_REAL_INTEGRAL_LE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN CONJ_TAC) THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN MATCH_MP_TAC REAL_INTEGRABLE_INTEGRAL THEN
      ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN CONJ_TAC) THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL];
      FIRST_ASSUM ACCEPT_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= real_integral (real_interval[s1,s2])
                        (\t. norm((eta':real^1->real^N)(lift t)) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `Q = real_integral (real_interval[s1,s2])
                    (\t. norm((eta':real^1->real^N)(lift t)) pow 2)` THEN
  ABBREV_TAC `W = real_integral (real_interval[s1,s2])
                    (\t. norm((eta:real^1->real^N)(lift t)) pow 2)` THEN
  ABBREV_TAC `P = real_integral (real_interval[s1,s2])
                    (\t. norm((eta:real^1->real^N)(lift t)) * norm((eta':real^1->real^N)(lift t)))` THEN
  ABBREV_TAC `Lz = real_integral (real_interval[s1,s2])
                     (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((z:real^1->real^N)(lift s))
                                   ((z':real^1->real^N)(lift s)))` THEN
  ABBREV_TAC `Ly = real_integral (real_interval[s1,s2])
                     (\s. p2a_llag (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                                   ((A:real^1->real^N)(lift s)))` THEN
  SUBGOAL_THEN `K1 * P <= K1 * ((s2 - s1) * Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `K2 * W <= K2 * ((s2 - s1) pow 2 * Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lam / &4 * Q <= (lam / &2 - K1 * (s2 - s1) - K2 * (s2 - s1) pow 2) * Q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lam / &2 * Q - K1 * P - K2 * W <= Lz - Ly - &0` THEN
  REPLICATE_TAC 3 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The energy ball (P2A_ENERGY_BALL) and the local minimality and uniqueness *)
(* (P2A_LOCAL_MIN) for piecewise C^1 competitors.                            *)
(* ========================================================================= *)

let P2A_ENERGY_BALL_PW = prove
 (`!(z:real^1->real^N) z' K s1 s2 E r M.
     s1 <= s2 /\ FINITE K /\ z continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> (z has_vector_derivative z'(lift s)) (at (lift s))) /\
     (!s. s1 <= s /\ s <= s2 ==> norm(z'(lift s)) <= M) /\
     real_integral (real_interval[s1,s2]) (\s. norm(z'(lift s)) pow 2) <= E /\
     (s2 - s1) * E <= r pow 2 /\ &0 <= r
     ==> !s. s1 <= s /\ s <= s2 ==> norm(z(lift s) - z(lift s1)) <= r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. (z:real^1->real^N) x - z(lift s1)`; `z':real^1->real^N`;
                 `K:real->bool`; `s1:real`; `s2:real`; `M:real`] P2A_WIRTINGER_PW) THEN
  REWRITE_TAC[VECTOR_SUB_REFL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [VECTOR_ARITH `v:real^N = v - vec 0`] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(s2 - s1) * real_integral (real_interval[s1,s2]) (\s. norm((z':real^1->real^N)(lift s)) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s2 - s1) * E` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let P2A_LOCAL_MIN_PW = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt sa sb (y:real^1->real^N) A (sig:real^1->real^N)
    s1 s2 C lam B0 B1 BR a0 r0 smax K M.
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s1 /\ s1 < s2 /\ s2 < sb /\ convex C /\ C SUBSET U /\
     (!s. s1 <= s /\ s <= s2
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ s pow 2 <= smax /\
              y(lift s) IN C /\ sig(lift s) IN C /\
              (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                (at (lift s)) /\
              norm(A(lift s)) <= a0 /\ norm(sig(lift s) - y(lift s)) <= r0) /\
     FINITE K /\ sig continuous_on interval[lift s1,lift s2] /\
     (!s. s1 < s /\ s < s2 /\ ~(s IN K)
          ==> sig differentiable (at (lift s)) /\
              norm(vector_derivative sig (at (lift s))) <= M) /\
     sig(lift s1) = y(lift s1) /\ sig(lift s2) = y(lift s2) /\
     &0 < lam /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\ &0 <= a0 /\ &0 <= r0 /\ &0 <= smax /\
     (!s v w u. s1 <= s /\ s <= s2 /\ v IN C /\ w IN C
                ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) w ** u) /\
                    norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                   mderiv (Gt(tt - s pow 2)) v (w - v))) <=
                    B1 * norm(w - v) pow 2 /\
                    norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                    abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                        drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                                (at v) (w - v))) <=
                    BR * norm(w - v) pow 2) /\
     lam / &4 <= lam / &2 - (B1 * r0 + B0) * a0 * (s2 - s1) -
                 inv(&2) * B1 * a0 pow 2 * (s2 - s1) pow 2 -
                 &2 * smax * BR * (s2 - s1) pow 2
     ==> p2a_cL Gt tt y s1 s2 <= p2a_cL Gt tt sig s1 s2 /\
         (p2a_cL Gt tt y s1 s2 = p2a_cL Gt tt sig s1 s2
          ==> !s. s1 <= s /\ s <= s2 ==> sig(lift s) = y(lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z' = \x:real^1. if s1 < drop x /\ drop x < s2 /\ ~(drop x IN K)
                              then vector_derivative (sig:real^1->real^N) (at x) else vec 0` THEN
  SUBGOAL_THEN
   `(!s. s1 < s /\ s < s2 /\ ~(s IN K)
         ==> ((sig:real^1->real^N) has_vector_derivative z'(lift s)) (at (lift s)) /\
             z'(lift s) = vector_derivative sig (at (lift s))) /\
    (!s. s1 <= s /\ s <= s2 ==> norm((z':real^1->real^N)(lift s)) <= abs M)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS];
      COND_CASES_TAC THEN REWRITE_TAC[NORM_0; REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= abs m`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `sa:real`; `sb:real`; `y:real^1->real^N`; `A:real^1->real^N`;
                 `sig:real^1->real^N`; `z':real^1->real^N`; `s1:real`; `s2:real`;
                 `C:real^N->bool`; `lam:real`; `B0:real`; `B1:real`; `BR:real`; `a0:real`;
                 `r0:real`; `smax:real`; `K:real->bool`; `abs M`] P2A_LOCAL_CONVEXITY_PW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `p2a_cL (Gt:real->real^N->real^N^N) tt y s1 s2 =
    real_integral (real_interval[s1,s2]) (\s. p2a_llag Gt tt s (y(lift s)) (A(lift s))) /\
    p2a_cL Gt tt sig s1 s2 =
    real_integral (real_interval[s1,s2]) (\s. p2a_llag Gt tt s (sig(lift s)) (z'(lift s)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[p2a_cL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `(s1:real) INSERT s2 INSERT K` THEN
      ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT] THEN
      REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; DE_MORGAN_THM] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `vector_derivative (sig:real^1->real^N)`)) (concl th) &&
        can (find_term ((=) `z':real^1->real^N`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ABBREV_TAC `Q = real_integral (real_interval[s1,s2])
                    (\s. norm((z':real^1->real^N)(lift s) - (A:real^1->real^N)(lift s)) pow 2)` THEN
  SUBGOAL_THEN `(y:real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`lam / &4`; `Q:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `Q <= &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Q:real`; `&0`; `lam / &4`] REAL_LE_LMUL_EQ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^1. (sig:real^1->real^N) x - y x`;
                 `\x:real^1. (z':real^1->real^N) x - A x`; `K:real->bool`;
                 `s1:real`; `s2:real`; `abs M + a0`] P2A_WIRTINGER_PW) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; VECTOR_SUB_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(u:real^N) <= M /\ norm(v:real^N) <= a0 ==> norm(u - v) <= M + a0`) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s2 - s1:real`; `--Q:real`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_RNEG]] THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm((sig:real^1->real^N)(lift s) - y(lift s)) pow 2 = &0` MP_TAC THENL
   [MP_TAC(ISPEC `norm((sig:real^1->real^N)(lift s) - y(lift s))` REAL_LE_POW_2) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ; ARITH]]);;


(* ========================================================================= *)
(* The data of the local boundary value problem (P2A_BVP_DATUM) with         *)
(* minimality and uniqueness against piecewise C^1 competitors.              *)
(* ========================================================================= *)

let P2A_BVP_DATUM_PW = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt Kc E sa sb sa' sb' r lam B0 B1 BR c d1
    s1 s2 (y1:real^N) y2 V (y:real^1->real^N).
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa' sb' (\s. Gt(tt - s pow 2)) /\
     (!s. sa' < s /\ s < sb' ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb) /\
     sa' < sa /\ sb < sb' /\ &0 <= sa /\ &0 < r /\ &0 < E /\
     (!y. y IN Kc ==> cball(y,&2 * r) SUBSET U) /\
     &0 < lam /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\
     (!s v w u. sa <= s /\ s <= sb /\
                segment[v,w] SUBSET {x + v | x IN Kc /\ v IN cball(vec 0,r)}
                ==> lam * norm u pow 2 <= u dot (Gt(tt - s pow 2) w ** u) /\
                    norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                   mderiv (Gt(tt - s pow 2)) v (w - v)))
                    <= B1 * norm(w - v) pow 2 /\
                    norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                    abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                        drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                                (at v) (w - v)))
                    <= BR * norm(w - v) pow 2) /\
     &0 < c /\ c <= &1 /\ (B1 * &2 * r + B0 + B1) * c <= lam / &12 /\
     &0 < d1 /\ d1 <= &1 /\ (&2 * sb pow 2 * BR) * d1 <= lam / &12 /\
     sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= d1 /\ (s2 - s1) * E <= r pow 2 /\
     y1 IN Kc /\
     (!sig. &0 <= sig /\ sig <= &1
            ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                              (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))) /\
                norm(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift sig)
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))) -
                     pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) < min r c) /\
     fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift(&1))
                       (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1)))))) = y2 /\
     (\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                 (lift((drop v - s1) / (s2 - s1)))
                 (pastecart (pastecart y1 V) (pastecart (lift s1) (lift(s2 - s1))))))) = y
     ==> y(lift s1) = y1 /\ y(lift s2) = y2 /\
         (!s. s1 <= s /\ s <= s2 ==> y(lift s) IN U) /\
         (!s. s1 <= s /\ s <= s2
              ==> (y has_vector_derivative vector_derivative y (at (lift s))) (at (lift s)) /\
                  ((\v. vector_derivative y (at v)) has_vector_derivative
                   p2a_lacc Gt tt s (y(lift s)) (vector_derivative y (at (lift s))))
                  (at (lift s))) /\
         !sig' K M. sig'(lift s1) = y1 /\ sig'(lift s2) = y2 /\
                (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                FINITE K /\ sig' continuous_on interval[lift s1,lift s2] /\
                (!s. s1 < s /\ s < s2 /\ ~(s IN K)
                     ==> sig' differentiable (at (lift s)) /\
                         norm(vector_derivative sig' (at (lift s))) <= M) /\
                p2a_cE Gt tt sig' s1 s2 <= E
                ==> p2a_cL Gt tt y s1 s2 <= p2a_cL Gt tt sig' s1 s2 /\
                    (p2a_cL Gt tt y s1 s2 = p2a_cL Gt tt sig' s1 s2
                     ==> !s. s1 <= s /\ s <= s2 ==> sig'(lift s) = y(lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y1:real^N) IN U` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `y1:real^N` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `cball:real^N#real->real^N->bool`)) (concl th) &&
      not (can (find_term ((=) `lam:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `y1:real^N`; `V:real^N`; `s1:real`; `s2:real`; `y2:real^N`; `min r c`;
                 `y:real^1->real^N`;
                 `\v. inv(s2 - s1) %
                      sndcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                        (p2a_rdom U sa' sb') (lift((drop v - s1) / (s2 - s1)))
                        (pastecart (pastecart (y1:real^N) V) (pastecart (lift s1) (lift(s2 - s1))))))`]
                P2A_SOL_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = \v. inv(s2 - s1) %
                      sndcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                        (p2a_rdom U sa' sb') (lift((drop v - s1) / (s2 - s1)))
                        (pastecart (pastecart (y1:real^N) V) (pastecart (lift s1) (lift(s2 - s1))))))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sf"))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cball(y1:real^N,r) SUBSET U /\
                cball(y1,r) SUBSET {x + v | x IN Kc /\ v IN cball(vec 0,r)}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^N,&2 * r)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_CBALL; IN_CBALL_0] THEN X_GEN_TAC `z:real^N` THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`y1:real^N`; `z - y1:real^N`] THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `y + (z - y):real^N = z`] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (y:real^1->real^N)(lift s) IN cball(y1,r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "sf" (MP_TAC o C MP (CONJ (ASSUME `s1 <= s`) (ASSUME `s <= s2`)) o SPEC `s:real`) THEN
    STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    REWRITE_TAC[dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "sf" (MP_TAC o C MP (CONJ (ASSUME `s1 <= s`) (ASSUME `s <= s2`)) o SPEC `s:real`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`sig:real^1->real^N`; `K:real->bool`; `M:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `z' = \x:real^1. if s1 < drop x /\ drop x < s2 /\ ~(drop x IN K)
                              then vector_derivative (sig:real^1->real^N) (at x) else vec 0` THEN
  SUBGOAL_THEN
   `(!s. s1 < s /\ s < s2 /\ ~(s IN K)
         ==> ((sig:real^1->real^N) has_vector_derivative z'(lift s)) (at (lift s)) /\
             z'(lift s) = vector_derivative sig (at (lift s))) /\
    (!s. s1 <= s /\ s <= s2 ==> norm((z':real^1->real^N)(lift s)) <= abs M)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS];
      COND_CASES_TAC THEN REWRITE_TAC[NORM_0; REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= abs m`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (real_interval[s1,s2]) (\s. norm((z':real^1->real^N)(lift s)) pow 2)
                <= E` ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_cE (Gt:real->real^N->real^N^N) tt sig s1 s2 <= E` THEN
    REWRITE_TAC[p2a_cE] THEN MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= e ==> a <= e`) THEN
    MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `(s1:real) INSERT s2 INSERT K` THEN
    ASM_SIMP_TAC[REAL_NEGLIGIBLE_FINITE; FINITE_INSERT] THEN
    REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; DE_MORGAN_THM] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[NORM_POW_2] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `vector_derivative (sig:real^1->real^N)`)) (concl th) &&
      can (find_term ((=) `z':real^1->real^N`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s1 <= s /\ s <= s2 ==> (sig:real^1->real^N)(lift s) IN cball(y1,r)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sig:real^1->real^N`; `z':real^1->real^N`; `K:real->bool`;
                   `s1:real`; `s2:real`; `E:real`; `r:real`; `abs M`] P2A_ENERGY_BALL_PW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_CBALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `sa':real`; `sb':real`; `y:real^1->real^N`; `A:real^1->real^N`;
                 `sig:real^1->real^N`; `s1:real`; `s2:real`; `cball(y1:real^N,r)`;
                 `lam:real`; `B0:real`; `B1:real`; `BR:real`; `min r c / (s2 - s1)`;
                 `&2 * r`; `sb pow 2`; `K:real->bool`; `M:real`] P2A_LOCAL_MIN_PW) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `sa' < s1 /\ s2 < sb' /\ &0 < s2 - s1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= min r c / (s2 - s1) /\ &0 <= &2 * r /\ &0 <= sb pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s1 <= s /\ s <= s2
        ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ s pow 2 <= sb pow 2 /\
            (y:real^1->real^N)(lift s) IN cball(y1,r) /\
            (sig:real^1->real^N)(lift s) IN cball(y1,r) /\
            (y has_vector_derivative (A:real^1->real^N)(lift s)) (at (lift s)) /\
            (A has_vector_derivative p2a_lacc (Gt:real->real^N->real^N^N) tt s (y(lift s)) (A(lift s)))
              (at (lift s)) /\
            norm(A(lift s)) <= min r c / (s2 - s1) /\
            norm(sig(lift s) - y(lift s)) <= &2 * r`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "sf" (MP_TAC o C MP (CONJ (ASSUME `s1 <= s`) (ASSUME `s <= s2`)) o SPEC `s:real`) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `ta:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `ta:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(y:real^1->real^N)(lift s) IN cball(y1,r) /\
                    (sig:real^1->real^N)(lift s) IN cball(y1,r)` MP_TAC THENL
       [ASM_SIMP_TAC[]; REWRITE_TAC[IN_CBALL] THEN CONV_TAC NORM_ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s v w u. s1 <= s /\ s <= s2 /\ v IN cball(y1:real^N,r) /\ w IN cball(y1,r)
              ==> lam * norm u pow 2 <= u dot ((Gt:real->real^N->real^N^N)(tt - s pow 2) w ** u) /\
                  norm(vectorize(Gt(tt - s pow 2) w - Gt(tt - s pow 2) v -
                                 mderiv (Gt(tt - s pow 2)) v (w - v))) <=
                  B1 * norm(w - v) pow 2 /\
                  norm(vectorize(mderiv (Gt(tt - s pow 2)) v u)) <= B0 * norm u /\
                  abs(lscalar (Gt(tt - s pow 2)) w - lscalar (Gt(tt - s pow 2)) v -
                      drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x))
                                              (at v) (w - v))) <=
                  BR * norm(w - v) pow 2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `lam:real`)) (concl th) &&
      can (find_term ((=) `Kc:real^N->bool`)) (concl th))) THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(y1:real^N,r)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `cball(y1:real^N,r)` CONVEX_CONTAINS_SEGMENT) THEN
    REWRITE_TAC[CONVEX_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lam:real`; `B0:real`; `B1:real`; `BR:real`; `r:real`; `c:real`; `min r c`;
                 `s2 - s1`; `sb pow 2`] P2A_CONVEX_COND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * sb pow 2 * BR) * d1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[CONVEX_CBALL]);;

(* ========================================================================= *)
(* The local boundary value problem for L-geodesics with minimality and      *)
(* uniqueness against piecewise C^1 competitors (P2A_LOC_BVP_GEN with the    *)
(* competitor class widened).                                                *)
(* ========================================================================= *)

let P2A_LOC_BVP_PW = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt Kc E sa sb.
       p2a_lsmooth U ta tb Gt /\ lricci_flow U ta tb Gt /\
       compact Kc /\ Kc SUBSET U /\ &0 <= sa /\ sa < sb /\
       ta < tt - sb pow 2 /\ tt - sa pow 2 < tb /\ &0 < E
       ==> ?delta rho (sol:real->real->real^N->real^N->real^1->real^N).
             &0 < delta /\ &0 < rho /\
             (!s1 s2 y1 y2.
                sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
                y1 IN Kc /\ norm(y2 - y1) <= rho
                ==> sol s1 s2 y1 y2 (lift s1) = y1 /\ sol s1 s2 y1 y2 (lift s2) = y2 /\
                    (!s. s1 <= s /\ s <= s2 ==> sol s1 s2 y1 y2 (lift s) IN U) /\
                    (!s. s1 <= s /\ s <= s2
                         ==> (sol s1 s2 y1 y2 has_vector_derivative
                              vector_derivative (sol s1 s2 y1 y2) (at (lift s)))
                             (at (lift s)) /\
                             ((\v. vector_derivative (sol s1 s2 y1 y2) (at v))
                              has_vector_derivative
                              p2a_lacc Gt tt s (sol s1 s2 y1 y2 (lift s))
                                       (vector_derivative (sol s1 s2 y1 y2) (at (lift s))))
                             (at (lift s))) /\
                    !sig' K M.
                           sig'(lift s1) = y1 /\ sig'(lift s2) = y2 /\
                           (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                           FINITE K /\ sig' continuous_on interval[lift s1,lift s2] /\
                           (!s. s1 < s /\ s < s2 /\ ~(s IN K)
                                ==> sig' differentiable (at (lift s)) /\
                                    norm(vector_derivative sig' (at (lift s))) <= M) /\
                           p2a_cE Gt tt sig' s1 s2 <= E
                           ==> p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 <= p2a_cL Gt tt sig' s1 s2 /\
                               (p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 = p2a_cL Gt tt sig' s1 s2
                                ==> !s. s1 <= s /\ s <= s2
                                        ==> sig'(lift s) = sol s1 s2 y1 y2 (lift s))) /\
             (!s1 s2 y1 y2 s1n s2n y1n y2n.
                sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
                y1 IN Kc /\ norm(y2 - y1) <= rho /\
                (!n:num. sa <= s1n n /\ s1n n < s2n n /\ s2n n <= sb /\
                         s2n n - s1n n <= delta /\ y1n n IN Kc /\
                         norm(y2n n - y1n n) <= rho) /\
                ((\n. lift(s1n n)) --> lift s1) sequentially /\
                ((\n. lift(s2n n)) --> lift s2) sequentially /\
                (y1n --> y1) sequentially /\ (y2n --> y2) sequentially
                ==> ((\n. lift(p2a_cL Gt tt (sol (s1n n) (s2n n) (y1n n) (y2n n))
                                     (s1n n) (s2n n)))
                     --> lift(p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2)) sequentially)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ta:real`; `tb:real`; `tt:real`; `sa:real`; `sb:real`] P2A_SWINDOW) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sa':real` (X_CHOOSE_THEN `sb':real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `p2a_lsmooth U sa' sb' (\s. (Gt:real->real^N->real^N^N)(tt - s pow 2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_LSMOOTH_SFAMILY THEN MAP_EVERY EXISTS_TAC [`ta:real`; `tb:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP P2A_LSMOOTH_BASIC o check (fun th ->
      can (find_term ((=) `ta:real`)) (concl th) &&
      (try fst(dest_const(fst(strip_comb(concl th)))) = "p2a_lsmooth" with Failure _ -> false))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Kc:real^N->bool`] P2A_MARGIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = r1 / &2` THEN
  SUBGOAL_THEN `&0 < r /\ !y:real^N. y IN Kc ==> cball(y,&2 * r) SUBSET U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_HALF; REAL_ARITH `&2 * r1 / &2 = r1`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Kc:real^N->bool`; `r:real`] P2A_KPRIME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `{x + v | x IN (Kc:real^N->bool) /\ v IN cball(vec 0:real^N,r)}`;
                 `sa:real`; `sb:real`] P2A_UNIFORM_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `B0:real` (X_CHOOSE_THEN `B1:real`
    (X_CHOOSE_THEN `BR:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`B1 * &2 * r + B0 + B1`; `lam / &12`] P2A_SMALL_POS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`&2 * sb pow 2 * BR`; `lam / &12`] P2A_SMALL_POS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2];
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `Kc:real^N->bool`; `sa:real`; `sb:real`; `min r c`] P2A_RSHOOT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dV:real` (X_CHOOSE_THEN `dh:real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `Vs:real^N->real^N->real->real->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "small")
        (CONJUNCTS_THEN2 (LABEL_TAC "exu") (LABEL_TAC "cont")))))))))) THEN
  SUBGOAL_THEN `&0 < r pow 2 / E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`min dh (min d1 (r pow 2 / E))`; `rho:real`;
    `\s1 s2 (y1:real^N) y2 v.
       fstcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa' sb')
         (lift((drop v - s1) / (s2 - s1)))
         (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                    (pastecart (lift s1) (lift(s2 - s1))))))`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s1 s2 y1 (y2:real^N).
      sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= min dh (min d1 (r pow 2 / E)) /\
      y1 IN Kc /\ norm(y2 - y1) <= rho
      ==> y1 IN U /\ sa' < s1 /\ s1 < sb' /\ s2 < sb' /\ ~(s2 - s1 = &0) /\
          norm((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)) <= dV /\
          fstcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt) (p2a_rdom U sa' sb')
            (lift(&1)) (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                  (pastecart (lift s1) (lift(s2 - s1)))))) = y2 /\
          (!sig. &0 <= sig /\ sig <= &1
                 ==> lift sig IN ode_vf_maxint (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                       (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                  (pastecart (lift s1) (lift(s2 - s1)))) /\
                     norm(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift sig)
                            (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                       (pastecart (lift s1) (lift(s2 - s1)))) -
                          pastecart (pastecart y1 (vec 0)) (pastecart (lift s1) (vec 0))) < min r c)`
  (LABEL_TAC "adm") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "exu" (MP_TAC o SPECL [`y1:real^N`; `y2:real^N`; `s1:real`; `s2 - s1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `y1:real^N` o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `&2 * r`)) (concl th))) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `sig:real` THEN STRIP_TAC THEN USE_THEN "small" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`] THEN STRIP_TAC THEN
    USE_THEN "adm" (MP_TAC o SPECL [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                   `Kc:real^N->bool`; `E:real`; `sa:real`; `sb:real`; `sa':real`; `sb':real`;
                   `r:real`; `lam:real`; `B0:real`; `B1:real`; `BR:real`; `c:real`; `d1:real`;
                   `s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`;
                   `(Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)`;
                   `\v. fstcart(fstcart(ode_vf_flow (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                          (p2a_rdom U sa' sb') (lift((drop v - s1) / (s2 - s1)))
                          (pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                     (pastecart (lift s1) (lift(s2 - s1))))))`]
                  P2A_BVP_DATUM_PW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s1 s2 y1 (y2:real^N).
      sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= min dh (min d1 (r pow 2 / E)) /\
      y1 IN Kc /\ norm(y2 - y1) <= rho
      ==> p2a_cL (Gt:real->real^N->real^N^N) tt
            (\v. fstcart(fstcart(ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb')
                   (lift((drop v - s1) / (s2 - s1)))
                   (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                              (pastecart (lift s1) (lift(s2 - s1))))))) s1 s2 =
          real_integral (real_interval[&0,&1])
            (\sig. p2a_rlag Gt tt (ode_vf_flow (p2a_rfield Gt tt) (p2a_rdom U sa' sb') (lift sig)
                     (pastecart (pastecart y1 ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                                (pastecart (lift s1) (lift(s2 - s1))))))`
  (LABEL_TAC "sigma") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "adm" (MP_TAC o SPECL [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC P2A_CL_SIGMA THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`; `s1n:num->real`;
                       `s2n:num->real`; `y1n:num->real^N`; `y2n:num->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                       (pastecart (lift s1) (lift(s2 - s1))) INSERT
        IMAGE (\n. pastecart (pastecart ((y1n:num->real^N) n)
                     ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n)
                         ((s2n:num->real) n - s1n n)))
                     (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))) (:num)
        ==> z IN p2a_rdom U sa' sb' /\ ~(drop(sndcart(sndcart z)) = &0) /\
            lift(&1) IN ode_vf_maxint (p2a_rfield (Gt:real->real^N->real^N^N) tt)
                          (p2a_rdom U sa' sb') z`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `z:real^((N,N)finite_sum,(1,1)finite_sum)finite_sum` THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THENL
     [USE_THEN "adm" (MP_TAC o SPECL [`s1:real`; `s2:real`; `y1:real^N`; `y2:real^N`]);
      USE_THEN "adm" (MP_TAC o SPECL [`(s1n:num->real) n`; `(s2n:num->real) n`;
                                      `(y1n:num->real^N) n`; `(y2n:num->real^N) n`])] THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[P2A_RDOM_PASTE; SNDCART_PASTECART; LIFT_DROP] THEN
    DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `&1` (last(CONJUNCTS th)))) THEN
    REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `sa':real`; `sb':real`; `Gt:real->real^N->real^N^N`; `tt:real`;
                 `pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1)))
                            (pastecart (lift s1) (lift(s2 - s1))) INSERT
                  IMAGE (\n. pastecart (pastecart ((y1n:num->real^N) n)
                               ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n)
                                   ((s2n:num->real) n - s1n n)))
                               (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))) (:num)`]
                P2A_CLSIG_CONTINUOUS) THEN
  SUBGOAL_THEN
   `((\n. pastecart (pastecart ((y1n:num->real^N) n)
            ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n) ((s2n:num->real) n - s1n n)))
            (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))) -->
     pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1))) (pastecart (lift s1) (lift(s2 - s1))))
    sequentially`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((\n. lift((s2n:num->real) n - s1n n)) --> lift(s2 - s1)) sequentially`
    ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC LIM_PASTECART THEN CONJ_TAC) THEN ASM_REWRITE_TAC[ETA_AX] THEN
    USE_THEN "cont" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `s1n:num->real`)) (concl th) &&
      can (find_term ((=) `rho:real`)) (concl th))) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_SEQUENCE_WITH_LIMIT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\n. pastecart (pastecart ((y1n:num->real^N) n)
            ((Vs:real^N->real^N->real->real->real^N) (y1n n) ((y2n:num->real^N) n) ((s1n:num->real) n) ((s2n:num->real) n - s1n n)))
            (pastecart (lift(s1n n)) (lift(s2n n - s1n n)))`;
    `pastecart (pastecart (y1:real^N) ((Vs:real^N->real^N->real->real->real^N) y1 y2 s1 (s2 - s1))) (pastecart (lift s1) (lift(s2 - s1)))`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC(MESON[] `!(f:num->real^1) g l m.
     f = g /\ l = m ==> (f --> l) sequentially ==> (g --> m) sequentially`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "sigma" MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `s1n:num->real`)) (concl th) &&
      can (find_term ((=) `rho:real`)) (concl th))) THEN
    SIMP_TAC[];
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN USE_THEN "sigma" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

