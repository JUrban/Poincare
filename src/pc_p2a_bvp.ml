(* ========================================================================= *)
(* pc_p2a_bvp: the local boundary value problem for L-geodesics with         *)
(* convexity of the L-functional (L11 P2A_LOC_BVP), and the view-level       *)
(* consequences (L2, L3, L4, L7, L12).  Generic in N.                        *)
(* The first part: the Euler-Lagrange identity along solutions of (6.5) for  *)
(* local Ricci flows (P2A_EL_IDENTITY, P2A_EL_VECTOR; this is where          *)
(* dG/dt = -2 Ric enters), its weak form (P2A_WEAK_EL) and the               *)
(* second-order expansion of the L-Lagrangian (P2A_LLAG_EXPAND).             *)
(* ========================================================================= *)

needs "src/pc_p2a_lgeo3.ml";;
needs "src/pc_mfd_tube.ml";;

prioritize_real();;
type_invention_error := true;;

let P2A_TIME_SQ_VDERIV = prove
 (`!tt s. ((\v:real^1. lift(tt - drop v pow 2)) has_vector_derivative lift(--(&2 * s)))
          (at (lift s))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\v:real^1. lift(tt - drop v pow 2)) = lift o (\r. tt - r pow 2) o drop`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let P2A_METRIC_CURVE_VDERIV = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A0 s.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A0) (at (lift s))
     ==> ((\v. (vectorize:real^N^N->real^(N,N)finite_prod) (Gt(tt - drop v pow 2) (y v)))
          has_vector_derivative
          vectorize((&4 * s) %%
                    ((lambda i j. lricci (Gt(tt - s pow 2)) (y(lift s)) (basis i) (basis j))
                     :real^N^N) +
                    mderiv (Gt(tt - s pow 2)) (y(lift s)) A0)) (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  ABBREV_TAC `H = \z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((Gt:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(H:real^(1,N)finite_sum->real^(N,N)finite_prod) differentiable
                at (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\v. (vectorize:real^N^N->real^(N,N)finite_prod) ((Gt:real->real^N->real^N^N)
            (tt - drop v pow 2) ((y:real^1->real^N) v))) =
    H o (\v. pastecart (lift(tt - drop v pow 2)) (y v))`
  SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART;
                                     SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\v. pastecart (lift(tt - drop v pow 2)) ((y:real^1->real^N) v)) has_vector_derivative
     pastecart (lift(--(&2 * s))) A0) (at (lift s))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[P2A_HVD_PASTECART_EQ; P2A_TIME_SQ_VDERIV]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\v. pastecart (lift(tt - drop v pow 2)) ((y:real^1->real^N) v)`;
                 `H:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                 `pastecart (lift(--(&2 * s))) (A0:real^N)`;
                 `frechet_derivative (H:real^(1,N)finite_sum->real^(N,N)finite_prod)
                    (at (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s))))`;
                 `lift s`; `(:real^1)`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
  ASM_REWRITE_TAC[WITHIN_UNIV; LIFT_DROP; GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (H:real^(1,N)finite_sum->real^(N,N)finite_prod)
                  (at (pastecart (lift(tt - s pow 2)) ((y:real^1->real^N)(lift s)))))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `pastecart (lift(--(&2 * s))) (A0:real^N) =
                --(&2 * s) % pastecart (lift(&1)) (vec 0) + pastecart (vec 0) A0`
  SUBST1_TAC THENL
   [REWRITE_TAC[PASTECART_EQ; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REWRITE_TAC[GSYM LIFT_CMUL; REAL_MUL_RID; VECTOR_ADD_RID; VECTOR_MUL_RZERO;
                VECTOR_ADD_LID];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
  EXPAND_TAC "H" THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt - s pow 2`; `(y:real^1->real^N)(lift s)`] LRG_FLOW_DT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `lift(tt - s pow 2)`;
                 `(y:real^1->real^N)(lift s)`; `A0:real^N`] LRG_FLOW_MDERIV_JOINT) THEN
  ANTS_TAC THENL [EXPAND_TAC "H" THEN ASM_REWRITE_TAC[] THEN
                  FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTORIZE_ADD; VECTORIZE_CMUL; VECTORIZE_MATRIFY] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VECTORIZE_CMUL] THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT] THEN REAL_ARITH_TAC);;

let P2A_DOT_LAMBDA_LINEAR = prove
 (`!(L:real^N->real^1) w.
     linear L ==> w dot ((lambda k. drop(L(basis k))):real^N) = drop(L w)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL; DROP_VSUM; DROP_CMUL] THEN
  REWRITE_TAC[dot] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  SIMP_TAC[LAMBDA_BETA]);;

let P2A_EL_IDENTITY = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s w.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s))
     ==> ((\v. lift(w dot (Gt(tt - drop v pow 2) (y v) ** A v))) has_vector_derivative
          lift(inv(&2) * (A(lift s) dot
                          (mderiv (Gt(tt - s pow 2)) (y(lift s)) w ** A(lift s))) +
               &2 * s pow 2 *
               drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                       (at (y(lift s))) w)))
         (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `(A:real^1->real^N)(lift s)`; `s:real`]
                P2A_METRIC_CURVE_VDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\v:real^1. (Gt:real->real^N->real^N^N) (tt - drop v pow 2) ((y:real^1->real^N) v)`;
                 `(&4 * s) %%
                  ((lambda i j. lricci ((Gt:real->real^N->real^N^N) (tt - s pow 2))
                                       ((y:real^1->real^N)(lift s)) (basis i) (basis j))
                   :real^N^N) +
                  mderiv (Gt(tt - s pow 2)) (y(lift s)) ((A:real^1->real^N)(lift s))`;
                 `A:real^1->real^N`;
                 `p2a_lacc (Gt:real->real^N->real^N^N) tt s ((y:real^1->real^N)(lift s))
                           ((A:real^1->real^N)(lift s))`;
                 `w:real^N`; `lift s`] LRG_VDERIV_DOT_PRODUCT) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  SUBGOAL_THEN `metric_field U ((Gt:real->real^N->real^N^N) (tt - s pow 2))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `G0 = (Gt:real->real^N->real^N^N) (tt - s pow 2)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `y0 = (y:real^1->real^N)(lift s)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `A0 = (A:real^1->real^N)(lift s)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `invertible((G0:real^N->real^N^N) y0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. (G0:real^N->real^N^N) y0 ** (matrix_inv(G0 y0) ** v) = v`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^N) dot ((G0:real^N->real^N^N) y0 ** christoffel G0 y0 A0 A0) =
    inv(&2) * (w dot (mderiv G0 y0 A0 ** A0) + w dot (mderiv G0 y0 A0 ** A0) -
               A0 dot (mderiv G0 y0 w ** A0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LRG_CHRISTOFFEL_DOT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^N) dot (((lambda i j. lricci (G0:real^N->real^N^N) y0 (basis i) (basis j))
                     :real^N^N) ** A0) = lricci G0 y0 A0 w`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y0:real^N`; `w:real^N`;
                   `A0:real^N`] LRG_LRICCI_DOT_FORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LRICCI_SYM THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^N) dot ((lambda k. lricci (G0:real^N->real^N^N) y0 A0 (basis k)):real^N) =
    lricci G0 y0 A0 w`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\b:real^N. lift(lricci (G0:real^N->real^N^N) y0 A0 b)`; `w:real^N`]
                  P2A_DOT_LAMBDA_LINEAR) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y0:real^N`] LRG_LRICCI_LINEAR) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^N) dot ((lambda k. drop(frechet_derivative (\z. lift(lscalar (G0:real^N->real^N^N) z))
                                       (at y0) (basis k))):real^N) =
    drop(frechet_derivative (\z. lift(lscalar G0 z)) (at y0) w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_DOT_LAMBDA_LINEAR THEN REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LRG_LSCALAR_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lacc] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_RDISTRIB; MATRIX_VECTOR_LMUL; DOT_RADD; DOT_RMUL;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_RNEG; DOT_RSUB; DOT_RNEG] THEN
  ASM_REWRITE_TAC[p2a_lgradR; p2a_lricop] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G0:real^N->real^N^N`; `y0:real^N`; `w:real^N`;
                 `A0:real^N`] LRICCI_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P2A_LLAG_DY_LINEAR = prove
 (`!U (G:real^N->real^N^N) y A c.
     metric_field U G /\ y IN U
     ==> linear (\w. lift(inv(&2) * (A dot (mderiv G y w ** A)) +
                          &2 * c * drop(frechet_derivative (\z. lift(lscalar G z)) (at y) w)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y /\
                (\z. lift(lscalar G z)) differentiable at y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH] THEN ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_ADD; LIFT_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN ASM_SIMP_TAC[LRG_MDERIV_DOT_LINEAR];
    MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
    REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]]);;

let P2A_EL_VECTOR = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s.
     lricci_flow U ta tb Gt /\ ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
     (y has_vector_derivative A(lift s)) (at (lift s)) /\
     (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s))) (at (lift s))
     ==> ((\v. Gt(tt - drop v pow 2) (y v) ** A v) has_vector_derivative
          ((lambda k. inv(&2) * (A(lift s) dot
                                  (mderiv (Gt(tt - s pow 2)) (y(lift s)) (basis k) **
                                   A(lift s))) +
                      &2 * s pow 2 *
                      drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                              (at (y(lift s))) (basis k))):real^N))
         (at (lift s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [HAS_VECTOR_DERIVATIVE_COMPONENTWISE_AT] THEN BETA_TAC THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^1. lift(((Gt:real->real^N->real^N^N) (tt - drop x pow 2) ((y:real^1->real^N) x) **
                      (A:real^1->real^N) x)$k)) =
    (\v. lift(basis k dot (Gt(tt - drop v pow 2) (y v) ** A v)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^1` THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[DOT_BASIS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`; `s:real`;
                 `basis k:real^N`] P2A_EL_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[LAMBDA_BETA]);;

let P2A_WEAK_EL = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A (eta:real^1->real^N)
    eta' s1 s2.
     lricci_flow U ta tb Gt /\ s1 <= s2 /\
     (!s. s1 <= s /\ s <= s2
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ y(lift s) IN U /\
              (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                (at (lift s)) /\
              (eta has_vector_derivative eta'(lift s))
                (at (lift s) within interval[lift s1,lift s2])) /\
     eta(lift s1) = vec 0 /\ eta(lift s2) = vec 0
     ==> ((\s. inv(&2) * (A(lift s) dot
                          (mderiv (Gt(tt - s pow 2)) (y(lift s)) (eta(lift s)) ** A(lift s))) +
               &2 * s pow 2 *
               drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z))
                                       (at (y(lift s))) (eta(lift s))) +
               eta'(lift s) dot (Gt(tt - s pow 2) (y(lift s)) ** A(lift s)))
          has_real_integral &0) (real_interval[s1,s2])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
    `s1:real`; `s2:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ASM_REWRITE_TAC[DOT_LZERO; REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`; `x:real`] P2A_EL_VECTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
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
                 `lift x`; `interval[lift s1,lift s2]`] HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
  ASM_SIMP_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN; BILINEAR_DOT] THEN
  REWRITE_TAC[LIFT_DROP] THEN
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

let P2A_LLAG_EXPAND = prove
 (`!(Gt:real->real^N->real^N^N) tt s y A eta etad.
     transp(Gt(tt - s pow 2) (y + eta)) = Gt(tt - s pow 2) (y + eta)
     ==> p2a_llag Gt tt s (y + eta) (A + etad) - p2a_llag Gt tt s y A -
         (inv(&2) * (A dot (mderiv (Gt(tt - s pow 2)) y eta ** A)) +
          &2 * s pow 2 *
          drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at y) eta) +
          etad dot (Gt(tt - s pow 2) y ** A)) =
         inv(&2) * (etad dot (Gt(tt - s pow 2) (y + eta) ** etad)) +
         etad dot ((Gt(tt - s pow 2) (y + eta) - Gt(tt - s pow 2) y) ** A) +
         inv(&2) * (A dot ((Gt(tt - s pow 2) (y + eta) - Gt(tt - s pow 2) y -
                            mderiv (Gt(tt - s pow 2)) y eta) ** A)) +
         &2 * s pow 2 *
         (lscalar (Gt(tt - s pow 2)) (y + eta) - lscalar (Gt(tt - s pow 2)) y -
          drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at y) eta))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[p2a_llag] THEN
  ABBREV_TAC `M = (Gt:real->real^N->real^N^N)(tt - s pow 2) (y + eta)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `(A:real^N) dot ((M:real^N^N) ** etad) = etad dot (M ** A)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(A:real^N) dot ((M:real^N^N) ** etad) = A dot (transp M ** etad)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN MATCH_ACCEPT_TAC DOT_SYM;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ADD_LDISTRIB; MATRIX_VECTOR_MUL_SUB_RDISTRIB;
              DOT_LADD; DOT_RADD; DOT_LSUB; DOT_RSUB] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Integral inequalities (Cauchy-Schwarz for real integrals P2A_REAL_CS,    *)
(* the norm bound by the integral of the derivative P2A_VNORM_FTC_BOUND,    *)
(* the Wirtinger-type inequalities P2A_WIRTINGER), the s-family of a smooth *)
(* metric family (P2A_LSMOOTH_SFAMILY), continuity of the L-Lagrangian      *)
(* along curves (P2A_LLAG_CURVE_CONTINUOUS) and the pointwise lower bound   *)
(* of the second-order remainder (P2A_QF_BOUND, P2A_DELTA_BOUND).           *)
(* ========================================================================= *)

let P2A_REAL_CS = prove
 (`!f a b. a <= b /\ f real_integrable_on real_interval[a,b] /\
           (\x. f x pow 2) real_integrable_on real_interval[a,b]
           ==> real_integral (real_interval[a,b]) f pow 2 <=
               (b - a) * real_integral (real_interval[a,b]) (\x. f x pow 2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b:real = a` THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `I1 = real_integral (real_interval[a,b]) (f:real->real)` THEN
  ABBREV_TAC `I2 = real_integral (real_interval[a,b]) (\x. (f:real->real) x pow 2)` THEN
  ABBREV_TAC `m = I1 / (b - a)` THEN
  SUBGOAL_THEN
   `(\x. m * (f:real->real) x) real_integrable_on real_interval[a,b] /\
    (\x. &2 * m * (f:real->real) x) real_integrable_on real_interval[a,b] /\
    (\x. (f:real->real) x pow 2 - &2 * m * f x) real_integrable_on real_interval[a,b] /\
    (\x:real. m pow 2) real_integrable_on real_interval[a,b]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
    SUBGOAL_THEN `(\x. m * (f:real->real) x) real_integrable_on real_interval[a,b]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. &2 * m * (f:real->real) x) real_integrable_on real_interval[a,b]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,b]) (\x. ((f:real->real) x - m) pow 2) =
    I2 - &2 * m * I1 + m pow 2 * (b - a)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(x - m) pow 2 = (x pow 2 - &2 * m * x) + m pow 2`] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRAL_SUB; REAL_INTEGRAL_LMUL;
                 REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN
    MAP_EVERY EXPAND_TAC ["I1"; "I2"] THEN REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_integral (real_interval[a,b]) (\x. ((f:real->real) x - m) pow 2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[REAL_ARITH `(x - m) pow 2 = (x pow 2 - &2 * m * x) + m pow 2`] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN
  SUBGOAL_THEN `I2 - &2 * I1 / (b - a) * I1 + (I1 / (b - a)) pow 2 * (b - a) =
                (I2 * (b - a) - I1 pow 2) / (b - a)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < b - a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN REAL_ARITH_TAC);;

let P2A_REAL_CONT_OF_VEC = prove
 (`!(g:real^1->real) a b.
     (\x. lift(g x)) continuous_on interval[lift a,lift b]
     ==> (\t. g(lift t)) real_continuous_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP]);;

let P2A_VNORM_FTC_BOUND = prove
 (`!(eta:real^1->real^N) eta' s1 s2 s.
     s1 <= s /\ s <= s2 /\
     (!x. x IN interval[lift s1,lift s2]
          ==> (eta has_vector_derivative eta' x) (at x within interval[lift s1,lift s2])) /\
     eta' continuous_on interval[lift s1,lift s2] /\ eta(lift s1) = vec 0
     ==> norm(eta(lift s)) <= real_integral (real_interval[s1,s]) (\t. norm(eta'(lift t)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `interval[lift s1,lift s] SUBSET interval[lift s1,lift s2]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `lift s1`; `lift s`]
                FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[lift s1,lift s2]` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(eta':real^1->real^N) continuous_on interval[lift s1,lift s]` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s1,s]) (\t. norm((eta':real^1->real^N)(lift t))) =
    drop(integral (interval[lift s1,lift s]) (\x. lift(norm(eta' x))))`
  SUBST1_TAC THENL
   [MP_TAC(INST [`\t. norm((eta':real^1->real^N)(lift t))`,`f:real->real`;
                 `real_interval[s1,s]`,`s:real->bool`] REAL_INTEGRAL) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      MP_TAC(ISPECL [`\x:real^1. norm((eta':real^1->real^N) x)`; `s1:real`; `s:real`]
                    P2A_REAL_CONT_OF_VEC) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_NORM_COMPOSE];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; o_DEF; LIFT_DROP]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(eta:real^1->real^N)(lift s) =
                integral (interval[lift s1,lift s]) (eta':real^1->real^N)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  ASM_SIMP_TAC[INTEGRABLE_CONTINUOUS; CONTINUOUS_ON_LIFT_NORM_COMPOSE; LIFT_DROP; REAL_LE_REFL]);;

let P2A_AMGM = prove
 (`!a b h. &0 < h ==> a * b <= inv(&2 * h) * a pow 2 + h / &2 * b pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= inv(&2 * h) * (a - h * b) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 * h) * (a - h * b) pow 2 =
                inv(&2 * h) * a pow 2 + h / &2 * b pow 2 - a * b` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < h` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]);;

let P2A_WIRTINGER = prove
 (`!(eta:real^1->real^N) eta' s1 s2.
     s1 <= s2 /\
     (!x. x IN interval[lift s1,lift s2]
          ==> (eta has_vector_derivative eta' x) (at x within interval[lift s1,lift s2])) /\
     eta' continuous_on interval[lift s1,lift s2] /\ eta(lift s1) = vec 0
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
  SUBGOAL_THEN `(eta:real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[differentiable_on; VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. s1 <= a /\ b <= s2
          ==> (\t. norm((eta:real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[a,b] /\
              (\t. norm((eta':real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[a,b] /\
              (\t. norm((eta':real^1->real^N)(lift t))) real_integrable_on real_interval[a,b] /\
              (\t. norm((eta:real^1->real^N)(lift t)) * norm((eta':real^1->real^N)(lift t)))
                real_integrable_on real_interval[a,b]`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `interval[lift a,lift b] SUBSET interval[lift s1,lift s2]` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(eta:real^1->real^N) continuous_on interval[lift a,lift b] /\
                  (eta':real^1->real^N) continuous_on interval[lift a,lift b]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THENL
     [MP_TAC(ISPECL [`\x:real^1. norm((eta:real^1->real^N) x) pow 2`; `a:real`; `b:real`]
                    P2A_REAL_CONT_OF_VEC);
      MP_TAC(ISPECL [`\x:real^1. norm((eta':real^1->real^N) x) pow 2`; `a:real`; `b:real`]
                    P2A_REAL_CONT_OF_VEC);
      MP_TAC(ISPECL [`\x:real^1. norm((eta':real^1->real^N) x)`; `a:real`; `b:real`]
                    P2A_REAL_CONT_OF_VEC);
      MP_TAC(ISPECL [`\x:real^1. norm((eta:real^1->real^N) x) * norm((eta':real^1->real^N) x)`;
                     `a:real`; `b:real`] P2A_REAL_CONT_OF_VEC)] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_CMUL; REAL_POW_2] THEN TRY(MATCH_MP_TAC CONTINUOUS_ON_MUL) THEN
    ASM_SIMP_TAC[o_DEF; CONTINUOUS_ON_LIFT_NORM_COMPOSE];
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
    MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `s1:real`; `s2:real`; `s:real`]
                  P2A_VNORM_FTC_BOUND) THEN
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

let P2A_LSMOOTH_SFAMILY = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt sa sb.
     p2a_lsmooth U ta tb Gt /\ sa < sb /\
     (!s. sa < s /\ s < sb ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb)
     ==> p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  REWRITE_TAC[p2a_lsmooth] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^(1,N)finite_sum. (vectorize:real^N^N->real^(N,N)finite_prod)
         ((Gt:real->real^N->real^N^N)(tt - drop(fstcart z) pow 2) (sndcart z))) =
    (\z. vectorize(Gt (drop(fstcart z)) (sndcart z))) o
    (\z:real^(1,N)finite_sum. pastecart (lift(tt - drop(fstcart z) pow 2)) (sndcart z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; P2A_SMOOTH_TIME_SQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GEOL_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  ASM_SIMP_TAC[]);;

let P2A_LLAG_CURVE_CONTINUOUS = prove
 (`!U sa sb (Gt:real->real^N->real^N^N) tt (y:real^1->real^N) A s1 s2.
     p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\ sa < s1 /\ s2 < sb /\
     y continuous_on interval[lift s1,lift s2] /\ A continuous_on interval[lift s1,lift s2] /\
     (!s. s1 <= s /\ s <= s2 ==> y(lift s) IN U)
     ==> (\s. p2a_llag Gt tt s (y(lift s)) (A(lift s))) real_continuous_on real_interval[s1,s2]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^1. p2a_llag (Gt:real->real^N->real^N^N) tt (drop x) ((y:real^1->real^N) x)
                                       ((A:real^1->real^N) x)`; `s1:real`; `s2:real`]
                P2A_REAL_CONT_OF_VEC) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2A_LLAG_SMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2A_LSMOOTH_BASIC) THEN
  SUBGOAL_THEN
   `(\x:real^1. lift(p2a_llag (Gt:real->real^N->real^N^N) tt (drop x) ((y:real^1->real^N) x)
                              ((A:real^1->real^N) x))) =
    (\z. lift(p2a_llag Gt tt (drop(fstcart z)) (fstcart(sndcart z)) (sndcart(sndcart z)))) o
    (\x. pastecart x (pastecart (y x) (A x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval(lift sa,lift sb) PCROSS ((U:real^N->bool) PCROSS (:real^N))` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_UNIV; IN_INTERVAL_1] THEN
  X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^1->real^N) (lift(drop x)) IN U` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_DROP] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIFT_DROP]) THEN ASM_REAL_ARITH_TAC]);;

let P2A_QF_BOUND = prove
 (`!(X:real^N^N) u v. abs(u dot (X ** v)) <= norm(vectorize X) * norm u * norm v`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(u:real^N) * norm((X:real^N^N) ** v)` THEN
  REWRITE_TAC[NORM_CAUCHY_SCHWARZ_ABS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(u:real^N) * (norm(vectorize(X:real^N^N)) * norm(v:real^N))` THEN
  SIMP_TAC[REAL_LE_LMUL; NORM_POS_LE; COMPATIBLE_NORM_VECTORIZE] THEN REAL_ARITH_TAC);;

let P2A_DELTA_BOUND = prove
 (`!(M:real^N^N) G D (A:real^N) (eta:real^N) (etad:real^N) lam B0 B1 BR dR c.
     lam * norm etad pow 2 <= etad dot (M ** etad) /\
     norm(vectorize(M - G - D)) <= B1 * norm eta pow 2 /\
     norm(vectorize D) <= B0 * norm eta /\
     abs dR <= BR * norm eta pow 2 /\ &0 <= c
     ==> lam / &2 * norm etad pow 2 -
         norm etad * norm eta * (B1 * norm eta + B0) * norm A -
         inv(&2) * B1 * norm eta pow 2 * norm A pow 2 - c * BR * norm eta pow 2
         <= inv(&2) * (etad dot (M ** etad)) + etad dot ((M - G) ** A) +
            inv(&2) * (A dot ((M - G - D) ** A)) + c * dR`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(etad:real^N) dot (((M:real^N^N) - G) ** A) =
                etad dot ((M - G - D) ** A) + etad dot (D ** A)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM DOT_RADD; GSYM MATRIX_VECTOR_MUL_ADD_RDISTRIB] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATRIX_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(M:real^N^N) - G - D`; `etad:real^N`; `A:real^N`] P2A_QF_BOUND) THEN
  MP_TAC(ISPECL [`D:real^N^N`; `etad:real^N`; `A:real^N`] P2A_QF_BOUND) THEN
  MP_TAC(ISPECL [`(M:real^N^N) - G - D`; `A:real^N`; `A:real^N`] P2A_QF_BOUND) THEN
  SUBGOAL_THEN `abs(c * dR) <= c * BR * norm(eta:real^N) pow 2` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vectorize((M:real^N^N) - G - D)) * norm(etad:real^N) * norm(A:real^N) <=
    B1 * norm(eta:real^N) pow 2 * norm etad * norm A /\
    norm(vectorize(D:real^N^N)) * norm(etad:real^N) * norm(A:real^N) <=
    B0 * norm(eta:real^N) * norm etad * norm A /\
    norm(vectorize((M:real^N^N) - G - D)) * norm(A:real^N) * norm A <=
    B1 * norm(eta:real^N) pow 2 * norm A pow 2`
  MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    REPEAT CONJ_TAC THEN REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Local convexity of the L-length.  P2A_LB_ARITH and P2A_CONVEX_POINTWISE   *)
(* give the pointwise lower bound of the second-order remainder of the       *)
(* L-Lagrangian around a solution of the L-geodesic equation;                *)
(* P2A_LOCAL_CONVEXITY integrates it against the weak Euler-Lagrange         *)
(* equation and the Wirtinger bounds: on a short enough parameter interval,  *)
(* a competitor curve z with the same endpoints has L-length at least the    *)
(* L-length of the L-geodesic plus lam/4 times the squared L2 distance of    *)
(* the velocities.                                                           *)
(* ========================================================================= *)

let P2A_LB_ARITH = prove
 (`!e ed a r0 a0 B0 B1 BR q smax lam.
     &0 <= e /\ &0 <= ed /\ &0 <= a /\ e <= r0 /\ a <= a0 /\
     &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\ &0 <= q /\ q <= smax
     ==> lam / &2 * ed pow 2 - ((B1 * r0 + B0) * a0) * (e * ed) -
         (inv(&2) * B1 * a0 pow 2 + &2 * smax * BR) * e pow 2
         <= lam / &2 * ed pow 2 - ed * e * (B1 * e + B0) * a -
            inv(&2) * B1 * e pow 2 * a pow 2 - &2 * q * BR * e pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(B1 * e + B0) * a <= (B1 * r0 + B0) * a0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + c <= y + c`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ed * e * (B1 * e + B0) * a <= ((B1 * r0 + B0) * a0) * (e * ed)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `ed * e * (B1 * e + B0) * a = (e * ed) * ((B1 * e + B0) * a) /\
                  ((B1 * r0 + B0) * a0) * (e * ed) = (e * ed) * ((B1 * r0 + B0) * a0)`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a pow 2 <= a0 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2) * B1 * e pow 2 * a pow 2 <= inv(&2) * B1 * a0 pow 2 * e pow 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `inv(&2) * B1 * e pow 2 * a pow 2 = (inv(&2) * B1 * e pow 2) * a pow 2 /\
                  inv(&2) * B1 * a0 pow 2 * e pow 2 = (inv(&2) * B1 * e pow 2) * a0 pow 2`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_LE_INV_EQ; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * q * BR * e pow 2 <= &2 * smax * BR * e pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * q * BR * e pow 2 = (&2 * BR * e pow 2) * q /\
                  &2 * smax * BR * e pow 2 = (&2 * BR * e pow 2) * smax`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_POS];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2A_CONVEX_POINTWISE = prove
 (`!(Gt:real->real^N->real^N^N) tt s (y:real^N) (A:real^N) (e:real^N) (ed:real^N)
    lam B0 B1 BR a0 r0 smax U.
     metric_field U (Gt(tt - s pow 2)) /\ y + e IN U /\
     lam * norm ed pow 2 <= ed dot (Gt(tt - s pow 2) (y + e) ** ed) /\
     norm(vectorize(Gt(tt - s pow 2) (y + e) - Gt(tt - s pow 2) y -
                    mderiv (Gt(tt - s pow 2)) y e)) <= B1 * norm e pow 2 /\
     norm(vectorize(mderiv (Gt(tt - s pow 2)) y e)) <= B0 * norm e /\
     abs(lscalar (Gt(tt - s pow 2)) (y + e) - lscalar (Gt(tt - s pow 2)) y -
         drop(frechet_derivative (\x. lift(lscalar (Gt(tt - s pow 2)) x)) (at y) e))
       <= BR * norm e pow 2 /\
     norm A <= a0 /\ norm e <= r0 /\ &0 <= B0 /\ &0 <= B1 /\ &0 <= BR /\ s pow 2 <= smax
     ==> lam / &2 * norm ed pow 2 - ((B1 * r0 + B0) * a0) * (norm e * norm ed) -
         (inv(&2) * B1 * a0 pow 2 + &2 * smax * BR) * norm e pow 2
         <= p2a_llag Gt tt s (y + e) (A + ed) - p2a_llag Gt tt s y A -
            (inv(&2) * (A dot (mderiv (Gt(tt - s pow 2)) y e ** A)) +
             &2 * s pow 2 *
             drop(frechet_derivative (\z. lift(lscalar (Gt(tt - s pow 2)) z)) (at y) e) +
             ed dot (Gt(tt - s pow 2) y ** A))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gt:real->real^N->real^N^N`; `tt:real`; `s:real`; `y:real^N`; `A:real^N`;
                 `e:real^N`; `ed:real^N`] P2A_LLAG_EXPAND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[metric_field]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam / &2 * norm(ed:real^N) pow 2 -
              norm ed * norm(e:real^N) * (B1 * norm e + B0) * norm(A:real^N) -
              inv(&2) * B1 * norm e pow 2 * norm A pow 2 -
              (&2 * s pow 2) * BR * norm e pow 2` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`norm(e:real^N)`; `norm(ed:real^N)`; `norm(A:real^N)`; `r0:real`;
                   `a0:real`; `B0:real`; `B1:real`; `BR:real`; `s pow 2`; `smax:real`;
                   `lam:real`] P2A_LB_ARITH) THEN
    ASM_REWRITE_TAC[NORM_POS_LE; REAL_LE_POW_2] THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL [`(Gt:real->real^N->real^N^N)(tt - s pow 2) (y + e)`;
                   `(Gt:real->real^N->real^N^N)(tt - s pow 2) y`;
                   `mderiv ((Gt:real->real^N->real^N^N)(tt - s pow 2)) y e`;
                   `A:real^N`; `e:real^N`; `ed:real^N`; `lam:real`; `B0:real`; `B1:real`;
                   `BR:real`;
                   `lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2)) (y + e) -
                    lscalar (Gt(tt - s pow 2)) y -
                    drop(frechet_derivative
                          (\z. lift(lscalar ((Gt:real->real^N->real^N^N)(tt - s pow 2)) z))
                          (at y) e)`;
                   `&2 * s pow 2`] P2A_DELTA_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let P2A_LOCAL_CONVEXITY = prove
 (`!U ta tb (Gt:real->real^N->real^N^N) tt sa sb (y:real^1->real^N) A (z:real^1->real^N) z'
    s1 s2 C lam B0 B1 BR a0 r0 smax.
     lricci_flow U ta tb Gt /\ p2a_lsmooth U sa sb (\s. Gt(tt - s pow 2)) /\
     sa < s1 /\ s1 < s2 /\ s2 < sb /\ convex C /\ C SUBSET U /\
     (!s. s1 <= s /\ s <= s2
          ==> ta < tt - s pow 2 /\ tt - s pow 2 < tb /\ s pow 2 <= smax /\
              y(lift s) IN C /\ z(lift s) IN C /\
              (y has_vector_derivative A(lift s)) (at (lift s)) /\
              (A has_vector_derivative p2a_lacc Gt tt s (y(lift s)) (A(lift s)))
                (at (lift s)) /\
              norm(A(lift s)) <= a0 /\ norm(z(lift s) - y(lift s)) <= r0) /\
     (!x. x IN interval[lift s1,lift s2]
          ==> (z has_vector_derivative z' x) (at x within interval[lift s1,lift s2])) /\
     z' continuous_on interval[lift s1,lift s2] /\
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
     ==> real_integral (real_interval[s1,s2])
           (\s. p2a_llag Gt tt s (y(lift s)) (A(lift s))) +
         lam / &4 *
         real_integral (real_interval[s1,s2]) (\s. norm(z'(lift s) - A(lift s)) pow 2)
         <= real_integral (real_interval[s1,s2])
              (\s. p2a_llag Gt tt s (z(lift s)) (z'(lift s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^1->real^N) continuous_on interval[lift s1,lift s2] /\
                (A:real^1->real^N) continuous_on interval[lift s1,lift s2] /\
                (z:real^1->real^N) continuous_on interval[lift s1,lift s2]`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[differentiable_on; VECTOR_DIFFERENTIABLE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `eta = \x:real^1. (z:real^1->real^N) x - (y:real^1->real^N) x` THEN
  ABBREV_TAC `eta' = \x:real^1. (z':real^1->real^N) x - (A:real^1->real^N) x` THEN
  SUBGOAL_THEN
   `!x. x IN interval[lift s1,lift s2]
        ==> ((eta:real^1->real^N) has_vector_derivative eta' x)
            (at x within interval[lift s1,lift s2])`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["eta"; "eta'"] THEN REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `s:real` THEN
    STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(eta':real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
   [EXPAND_TAC "eta'" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(eta:real^1->real^N)(lift s1) = vec 0 /\ eta(lift s2) = vec 0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_FLOW_BASIC) THEN
  (* the weak Euler-Lagrange equation *)
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `Gt:real->real^N->real^N^N`;
                 `tt:real`; `y:real^1->real^N`; `A:real^1->real^N`; `eta:real^1->real^N`;
                 `eta':real^1->real^N`; `s1:real`; `s2:real`] P2A_WEAK_EL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `eta:real^1->real^N`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
          (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP];
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
   [CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC P2A_LLAG_CURVE_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `sa:real`; `sb:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`eta:real^1->real^N`; `eta':real^1->real^N`; `s1:real`; `s2:real`]
                P2A_WIRTINGER) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. norm((eta:real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[s1,s2] /\
    (\t. norm((eta':real^1->real^N)(lift t)) pow 2) real_integrable_on real_interval[s1,s2] /\
    (\t. norm((eta:real^1->real^N)(lift t)) * norm((eta':real^1->real^N)(lift t)))
      real_integrable_on real_interval[s1,s2]`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(eta:real^1->real^N) continuous_on interval[lift s1,lift s2]` ASSUME_TAC THENL
     [EXPAND_TAC "eta" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THENL
     [MP_TAC(ISPECL [`\x:real^1. norm((eta:real^1->real^N) x) pow 2`; `s1:real`; `s2:real`]
                    P2A_REAL_CONT_OF_VEC);
      MP_TAC(ISPECL [`\x:real^1. norm((eta':real^1->real^N) x) pow 2`; `s1:real`; `s2:real`]
                    P2A_REAL_CONT_OF_VEC);
      MP_TAC(ISPECL [`\x:real^1. norm((eta:real^1->real^N) x) * norm((eta':real^1->real^N) x)`;
                     `s1:real`; `s2:real`] P2A_REAL_CONT_OF_VEC)] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LIFT_CMUL; REAL_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_SIMP_TAC[o_DEF; CONTINUOUS_ON_LIFT_NORM_COMPOSE];
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

