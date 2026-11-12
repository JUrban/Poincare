(* ========================================================================= *)
(* Unit pc_p3_s13conf (Part 3 proofs; MT Ch 13): curvature of a             *)
(* conformal change Ghat = exp(-2 F) G of a metric field in coordinates     *)
(* (MT (13.1) and the scalar formula of Cor 13.5): the derivative of the    *)
(* metric, the Christoffel symbols                                          *)
(*   Gammahat(a,b) = Gamma(a,b) - dF(a) b - dF(b) a + G(a,b) grad F,         *)
(* the curvature tensor, and the sectional curvature                        *)
(*   Khat(u,v) = exp(2F) [K(u,v) + Q(u,v)/Gram(u,v) - |dF|^2]                *)
(* with Q the Kulkarni-Nomizu product of Hess F + dF dF with G evaluated on *)
(* (u,v,v,u).                                                               *)
(* ========================================================================= *)

needs "src/pc_p2b_scalpos.ml";;
needs "src/ns_smooth_elem.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The conformal metric field, the gradient, the derivative of              *)
(* the metric and the Christoffel symbols.                                   *)
(* ========================================================================= *)

let p3s_cdf = new_definition
 `p3s_cdf (cf:real^N->real) (y:real^N) (a:real^N) =
    drop(frechet_derivative (\z. lift(cf z)) (at y) a)`;;

let p3s_cgrad = new_definition
 `p3s_cgrad (G:real^N->real^N^N) (cf:real^N->real) (y:real^N) =
    matrix_inv(G y) ** (jacobian (\z. lift(cf z)) (at y))$1`;;

let p3s_cd2f = new_definition
 `p3s_cd2f (cf:real^N->real) (y:real^N) (a:real^N) (b:real^N) =
    drop(frechet_derivative (\z. frechet_derivative (\x. lift(cf x)) (at z) b) (at y) a)`;;

let p3s_chess = new_definition
 `p3s_chess (G:real^N->real^N^N) (cf:real^N->real) (y:real^N) (a:real^N) (b:real^N) =
    p3s_cd2f cf y a b - p3s_cdf cf y (christoffel G y a b)`;;

let P3S_CONF_FIELD = prove
 (`!U (G:real^N->real^N^N) cf.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z))
     ==> metric_field U (\z. exp(--(&2 * cf z)) %% G z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. exp(--(&2 * cf z)) %% (G:real^N->real^N^N) z) =
      (\z. drop((\z. lift(exp(drop((\z. lift(--(&2) * cf z)) z)))) z) %
           (vectorize o G) z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL; LIFT_DROP] THEN
      REWRITE_TAC[REAL_ARITH `--(&2 * x) = --(&2) * x`];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_EXP THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[TRANSP_MATRIX_CMUL] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_EXP_POS_LT]]);;

let P3S_CDF_LINEAR = prove
 (`!(cf:real^N->real) y.
     (\z. lift(cf z)) differentiable at y
     ==> (!a b. p3s_cdf cf y (a + b) = p3s_cdf cf y a + p3s_cdf cf y b) /\
         (!c a. p3s_cdf cf y (c % a) = c * p3s_cdf cf y a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  SIMP_TAC[p3s_cdf; LINEAR_ADD; LINEAR_CMUL; DROP_ADD; DROP_CMUL]);;

let P3S_CGRAD_DOT = prove
 (`!U (G:real^N->real^N^N) cf y w.
     metric_field U G /\ y IN U /\ (\z. lift(cf z)) differentiable at y
     ==> w dot (G y ** p3s_cgrad G cf y) = p3s_cdf cf y w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cgrad; p3s_cdf] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRG_METRIC_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  SUBGOAL_THEN `linear(frechet_derivative (\z. lift((cf:real^N->real) z)) (at y))`
  ASSUME_TAC THENL [ASM_MESON_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  REWRITE_TAC[jacobian] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(MATCH_MP MATRIX_WORKS
    (ASSUME `linear(frechet_derivative (\z. lift((cf:real^N->real) z)) (at y))`))] THEN
  SIMP_TAC[drop; MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[DOT_SYM]);;

let P3S_CF_HAS_DERIV = prove
 (`!U (cf:real^N->real) y.
     open U /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> ((\z. lift(cf z)) has_derivative (\h. lift(p3s_cdf cf y h))) (at y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cdf; LIFT_DROP; ETA_AX] THEN
  REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P3S_EXP_CF_DERIV = prove
 (`!U (cf:real^N->real) y.
     open U /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> ((\z. lift(exp(--(&2 * cf z)))) has_derivative
          (\h. lift(exp(--(&2 * cf y)) * (--(&2) * p3s_cdf cf y h)))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`] P3S_CF_HAS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `--(&2)` o MATCH_MP HAS_DERIVATIVE_CMUL) THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`exp`; `exp(--(&2 * (cf:real^N->real) y))`;
                 `\z:real^N. lift(--(&2) * cf z)`;
                 `\h:real^N. lift(--(&2) * p3s_cdf cf y h)`; `y:real^N`]
                LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  REWRITE_TAC[REAL_ARITH `--(&2 * x) = --(&2) * x`; LIFT_DROP] THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_EXP; GSYM LIFT_CMUL]);;

let P3S_CONF_MDERIV = prove
 (`!U (G:real^N->real^N^N) cf y c x w.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> x dot (mderiv (\z. exp(--(&2 * cf z)) %% G z) y c ** w) =
         exp(--(&2 * cf y)) *
         (x dot (mderiv G y c ** w) - &2 * p3s_cdf cf y c * (x dot (G y ** w)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`]
         P3S_CONF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(vectorize o (\z. exp(--(&2 * cf z)) %% (G:real^N->real^N^N) z)) differentiable at y /\
    (vectorize o G) differentiable at y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. exp(--(&2 * cf z)) %% (G:real^N->real^N^N) z`; `y:real^N`;
                 `x:real^N`; `w:real^N`] LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "D1") THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`] P3S_EXP_CF_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `y:real^N`; `x:real^N`; `w:real^N`]
         LRG_HAS_DERIVATIVE_GDOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:real^N. exp(--(&2 * cf z))`;
                 `\h:real^N. exp(--(&2 * cf y)) * (--(&2) * p3s_cdf cf y h)`;
                 `\z:real^N. x dot ((G:real^N->real^N^N) z ** w)`;
                 `\h:real^N. x dot (mderiv (G:real^N->real^N^N) y h ** w)`; `y:real^N`]
                LRG_HAS_DERIVATIVE_LIFT_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\z. lift(x dot ((exp(--(&2 * cf z)) %% (G:real^N->real^N^N) z) ** w)))
     has_derivative
     (\h. lift(exp(--(&2 * cf y)) * x dot (mderiv G y h ** w) +
               (exp(--(&2 * cf y)) * --(&2) * p3s_cdf cf y h) * x dot (G y ** w))))
    (at y)`
  (LABEL_TAC "D2") THENL
   [REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "D1" (fun d1 -> USE_THEN "D2" (fun d2 ->
    MP_TAC(MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT (CONJ d1 d2)))) THEN
  DISCH_THEN(MP_TAC o C AP_THM `c:real^N`) THEN REWRITE_TAC[LIFT_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let P3S_CONF_CHRISTOFFEL = prove
 (`!U (G:real^N->real^N^N) cf y a b.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> christoffel (\z. exp(--(&2 * cf z)) %% G z) y a b =
         christoffel G y a b - p3s_cdf cf y a % b - p3s_cdf cf y b % a +
         (a dot (G y ** b)) % p3s_cgrad G cf y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`]
         P3S_CONF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\z. lift((cf:real^N->real) z)) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^N->bool`; `\z. exp(--(&2 * cf z)) %% (G:real^N->real^N^N) z`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `\z. exp(--(&2 * cf z)) %% (G:real^N->real^N^N) z`;
                 `y:real^N`; `a:real^N`; `b:real^N`; `v:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`]
         P3S_CONF_MDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
              MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RADD;
              DOT_RSUB] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `a:real^N`;
                 `b:real^N`; `v:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `v:real^N`] P3S_CGRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC REAL_RING);;

(* ========================================================================= *)
(* The gradient field is smooth, and its derivative satisfies               *)
(* G(Dgrad(c)) = D2F(c,.) - (D_c G)(grad, .).                               *)
(* ========================================================================= *)

let P3S_JAC_ROW1 = prove
 (`!(f:real^N->real^1) z.
     (jacobian f (at z))$1 = (lambda j. drop(frechet_derivative f (at z) (basis j)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[jacobian; matrix] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; LE_REFL; drop]);;

let P3S_CGRAD_SMOOTH = prove
 (`!U (G:real^N->real^N^N) cf.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z))
     ==> smooth_map_on U (\z. p3s_cgrad G cf z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  REWRITE_TAC[p3s_cgrad; P3S_JAC_ROW1] THEN MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
    ASM_MESON_TAC[LRG_METRIC_INVERTIBLE];
    MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]);;

let P3S_CGRAD_DERIV = prove
 (`!U (G:real^N->real^N^N) cf y c x.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> x dot (G y ** frechet_derivative (\z. p3s_cgrad G cf z) (at y) c) =
         p3s_cd2f cf y c x - x dot (mderiv G y c ** p3s_cgrad G cf y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`]
         P3S_CGRAD_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\z. p3s_cgrad (G:real^N->real^N^N) cf z) has_derivative
     frechet_derivative (\z. p3s_cgrad G cf z) (at y)) (at y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((vectorize o (G:real^N->real^N^N)) has_derivative
     frechet_derivative (vectorize o G) (at y)) (at y)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `frechet_derivative (vectorize o (G:real^N->real^N^N)) (at y)`;
                 `(\z. x):real^N->real^N`; `(\w. vec 0):real^N->real^N`;
                 `\z. p3s_cgrad (G:real^N->real^N^N) cf z`;
                 `frechet_derivative (\z. p3s_cgrad (G:real^N->real^N^N) cf z) (at y)`;
                 `y:real^N`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST; DOT_LZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[GSYM mderiv; MATRIX_VECTOR_MUL_ADD_RDISTRIB; DOT_RADD] THEN
  DISCH_THEN(LABEL_TAC "D1") THEN
  SUBGOAL_THEN
   `((\z. lift(x dot ((G:real^N->real^N^N) z ** p3s_cgrad G cf z))) has_derivative
     (\w. lift(p3s_cd2f cf y w x))) (at y)`
  (LABEL_TAC "D2") THENL
   [SUBGOAL_THEN `?d. &0 < d /\ ball(y:real^N,d) SUBSET U` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\z. frechet_derivative (\x. lift((cf:real^N->real) x)) (at z) x` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN U` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`;
                     `z:real^N`; `x:real^N`] P3S_CGRAD_DOT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p3s_cdf; LIFT_DROP]];
      REWRITE_TAC[p3s_cd2f; LIFT_DROP; ETA_AX] THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MP_TAC(ISPECL [`U:real^N->bool`; `\x. lift((cf:real^N->real) x)`; `y:real^N`;
                     `x:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "D1" (fun d1 -> USE_THEN "D2" (fun d2 ->
    MP_TAC(MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT (CONJ d1 d2)))) THEN
  DISCH_THEN(MP_TAC o C AP_THM `c:real^N`) THEN REWRITE_TAC[LIFT_EQ] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The derivative of the conformal Christoffel field.                       *)
(* ========================================================================= *)

let P3S_CONF_DCHRISTOFFEL = prove
 (`!U (G:real^N->real^N^N) cf y v w a.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> frechet_derivative (\z. christoffel (\z. exp(--(&2 * cf z)) %% G z) z v w)
                            (at y) a =
         frechet_derivative (\z. christoffel G z v w) (at y) a -
         p3s_cd2f cf y a v % w - p3s_cd2f cf y a w % v +
         (v dot (mderiv G y a ** w)) % p3s_cgrad G cf y +
         (v dot (G y ** w)) % frechet_derivative (\z. p3s_cgrad G cf z) (at y) a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative
      (\z. christoffel (\z. exp(--(&2 * cf z)) %% (G:real^N->real^N^N) z) z v w) (at y) =
    frechet_derivative
      (\z. christoffel G z v w - p3s_cdf cf z v % w - p3s_cdf cf z w % v +
           (v dot (G z ** w)) % p3s_cgrad G cf z) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P3S_CONF_CHRISTOFFEL THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. christoffel (G:real^N->real^N^N) z v w) has_derivative
     frechet_derivative (\z. christoffel G z v w) (at y)) (at y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b:real^N. ((\z. p3s_cdf cf z b % w) has_derivative
                (\h. p3s_cd2f cf y h b % (w:real^N))) (at y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^N` THEN REWRITE_TAC[p3s_cdf; p3s_cd2f] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\x. lift((cf:real^N->real) x)`; `y:real^N`;
                   `b:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b:real^N. ((\z. p3s_cdf cf z b % v) has_derivative
                (\h. p3s_cd2f cf y h b % (v:real^N))) (at y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:real^N` THEN REWRITE_TAC[p3s_cdf; p3s_cd2f] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_VMUL_DROP THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `\x. lift((cf:real^N->real) x)`; `y:real^N`;
                   `b:real^N`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. (v dot ((G:real^N->real^N^N) z ** w)) % p3s_cgrad G cf z) has_derivative
     (\h. (v dot (G y ** w)) % frechet_derivative (\z. p3s_cgrad G cf z) (at y) h +
          (v dot (mderiv G y h ** w)) % p3s_cgrad G cf y)) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z. v dot ((G:real^N->real^N^N) z ** w)`;
                   `\h. v dot (mderiv (G:real^N->real^N^N) y h ** w)`;
                   `\z. p3s_cgrad (G:real^N->real^N^N) cf z`;
                   `frechet_derivative (\z. p3s_cgrad (G:real^N->real^N^N) cf z) (at y)`;
                   `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LRG_HAS_DERIVATIVE_GDOT THEN ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P3S_CGRAD_SMOOTH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\z. christoffel (G:real^N->real^N^N) z v w - p3s_cdf cf z v % w - p3s_cdf cf z w % v +
          (v dot (G z ** w)) % p3s_cgrad G cf z) has_derivative
     (\h. frechet_derivative (\z. christoffel G z v w) (at y) h -
          p3s_cd2f cf y h v % w - p3s_cd2f cf y h w % v +
          ((v dot (G y ** w)) % frechet_derivative (\z. p3s_cgrad G cf z) (at y) h +
           (v dot (mderiv G y h ** w)) % p3s_cgrad G cf y))) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* The sectional curvature of the conformal metric.                         *)
(* ========================================================================= *)

let P3S_CDF_LIN3 = prove
 (`!U (cf:real^N->real) y.
     open U /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> (!a b. p3s_cdf cf y (a + b) = p3s_cdf cf y a + p3s_cdf cf y b) /\
         (!a b. p3s_cdf cf y (a - b) = p3s_cdf cf y a - p3s_cdf cf y b) /\
         (!c a. p3s_cdf cf y (c % a) = c * p3s_cdf cf y a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((cf:real^N->real) z)) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P3S_CDF_LINEAR) THEN
  ASM_REWRITE_TAC[VECTOR_SUB; REAL_ARITH `a - b = a + -- &1 * b`] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `--b:real^N = -- &1 % b`]);;

let P3S_CD2F_SYM = prove
 (`!U (cf:real^N->real) y a b.
     open U /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> p3s_cd2f cf y a b = p3s_cd2f cf y b a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p3s_cd2f] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LRG_SECOND_DERIVATIVE_SYM THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P3S_CDF_CHRISTOFFEL = prove
 (`!U (G:real^N->real^N^N) cf y a b.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U
     ==> p3s_cdf cf y (christoffel G y a b) =
         inv(&2) * (p3s_cgrad G cf y dot (mderiv G y a ** b) +
                    p3s_cgrad G cf y dot (mderiv G y b ** a) -
                    a dot (mderiv G y (p3s_cgrad G cf y) ** b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. lift((cf:real^N->real) z)) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y a b`] P3S_CGRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel (G:real^N->real^N^N) y a b`; `p3s_cgrad (G:real^N->real^N^N) cf y`]
                LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LRG_CHRISTOFFEL_DOT THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let P3S_CONF_SECTIONAL = prove
 (`!U (G:real^N->real^N^N) cf y u v.
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U /\
     ~((u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2 = &0)
     ==> lsectional (\z. exp(--(&2 * cf z)) %% G z) y u v =
         exp(&2 * cf y) *
         (lsectional G y u v +
          (p3s_chess G cf y u u * (v dot (G y ** v)) +
           p3s_chess G cf y v v * (u dot (G y ** u)) -
           &2 * p3s_chess G cf y u v * (u dot (G y ** v)) +
           p3s_cdf cf y u pow 2 * (v dot (G y ** v)) +
           p3s_cdf cf y v pow 2 * (u dot (G y ** u)) -
           &2 * p3s_cdf cf y u * p3s_cdf cf y v * (u dot (G y ** v))) /
          ((u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2) -
          p3s_cdf cf y (p3s_cgrad G cf y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `cf:real^N->real`; `y:real^N`] P3S_CDF_LIN3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `bilinear(christoffel (G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [MATCH_MP_TAC CHRISTOFFEL_BILINEAR THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  REWRITE_TAC[lsectional; lriemann] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`]
         P3S_CONF_DCHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `cf:real^N->real`; `y:real^N`]
         P3S_CONF_CHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[BILINEAR_RADD; BILINEAR_RSUB; BILINEAR_RMUL] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_ADD_LDISTRIB;
                  MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RADD;
                  DOT_RSUB] THEN
  ABBREV_TAC `gg = p3s_cgrad (G:real^N->real^N^N) cf y` THEN
  SUBGOAL_THEN `!w:real^N. w dot ((G:real^N->real^N^N) y ** gg) = p3s_cdf cf y w`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "gg" THEN MATCH_MP_TAC P3S_CGRAD_DOT THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c w:real^N. w dot ((G:real^N->real^N^N) y **
                         frechet_derivative (\z. p3s_cgrad G cf z) (at y) c) =
                 p3s_cd2f cf y c w - w dot (mderiv G y c ** gg)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "gg" THEN MATCH_MP_TAC P3S_CGRAD_DERIV THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^N. p3s_cdf cf y (christoffel (G:real^N->real^N^N) y a b) =
                 inv(&2) * (gg dot (mderiv G y a ** b) + gg dot (mderiv G y b ** a) -
                            a dot (mderiv G y gg ** b))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "gg" THEN MATCH_MP_TAC P3S_CDF_CHRISTOFFEL THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w a b:real^N. w dot ((G:real^N->real^N^N) y ** christoffel G y a b) =
                   inv(&2) * (w dot (mderiv G y a ** b) + w dot (mderiv G y b ** a) -
                              a dot (mderiv G y w ** b))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_CHRISTOFFEL_DOT THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!c. v dot (mderiv (G:real^N->real^N^N) y c ** u) = u dot (mderiv G y c ** v)) /\
    (!c. gg dot (mderiv (G:real^N->real^N^N) y c ** u) = u dot (mderiv G y c ** gg)) /\
    (!c. gg dot (mderiv (G:real^N->real^N^N) y c ** v) = v dot (mderiv G y c ** gg)) /\
    p3s_cd2f cf y v u = p3s_cd2f cf y u v /\
    v dot ((G:real^N->real^N^N) y ** u) = u dot (G y ** v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY GEN_TAC THENL
     [MATCH_MP_TAC LRG_MDERIV_SYM; MATCH_MP_TAC LRG_MDERIV_SYM;
      MATCH_MP_TAC LRG_MDERIV_SYM; MATCH_MP_TAC P3S_CD2F_SYM;
      MATCH_MP_TAC LRG_METRIC_SYM] THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p3s_chess] THEN
  ABBREV_TAC `ee = exp(--(&2 * cf (y:real^N)))` THEN
  SUBGOAL_THEN `exp(&2 * cf (y:real^N)) = inv ee /\ &0 < ee` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV; REAL_EXP_POS_LT] THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < ee` THEN
  UNDISCH_TAC `~((u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
                 (u dot (G y ** v)) pow 2 = &0)` THEN
  CONV_TAC REAL_FIELD);;

(* ========================================================================= *)
(* In dimension 3, in a G-orthonormal frame f_i = M^-1 e_i the               *)
(* scalar curvature is 2 (K(f1,f2) + K(f1,f3) + K(f2,f3)); the sectional    *)
(* curvature is homogeneous of degree 0 in u and v.                          *)
(* ========================================================================= *)

let P3S_LSECT_HOMOG = prove
 (`!U (G:real^N->real^N^N) y c d u v.
     metric_field U G /\ y IN U /\ ~(c = &0) /\ ~(d = &0)
     ==> lsectional G y (c % u) (d % v) = lsectional G y u v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsectional] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
         LRIEMANN_TRILINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `lriemann (G:real^N->real^N^N) y (c % u) (d % v) (d % v) =
    (c * d * d) % lriemann G y u v v`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. lriemann (G:real^N->real^N^N) y x (d % v) (d % v)`;
                   `c:real`; `u:real^N`] LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lriemann (G:real^N->real^N^N) y u x (d % v)`;
                   `d:real`; `v:real^N`] LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lriemann (G:real^N->real^N^N) y u v x`;
                   `d:real`; `v:real^N`] LINEAR_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN
  ASM_CASES_TAC
   `(u dot ((G:real^N->real^N^N) y ** u)) * (v dot (G y ** v)) -
    (u dot (G y ** v)) pow 2 = &0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(c * c * (u dot ((G:real^N->real^N^N) y ** u))) * d * d * (v dot (G y ** v)) -
      (c * d * (u dot (G y ** v))) pow 2 =
      (c * c * d * d) * ((u dot (G y ** u)) * (v dot (G y ** v)) - (u dot (G y ** v)) pow 2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_INV_0]] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `~(c = &0)` THEN UNDISCH_TAC `~(d = &0)` THEN
  CONV_TAC REAL_FIELD);;

let P3S_LSCALAR_SECT3 = prove
 (`!U (G:real^3->real^3^3) y (M:real^3^3).
     metric_field U G /\ y IN U /\ G y = transp M ** M /\ invertible M
     ==> lscalar G y =
         &2 * (lsectional G y (matrix_inv M ** basis 1) (matrix_inv M ** basis 2) +
               lsectional G y (matrix_inv M ** basis 1) (matrix_inv M ** basis 3) +
               lsectional G y (matrix_inv M ** basis 2) (matrix_inv M ** basis 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (matrix_inv(M:real^3^3) ** basis i) dot
              ((G:real^3->real^3^3) y ** (matrix_inv M ** basis j)) =
              if i = j then &1 else &0`
  (LABEL_TAC "ON") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_FRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^3. a dot ((G:real^3->real^3^3) y ** lriemann G y a a b) = &0`
  (LABEL_TAC "Z") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `a:real^3`;
                   `a:real^3`; `b:real^3`] LRIEMANN_ANTISYM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `x:real^3 = --x <=> x = vec 0`] THEN
    SIMP_TAC[MATRIX_VECTOR_MUL_RZERO; DOT_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b:real^3. b dot ((G:real^3->real^3^3) y ** lriemann G y b a a) =
                 a dot (G y ** lriemann G y a b b)`
  (LABEL_TAC "S") THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `a:real^3`;
                   `b:real^3`; `a:real^3`] LRIEMANN_ANTISYM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_RNEG] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `a:real^3`;
                   `b:real^3`; `a:real^3`; `b:real^3`] LRG_RM_ANTISYM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `M:real^3^3`]
         P2B_LSCALAR_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!v. lricci (G:real^3->real^3^3) y v v =
        sum(1..dimindex(:3))
           (\i. (matrix_inv(M:real^3^3) ** basis i) dot
                (G y ** lriemann G y (matrix_inv M ** basis i) v v))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC P2B_LRICCI_FRAME THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3; lsectional] THEN
  USE_THEN "Z" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "ON" (fun th -> REWRITE_TAC(map (fun (i,j) ->
     REWRITE_RULE[] (CONV_RULE NUM_REDUCE_CONV
       (SPECL [mk_small_numeral i; mk_small_numeral j] th)))
     [(1,1);(2,2);(3,3);(1,2);(1,3);(2,3);(2,1);(3,1);(3,2)])) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  USE_THEN "S" (fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* In dimension 3, for a G-orthonormal frame f_i = M^-1 e_i,                  *)
(* |dF|^2 = sum dF(f_i)^2 and the scalar curvature of the conformal metric:  *)
(*   Rhat = exp(2F) (R + 4 sum_i Hess F(f_i,f_i) - 2 |dF|^2).                *)
(* ========================================================================= *)

let P3S_FRAME_COORD = prove
 (`!(A:real^3^3) (M:real^3^3) x i.
     A = transp M ** M /\ invertible M /\ 1 <= i /\ i <= 3
     ==> x dot (A ** (matrix_inv M ** basis i)) = (M ** x)$i`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `(M:real^3^3) ** matrix_inv M ** basis i = basis i` SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MATRIX_INV th)]) THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3]);;

let P3S_FRAME_PARSEVAL3 = prove
 (`!(A:real^3^3) (M:real^3^3) x.
     A = transp M ** M /\ invertible M
     ==> x dot (A ** x) =
         (x dot (A ** (matrix_inv M ** basis 1))) pow 2 +
         (x dot (A ** (matrix_inv M ** basis 2))) pow 2 +
         (x dot (A ** (matrix_inv M ** basis 3))) pow 2`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[P3S_FRAME_COORD; ARITH] THEN
  MP_TAC(ISPECL [`A:real^3^3`; `M:real^3^3`; `x:real^3`; `x:real^3`] LRG_FRAME_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DOT_3] THEN REAL_ARITH_TAC);;

let P3S_CONF_SCALAR3 = prove
 (`!U (G:real^3->real^3^3) cf y (M:real^3^3).
     metric_field U G /\ smooth_map_on U (\z. lift(cf z)) /\ y IN U /\
     G y = transp M ** M /\ invertible M
     ==> lscalar (\z. exp(--(&2 * cf z)) %% G z) y =
         exp(&2 * cf y) *
         (lscalar G y +
          &4 * (p3s_chess G cf y (matrix_inv M ** basis 1) (matrix_inv M ** basis 1) +
                p3s_chess G cf y (matrix_inv M ** basis 2) (matrix_inv M ** basis 2) +
                p3s_chess G cf y (matrix_inv M ** basis 3) (matrix_inv M ** basis 3)) -
          &2 * p3s_cdf cf y (p3s_cgrad G cf y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `cf:real^3->real`]
         P3S_CONF_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `ec = exp(cf(y:real^3))` THEN
  SUBGOAL_THEN `&0 < ec` ASSUME_TAC THENL
   [EXPAND_TAC "ec" THEN REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--(&2 * cf(y:real^3))) = inv ec pow 2 /\ exp(&2 * cf y) = ec pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ec" THEN REWRITE_TAC[REAL_EXP_NEG; REAL_EXP_N; REAL_POW_INV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `\z. exp(--(&2 * cf z)) %% (G:real^3->real^3^3) z`;
                 `y:real^3`; `inv ec %% (M:real^3^3)`] P3S_LSCALAR_SECT3) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INVERTIBLE_CMUL; TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL;
                    MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIX_INV_CMUL; REAL_INV_INV; MATRIX_VECTOR_LMUL] THEN
  SUBGOAL_THEN `~(ec = &0)` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `\z. exp(--(&2 * cf z)) %% (G:real^3->real^3^3) z`;
                 `y:real^3`; `ec:real`; `ec:real`] P3S_LSECT_HOMOG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `f1 = matrix_inv(M:real^3^3) ** basis 1` THEN
  ABBREV_TAC `f2 = matrix_inv(M:real^3^3) ** basis 2` THEN
  ABBREV_TAC `f3 = matrix_inv(M:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (matrix_inv(M:real^3^3) ** basis i) dot
              ((G:real^3->real^3^3) y ** (matrix_inv M ** basis j)) =
              if i = j then &1 else &0`
  (LABEL_TAC "ON") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2B_FRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f1 dot ((G:real^3->real^3^3) y ** f1) = &1 /\ f2 dot (G y ** f2) = &1 /\
    f3 dot (G y ** f3) = &1 /\ f1 dot (G y ** f2) = &0 /\
    f1 dot (G y ** f3) = &0 /\ f2 dot (G y ** f3) = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f1"; "f2"; "f3"] THEN
    USE_THEN "ON" (fun th -> REWRITE_TAC(map (fun (i,j) ->
       REWRITE_RULE[] (CONV_RULE NUM_REDUCE_CONV
         (SPECL [mk_small_numeral i; mk_small_numeral j] th)))
       [(1,1);(2,2);(3,3);(1,2);(1,3);(2,3)]));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. ~((a dot ((G:real^3->real^3^3) y ** a)) * (b dot (G y ** b)) -
            (a dot (G y ** b)) pow 2 = &0) /\
          ((a dot (G y ** a)) = &1 /\ (b dot (G y ** b)) = &1 /\ (a dot (G y ** b)) = &0)
          ==> lsectional (\z. exp(--(&2 * cf z)) %% G z) y a b =
              ec pow 2 * (lsectional G y a b +
                          p3s_chess G cf y a a + p3s_chess G cf y b b +
                          p3s_cdf cf y a pow 2 + p3s_cdf cf y b pow 2 -
                          p3s_cdf cf y (p3s_cgrad G cf y))`
  (LABEL_TAC "K") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `cf:real^3->real`;
                   `y:real^3`; `a:real^3`; `b:real^3`] P3S_CONF_SECTIONAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. (a dot ((G:real^3->real^3^3) y ** a)) = &1 /\ (b dot (G y ** b)) = &1 /\
          (a dot (G y ** b)) = &0
          ==> lsectional (\z. exp(--(&2 * cf z)) %% G z) y a b =
              ec pow 2 * (lsectional G y a b +
                          p3s_chess G cf y a a + p3s_chess G cf y b b +
                          p3s_cdf cf y a pow 2 + p3s_cdf cf y b pow 2 -
                          p3s_cdf cf y (p3s_cgrad G cf y))`
  (LABEL_TAC "K2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "K" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  USE_THEN "K2" (fun th -> MP_TAC(SPECL [`f1:real^3`; `f2:real^3`] th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "K2" (fun th -> MP_TAC(SPECL [`f1:real^3`; `f3:real^3`] th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  USE_THEN "K2" (fun th -> MP_TAC(SPECL [`f2:real^3`; `f3:real^3`] th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `M:real^3^3`]
         P3S_LSCALAR_SECT3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `M:real^3^3`;
                 `p3s_cgrad (G:real^3->real^3^3) cf y`] P3S_FRAME_PARSEVAL3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w dot ((G:real^3->real^3^3) y ** p3s_cgrad G cf y) = p3s_cdf cf y w`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P3S_CGRAD_DOT THEN EXISTS_TAC `U:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. p3s_cgrad (G:real^3->real^3^3) cf y dot (G y ** w) = p3s_cdf cf y w`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `w:real^3`) THEN
    MATCH_MP_TAC LRG_METRIC_SYM THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

