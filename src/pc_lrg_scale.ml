(* ========================================================================= *)
(* Local Riemannian geometry under constant rescaling, and Ricci curvature   *)
(* of the round 3-sphere and of the round cylinder in explicit conformal     *)
(* coordinates.  Builds on pc_lrg.                                           *)
(* ========================================================================= *)

needs "src/pc_lrg.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Behaviour of the curvature quantities under constant rescaling of the     *)
(* metric.                                                                   *)
(* ========================================================================= *)

let LRG_MDERIV_SCALE = prove
 (`!(G:real^N->real^N^N) c y w.
        (vectorize o G) differentiable at y
        ==> mderiv (\z. c %% G z) y w = c %% mderiv G y w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o (\z. c %% (G:real^N->real^N^N) z) =
    (\z. c % (vectorize o G) z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real` o MATCH_MP HAS_DERIVATIVE_CMUL o
                GEN_REWRITE_RULE I [FRECHET_DERIVATIVE_WORKS]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[MATRIFY_CMUL]);;

let LRG_SCALE_LAMBDA = prove
 (`!(A:real^N^N) a b d c.
        ~(c = &0)
        ==> inv c %
            (A ** ((lambda k. inv(&2) * (c * a k + c * b k - c * d k)):real^N)) =
            A ** ((lambda k. inv(&2) * (a k + b k - d k)):real^N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((lambda k. inv(&2) * (c * a k + c * b k - c * d k)):real^N) =
    c % ((lambda k. inv(&2) * (a k + b k - d k)):real^N)`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_RMUL; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
               VECTOR_MUL_LID]);;

let CHRISTOFFEL_SCALE = prove
 (`!U (G:real^N->real^N^N) c y u v.
        metric_field U G /\ y IN U /\ &0 < c
        ==> christoffel (\z. c %% G z) y u v = christoffel G y u v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vectorize o (G:real^N->real^N^N)) differentiable at y`
  ASSUME_TAC THENL [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF]; ALL_TAC] THEN
  ASM_SIMP_TAC[christoffel; LRG_MDERIV_SCALE; MATRIX_INV_CMUL;
               MATRIX_VECTOR_LMUL; DOT_RMUL; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC LRG_SCALE_LAMBDA THEN ASM_REAL_ARITH_TAC);;

let LRIEMANN_SCALE = prove
 (`!U (G:real^N->real^N^N) c y u v w.
        metric_field U G /\ y IN U /\ &0 < c
        ==> lriemann (\z. c %% G z) y u v w = lriemann G y u v w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!z a b. z IN U ==> christoffel (\z. c %% (G:real^N->real^N^N) z) z a b =
                       christoffel G z a b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CHRISTOFFEL_SCALE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. frechet_derivative
            (\z. christoffel (\z. c %% (G:real^N->real^N^N) z) z a b) (at y) =
          frechet_derivative (\z. christoffel G z a b) (at y)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[metric_field];
    ASM_SIMP_TAC[lriemann]]);;

let LRICCI_SCALE = prove
 (`!U (G:real^N->real^N^N) c y u v.
        metric_field U G /\ y IN U /\ &0 < c
        ==> lricci (\z. c %% G z) y u v = lricci G y u v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `c:real`; `y:real^N`]
         LRIEMANN_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[lricci]);;

let LSCALAR_SCALE = prove
 (`!U (G:real^N->real^N^N) c y.
        metric_field U G /\ y IN U /\ &0 < c
        ==> lscalar (\z. c %% G z) y = lscalar G y / c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `c:real`; `y:real^N`]
         LRICCI_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[lscalar; MATRIX_INV_CMUL; MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN REWRITE_TAC[REAL_MUL_AC]);;

(* ========================================================================= *)
(* Metrics whose Christoffel symbols near y have the radial                  *)
(* conformal form  Gamma_z(a,b) = m(z) ((z.a) b + (z.b) a - (a.b) z),        *)
(* with m differentiable at y with derivative h -> p (y.h): the curvature    *)
(* tensor and the Ricci tensor at y in closed form.                          *)
(* ========================================================================= *)

let LRG_LINEAR_RADIAL_L = prove
 (`!a b:real^N.
        linear (\x:real^N. (x dot a) % b + (x dot b) % a - (a dot b) % x)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN REWRITE_TAC[LRG_LINEAR_DOT_SCALE] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN REWRITE_TAC[LRG_LINEAR_DOT_SCALE] THEN
  MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN REWRITE_TAC[LINEAR_ID]);;

let LRG_RADIAL_DCHRISTOFFEL = prove
 (`!(G:real^N->real^N^N) S m p y a b u.
        open S /\ y IN S /\
        (!z a b. z IN S
                 ==> christoffel G z a b =
                     m z % ((z dot a) % b + (z dot b) % a - (a dot b) % z)) /\
        ((\z. lift(m z)) has_derivative (\h. lift(p * (y dot h)))) (at y)
        ==> frechet_derivative (\z. christoffel G z a b) (at y) u =
            m y % ((u dot a) % b + (u dot b) % a - (a dot b) % u) +
            (p * (y dot u)) % ((y dot a) % b + (y dot b) % a - (a dot b) % y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. christoffel (G:real^N->real^N^N) z a b) (at y) =
    frechet_derivative
      (\z. (m:real^N->real) z % ((z dot a) % b + (z dot b) % a - (a dot b) % z))
      (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:real^N->real`; `\h:real^N. p * (y dot h)`;
                 `\x:real^N. (x dot a) % b + (x dot b) % a - (a dot b) % x`;
                 `\x:real^N. (x dot a) % b + (x dot b) % a - (a dot b) % x`;
                 `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[HAS_DERIVATIVE_LINEAR; LRG_LINEAR_RADIAL_L] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]));;

let LRG_RADIAL_RIEMANN = prove
 (`!(G:real^N->real^N^N) S m p y a v w.
        open S /\ y IN S /\
        (!z a b. z IN S
                 ==> christoffel G z a b =
                     m z % ((z dot a) % b + (z dot b) % a - (a dot b) % z)) /\
        ((\z. lift(m z)) has_derivative (\h. lift(p * (y dot h)))) (at y)
        ==> lriemann G y a v w =
            (&2 * m y + m y pow 2 * (y dot y)) %
            ((a dot w) % v - (v dot w) % a) +
            (p - m y pow 2) %
            (((y dot a) * (y dot w)) % v - ((y dot v) * (y dot w)) % a -
             ((y dot a) * (v dot w)) % y + ((y dot v) * (a dot w)) % y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `S:real^N->bool`; `m:real^N->real`;
                 `p:real`; `y:real^N`] LRG_RADIAL_DCHRISTOFFEL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `t:real^N` THEN
  ASM_SIMP_TAC[lriemann] THEN
  REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL; DOT_LADD; DOT_LSUB; DOT_LMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING);;

let LRG_RADIAL_TRACE = prove
 (`!c1 c2 (v:real^N) w y.
        sum (1..dimindex(:N))
          (\k. (c1 % ((basis k dot w) % v - (v dot w) % basis k) +
                c2 % (((y dot basis k) * (y dot w)) % v -
                      ((y dot v) * (y dot w)) % basis k -
                      ((y dot basis k) * (v dot w)) % y +
                      ((y dot v) * (basis k dot w)) % y))$k) =
        (&1 - &(dimindex(:N))) * c1 * (v dot w) +
        c2 * ((&2 - &(dimindex(:N))) * (y dot v) * (y dot w) -
              (y dot y) * (v dot w))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (1..dimindex(:N))
      (\k. c1 * ((v:real^N)$k * (w:real^N)$k) - c1 * (v dot w) +
           c2 * ((y dot w) * ((y:real^N)$k * v$k)) -
           c2 * ((y dot v) * (y dot w)) -
           c2 * ((v dot w) * (y$k * y$k)) +
           c2 * ((y dot v) * (y$k * w$k)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                 VECTOR_MUL_COMPONENT; DOT_BASIS; BASIS_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL; SUM_CONST_NUMSEG] THEN
  REWRITE_TAC[GSYM dot; ADD_SUB] THEN REWRITE_TAC[DOT_SYM] THEN
  CONV_TAC REAL_RING);;

let LRG_RADIAL_RICCI = prove
 (`!(G:real^N->real^N^N) S m p y v w.
        open S /\ y IN S /\
        (!z a b. z IN S
                 ==> christoffel G z a b =
                     m z % ((z dot a) % b + (z dot b) % a - (a dot b) % z)) /\
        ((\z. lift(m z)) has_derivative (\h. lift(p * (y dot h)))) (at y)
        ==> lricci G y v w =
            (&1 - &(dimindex(:N))) * (&2 * m y + m y pow 2 * (y dot y)) *
            (v dot w) +
            (p - m y pow 2) *
            ((&2 - &(dimindex(:N))) * (y dot v) * (y dot w) -
             (y dot y) * (v dot w))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lricci] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`; `S:real^N->bool`; `m:real^N->real`;
                 `p:real`; `y:real^N`] LRG_RADIAL_RIEMANN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[LRG_RADIAL_TRACE]);;

(* ========================================================================= *)
(* Ricci curvature of the round sphere (any dimension, and the case of the   *)
(* 3-sphere) in stereographic coordinates.                                   *)
(* ========================================================================= *)

let LRG_SPH_M_DERIV = prove
 (`!y:real^N.
        ((\x. lift(--(&2) / (&1 + norm x pow 2))) has_derivative
         (\h. lift((&4 / (&1 + norm y pow 2) pow 2) * (y dot h)))) (at y)`,
  GEN_TAC THEN MP_TAC(SPEC `y:real^N` LRG_SPH_G_DERIV) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let LRG_SPH_RICCI = prove
 (`!y u v:real^N.
        lricci (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) y u v =
        (&(dimindex(:N)) - &1) * (&4 / (&1 + norm y pow 2) pow 2) * (u dot v)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`(\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1):real^N->real^N^N`;
    `(:real^N)`; `\x:real^N. --(&2) / (&1 + norm x pow 2)`;
    `&4 / (&1 + norm(y:real^N) pow 2) pow 2`; `y:real^N`; `u:real^N`;
    `v:real^N`] LRG_RADIAL_RICCI) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; LRG_SPH_CHRISTOFFEL; LRG_SPH_M_DERIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPEC `y:real^N` LRG_SPH_POS) THEN REWRITE_TAC[NORM_POW_2] THEN
  CONV_TAC REAL_FIELD);;

(* LRICCI_ROUND_SPHERE_3: the unit 3-sphere in stereographic coordinates,   *)
(* Ric = 2 g.                                                               *)

let LRICCI_ROUND_SPHERE_3 = prove
 (`!y u v:real^3.
        lricci (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1) y u v =
        &2 * (&4 / (&1 + norm y pow 2) pow 2) * (u dot v)`,
  REWRITE_TAC[LRG_SPH_RICCI; DIMINDEX_3] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The round cylinder S^2 x R, as real^3 minus the origin with               *)
(* the metric (2/|z|^2) delta (z = e^t theta gives 2(dt^2 + dtheta^2)).      *)
(* The computation is done on real^N minus the origin and specialised.       *)
(* ========================================================================= *)

let LRG_CYL_POS = prove
 (`!z:real^N. ~(z = vec 0) ==> &0 < norm z pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
  ASM_REWRITE_TAC[NORM_POS_LT]);;

let LRG_CYL_OPEN = prove
 (`open((:real^N) DELETE vec 0)`,
  MATCH_MP_TAC OPEN_DELETE THEN REWRITE_TAC[OPEN_UNIV]);;

let LRG_CYL_SMOOTH_C = prove
 (`smooth_map_on ((:real^N) DELETE vec 0) (\x. lift(&2 / norm x pow 2))`,
  SUBGOAL_THEN `smooth_map_on ((:real^N) DELETE vec 0) (\x. lift(norm x pow 2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N) DELETE vec 0`; `\x:real^N. x`]
           SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    REWRITE_TAC[LRG_CYL_OPEN; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N) DELETE vec 0`; `\x:real^N. lift(&2)`;
                 `\x:real^N. lift(norm x pow 2)`] SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_REWRITE_TAC[LRG_CYL_OPEN; SMOOTH_MAP_ON_CONST; LIFT_DROP;
                  IN_DELETE; IN_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LRG_CYL_POS THEN
  ASM_REWRITE_TAC[]);;

let LRG_CYL_METRIC = prove
 (`metric_field ((:real^N) DELETE vec 0) (\z. (&2 / norm z pow 2) %% mat 1)`,
  REWRITE_TAC[metric_field; LRG_CYL_OPEN; IN_DELETE; IN_UNIV] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z:real^N. (&2 / norm z pow 2) %% mat 1) =
      (\z. drop((\x:real^N. lift(&2 / norm x pow 2)) z) %
           vectorize(mat 1:real^N^N))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    REWRITE_TAC[LRG_CYL_OPEN; SMOOTH_MAP_ON_CONST; LRG_CYL_SMOOTH_C];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT; MATRIX_VECTOR_LMUL;
                MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[DOT_POS_LT] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    MATCH_MP_TAC LRG_CYL_POS THEN ASM_REWRITE_TAC[]]);;

let LRG_CYL_Q1 = prove
 (`!t. &0 < t
       ==> ((\t. &2 / t) has_real_derivative (--(&2) / t pow 2)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\t. &2 / t) has_real_derivative f') (atreal t)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(t = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let LRG_CYL_Q2 = prove
 (`!t. &0 < t
       ==> ((\t. --(&1) / t) has_real_derivative (&1 / t pow 2)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\t. --(&1) / t) has_real_derivative f') (atreal t)`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(t = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let LRG_CYL_C_DERIV = prove
 (`!z:real^N.
        ~(z = vec 0)
        ==> ((\x. lift(&2 / norm x pow 2)) has_derivative
             (\h. lift(--(&4) * (z dot h) / (norm z pow 2) pow 2))) (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. &2 / t`; `--(&2) / (norm(z:real^N) pow 2) pow 2`;
                 `\x:real^N. lift(norm x pow 2)`;
                 `\h:real^N. &2 % lift(z dot h)`; `z:real^N`]
         LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT] THEN
  ASM_SIMP_TAC[LRG_CYL_Q1; LRG_CYL_POS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let LRG_CYL_M_DERIV = prove
 (`!y:real^N.
        ~(y = vec 0)
        ==> ((\x. lift(--(&1) / norm x pow 2)) has_derivative
             (\h. lift((&2 / (norm y pow 2) pow 2) * (y dot h)))) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. --(&1) / t`; `&1 / (norm(y:real^N) pow 2) pow 2`;
                 `\x:real^N. lift(norm x pow 2)`;
                 `\h:real^N. &2 % lift(y dot h)`; `y:real^N`]
         LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT] THEN
  ASM_SIMP_TAC[LRG_CYL_Q2; LRG_CYL_POS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
  GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let LRG_CYL_MDERIV = prove
 (`!z a:real^N.
        ~(z = vec 0)
        ==> mderiv (\z. (&2 / norm z pow 2) %% mat 1) z a =
            (--(&4) * (z dot a) / (norm z pow 2) pow 2) %% mat 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mderiv] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o
    (\z:real^N. (&2 / norm z pow 2) %% mat 1) =
    (\x. (&2 / norm x pow 2) % vectorize(mat 1:real^N^N))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTORIZE_CMUL]; ALL_TAC] THEN
  MP_TAC(ISPEC `vectorize(mat 1:real^N^N)`
    (MATCH_MP HAS_DERIVATIVE_VMUL_DROP
      (MATCH_MP LRG_CYL_C_DERIV (ASSUME `~(z:real^N = vec 0)`)))) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[MATRIFY_CMUL; MATRIFY_VECTORIZE]);;

let LRG_CYL_CHRISTOFFEL = prove
 (`!z a b:real^N.
        ~(z = vec 0)
        ==> christoffel (\z. (&2 / norm z pow 2) %% mat 1) z a b =
            (--(&1) / norm z pow 2) %
            ((z dot a) % b + (z dot b) % a - (a dot b) % z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LRG_METRIC_DOT_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(:real^N) DELETE vec 0`;
    `(\z. (&2 / norm z pow 2) %% mat 1):real^N->real^N^N`; `z:real^N`] THEN
  ASM_REWRITE_TAC[LRG_CYL_METRIC; IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `w:real^N` THEN
  MP_TAC(ISPECL
   [`(:real^N) DELETE vec 0`;
    `(\z. (&2 / norm z pow 2) %% mat 1):real^N->real^N^N`;
    `z:real^N`; `a:real^N`; `b:real^N`; `w:real^N`] LRG_CHRISTOFFEL_DOT) THEN
  ASM_REWRITE_TAC[LRG_CYL_METRIC; IN_DELETE; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LRG_CYL_MDERIV; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  REWRITE_TAC[DOT_RMUL; DOT_RADD; DOT_RSUB] THEN REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(SPEC `z:real^N` LRG_CYL_POS) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_FIELD);;

let LRG_CYL_RICCI = prove
 (`!y u v:real^N.
        ~(y = vec 0)
        ==> lricci (\z. (&2 / norm z pow 2) %% mat 1) y u v =
            (&(dimindex(:N)) - &2) *
            ((u dot v) - (u dot y) * (v dot y) / norm y pow 2) / norm y pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(\z. (&2 / norm z pow 2) %% mat 1):real^N->real^N^N`;
    `(:real^N) DELETE vec 0`; `\x:real^N. --(&1) / norm x pow 2`;
    `&2 / (norm(y:real^N) pow 2) pow 2`; `y:real^N`; `u:real^N`;
    `v:real^N`] LRG_RADIAL_RICCI) THEN
  ASM_SIMP_TAC[LRG_CYL_OPEN; IN_DELETE; IN_UNIV; LRG_CYL_CHRISTOFFEL;
               LRG_CYL_M_DERIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPEC `y:real^N` LRG_CYL_POS) THEN ASM_REWRITE_TAC[NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* Ricci and scalar curvature of the round cylinder S^2 x R.                *)

let LRICCI_ROUND_CYLINDER = prove
 (`!y u v:real^3.
        ~(y = vec 0)
        ==> lricci (\z. (&2 / norm z pow 2) %% mat 1) y u v =
            ((u dot v) - (u dot y) * (v dot y) / norm y pow 2) / norm y pow 2`,
  SIMP_TAC[LRG_CYL_RICCI; DIMINDEX_3] THEN REAL_ARITH_TAC);;

let LSCALAR_ROUND_CYLINDER = prove
 (`!y:real^3.
        ~(y = vec 0) ==> lscalar (\z. (&2 / norm z pow 2) %% mat 1) y = &1`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[lscalar; LRICCI_ROUND_CYLINDER; MATRIX_INV_CMUL; MATRIX_INV_I;
               MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
  SIMP_TAC[MAT_COMPONENT; DOT_BASIS_BASIS; DOT_BASIS; DIMINDEX_3; ARITH] THEN
  MP_TAC(ISPEC `y:real^3` LRG_CYL_POS) THEN ASM_REWRITE_TAC[NORM_POW_2; DOT_3] THEN
  CONV_TAC REAL_FIELD);;

