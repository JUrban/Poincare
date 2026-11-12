(* ========================================================================= *)
(* Unit pc_geo_s3 (geodesics layer): the round 3-sphere as the model.        *)
(* round3_metric (pc_rf_basic) is the metric induced from real^4             *)
(* (SPHERE3_ROUND_INDUCED); great circles are geodesics                      *)
(* (SPHERE3_GREAT_CIRCLE); the explicit exponential map (SPHERE3_EXP); exp_q *)
(* maps the tangent ball of radius pi diffeomorphically onto the sphere      *)
(* minus -q (SPHERE3_EXP_BALL_PI); the injectivity radius is pi              *)
(* (MFD_INJRAD_SPHERE3).                                                     *)
(* ========================================================================= *)

needs "src/pc_geo_lisom.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The inverse stereographic maps written as                                 *)
(* e + (2 / (1 + |y|^2)) (J y - e) with e = +/- basis 4 and J the standard   *)
(* embedding of real^3 into real^4; their derivatives are conformal with     *)
(* factor 4 / (1 + |y|^2)^2 and tangent to the sphere; hence                 *)
(* SPHERE3_ROUND_INDUCED.                                                     *)
(* ========================================================================= *)

let GEOS_J_COMPONENTS = prove
 (`!y:real^3. ((lambda i. if i = 4 then &0 else y$i):real^4)$1 = y$1 /\
              ((lambda i. if i = 4 then &0 else y$i):real^4)$2 = y$2 /\
              ((lambda i. if i = 4 then &0 else y$i):real^4)$3 = y$3 /\
              ((lambda i. if i = 4 then &0 else y$i):real^4)$4 = &0`,
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_4; ARITH]);;

let GEOS_J_DOT = prove
 (`!y w:real^3. ((lambda i. if i = 4 then &0 else y$i):real^4) dot
                ((lambda i. if i = 4 then &0 else w$i):real^4) = y dot w`,
  REWRITE_TAC[DOT_4; DOT_3; GEOS_J_COMPONENTS] THEN REAL_ARITH_TAC);;

let GEOS_J_LINEAR = prove
 (`linear (\y:real^3. (lambda i. if i = 4 then &0 else y$i):real^4)`,
  SIMP_TAC[linear; CART_EQ; DIMINDEX_4; FORALL_4; LAMBDA_BETA; ARITH;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let GEOS_J_BASIS4 = prove
 (`!y:real^3. ((lambda i. if i = 4 then &0 else y$i):real^4) dot basis 4 = &0 /\
              ((lambda i. if i = 4 then &0 else y$i):real^4) dot --(basis 4) = &0`,
  SIMP_TAC[DOT_RNEG; DOT_BASIS; DIMINDEX_4; ARITH; GEOS_J_COMPONENTS] THEN
  REAL_ARITH_TAC);;

let GEOS_BASIS4_DOT = prove
 (`basis 4 dot (basis 4:real^4) = &1 /\ --(basis 4) dot --(basis 4:real^4) = &1`,
  SIMP_TAC[DOT_LNEG; DOT_RNEG; REAL_NEG_NEG; DOT_BASIS_BASIS; DIMINDEX_4; ARITH]);;

let GEOS_STEREO_N_INV_REP = prove
 (`!y:real^3.
        stereo3_n_inv y =
        basis 4 + (&2 / (&1 + norm y pow 2)) %
                  ((lambda i. if i = 4 then &0 else y$i):real^4 - basis 4)`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4] THEN
  REWRITE_TAC[STEX_STEREO3_N_INV_COMPONENTS; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; GEOS_J_COMPONENTS] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN
  MP_TAC(ISPEC `y:real^3` STEX_INV_STEREO_DENOM) THEN CONV_TAC REAL_FIELD);;

let GEOS_STEREO_S_INV_REP = prove
 (`!y:real^3.
        stereo3_s_inv y =
        --(basis 4) + (&2 / (&1 + norm y pow 2)) %
                      ((lambda i. if i = 4 then &0 else y$i):real^4 - --(basis 4))`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4] THEN
  REWRITE_TAC[STEX_STEREO3_S_INV_COMPONENTS; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_NEG_COMPONENT;
              GEOS_J_COMPONENTS] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN
  MP_TAC(ISPEC `y:real^3` STEX_INV_STEREO_DENOM) THEN CONV_TAC REAL_FIELD);;

(* The scalar factor and its derivative. *)

let GEOS_C_DERIV = prove
 (`!y:real^3.
        ((lift o (\z. &2 / (&1 + norm z pow 2))) has_derivative
         (lift o (\h. --(&4) * (y dot h) / (&1 + norm y pow 2) pow 2))) (at y)`,
  GEN_TAC THEN MP_TAC(ISPEC `y:real^3` LRG_SPH_G_DERIV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_NEG) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM LIFT_NEG] THEN GEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let GEOS_SIGMA_DERIV = prove
 (`!(e:real^4) (y:real^3).
        ((\z. e + (&2 / (&1 + norm z pow 2)) %
                  ((lambda i. if i = 4 then &0 else z$i):real^4 - e)) has_derivative
         (\h. (&2 / (&1 + norm y pow 2)) % ((lambda i. if i = 4 then &0 else h$i):real^4) +
              (--(&4) * (y dot h) / (&1 + norm y pow 2) pow 2) %
              ((lambda i. if i = 4 then &0 else y$i):real^4 - e))) (at y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL
   [`(\z. e):real^3->real^4`; `(\h. vec 0):real^3->real^4`;
    `\z:real^3. (&2 / (&1 + norm z pow 2)) %
                ((lambda i. if i = 4 then &0 else z$i):real^4 - e)`;
    `\h:real^3. (&2 / (&1 + norm y pow 2)) % ((lambda i. if i = 4 then &0 else h$i):real^4) +
                (--(&4) * (y dot h) / (&1 + norm y pow 2) pow 2) %
                ((lambda i. if i = 4 then &0 else y$i):real^4 - e)`;
    `at (y:real^3)`] HAS_DERIVATIVE_ADD) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL
   [`\z:real^3. &2 / (&1 + norm z pow 2)`;
    `\h:real^3. --(&4) * (y dot h) / (&1 + norm y pow 2) pow 2`;
    `\z:real^3. (lambda i. if i = 4 then &0 else z$i):real^4 - e`;
    `\h:real^3. (lambda i. if i = 4 then &0 else h$i):real^4`;
    `y:real^3`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[GEOS_C_DERIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL
   [`\z:real^3. (lambda i. if i = 4 then &0 else z$i):real^4`;
    `\z:real^3. (lambda i. if i = 4 then &0 else z$i):real^4`;
    `(\z. e):real^3->real^4`; `(\h. vec 0):real^3->real^4`;
    `at (y:real^3)`] HAS_DERIVATIVE_SUB) THEN
  REWRITE_TAC[HAS_DERIVATIVE_CONST; VECTOR_SUB_RZERO] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[GEOS_J_LINEAR]);;

(* Conformality and tangency of the derivative. *)

let GEOS_SIGMA_DIFF_DOT = prove
 (`!(e:real^4) (y:real^3) v w.
        (!z:real^3. ((lambda i. if i = 4 then &0 else z$i):real^4) dot e = &0) /\
        e dot e = &1
        ==> ((&2 / (&1 + norm y pow 2)) % ((lambda i. if i = 4 then &0 else v$i):real^4) +
             (--(&4) * (y dot v) / (&1 + norm y pow 2) pow 2) %
             ((lambda i. if i = 4 then &0 else y$i):real^4 - e)) dot
            ((&2 / (&1 + norm y pow 2)) % ((lambda i. if i = 4 then &0 else w$i):real^4) +
             (--(&4) * (y dot w) / (&1 + norm y pow 2) pow 2) %
             ((lambda i. if i = 4 then &0 else y$i):real^4 - e)) =
            (&4 / (&1 + norm y pow 2) pow 2) * (v dot w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. e dot ((lambda i. if i = 4 then &0 else z$i):real^4) = &0`
  ASSUME_TAC THENL [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_LSUB; DOT_RSUB] THEN
  ASM_REWRITE_TAC[GEOS_J_DOT] THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(ISPEC `y:real^3` LRG_SPH_POS) THEN CONV_TAC REAL_FIELD);;

let GEOS_SIGMA_DIFF_TANGENT = prove
 (`!(e:real^4) (y:real^3) h.
        (!z:real^3. ((lambda i. if i = 4 then &0 else z$i):real^4) dot e = &0) /\
        e dot e = &1
        ==> (e + (&2 / (&1 + norm y pow 2)) %
                 ((lambda i. if i = 4 then &0 else y$i):real^4 - e)) dot
            ((&2 / (&1 + norm y pow 2)) % ((lambda i. if i = 4 then &0 else h$i):real^4) +
             (--(&4) * (y dot h) / (&1 + norm y pow 2) pow 2) %
             ((lambda i. if i = 4 then &0 else y$i):real^4 - e)) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. e dot ((lambda i. if i = 4 then &0 else z$i):real^4) = &0`
  ASSUME_TAC THENL [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_LSUB; DOT_RSUB] THEN
  ASM_REWRITE_TAC[GEOS_J_DOT] THEN REWRITE_TAC[GSYM NORM_POW_2] THEN
  REWRITE_TAC[DOT_SYM] THEN
  MP_TAC(ISPEC `y:real^3` LRG_SPH_POS) THEN CONV_TAC REAL_FIELD);;

let GEOS_SIGMA_FACTS = prove
 (`!(e:real^4) (y:real^3).
        (!z:real^3. ((lambda i. if i = 4 then &0 else z$i):real^4) dot e = &0) /\
        e dot e = &1
        ==> ((\z. e + (&2 / (&1 + norm z pow 2)) %
                      ((lambda i. if i = 4 then &0 else z$i):real^4 - e)) has_derivative
             frechet_derivative
               (\z. e + (&2 / (&1 + norm z pow 2)) %
                        ((lambda i. if i = 4 then &0 else z$i):real^4 - e)) (at y))
            (at y) /\
            (!v w. frechet_derivative
                     (\z. e + (&2 / (&1 + norm z pow 2)) %
                              ((lambda i. if i = 4 then &0 else z$i):real^4 - e)) (at y) v dot
                   frechet_derivative
                     (\z. e + (&2 / (&1 + norm z pow 2)) %
                              ((lambda i. if i = 4 then &0 else z$i):real^4 - e)) (at y) w =
                   (&4 / (&1 + norm y pow 2) pow 2) * (v dot w)) /\
            (!h. (e + (&2 / (&1 + norm y pow 2)) %
                      ((lambda i. if i = 4 then &0 else y$i):real^4 - e)) dot
                 frechet_derivative
                   (\z. e + (&2 / (&1 + norm z pow 2)) %
                            ((lambda i. if i = 4 then &0 else z$i):real^4 - e)) (at y) h = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:real^4`; `y:real^3`] GEOS_SIGMA_DERIV) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    SUBST1_TAC(SYM(MATCH_MP FRECHET_DERIVATIVE_AT th))) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GEOS_SIGMA_DIFF_DOT; GEOS_SIGMA_DIFF_TANGENT]);;

(* The two charts of sphere3_atlas. *)

let GEOS_CHART_INV_DIFF = prove
 (`!c y. c IN sphere3_atlas
         ==> (chart_inv c has_derivative frechet_derivative (chart_inv c) (at y)) (at y) /\
             linear(frechet_derivative (chart_inv c) (at y)) /\
             (!v w. frechet_derivative (chart_inv c) (at y) v dot
                    frechet_derivative (chart_inv c) (at y) w =
                    (&4 / (&1 + norm y pow 2) pow 2) * (v dot w)) /\
             (!h. chart_inv c y dot frechet_derivative (chart_inv c) (at y) h = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RFB_SPHERE3_ATLAS_CASES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[STEX_SPHERE3_CHART_INV] THENL
   [SUBGOAL_THEN
     `stereo3_n_inv =
      (\z. basis 4 + (&2 / (&1 + norm z pow 2)) %
                     ((lambda i. if i = 4 then &0 else z$i):real^4 - basis 4))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; GEOS_STEREO_N_INV_REP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`basis 4:real^4`; `y:real^3`] GEOS_SIGMA_FACTS);
    SUBGOAL_THEN
     `stereo3_s_inv =
      (\z. --(basis 4) + (&2 / (&1 + norm z pow 2)) %
                         ((lambda i. if i = 4 then &0 else z$i):real^4 - --(basis 4)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; GEOS_STEREO_S_INV_REP]; ALL_TAC] THEN
    MP_TAC(ISPECL [`--(basis 4):real^4`; `y:real^3`] GEOS_SIGMA_FACTS)] THEN
  REWRITE_TAC[GEOS_J_BASIS4; GEOS_BASIS4_DOT] THEN
  MESON_TAC[has_derivative]);;

(* The inclusion of the sphere into real^4 in preferred charts. *)

let GEOS_INCL_DIFF = prove
 (`!x:real^4.
        mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) x =
        frechet_derivative (chart_inv (chart_at sphere3_atlas x))
                           (at (SND (chart_at sphere3_atlas x) x))`,
  GEN_TAC THEN REWRITE_TAC[mfd_differential] THEN
  SIMP_TAC[MFDD_OPEN_SET_CHART_AT; IN_UNIV; SND] THEN REWRITE_TAC[ETA_AX]);;

let GEOS_CHART_AT = prove
 (`!x:real^4. x IN sphere(vec 0,&1)
              ==> chart_at sphere3_atlas x IN sphere3_atlas /\
                  x IN FST(chart_at sphere3_atlas x)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CHART_AT THEN
  EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^4,&1))` THEN
  ASM_REWRITE_TAC[SPHERE3_ATLAS; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]);;

let SPHERE3_ROUND_INDUCED = prove
 (`!x v w.
        x IN sphere(vec 0:real^4,&1)
        ==> v dot (round3_metric x ** w) =
            mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) x v dot
            mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) x w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GEOS_INCL_DIFF] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_CHART_AT) THEN
  ASM_SIMP_TAC[GEOS_CHART_INV_DIFF] THEN
  REWRITE_TAC[round3_metric; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL]);;

(* ========================================================================= *)
(* Great circles t -> cos t q + sin t u are geodesics                        *)
(* (SPHERE3_GREAT_CIRCLE).  In the north chart the chart curve is            *)
(* inv(1 - a) A with A = cos t Q + sin t U (Q, U the first three coordinates  *)
(* of q, u) and a = cos t q4 + sin t u4; its velocity is                      *)
(* V = inv(1 - a) B + (b / (1 - a)^2) A with B = A', b = a', and the geodesic *)
(* equation V' = -Gamma(V,V) is the identity GEOS_ODE_ALG, which only uses    *)
(* |A|^2 = 1 - a^2, A.B = -ab, |B|^2 = 1 - b^2.  The south chart is the north *)
(* chart composed with the reflection in the fourth coordinate.              *)
(* ========================================================================= *)

(* Vector derivatives of scalar multiples and of combinations of two fixed   *)
(* vectors.                                                                   *)

let GEOS_VDERIV_SMUL = prove
 (`!(c:real->real) c' (f:real^1->real^N) f' t.
        (c has_real_derivative c') (atreal t) /\
        (f has_vector_derivative f') (at (lift t))
        ==> ((\s. c(drop s) % f s) has_vector_derivative (c t % f' + c' % f(lift t)))
            (at (lift t))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(c:real->real) o drop`; `\h:real^1. drop h * c'`; `f:real^1->real^N`;
                 `\h:real^1. drop h % (f':real^N)`; `lift t`] HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(lift o (\h:real^1. drop h * c')) = (\h. drop h % lift c')`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ASM_REWRITE_TAC[o_ASSOC]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN
  GEN_TAC THEN REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let GEOS_VDERIV_LINCOMB = prove
 (`!(f1:real->real) f1' f2 f2' (X:real^N) Y Z t.
        (f1 has_real_derivative f1') (atreal t) /\
        (f2 has_real_derivative f2') (atreal t) /\
        f1' % X + f2' % Y = Z
        ==> ((\s. f1(drop s) % X + f2(drop s) % Y) has_vector_derivative Z)
            (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f1:real->real`; `f1':real`; `(\s. X):real^1->real^N`;
                   `vec 0:real^N`; `t:real`] GEOS_VDERIV_SMUL);
    MP_TAC(ISPECL [`f2:real->real`; `f2':real`; `(\s. Y):real^1->real^N`;
                   `vec 0:real^N`; `t:real`] GEOS_VDERIV_SMUL)] THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

let GEOS_CIRCLE_DERIV = prove
 (`!q u:real^4 t.
        ((\s. cos(drop s) % q + sin(drop s) % u) has_vector_derivative
         (--sin t % q + cos t % u)) (at (lift t))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC GEOS_VDERIV_LINCOMB THEN
  MAP_EVERY EXISTS_TAC [`--sin t`; `cos t`] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_COS; HAS_REAL_DERIVATIVE_SIN]);;

let GEOS_CIRCLE_SPHERE = prove
 (`!q u:real^4 t.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> cos t % q + sin t % u IN sphere(vec 0,&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^4) dot q = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

(* The projection to the first three coordinates. *)

let GEOS_P_COMPONENTS = prove
 (`!x:real^4. ((lambda i. x$i):real^3)$1 = x$1 /\ ((lambda i. x$i):real^3)$2 = x$2 /\
              ((lambda i. x$i):real^3)$3 = x$3`,
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH]);;

let GEOS_P_DOT = prove
 (`!x y:real^4. ((lambda i. x$i):real^3) dot ((lambda i. y$i):real^3) =
                x dot y - x$4 * y$4`,
  REWRITE_TAC[DOT_3; DOT_4; GEOS_P_COMPONENTS] THEN REAL_ARITH_TAC);;

let GEOS_STEREO_N_CIRCLE = prove
 (`!q u:real^4 s.
        stereo3_n(cos s % q + sin s % u) =
        inv(&1 - (cos s * q$4 + sin s * u$4)) %
        (cos s % ((lambda i. q$i):real^3) + sin s % ((lambda i. u$i):real^3))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO3_N_COMPONENTS;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; GEOS_P_COMPONENTS] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* The geodesic equation in the north chart, abstractly. *)

let GEOS_ODE_ALG = prove
 (`!(A:real^3) B a b.
        ~(&1 - a = &0) /\
        A dot A = &1 - a pow 2 /\ A dot B = --(a * b) /\ B dot B = &1 - b pow 2
        ==> (&2 * b / (&1 - a) pow 2) % B +
            (&2 * b pow 2 / (&1 - a) pow 3 - &1 / (&1 - a) pow 2) % A =
            --(christoffel (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1)
                 (inv(&1 - a) % A)
                 (inv(&1 - a) % B + (b / (&1 - a) pow 2) % A)
                 (inv(&1 - a) % B + (b / (&1 - a) pow 2) % A))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LRG_SPH_CHRISTOFFEL] THEN
  SUBGOAL_THEN `B dot (A:real^3) = --(a * b)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&2) / (&1 + norm(inv(&1 - a) % (A:real^3)) pow 2) = --(&1 - a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2; DOT_LMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&1 - a = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(inv(&1 - a) % (A:real^3)) dot (inv(&1 - a) % B + (b / (&1 - a) pow 2) % A) =
    b / (&1 - a) pow 2 /\
    (inv(&1 - a) % B + (b / (&1 - a) pow 2) % A) dot
    (inv(&1 - a) % B + (b / (&1 - a) pow 2) % (A:real^3)) = &1 / (&1 - a) pow 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&1 - a = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[CART_EQ] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
              VECTOR_NEG_COMPONENT] THEN
  UNDISCH_TAC `~(&1 - a = &0)` THEN CONV_TAC REAL_FIELD);;

(* The constraints for a great circle. *)

let GEOS_CIRCLE_CONSTRAINTS = prove
 (`!q u:real^4 t.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> (cos t % ((lambda i. q$i):real^3) + sin t % ((lambda i. u$i):real^3)) dot
            (cos t % ((lambda i. q$i):real^3) + sin t % ((lambda i. u$i):real^3)) =
            &1 - (cos t * q$4 + sin t * u$4) pow 2 /\
            (cos t % ((lambda i. q$i):real^3) + sin t % ((lambda i. u$i):real^3)) dot
            (--sin t % ((lambda i. q$i):real^3) + cos t % ((lambda i. u$i):real^3)) =
            --((cos t * q$4 + sin t * u$4) * (--sin t * q$4 + cos t * u$4)) /\
            (--sin t % ((lambda i. q$i):real^3) + cos t % ((lambda i. u$i):real^3)) dot
            (--sin t % ((lambda i. q$i):real^3) + cos t % ((lambda i. u$i):real^3)) =
            &1 - (--sin t * q$4 + cos t * u$4) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NORM_EQ_1] THEN STRIP_TAC THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; GEOS_P_DOT] THEN
  SUBGOAL_THEN `(u:real^4) dot q = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `t:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;

(* ========================================================================= *)
(* The geodesic equation of great circles in the north chart                 *)
(* (GEOS_NORTH_GEODESIC) and, by the reflection in the fourth coordinate, in *)
(* the south chart (GEOS_SOUTH_GEODESIC).                                     *)
(* ========================================================================= *)

let GEOS_INV_LINCOMB = prove
 (`!d c s (X:real^N) Y. inv d % (c % X + s % Y) = (c / d) % X + (s / d) % Y`,
  REWRITE_TAC[real_div] THEN VECTOR_ARITH_TAC);;

let GEOS_NORTH_GEODESIC = prove
 (`!q u:real^4.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> ?V. !t. ~(cos t % q + sin t % u = basis 4)
                    ==> ((\s. stereo3_n(cos(drop s) % q + sin(drop s) % u))
                         has_vector_derivative V t) (at (lift t)) /\
                        ((\s. V(drop s)) has_vector_derivative
                         --(christoffel (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1)
                                        (stereo3_n(cos t % q + sin t % u)) (V t) (V t)))
                        (at (lift t))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `\s. (--sin s / (&1 - (cos s * (q:real^4)$4 + sin s * (u:real^4)$4)) +
         (--sin s * q$4 + cos s * u$4) * cos s /
         (&1 - (cos s * q$4 + sin s * u$4)) pow 2) % ((lambda i. q$i):real^3) +
        (cos s / (&1 - (cos s * q$4 + sin s * u$4)) +
         (--sin s * q$4 + cos s * u$4) * sin s /
         (&1 - (cos s * q$4 + sin s * u$4)) pow 2) % ((lambda i. u$i):real^3)` THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4) = &0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`q:real^4`; `u:real^4`; `t:real`] GEOS_CIRCLE_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC STEX_STEREO3_N_DOMAIN THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DELETE] THEN
    DISCH_THEN(MP_TAC o SPEC `cos t % q + sin t % u:real^4`) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GEOS_STEREO_N_CIRCLE] THEN CONJ_TAC THENL
   [REWRITE_TAC[GEOS_INV_LINCOMB] THEN
    MP_TAC(ISPECL
     [`\s. cos s / (&1 - (cos s * (q:real^4)$4 + sin s * (u:real^4)$4))`;
      `--sin t / (&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4)) +
       (--sin t * q$4 + cos t * u$4) * cos t /
       (&1 - (cos t * q$4 + sin t * u$4)) pow 2`;
      `\s. sin s / (&1 - (cos s * (q:real^4)$4 + sin s * (u:real^4)$4))`;
      `cos t / (&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4)) +
       (--sin t * q$4 + cos t * u$4) * sin t /
       (&1 - (cos t * q$4 + sin t * u$4)) pow 2`;
      `(lambda i. (q:real^4)$i):real^3`; `(lambda i. (u:real^4)$i):real^3`;
      `(--sin t / (&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4)) +
        (--sin t * q$4 + cos t * u$4) * cos t /
        (&1 - (cos t * q$4 + sin t * u$4)) pow 2) % ((lambda i. q$i):real^3) +
       (cos t / (&1 - (cos t * q$4 + sin t * u$4)) +
        (--sin t * q$4 + cos t * u$4) * sin t /
        (&1 - (cos t * q$4 + sin t * u$4)) pow 2) % ((lambda i. u$i):real^3)`;
      `t:real`] GEOS_VDERIV_LINCOMB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4) = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. --sin s / (&1 - (cos s * (q:real^4)$4 + sin s * (u:real^4)$4)) +
         (--sin s * q$4 + cos s * u$4) * cos s /
         (&1 - (cos s * q$4 + sin s * u$4)) pow 2`;
    `&2 * (--sin t * (q:real^4)$4 + cos t * (u:real^4)$4) /
     (&1 - (cos t * q$4 + sin t * u$4)) pow 2 * --sin t +
     (&2 * (--sin t * q$4 + cos t * u$4) pow 2 /
      (&1 - (cos t * q$4 + sin t * u$4)) pow 3 -
      &1 / (&1 - (cos t * q$4 + sin t * u$4)) pow 2) * cos t`;
    `\s. cos s / (&1 - (cos s * (q:real^4)$4 + sin s * (u:real^4)$4)) +
         (--sin s * q$4 + cos s * u$4) * sin s /
         (&1 - (cos s * q$4 + sin s * u$4)) pow 2`;
    `&2 * (--sin t * (q:real^4)$4 + cos t * (u:real^4)$4) /
     (&1 - (cos t * q$4 + sin t * u$4)) pow 2 * cos t +
     (&2 * (--sin t * q$4 + cos t * u$4) pow 2 /
      (&1 - (cos t * q$4 + sin t * u$4)) pow 3 -
      &1 / (&1 - (cos t * q$4 + sin t * u$4)) pow 2) * sin t`;
    `(lambda i. (q:real^4)$i):real^3`; `(lambda i. (u:real^4)$i):real^3`;
    `--(christoffel (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1)
         (inv(&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4)) %
          (cos t % ((lambda i. q$i):real^3) + sin t % ((lambda i. u$i):real^3)))
         ((--sin t / (&1 - (cos t * q$4 + sin t * u$4)) +
           (--sin t * q$4 + cos t * u$4) * cos t /
           (&1 - (cos t * q$4 + sin t * u$4)) pow 2) % ((lambda i. q$i):real^3) +
          (cos t / (&1 - (cos t * q$4 + sin t * u$4)) +
           (--sin t * q$4 + cos t * u$4) * sin t /
           (&1 - (cos t * q$4 + sin t * u$4)) pow 2) % ((lambda i. u$i):real^3))
         ((--sin t / (&1 - (cos t * q$4 + sin t * u$4)) +
           (--sin t * q$4 + cos t * u$4) * cos t /
           (&1 - (cos t * q$4 + sin t * u$4)) pow 2) % ((lambda i. q$i):real^3) +
          (cos t / (&1 - (cos t * q$4 + sin t * u$4)) +
           (--sin t * q$4 + cos t * u$4) * sin t /
           (&1 - (cos t * q$4 + sin t * u$4)) pow 2) % ((lambda i. u$i):real^3)))`;
    `t:real`] GEOS_VDERIV_LINCOMB) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4) = &0)` THEN
    CONV_TAC REAL_FIELD;
    REAL_DIFF_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&1 - (cos t * (q:real^4)$4 + sin t * (u:real^4)$4) = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `Q = (lambda i. (q:real^4)$i):real^3` THEN
  ABBREV_TAC `U = (lambda i. (u:real^4)$i):real^3` THEN
  ABBREV_TAC `a = cos t * (q:real^4)$4 + sin t * (u:real^4)$4` THEN
  ABBREV_TAC `b = --sin t * (q:real^4)$4 + cos t * (u:real^4)$4` THEN
  MP_TAC(ISPECL [`cos t % Q + sin t % U:real^3`; `--sin t % Q + cos t % U:real^3`;
                 `a:real`; `b:real`] GEOS_ODE_ALG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`q:real^4`; `u:real^4`; `t:real`] GEOS_CIRCLE_CONSTRAINTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(--sin t / (&1 - a) + b * cos t / (&1 - a) pow 2) % Q +
    (cos t / (&1 - a) + b * sin t / (&1 - a) pow 2) % U =
    inv(&1 - a) % (--sin t % Q + cos t % U) +
    (b / (&1 - a) pow 2) % (cos t % Q + sin t % U:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[real_div] THEN VECTOR_ARITH_TAC);;

(* The reflection in the fourth coordinate exchanges the two charts. *)

let GEOS_R_COMPONENTS = prove
 (`!z:real^4. ((lambda i. if i = 4 then --(z$4) else z$i):real^4)$1 = z$1 /\
              ((lambda i. if i = 4 then --(z$4) else z$i):real^4)$2 = z$2 /\
              ((lambda i. if i = 4 then --(z$4) else z$i):real^4)$3 = z$3 /\
              ((lambda i. if i = 4 then --(z$4) else z$i):real^4)$4 = --(z$4)`,
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_4; ARITH]);;

let GEOS_STEREO_S_REFLECT = prove
 (`!z:real^4. stereo3_s z =
              stereo3_n ((lambda i. if i = 4 then --(z$4) else z$i):real^4)`,
  GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; STEX_STEREO3_N_COMPONENTS;
              STEX_STEREO3_S_COMPONENTS; GEOS_R_COMPONENTS] THEN
  REWRITE_TAC[REAL_ARITH `&1 - --x = &1 + x`]);;

let GEOS_R_LINEAR_COMB = prove
 (`!q u:real^4 c s.
        ((lambda i. if i = 4 then --((c % q + s % u)$4) else (c % q + s % u)$i):real^4) =
        c % ((lambda i. if i = 4 then --(q$4) else q$i):real^4) +
        s % ((lambda i. if i = 4 then --(u$4) else u$i):real^4)`,
  SIMP_TAC[CART_EQ; DIMINDEX_4; FORALL_4; LAMBDA_BETA; ARITH;
           VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let GEOS_R_DOT = prove
 (`!x y:real^4.
        ((lambda i. if i = 4 then --(x$4) else x$i):real^4) dot
        ((lambda i. if i = 4 then --(y$4) else y$i):real^4) = x dot y`,
  REWRITE_TAC[DOT_4; GEOS_R_COMPONENTS] THEN REAL_ARITH_TAC);;

let GEOS_R_BASIS = prove
 (`!z:real^4. ((lambda i. if i = 4 then --(z$4) else z$i):real^4) = basis 4 <=>
              z = --(basis 4)`,
  GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; GEOS_R_COMPONENTS;
                           VECTOR_NEG_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_4; ARITH] THEN REAL_ARITH_TAC);;

let GEOS_SOUTH_GEODESIC = prove
 (`!q u:real^4.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> ?V. !t. ~(cos t % q + sin t % u = --(basis 4))
                    ==> ((\s. stereo3_s(cos(drop s) % q + sin(drop s) % u))
                         has_vector_derivative V t) (at (lift t)) /\
                        ((\s. V(drop s)) has_vector_derivative
                         --(christoffel (\z. (&4 / (&1 + norm z pow 2) pow 2) %% mat 1)
                                        (stereo3_s(cos t % q + sin t % u)) (V t) (V t)))
                        (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(lambda i. if i = 4 then --((q:real^4)$4) else q$i):real^4`;
                 `(lambda i. if i = 4 then --((u:real^4)$4) else u$i):real^4`]
    GEOS_NORTH_GEODESIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_1; GEOS_R_DOT] THEN ASM_REWRITE_TAC[GSYM NORM_EQ_1];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `V:real->real^3` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real` THEN
  REWRITE_TAC[GEOS_STEREO_S_REFLECT; GEOS_R_LINEAR_COMB] THEN
  REWRITE_TAC[GSYM GEOS_R_LINEAR_COMB; GEOS_R_BASIS]);;

(* ========================================================================= *)
(* SPHERE3_GREAT_CIRCLE.                                                     *)
(* ========================================================================= *)

let GEOS_CIRCLE_CONTINUOUS = prove
 (`!q u:real^4.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> continuous_map (subtopology euclideanreal (:real),
                            subtopology euclidean (sphere(vec 0,&1)))
                           (\t. cos t % q + sin t % u)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; IMAGE_LIFT_UNIV] THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_IMP_DIFFERENTIABLE THEN
    MP_TAC(ISPECL [`q:real^4`; `u:real^4`; `drop x`] GEOS_CIRCLE_DERIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    ASM_SIMP_TAC[GEOS_CIRCLE_SPHERE]]);;

let SPHERE3_GREAT_CIRCLE = prove
 (`!q u:real^4.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> mfd_geodesic (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                         round3_metric (\t. cos t % q + sin t % u) (:real)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_geodesic; IS_REALINTERVAL_UNIV; REAL_OPEN_UNIV; IN_UNIV] THEN
  ASM_SIMP_TAC[GEOS_CIRCLE_CONTINUOUS] THEN
  X_GEN_TAC `c:(real^4->bool)#(real^4->real^3)` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RFB_ROUND3_LOCAL_FUN th]) THEN
  UNDISCH_TAC `(c:(real^4->bool)#(real^4->real^3)) IN sphere3_atlas` THEN
  REWRITE_TAC[RFB_SPHERE3_ATLAS_CASES] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[FST; SND; IN_DELETE] THENL
   [MP_TAC(ISPECL [`q:real^4`; `u:real^4`] GEOS_NORTH_GEODESIC);
    MP_TAC(ISPECL [`q:real^4`; `u:real^4`] GEOS_SOUTH_GEODESIC)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `V:real->real^3`) THEN
  EXISTS_TAC `V:real->real^3` THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The exponential map of the round sphere (SPHERE3_EXP):                    *)
(* exp_q v = cos |v| q + (sin |v| / |v|) D v with D the differential of the  *)
(* inclusion; the geodesic t -> cos(r t) q + sin(r t) u, u = D v / r, has    *)
(* initial velocity v and is defined on the whole line.                       *)
(* ========================================================================= *)

let GEOS_S3_BASIC = prove
 (`hausdorff_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   smooth_manifold_atlas (subtopology euclidean (sphere(vec 0:real^4,&1)))
                         sphere3_atlas /\
   riemannian_metric sphere3_atlas round3_metric /\
   compact_space (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
   topspace (subtopology euclidean (sphere(vec 0:real^4,&1))) = sphere(vec 0,&1) /\
   (!x u v. x IN topspace (subtopology euclidean (sphere(vec 0:real^4,&1))) /\
            ~collinear {vec 0,u,v}
            ==> mfd_sectional sphere3_atlas round3_metric x u v = &1)`,
  REWRITE_TAC[POINCARE_SMOOTH_HYPOTHESES_SPHERE_3; ROUND3_METRIC;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REWRITE_TAC[ROUND3_SECTIONAL]);;

(* The chart maps are differentiable and left inverse to chart_inv at the   *)
(* level of derivatives.                                                      *)

let GEOS_CHART_DERIV = prove
 (`!c x. c IN sphere3_atlas /\ x IN FST c
         ==> (SND c has_derivative frechet_derivative (SND c) (at x)) (at x) /\
             !h. frechet_derivative (SND c) (at x)
                   (frechet_derivative (chart_inv c) (at (SND c x)) h) = h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(SND (c:(real^4->bool)#(real^4->real^3)) has_derivative
     frechet_derivative (SND c) (at x)) (at x)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    UNDISCH_TAC `x IN FST (c:(real^4->bool)#(real^4->real^3))` THEN
    UNDISCH_TAC `(c:(real^4->bool)#(real^4->real^3)) IN sphere3_atlas` THEN
    REWRITE_TAC[RFB_SPHERE3_ATLAS_CASES] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[FST; SND] THEN
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `{x:real^4 | x$4 < &1}` THEN REWRITE_TAC[STEX_STEREO3_N_CHART] THEN
      MP_TAC STEX_STEREO3_N_CHART THEN ASM SET_TAC[];
      EXISTS_TAC `{x:real^4 | x$4 > -- &1}` THEN REWRITE_TAC[STEX_STEREO3_S_CHART] THEN
      MP_TAC STEX_STEREO3_S_CHART THEN ASM SET_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `h:real^3` THEN
  MP_TAC(ISPECL [`c:(real^4->bool)#(real^4->real^3)`;
                 `SND (c:(real^4->bool)#(real^4->real^3)) x`] GEOS_CHART_INV_DIFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(real^4->bool)#(real^4->real^3)) (SND c x) = x`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `c:(real^4->bool)#(real^4->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[SPHERE3_ATLAS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`chart_inv (c:(real^4->bool)#(real^4->real^3))`;
    `SND (c:(real^4->bool)#(real^4->real^3))`;
    `frechet_derivative (chart_inv (c:(real^4->bool)#(real^4->real^3)))
                        (at (SND c x))`;
    `frechet_derivative (SND (c:(real^4->bool)#(real^4->real^3))) (at x)`;
    `SND (c:(real^4->bool)#(real^4->real^3)) x`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SND (c:(real^4->bool)#(real^4->real^3)) o chart_inv c = (\y. y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[RFB_SPHERE3_CHART_FACTS];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\y:real^3. y`; `\h:real^3. h`;
    `frechet_derivative (SND (c:(real^4->bool)#(real^4->real^3))) (at x) o
     frechet_derivative (chart_inv c) (at (SND c x))`;
    `SND (c:(real^4->bool)#(real^4->real^3)) x`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
  DISCH_THEN(MP_TAC o C AP_THM `h:real^3`) THEN REWRITE_TAC[o_THM] THEN
  MESON_TAC[]);;

(* Tangent-space facts at a point q of the sphere. *)

let GEOS_S3_TANGENT = prove
 (`!q. q IN sphere(vec 0:real^4,&1)
       ==> linear(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q) /\
           (!v. mfd_tnorm round3_metric q v =
                norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v)) /\
           (!v. q dot mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                        (\y. y) q v = &0) /\
           (!v. mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v =
                vec 0 <=> v = vec 0) /\
           (SND(chart_at sphere3_atlas q) has_derivative
            frechet_derivative (SND(chart_at sphere3_atlas q)) (at q)) (at q) /\
           (!v. frechet_derivative (SND(chart_at sphere3_atlas q)) (at q)
                  (mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v) =
                v)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_CHART_AT) THEN
  REWRITE_TAC[GEOS_INCL_DIFF] THEN
  ABBREV_TAC `c = chart_at sphere3_atlas (q:real^4)` THEN
  MP_TAC(ISPECL [`c:(real^4->bool)#(real^4->real^3)`;
                 `SND (c:(real^4->bool)#(real^4->real^3)) q`] GEOS_CHART_INV_DIFF) THEN
  MP_TAC(ISPECL [`c:(real^4->bool)#(real^4->real^3)`; `q:real^4`] GEOS_CHART_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `chart_inv (c:(real^4->bool)#(real^4->real^3)) (SND c q) = q`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `c:(real^4->bool)#(real^4->real^3)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[SPHERE3_ATLAS];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[mfd_tnorm; vector_norm] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`q:real^4`; `v:real^3`; `v:real^3`] SPHERE3_ROUND_INDUCED) THEN
    ASM_REWRITE_TAC[GEOS_INCL_DIFF];
    REWRITE_TAC[GSYM DOT_EQ_0] THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
    MATCH_MP_TAC(TAUT `~p ==> (p \/ q <=> q)`) THEN
    MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN
    MP_TAC(ISPEC `SND (c:(real^4->bool)#(real^4->real^3)) q` LRG_SPH_POS) THEN
    SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC]);;

(* The chain rule for curves, and the velocity of a great circle at 0. *)

let GEOS_VDERIV_CHAIN = prove
 (`!(g:real^1->real^M) g' (Fm:real^M->real^N) Fm' t.
        (g has_vector_derivative g') (at t) /\ (Fm has_derivative Fm') (at (g t))
        ==> ((\s. Fm(g s)) has_vector_derivative Fm' g') (at t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^1->real^M`; `Fm:real^M->real^N`; `\h:real^1. drop h % (g':real^M)`;
                 `Fm':real^M->real^N`; `t:real^1`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(Fm':real^M->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL]);;

let GEOS_CIRCLE_VEL = prove
 (`!q u:real^4.
        q IN sphere(vec 0,&1)
        ==> mfd_vel sphere3_atlas (\t. cos t % q + sin t % u) (&0) =
            frechet_derivative (SND(chart_at sphere3_atlas q)) (at q) u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_vel] THEN
  REWRITE_TAC[COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MP_TAC(ISPECL
   [`\s. cos(drop s) % q + sin(drop s) % (u:real^4)`; `u:real^4`;
    `SND(chart_at sphere3_atlas (q:real^4))`;
    `frechet_derivative (SND(chart_at sphere3_atlas (q:real^4))) (at q)`;
    `lift(&0)`] GEOS_VDERIV_CHAIN) THEN
  REWRITE_TAC[LIFT_DROP; COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
              VECTOR_ADD_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`q:real^4`; `u:real^4`; `&0`] GEOS_CIRCLE_DERIV) THEN
    REWRITE_TAC[COS_0; SIN_0; REAL_NEG_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                VECTOR_ADD_LID];
    FIRST_ASSUM(MP_TAC o MATCH_MP GEOS_S3_TANGENT) THEN SIMP_TAC[]]);;

let SPHERE3_EXP = prove
 (`!q v.
        q IN sphere(vec 0:real^4,&1)
        ==> mfd_exp_dom (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                        round3_metric q = (:real^3) /\
            mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                    round3_metric q v =
            cos(mfd_tnorm round3_metric q v) % q +
            (sin(mfd_tnorm round3_metric q v) / mfd_tnorm round3_metric q v) %
            mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `q:real^4`; `v:real^3`] MFD_COMPACT_GEO_COMPLETE) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  ABBREV_TAC `D = mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                    (\y:real^4. y) q` THEN
  ABBREV_TAC `L = frechet_derivative (SND(chart_at sphere3_atlas (q:real^4))) (at q)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `v:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                   `round3_metric`; `q:real^4`] MFD_EXP_DOM) THEN
    ASM_REWRITE_TAC[GEOS_S3_BASIC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(D:real^3->real^4) (vec 0) = vec 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
    REWRITE_TAC[NORM_0; COS_0; VECTOR_MUL_RZERO; VECTOR_MUL_LID; VECTOR_ADD_RID];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm((D:real^3->real^4) v)` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `u = inv r % (D:real^3->real^4) v` THEN
  SUBGOAL_THEN `norm(u:real^4) = &1 /\ q dot u = &0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ARITH `&0 < r ==> abs r = r`;
                 REAL_MUL_LINV; REAL_LT_IMP_NZ; DOT_RMUL; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^4`; `u:real^4`] SPHERE3_GREAT_CIRCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `\t. cos t % q + sin t % (u:real^4)`; `(:real)`;
                 `r:real`; `&0`] MFD_GEODESIC_AFFINE) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC; IN_UNIV; REAL_ADD_RID;
                  SET_RULE `{t:real | T} = (:real)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_vel sphere3_atlas (\t. cos(r * t) % q + sin(r * t) % (u:real^4)) (&0) = v`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_SIMP_TAC[GEOS_CIRCLE_VEL] THEN
    EXPAND_TAC "u" THEN
    SUBGOAL_THEN `linear(L:real^4->real^3)` ASSUME_TAC THENL
     [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                 VECTOR_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `\t. cos(r * t) % q + sin(r * t) % (u:real^4)`;
                 `(:real)`; `q:real^4`; `v:real^3`] MFD_GEO_MAXIMAL_UNIQUE) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC; IN_UNIV; REAL_MUL_RZERO; COS_0; SIN_0;
                  VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  DISCH_THEN(MP_TAC o SPEC `&1` o CONJUNCT2) THEN
  REWRITE_TAC[mfd_exp; REAL_MUL_RID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "u" THEN REWRITE_TAC[VECTOR_MUL_ASSOC; real_div; REAL_MUL_SYM]);;

(* ========================================================================= *)
(* An injective smooth map of an open set of real^N with                     *)
(* injective differential everywhere is a parametrization                    *)
(* (GEOS_INJECTIVE_PARAM): the local inverses of MFD_LOCAL_PARAM agree with  *)
(* the global inverse, which is therefore continuous and smooth.              *)
(* ========================================================================= *)

let GEOS_INJECTIVE_PARAM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Fm:real^N->A) U.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        open U /\ continuous_map (subtopology euclidean U,top) Fm /\
        mfd_smooth_map (open_set_atlas (:real^N)) atlas U Fm /\
        (!v w. v IN U /\ w IN U /\ Fm v = Fm w ==> v = w) /\
        (!v h. v IN U /\
               mfd_differential (open_set_atlas (:real^N)) atlas Fm v h = vec 0
               ==> h = vec 0)
        ==> mfd_param top atlas U Fm`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. v IN U
        ==> ?V e'. open V /\ v IN V /\ V SUBSET U /\
                   mfd_diffeo euclidean (open_set_atlas (:real^N)) V top
                              (atlas:((A->bool)#(A->real^N))->bool)
                              (IMAGE (Fm:real^N->A) V) Fm e'`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `Fm:real^N->A`; `U:real^N->bool`; `v:real^N`] MFD_LOCAL_PARAM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_param] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:real^N->real^N->bool`; `E:real^N->A->real^N`] THEN
  DISCH_THEN(LABEL_TAC "loc") THEN REWRITE_TAC[mfd_param; mfd_diffeo] THEN
  ABBREV_TAC `G = \y:A. @v. v IN U /\ (Fm:real^N->A) v = y` THEN
  EXISTS_TAC `G:A->real^N` THEN
  SUBGOAL_THEN `!v. v IN U ==> (G:A->real^N) ((Fm:real^N->A) v) = v`
  (LABEL_TAC "left") THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the local pieces *)
  SUBGOAL_THEN
   `!v. v IN U
        ==> open_in top (IMAGE (Fm:real^N->A) (V v)) /\
            IMAGE Fm (V v) SUBSET IMAGE Fm U /\
            continuous_map (subtopology top (IMAGE Fm (V v)),
                            subtopology euclidean (V v)) ((E:real^N->A->real^N) v) /\
            (!y. y IN IMAGE Fm (V v) ==> E v y IN V v /\ Fm(E v y) = y) /\
            mfd_smooth_map (atlas:((A->bool)#(A->real^N))->bool) (open_set_atlas (:real^N))
                           (IMAGE Fm (V v)) (E v)`
  (LABEL_TAC "pc") THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN ASM_REWRITE_TAC[mfd_diffeo] THEN
    REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
                INTER_UNIV] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `continuous_map (subtopology top (IMAGE (Fm:real^N->A) (V(v:real^N))),
                                  subtopology euclidean (V v)) ((E:real^N->A->real^N) v)` THEN
      REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN; INTER_UNIV;
                  IN_INTER] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v y. v IN U /\ y IN IMAGE (Fm:real^N->A) (V v)
          ==> (G:A->real^N) y = (E:real^N->A->real^N) v y`
  (LABEL_TAC "agree") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `y:A` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(E:real^N->A->real^N) v y IN U` ASSUME_TAC THENL
     [USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "left" (MP_TAC o C MATCH_MP (ASSUME `(E:real^N->A->real^N) v y IN U`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (Fm:real^N->A) U)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE (Fm:real^N->A) (V(v:real^N))` THEN
    USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top (IMAGE (Fm:real^N->A) U),subtopology euclidean U)
                   (G:A->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `(z:A) IN IMAGE (Fm:real^N->A) U` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE (Fm:real^N->A) (V(v:real^N))` THEN
    USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
     [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
      EXISTS_TAC `IMAGE (Fm:real^N->A) (V(v:real^N))` THEN ASM SET_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `IMAGE (Fm:real^N->A) U INTER IMAGE Fm (V(v:real^N)) = IMAGE Fm (V v)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `(E:real^N->A->real^N) v` THEN CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN REPEAT STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `continuous_map (subtopology top (IMAGE (Fm:real^N->A) (V(v:real^N))),
                                subtopology euclidean (V v)) ((E:real^N->A->real^N) v)` THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN] THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic_maps] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                      TOPSPACE_EUCLIDEAN; INTER_UNIV; SUBSET_REFL];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      REPEAT STRIP_TAC THEN USE_THEN "left" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      AP_TERM_TAC THEN USE_THEN "left" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^N)` OPEN_SET_ATLAS) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV] THEN DISCH_TAC THEN
  MATCH_MP_TAC MFDD_SMOOTH_MAP_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `euclidean:(real^N)topology`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `continuous_map (subtopology top (IMAGE (Fm:real^N->A) U),
                                subtopology euclidean U) (G:A->real^N)` THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (Fm:real^N->A) (V(v:real^N))` THEN
  USE_THEN "pc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN
  USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(v:real^N) IN U`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MFDD_SMOOTH_MAP_EQ THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `(E:real^N->A->real^N) v`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  USE_THEN "agree" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* exp_q is injective with injective differential on the                     *)
(* tangent ball of radius pi and maps it onto the sphere minus -q            *)
(* (SPHERE3_EXP_BALL_PI); the injectivity radius is pi (MFD_INJRAD_SPHERE3). *)
(* ========================================================================= *)

let GEOS_D_INJ = prove
 (`!q v w. q IN sphere(vec 0:real^4,&1) /\
           mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v =
           mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q w
           ==> v = w`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  MP_TAC(ISPEC `mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                  (\y:real^4. y) q` LINEAR_INJECTIVE_0) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let GEOS_HYPERPLANE_IMAGE = prove
 (`!(D:real^3->real^4) q.
        linear D /\ (!x y. D x = D y ==> x = y) /\ ~(q = vec 0) /\
        (!v. q dot D v = &0)
        ==> IMAGE D (:real^3) = {x | q dot x = &0}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (D:real^3->real^4) (:real^3)`; `{x:real^4 | q dot x = &0}`]
    DIM_EQ_SPAN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`D:real^3->real^4`; `(:real^3)`] DIM_INJECTIVE_LINEAR_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[DIM_HYPERPLANE; DIM_UNIV; DIMINDEX_3; DIMINDEX_4] THEN ARITH_TAC];
    ASM_SIMP_TAC[SPAN_OF_SUBSPACE; SUBSPACE_LINEAR_IMAGE; SUBSPACE_UNIV;
                 SUBSPACE_HYPERPLANE]]);;

let GEOS_TANGENT_SURJ = prove
 (`!q w. q IN sphere(vec 0:real^4,&1) /\ q dot w = &0
         ==> ?v. mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v = w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q:real^4 = vec 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^4) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  MP_TAC(ISPECL [`mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                    (\y:real^4. y) q`; `q:real^4`] GEOS_HYPERPLANE_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOS_D_INJ THEN
    EXISTS_TAC `q:real^4` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^4`) THEN ASM_MESON_TAC[]]);;

(* The explicit exponential map in terms of the Euclidean norm of D v. *)

let GEOS_EXP_FORMULA = prove
 (`!q v. q IN sphere(vec 0:real^4,&1)
         ==> mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                     round3_metric q v =
             cos(norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                        (\y. y) q v)) % q +
             (sin(norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                         (\y. y) q v)) /
              norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                     (\y. y) q v)) %
             mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SPHERE3_EXP] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  ASM_REWRITE_TAC[]);;

let GEOS_EXP_DOTQ = prove
 (`!q v. q IN sphere(vec 0:real^4,&1)
         ==> q dot mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                           round3_metric q v =
             cos(norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                        (\y. y) q v))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GEOS_EXP_FORMULA] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  UNDISCH_TAC `(q:real^4) IN sphere(vec 0,&1)` THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN SIMP_TAC[REAL_MUL_RID]);;

let GEOS_EXP_INJ = prove
 (`!q v w.
        q IN sphere(vec 0:real^4,&1) /\
        norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v) < pi /\
        norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q w) < pi /\
        mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas) round3_metric q v =
        mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas) round3_metric q w
        ==> v = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  MAP_EVERY (fun t -> MP_TAC(ISPECL [`q:real^4`; t] GEOS_EXP_FORMULA))
    [`v:real^3`; `w:real^3`] THEN
  MAP_EVERY (fun t -> MP_TAC(ISPECL [`q:real^4`; t] GEOS_EXP_DOTQ))
    [`v:real^3`; `w:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `D = mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                    (\y:real^4. y) q` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `norm((D:real^3->real^4) v) = norm(D w)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_INJ_PI THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOS_D_INJ THEN EXISTS_TAC `q:real^4` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `norm((D:real^3->real^4) v) = &0` THENL
   [SUBGOAL_THEN `norm((D:real^3->real^4) w) = &0` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `norm((D:real^3->real^4) v) = &0` THEN
    REWRITE_TAC[NORM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = norm((D:real^3->real^4) w)` THEN
  SUBGOAL_THEN `&0 < r /\ r < pi` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sin r / r = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[SIN_POS_PI];
    ALL_TAC] THEN
  SUBGOAL_THEN `cos r % q + (sin r / r) % (D:real^3->real^4) v =
                cos r % q + (sin r / r) % D w`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]);;

(* ========================================================================= *)
(* The image of the open tangent ball of radius pi, the                      *)
(* nonsingularity of d(exp_q) there (from MFD_EXP_DIFFERENTIAL_CONST1),      *)
(* SPHERE3_EXP_BALL_PI and MFD_INJRAD_SPHERE3.                               *)
(* ========================================================================= *)

let GEOS_EXP_IN_SPHERE = prove
 (`!q v. q IN sphere(vec 0:real^4,&1)
         ==> mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                     round3_metric q v IN sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GEOS_EXP_FORMULA] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  SUBGOAL_THEN `(q:real^4) dot q = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^4) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1];
    ALL_TAC] THEN
  ABBREV_TAC `D = mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                    (\y:real^4. y) q` THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1] THEN
  ASM_CASES_TAC `(D:real^3->real^4) v = vec 0` THENL
   [ASM_REWRITE_TAC[NORM_0; COS_0; VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(D:real^3->real^4) v dot q = &0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL] THEN
  ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN
  SUBGOAL_THEN `~(norm((D:real^3->real^4) v) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  MP_TAC(SPEC `norm((D:real^3->real^4) v)` SIN_CIRCLE) THEN CONV_TAC REAL_FIELD);;

let GEOS_EXP_ANTIPODAL = prove
 (`!q v. q IN sphere(vec 0:real^4,&1) /\
         norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v) = pi
         ==> mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                     round3_metric q v = --q`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GEOS_EXP_FORMULA] THEN
  REWRITE_TAC[COS_PI; SIN_PI; real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO;
              VECTOR_ADD_RID] THEN
  VECTOR_ARITH_TAC);;

(* The real arithmetic behind the nonsingularity of d(exp_q). *)

let GEOS_REAL_NONSING = prove
 (`!a nv nh s.
        &0 < nv /\ &0 < s /\ &0 <= nh /\ abs a <= nv * nh /\
        (a / nv) pow 2 + s pow 2 * (nh pow 2 - (a / nv) pow 2) = &0
        ==> nh = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a / nv) pow 2 <= nh pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_DIV; REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < x ==> abs x = x`;
                 REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s pow 2 * (nh pow 2 - (a / nv) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `a / nv` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `s pow 2 * (nh pow 2 - (a / nv) pow 2) = &0 /\ (a / nv) pow 2 = &0`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `s pow 2 * (nh pow 2 - (a / nv) pow 2) = &0` THEN
  ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_RZERO; ARITH_EQ] THEN
  ASM_MESON_TAC[REAL_LT_IMP_NZ]);;

let GEOS_TNORM_ZERO = prove
 (`!(g:A->real^N^N) x. mfd_tnorm g x (vec 0) = &0`,
  REWRITE_TAC[mfd_tnorm; MATRIX_VECTOR_MUL_RZERO; DOT_LZERO; SQRT_0]);;

let GEOS_EXP_NONSING = prove
 (`!q v h.
        q IN sphere(vec 0:real^4,&1) /\
        norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y. y) q v) < pi /\
        mfd_differential (open_set_atlas (:real^3)) sphere3_atlas
          (mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                   round3_metric q) v h = vec 0
        ==> h = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `q:real^4`; `v:real^3`; `h:real^3`]
    MFD_EXP_DIFFERENTIAL_CONST1) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[SPHERE3_EXP; IN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[GEOS_TNORM_ZERO] THEN ASM_SIMP_TAC[SPHERE3_ROUND_INDUCED] THEN
  ABBREV_TAC `D = mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                    (\y:real^4. y) q` THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ] THEN
  COND_CASES_TAC THENL
   [DISCH_THEN(ASSUME_TAC o SYM) THEN
    SUBGOAL_THEN `norm((D:real^3->real^4) h) = &0` MP_TAC THENL
     [UNDISCH_TAC `norm((D:real^3->real^4) h) pow 2 = &0` THEN CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[NORM_EQ_0]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN SUBGOAL_THEN `norm((D:real^3->real^4) h) = &0` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[NORM_EQ_0]] THEN
  MATCH_MP_TAC GEOS_REAL_NONSING THEN
  MAP_EVERY EXISTS_TAC
   [`(D:real^3->real^4) v dot D h`; `norm((D:real^3->real^4) v)`;
    `sin(norm((D:real^3->real^4) v)) / norm(D v)`] THEN
  SUBGOAL_THEN `&0 < norm((D:real^3->real^4) v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_POS_LE; NORM_CAUCHY_SCHWARZ_ABS] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[SIN_POS_PI]);;

(* ========================================================================= *)
(* The image of the tangent ball of radius pi is the sphere                  *)
(* minus -q; SPHERE3_EXP_BALL_PI and MFD_INJRAD_SPHERE3.                      *)
(* ========================================================================= *)

let GEOS_EXP_IMAGE = prove
 (`!q. q IN sphere(vec 0:real^4,&1)
       ==> IMAGE (mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                          round3_metric q)
                 {v | norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                             (\y. y) q v) < pi} =
           sphere(vec 0,&1) DELETE --q`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  SUBGOAL_THEN `(q:real^4) dot q = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^4) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_DELETE] THEN
  X_GEN_TAC `p:real^4` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[GEOS_EXP_IN_SPHERE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`q:real^4`; `v:real^3`] GEOS_EXP_DOTQ) THEN
    ASM_REWRITE_TAC[DOT_RNEG] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4)) (\y:real^4. y) q v) =
      pi`
    MP_TAC THENL
     [MATCH_MP_TAC COS_INJ_PI THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE; PI_POS_LE; REAL_LE_REFL; COS_PI] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN
  ABBREV_TAC `D = mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                    (\y:real^4. y) q` THEN
  ASM_CASES_TAC `p:real^4 = q` THENL
   [EXISTS_TAC `vec 0:real^3` THEN
    MP_TAC(ISPECL [`q:real^4`; `vec 0:real^3`] GEOS_EXP_FORMULA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(D:real^3->real^4) (vec 0) = vec 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
    REWRITE_TAC[NORM_0; COS_0; VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                PI_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^4) dot p = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^4) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1];
    ALL_TAC] THEN
  ABBREV_TAC `c = (q:real^4) dot p` THEN
  SUBGOAL_THEN `(p:real^4) dot q = c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) < c /\ c < &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `abs c <= &1 /\ ~(c = &1) /\ ~(c = --(&1))` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "c" THEN MP_TAC(ISPECL [`q:real^4`; `p:real^4`] NORM_CAUCHY_SCHWARZ_ABS) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0]) THEN ASM_REWRITE_TAC[REAL_MUL_LID];
        DISCH_TAC THEN UNDISCH_TAC `~(p:real^4 = q)` THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
        REWRITE_TAC[GSYM DOT_EQ_0; DOT_LSUB; DOT_RSUB] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        DISCH_TAC THEN UNDISCH_TAC `~(p:real^4 = --q)` THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
        REWRITE_TAC[VECTOR_ARITH `x - --y:real^N = x + y`; GSYM DOT_EQ_0;
                    DOT_LADD; DOT_RADD] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `w = p - c % (q:real^4)` THEN
  SUBGOAL_THEN `(q:real^4) dot w = &0 /\ w dot w = &1 - c pow 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^4`; `w:real^4`] GEOS_TANGENT_SURJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v0:real^3`) THEN
  SUBGOAL_THEN `&0 < acs c /\ acs c < pi /\ cos(acs c) = c /\ sin(acs c) = norm(w:real^4)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ACS_BOUNDS_LT; COS_ACS; SIN_ACS; REAL_LT_IMP_LE] THEN
    ASM_REWRITE_TAC[vector_norm];
    ALL_TAC] THEN
  ABBREV_TAC `r = acs c` THEN
  SUBGOAL_THEN `&0 < norm(w:real^4)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIN_POS_PI]; ALL_TAC] THEN
  EXISTS_TAC `(r / norm(w:real^4)) % (v0:real^3)` THEN
  SUBGOAL_THEN
   `(D:real^3->real^4) ((r / norm(w:real^4)) % (v0:real^3)) = (r / norm w) % w`
  ASSUME_TAC THENL [ASM_SIMP_TAC[LINEAR_CMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((r / norm(w:real^4)) % w) = r` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`; REAL_DIV_RMUL;
                 REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`q:real^4`; `(r / norm(w:real^4)) % (v0:real^3)`] GEOS_EXP_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN `norm(w:real^4) / r * r / norm w = &1` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(w:real^4)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  UNDISCH_TAC `(p:real^4) - c % q = w` THEN VECTOR_ARITH_TAC);;

let SPHERE3_EXP_BALL_PI = prove
 (`!q.
        q IN sphere(vec 0:real^4,&1)
        ==> mfd_inj_ball (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                         round3_metric q pi /\
            IMAGE (mfd_exp (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                           round3_metric q)
                  (mfd_tball round3_metric q pi) =
            sphere(vec 0,&1) DELETE --q`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  SUBGOAL_THEN
   `mfd_tball round3_metric q pi =
    {v | norm(mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                (\y:real^4. y) q v) < pi}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[mfd_tball]; ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^4`; `vec 0:real^3`] SPHERE3_EXP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[GEOS_EXP_IMAGE] THEN REWRITE_TAC[mfd_inj_ball] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC GEOS_INJECTIVE_PARAM THEN REWRITE_TAC[GEOS_S3_BASIC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `q:real^4`] MFD_EXP_SMOOTH) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`round3_metric`; `q:real^4`; `pi`] GEOI_TBALL_OPEN) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN
    EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GEOS_EXP_INJ THEN EXISTS_TAC `q:real^4` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC GEOS_EXP_NONSING THEN
    MAP_EVERY EXISTS_TAC [`q:real^4`; `v:real^3`] THEN ASM_REWRITE_TAC[]]);;

let MFD_INJRAD_SPHERE3 = prove
 (`!q. q IN sphere(vec 0:real^4,&1)
       ==> mfd_injrad (subtopology euclidean (sphere(vec 0,&1)),sphere3_atlas)
                      round3_metric q = pi`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mfd_injrad] THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN EXISTS_TAC `pi` THEN
    ASM_SIMP_TAC[PI_POS; SPHERE3_EXP_BALL_PI]] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  UNDISCH_TAC `mfd_inj_ball (subtopology euclidean (sphere(vec 0:real^4,&1)),sphere3_atlas)
                            round3_metric q r` THEN
  REWRITE_TAC[mfd_inj_ball; mfd_param; mfd_diffeo; homeomorphic_maps;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `e':real^4->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `D = mfd_differential sphere3_atlas (open_set_atlas (:real^4))
                    (\y:real^4. y) q` THEN
  SUBGOAL_THEN `~((D:real^3->real^4) (basis 1) = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((D:real^3->real^4) ((pi / norm(D (basis 1))) % basis 1)) = pi /\
    norm(D(--((pi / norm(D (basis 1))) % basis 1))) = pi`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_NEG; NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_PI; REAL_ABS_NORM; REAL_DIV_RMUL; NORM_EQ_0];
    ALL_TAC] THEN
  ABBREV_TAC `v0 = (pi / norm((D:real^3->real^4) (basis 1))) % (basis 1:real^3)` THEN
  SUBGOAL_THEN `v0 IN mfd_tball round3_metric q r /\ --v0 IN mfd_tball round3_metric q r`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_tball; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `v0:real^3 = --v0` MP_TAC THENL
   [MP_TAC(ISPECL [`q:real^4`; `v0:real^3`] GEOS_EXP_ANTIPODAL) THEN
    MP_TAC(ISPECL [`q:real^4`; `--v0:real^3`] GEOS_EXP_ANTIPODAL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `v:real^N = --v <=> v = vec 0`] THEN DISCH_TAC THEN
  UNDISCH_TAC `norm((D:real^3->real^4) v0) = pi` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(D:real^3->real^4) (vec 0) = vec 0` SUBST1_TAC THENL
   [ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
  REWRITE_TAC[NORM_0] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Antipodal points are conjugate along great circles                        *)
(* (MFD_CONJUGATE_SPHERE3_PI): Y t = sin t E t with E a parallel field        *)
(* orthogonal to the unit velocity is a Jacobi field (MFD_JACOBI_CONST1)      *)
(* vanishing at 0 and pi but not at pi / 2.                                   *)
(* ========================================================================= *)

let GEOS_CIRCLE_UNIT_SPEED = prove
 (`!q u:real^4.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> mfd_tnorm round3_metric q
              (mfd_vel sphere3_atlas (\t. cos t % q + sin t % u) (&0)) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^4) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[GEOS_CIRCLE_VEL] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP GEOS_S3_TANGENT) THEN
  MP_TAC(ISPECL [`q:real^4`; `u:real^4`] GEOS_TANGENT_SURJ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (SUBST_ALL_TAC o SYM)) THEN
  ASM_REWRITE_TAC[]);;

let MFD_CONJUGATE_SPHERE3_PI = prove
 (`!q u:real^4.
        norm q = &1 /\ norm u = &1 /\ q dot u = &0
        ==> mfd_conjugate sphere3_atlas round3_metric (\t. cos t % q + sin t % u)
                          (:real) (&0) pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q:real^4) IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SPHERE_0]; ALL_TAC] THEN
  REWRITE_TAC[mfd_conjugate; IN_UNIV] THEN
  CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^4`; `u:real^4`] SPHERE3_GREAT_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `\t. cos t % q + sin t % (u:real^4)`; `(:real)`]
    CMPG_GEODESIC_C1) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `mfd_vel sphere3_atlas (\t. cos t % q + sin t % (u:real^4)) (&0)`
    ORTHOGONAL_TO_VECTOR_EXISTS) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH; orthogonal] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `\t. cos t % q + sin t % (u:real^4)`; `(:real)`;
                 `&0`; `e0:real^3`] MFD_PARALLEL_EXISTS_UNIQUE) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC; IN_UNIV; REAL_OPEN_UNIV; IS_REALINTERVAL_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `E:real->real^3`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `\t. cos t % q + sin t % (u:real^4)`; `(:real)`;
                 `E:real->real^3`; `&0`; `&1`; `&0`] MFD_JACOBI_CONST1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GEOS_S3_BASIC; IN_UNIV] THEN
    REWRITE_TAC[COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[round3_metric; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
    ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ASM_SIMP_TAC[GEOS_CIRCLE_UNIT_SPEED] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_SUB_RZERO; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  DISCH_TAC THEN EXISTS_TAC `\t. sin t % (E:real->real^3) t` THEN
  ASM_REWRITE_TAC[SIN_0; SIN_PI; VECTOR_MUL_LZERO] THEN
  EXISTS_TAC `pi / &2` THEN REWRITE_TAC[SIN_PI2; VECTOR_MUL_LID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^4,&1))`; `sphere3_atlas`;
                 `round3_metric`; `\t. cos t % q + sin t % (u:real^4)`; `(:real)`;
                 `E:real->real^3`; `E:real->real^3`; `pi / &2`; `&0`]
    MFD_PARALLEL_INNER) THEN
  ASM_REWRITE_TAC[GEOS_S3_BASIC; IN_UNIV; REAL_OPEN_UNIV; IS_REALINTERVAL_UNIV] THEN
  REWRITE_TAC[DOT_LZERO; COS_0; SIN_0; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
              VECTOR_ADD_RID] THEN
  REWRITE_TAC[round3_metric; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(&0 = x)`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[DOT_POS_LT] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_POW_LT THEN
  MP_TAC(ISPEC `SND(chart_at sphere3_atlas (q:real^4)) q` LRG_SPH_POS) THEN
  REAL_ARITH_TAC);;

