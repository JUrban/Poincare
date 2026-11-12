(* ========================================================================= *)
(* Unit pc_p2a_wk5: the nonlinear barrier principle (P2AW_NBP).  Pure        *)
(* analysis on real^M.  A locally Lipschitz u that is semiconcave along      *)
(* finitely many directions e_k and has, at almost every point x, a smooth   *)
(* upper barrier psi with sum_k (W_k psi_e)_e (x) <= F(x) (W_k >= 0 smooth)  *)
(* satisfies the weak inequality                                             *)
(*   int phi F + sum_k W_k (D_e u)(D_e phi) >= 0                             *)
(* for every nonnegative test phi.  The proof uses the discrete              *)
(* divergence-form operator p2aw_dq, exact summation by parts (translation   *)
(* invariance), its uniform consistency on smooth functions, dominated       *)
(* convergence for the positive part, and integration by parts for Lipschitz *)
(* functions (WAN_LIP_IBP).                                                  *)
(*                                                                           *)
(* First: definitions, translation and summation by parts.                   *)
(* ========================================================================= *)

needs "src/pc_wan_weak.ml";;
needs "src/ns_smooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* The discrete divergence-form operator along e with weight w and step h: *)
(*   (w(z + h e/2) (f(z + h e) - f z) + w(z - h e/2) (f(z - h e) - f z))/h^2 *)
(* (the finite-difference form of D_e (w D_e f)), and the first and second  *)
(* directional derivatives along e.                                          *)

let p2aw_dq = new_definition
 `p2aw_dq (w:real^M->real) (e:real^M) (h:real) (f:real^M->real) (z:real^M) =
    (w(z + (h / &2) % e) * (f(z + h % e) - f z) +
     w(z - (h / &2) % e) * (f(z - h % e) - f z)) / h pow 2`;;

let p2aw_d1 = new_definition
 `p2aw_d1 (f:real^M->real) (e:real^M) (x:real^M) =
    drop(frechet_derivative (\y. lift(f y)) (at x) e)`;;

let p2aw_d2 = new_definition
 `p2aw_d2 (f:real^M->real) (e:real^M) (x:real^M) =
    drop(frechet_derivative (\y. frechet_derivative (\z. lift(f z)) (at y) e) (at x) e)`;;

let p2aw_dlim = new_definition
 `p2aw_dlim (w:real^M->real) (e:real^M) (f:real^M->real) (x:real^M) =
    w x * p2aw_d2 f e x + p2aw_d1 w e x * p2aw_d1 f e x`;;

let P2AW_INTEGRAL_SHIFT = prove
 (`!(g:real^M->real) c.
     integral (:real^M) (\x. lift(g(x + c))) = integral (:real^M) (\x. lift(g x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\x:real^M. lift((g:real^M->real) x)`; `(:real^M)`; `c:real^M`]
                INTEGRAL_TRANSLATION) THEN
  REWRITE_TAC[TRANSLATION_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);;

let P2AW_CONT_SHIFT = prove
 (`!(f:real^M->real) c.
     (\x. lift(f x)) continuous_on (:real^M)
     ==> (\x. lift(f(x + c))) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^M. lift((f:real^M->real) x)`; `c:real^M`] WAN_CONT_TRANSLATE) THEN
  ASM_REWRITE_TAC[]);;

(* A product with a continuous factor of compact support is integrable on   *)
(* the whole space.                                                          *)

let P2AW_CONT_SUPPORT_INT = prove
 (`!(f:real^M->real) k.
     (\x. lift(f x)) continuous_on (:real^M) /\ compact k /\ (!x. ~(x IN k) ==> f x = &0)
     ==> (\x. lift(f x)) integrable_on (:real^M)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_CONT_SUPPORT_INTEGRABLE THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[LIFT_NUM]);;

(* Summation by parts for the discrete operator: for continuous w, f and a *)
(* continuous phi of compact support,                                        *)
(*   int phi (dq w e h f) = int f (dq w e h phi)                            *)
(* (both integrands are integrable).  The cross terms are exchanged by the  *)
(* translations z -> z + h e and z -> z - h e.                              *)

let P2AW_DQ_SBP = prove
 (`!(w:real^M->real) e h f phi k.
     (\x. lift(w x)) continuous_on (:real^M) /\ (\x. lift(f x)) continuous_on (:real^M) /\
     (\x. lift(phi x)) continuous_on (:real^M) /\ compact k /\
     (!x. ~(x IN k) ==> phi x = &0)
     ==> (\z. lift(phi z * p2aw_dq w e h f z)) integrable_on (:real^M) /\
         (\z. lift(f z * p2aw_dq w e h phi z)) integrable_on (:real^M) /\
         integral (:real^M) (\z. lift(phi z * p2aw_dq w e h f z)) =
         integral (:real^M) (\z. lift(f z * p2aw_dq w e h phi z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2aw_dq] THEN
  ABBREV_TAC `c:real^M = h % e` THEN ABBREV_TAC `c2:real^M = (h / &2) % e` THEN
  SUBGOAL_THEN `!z:real^M. (z + c) - c2 = z + c2 /\ (z + --c) + c2 = z - c2 /\
                           (z + c) - c = z /\ (z + --c) + c = z`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c"; "c2"] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((w:real^M->real)(z + c2))) continuous_on (:real^M) /\
    (\z. lift(w(z + --c2))) continuous_on (:real^M) /\
    (\z. lift((f:real^M->real)(z + c))) continuous_on (:real^M) /\
    (\z. lift(f(z + --c))) continuous_on (:real^M) /\
    (\z. lift((phi:real^M->real)(z + c))) continuous_on (:real^M) /\
    (\z. lift(phi(z + --c))) continuous_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC P2AW_CONT_SHIFT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM VECTOR_SUB]) THEN
  SUBGOAL_THEN
   `(\z. lift((phi:real^M->real) z * w(z + c2) * f(z + c))) integrable_on (:real^M) /\
    (\z. lift(phi z * w(z + c2) * f z)) integrable_on (:real^M) /\
    (\z. lift(phi z * w(z - c2) * f(z - c))) integrable_on (:real^M) /\
    (\z. lift(phi z * w(z - c2) * f z)) integrable_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC P2AW_CONT_SUPPORT_INT THEN
    EXISTS_TAC `k:real^M->bool` THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; WAN_CONT_LIFT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((f:real^M->real) z * w(z + c2) * phi(z + c))) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CONT_SUPPORT_INT THEN
    EXISTS_TAC `IMAGE (\x:real^M. --c + x) k` THEN
    ASM_SIMP_TAC[COMPACT_TRANSLATION; WAN_CONT_LIFT_MUL] THEN
    X_GEN_TAC `z:real^M` THEN REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z + c:real^M`) THEN
    REWRITE_TAC[VECTOR_ARITH `z:real^M = --c + z + c`] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((f:real^M->real) z * w(z - c2) * phi(z - c))) integrable_on (:real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CONT_SUPPORT_INT THEN
    EXISTS_TAC `IMAGE (\x:real^M. c + x) k` THEN
    ASM_SIMP_TAC[COMPACT_TRANSLATION; WAN_CONT_LIFT_MUL] THEN
    X_GEN_TAC `z:real^M` THEN REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z - c:real^M`) THEN
    REWRITE_TAC[VECTOR_ARITH `z:real^M = c + z - c`] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^M) (\z. lift((phi:real^M->real) z * w(z + c2) * f(z + c))) =
    integral (:real^M) (\z. lift(f z * w(z - c2) * phi(z - c))) /\
    integral (:real^M) (\z. lift(phi z * w(z - c2) * f(z - c))) =
    integral (:real^M) (\z. lift(f z * w(z + c2) * phi(z + c)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
        [`\z:real^M. (f:real^M->real) z * w(z - c2) * phi(z - c)`; `c:real^M`]
        P2AW_INTEGRAL_SHIFT));
      MP_TAC(BETA_RULE(ISPECL
        [`\z:real^M. (f:real^M->real) z * w(z + c2) * phi(z + c)`; `--c:real^M`]
        P2AW_INTEGRAL_SHIFT))] THEN
    REWRITE_TAC[GSYM VECTOR_SUB] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; LIFT_EQ] THEN GEN_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. lift((phi:real^M->real) z *
              (w(z + c2) * (f(z + c) - f z) + w(z - c2) * (f(z - c) - f z)) / h pow 2)) =
    (\z. inv(h pow 2) %
         ((lift(phi z * w(z + c2) * f(z + c)) - lift(phi z * w(z + c2) * f z)) +
          (lift(phi z * w(z - c2) * f(z - c)) - lift(phi z * w(z - c2) * f z)))) /\
    (\z. lift(f z *
              (w(z + c2) * (phi(z + c) - phi z) + w(z - c2) * (phi(z - c) - phi z)) / h pow 2)) =
    (\z. inv(h pow 2) %
         ((lift(f z * w(z + c2) * phi(z + c)) - lift(phi z * w(z + c2) * f z)) +
          (lift(f z * w(z - c2) * phi(z - c)) - lift(phi z * w(z - c2) * f z))))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_SUB; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REWRITE_TAC[real_div] THEN CONJ_TAC THEN GEN_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRABLE_ADD; INTEGRABLE_SUB; INTEGRAL_CMUL; INTEGRAL_ADD;
               INTEGRAL_SUB] THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* One-variable estimates: the second-order Taylor bound with a modulus B  *)
(* for the second derivative (from REAL_TAYLOR with n = 1).                 *)
(* ========================================================================= *)

let P2AW_QUAD_DERIV = prove
 (`!c x. ((\x. c * x pow 2 / &2) has_real_derivative c * x) (atreal x) /\
         ((\x. c * x) has_real_derivative c) (atreal x)`,
  REPEAT GEN_TAC THEN CONJ_TAC THEN REAL_DIFF_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let P2AW_TAYLOR2 = prove
 (`!(p:real->real) p1 p2 r B.
     (!t. abs t <= r ==> (p has_real_derivative p1 t) (atreal t) /\
                         (p1 has_real_derivative p2 t) (atreal t)) /\
     (!t. abs t <= r ==> abs(p2 t - p2(&0)) <= B)
     ==> !t. abs t <= r
             ==> abs(p t - p(&0) - p1(&0) * t - p2(&0) * t pow 2 / &2) <= B * t pow 2 / &2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "D") (LABEL_TAC "B")) THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\i:num. if i = 0 then (\x. (p:real->real) x - p2(&0) * x pow 2 / &2)
                          else if i = 1 then (\x. (p1:real->real) x - p2(&0) * x)
                          else (\x. (p2:real->real) x - p2(&0))`;
                 `1`; `real_interval[--r,r]`; `B:real`] REAL_TAYLOR) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `x:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SUBGOAL_THEN `abs x <= r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "D" (STRIP_ASSUME_TAC o C MP (ASSUME `abs x <= r`) o SPEC `x:real`) THEN
      SUBGOAL_THEN `i = 0 \/ i = 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[P2AW_QUAD_DERIV];
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN USE_THEN "B" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`&0`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ONE; SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[FACT; REAL_SUB_RZERO; real_pow; REAL_POW_1; REAL_ABS_POW; REAL_POW2_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> abs x <= b ==> abs y <= b`) THEN
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The consistency estimate of the one-dimensional discrete                  *)
(* operator.  For p, q twice differentiable on [-r,r] with bounds M and a   *)
(* modulus B for p'':                                                        *)
(*   |(q(h/2)(p(h) - p(0)) + q(-h/2)(p(-h) - p(0)))/h^2 - (q p'' + q' p')(0)| *)
(*      <= 6 M^2 |h| + M B   (0 < |h| <= min(r,1), B <= 2 M).                *)
(* The quotient is split as X Y + C D with X = (q(h/2) - q(-h/2))/h,        *)
(* Y = (p(h) - p(0))/h, C = q(-h/2), D the second difference of p.          *)
(* ========================================================================= *)

let P2AW_PROD_ERR = prove
 (`!x x0 y y0 ex ey X0 Y0.
     abs(x - x0) <= ex /\ abs(y - y0) <= ey /\ abs x0 <= X0 /\ abs y0 <= Y0
     ==> abs(x * y - x0 * y0) <= ex * (Y0 + ey) + X0 * ey`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x * y - x0 * y0 = (x - x0) * y + x0 * (y - y0)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs a <= u /\ abs b <= v ==> abs(a + b) <= u + v`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REAL_ARITH_TAC);;

let P2AW_DIV_BOUND = prove
 (`!x h c. &0 < abs h /\ abs x <= c * h pow 2
           ==> abs(x / h) <= c * abs h /\ abs(x / h pow 2) <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ abs h * abs h = h pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_POW_2; REAL_POW_2; GSYM REAL_ABS_MUL; REAL_ABS_REFL;
                REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_ABS_POW; REAL_POW2_ABS] THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]);;

let P2AW_DIV_BOUND1 = prove
 (`!x h c. &0 < abs h /\ abs x <= c * h pow 2 ==> abs(x / h) <= c * abs h`,
  MESON_TAC[P2AW_DIV_BOUND]);;

let P2AW_DIV_BOUND2 = prove
 (`!x h c. &0 < abs h /\ abs x <= c * h pow 2 ==> abs(x / h pow 2) <= c`,
  MESON_TAC[P2AW_DIV_BOUND]);;

let P2AW_DQ_1D = prove
 (`!(p:real->real) p1 p2 q q1 q2 r M B h.
     (!t. abs t <= r ==> (p has_real_derivative p1 t) (atreal t) /\
                         (p1 has_real_derivative p2 t) (atreal t) /\
                         (q has_real_derivative q1 t) (atreal t) /\
                         (q1 has_real_derivative q2 t) (atreal t)) /\
     (!t. abs t <= r
          ==> abs(p2 t) <= M /\ abs(q t) <= M /\ abs(q1 t) <= M /\ abs(q2 t) <= M) /\
     abs(p1(&0)) <= M /\
     (!t. abs t <= r ==> abs(p2 t - p2(&0)) <= B) /\ B <= &2 * M /\
     &0 < abs h /\ abs h <= r /\ abs h <= &1
     ==> abs((q(h / &2) * (p h - p(&0)) + q(--(h / &2)) * (p(--h) - p(&0))) / h pow 2 -
             (q(&0) * p2(&0) + q1(&0) * p1(&0))) <= &6 * M pow 2 * abs h + M * B`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= r /\ &0 <= M /\ &0 <= B` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (find_term ((=) `p2:real->real`)) (concl th) &&
                               is_forall (concl th) &&
                               can (find_term ((=) `B:real`)) (concl th)
                            then MP_TAC(SPEC `&0` th) else failwith "") THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th ->
       is_forall(concl th) && can (find_term ((=) `M:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(h = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Taylor bounds for p at h and -h, for q at h/2 and -h/2. *)
  MP_TAC(ISPECL [`p:real->real`; `p1:real->real`; `p2:real->real`; `r:real`; `B:real`]
                P2AW_TAYLOR2) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `h:real` th) THEN MP_TAC(SPEC `--h:real` th)) THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
  REWRITE_TAC[REAL_ARITH `(--h) pow 2 = h pow 2`] THEN
  DISCH_THEN(LABEL_TAC "E2") THEN DISCH_THEN(LABEL_TAC "E1") THEN
  MP_TAC(ISPECL [`q:real->real`; `q1:real->real`; `q2:real->real`; `r:real`; `&2 * M`]
                P2AW_TAYLOR2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `M:real`)) (concl th)
                            then MP_TAC(SPEC `t:real` th) THEN MP_TAC(SPEC `&0` th)
                            else failwith "") THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `h / &2` th) THEN MP_TAC(SPEC `--(h / &2)` th)) THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ARITH `(--x) pow 2 = x pow 2`] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "E4")] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "E3")] THEN
  (* The algebraic split. *)
  ABBREV_TAC `X = (q(h / &2) - q(--(h / &2))) / h` THEN
  ABBREV_TAC `Y = (p h - p(&0)) / h` THEN
  ABBREV_TAC `D = ((p h - p(&0)) + (p(--h) - p(&0))) / h pow 2` THEN
  SUBGOAL_THEN
   `(q(h / &2) * (p h - p(&0)) + q(--(h / &2)) * (p(--h) - p(&0))) / h pow 2 =
    X * Y + q(--(h / &2)) * D`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"; "D"] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `h = &0` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Error bounds of the four factors. *)
  SUBGOAL_THEN `abs(X - q1(&0)) <= M / &2 * abs h` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN `(q(h / &2) - q(--(h / &2))) / h - q1(&0) =
                  ((q(h / &2) - q(&0) - q1(&0) * h / &2 - q2(&0) * (h / &2) pow 2 / &2) -
                   (q(--(h / &2)) - q(&0) - q1(&0) * --(h / &2) -
                    q2(&0) * (h / &2) pow 2 / &2)) / h`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(h = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC P2AW_DIV_BOUND1 THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "E3" MP_TAC THEN REMOVE_THEN "E4" MP_TAC THEN
    REWRITE_TAC[REAL_ARITH `(h / &2) pow 2 = h pow 2 / &4`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(Y - p1(&0)) <= (M + B) / &2 * abs h` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN
    SUBGOAL_THEN `(p h - p(&0)) / h - p1(&0) =
                  ((p h - p(&0) - p1(&0) * h - p2(&0) * h pow 2 / &2) +
                   p2(&0) * h pow 2 / &2) / h`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(h = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC P2AW_DIV_BOUND1 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(p2(&0)) <= M` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `M:real`)) (concl th)
                              then MP_TAC(SPEC `&0` th) else failwith "") THEN
      ASM_REWRITE_TAC[REAL_ABS_NUM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "E1" MP_TAC THEN
    SUBGOAL_THEN `&0 <= h pow 2` MP_TAC THENL [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SPEC_TAC(`h pow 2`,`hh:real`) THEN GEN_TAC THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `abs(p2(&0) * hh) <= M * hh` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 <= hh ==> abs hh = hh`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(q(--(h / &2)) - q(&0)) <= M * abs h` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`q:real->real`; `q1:real->real`; `real_interval[--r,r]`; `M:real`]
                  REAL_DIFFERENTIABLE_BOUND) THEN
    REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN ANTS_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `abs t <= r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      DISCH_THEN(MP_TAC o SPECL [`--(h / &2)`; `&0`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_RZERO; REAL_ABS_NEG; REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(D - p2(&0)) <= B` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    SUBGOAL_THEN `((p h - p(&0)) + (p(--h) - p(&0))) / h pow 2 - p2(&0) =
                  ((p h - p(&0) - p1(&0) * h - p2(&0) * h pow 2 / &2) +
                   (p(--h) - p(&0) - p1(&0) * --h - p2(&0) * h pow 2 / &2)) / h pow 2`
    SUBST1_TAC THENL
     [UNDISCH_TAC `~(h = &0)` THEN REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC P2AW_DIV_BOUND2 THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "E1" MP_TAC THEN REMOVE_THEN "E2" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* Combination. *)
  SUBGOAL_THEN `abs(q1(&0)) <= M /\ abs(q(&0)) <= M /\ abs(p2(&0)) <= M` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `M:real`)) (concl th)
                            then MP_TAC(SPEC `&0` th) else failwith "") THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real`; `q1(&0):real`; `Y:real`; `p1(&0):real`;
                 `M / &2 * abs h`; `(M + B) / &2 * abs h`; `M:real`; `M:real`]
                P2AW_PROD_ERR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q(--(h / &2)):real`; `q(&0):real`; `D:real`; `p2(&0):real`;
                 `M * abs h`; `B:real`; `M:real`; `M:real`] P2AW_PROD_ERR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `M * M * abs h * abs h <= M * M * abs h /\
                M * B * abs h * abs h <= M * B * abs h /\
                M * B * abs h <= &2 * M * M * abs h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x * y <= x * &1 ==> x * y <= x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS];
      MATCH_MP_TAC(REAL_ARITH `x * y <= x * &1 ==> x * y <= x`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(&2 * M) * M = M * &2 * M`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!u v. abs(a - a0) <= u /\ abs(b - b0) <= v /\ u + v <= w
          ==> abs((a + b) - (b0 + a0)) <= w`) THEN
  EXISTS_TAC `M / &2 * abs h * (M + (M + B) / &2 * abs h) + M * (M + B) / &2 * abs h` THEN
  EXISTS_TAC `M * abs h * (M + B) + M * B` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Directional derivatives along lines, functions of compact                 *)
(* support (bounds, uniform continuity, vanishing derivatives), and the     *)
(* uniform consistency of p2aw_dq on smooth functions of compact support:   *)
(*   p2aw_dq w e h f -> p2aw_dlim w e f  uniformly on real^M as h -> 0.      *)
(* ========================================================================= *)

let P2AW_LINE_DERIV = prove
 (`!(s:real^M->bool) (f:real^M->real) x e t.
     open s /\ smooth_map_on s (\y. lift(f y)) /\ x + t % e IN s
     ==> ((\t. f(x + t % e)) has_real_derivative p2aw_d1 f e (x + t % e)) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; p2aw_d1; LIFT_DROP] THEN
  SUBGOAL_THEN `(lift o (\t. (f:real^M->real)(x + t % e)) o drop) =
                (\y. lift(f y)) o (\u:real^1. x + drop u % e)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC WAN_HVD_FRECHET_COMPOSE THEN
  REWRITE_TAC[WAN_NT_LINE_VECTOR_DERIVATIVE; LIFT_DROP] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\y:real^M. lift((f:real^M->real) y)`]
                SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[]);;

let P2AW_D1_SMOOTH = prove
 (`!(s:real^M->bool) (f:real^M->real) e.
     open s /\ smooth_map_on s (\y. lift(f y))
     ==> smooth_map_on s (\y. lift(p2aw_d1 f e y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1; LIFT_DROP] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\y:real^M. lift((f:real^M->real) y)`; `e:real^M`]
                SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
  ASM_REWRITE_TAC[]);;

let P2AW_D2_D1 = prove
 (`!(f:real^M->real) e y. p2aw_d2 f e y = p2aw_d1 (\y. p2aw_d1 f e y) e y`,
  REWRITE_TAC[p2aw_d2; p2aw_d1; LIFT_DROP; ETA_AX]);;

let P2AW_LINE_DERIV2 = prove
 (`!(s:real^M->bool) (f:real^M->real) x e t.
     open s /\ smooth_map_on s (\y. lift(f y)) /\ x + t % e IN s
     ==> ((\t. p2aw_d1 f e (x + t % e)) has_real_derivative p2aw_d2 f e (x + t % e))
         (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2AW_D2_D1] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\y. p2aw_d1 (f:real^M->real) e y`; `x:real^M`;
                 `e:real^M`; `t:real`] P2AW_LINE_DERIV) THEN
  ASM_SIMP_TAC[P2AW_D1_SMOOTH]);;

(* Functions of compact support. *)

let P2AW_SUPPORT_BOUNDED = prove
 (`!(g:real^M->real) k.
     (\y. lift(g y)) continuous_on (:real^M) /\ compact k /\ (!y. ~(y IN k) ==> g y = &0)
     ==> ?B. &0 < B /\ !y. abs(g y) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^M. lift((g:real^M->real) y)`; `k:real^M->bool`]
                COMPACT_CONTINUOUS_IMAGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN
  ASM_CASES_TAC `(y:real^M) IN k` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2AW_SUPPORT_UNIFORM = prove
 (`!(g:real^M->real) k.
     (\y. lift(g y)) continuous_on (:real^M) /\ compact k /\ (!y. ~(y IN k) ==> g y = &0)
     ==> !e. &0 < e
             ==> ?d. &0 < d /\
                     !y y'. norm(y - y') < d ==> abs(g y - g y') < e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `k1 = {y + z:real^M | y IN k /\ z IN cball(vec 0,&1)}` THEN
  SUBGOAL_THEN `compact(k1:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k1" THEN MATCH_MP_TAC COMPACT_SUMS THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^M. lift((g:real^M->real) y)`; `k1:real^M->bool`]
                COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[DIST_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y z:real^M. y IN k /\ norm(z - y) <= &1 ==> z IN k1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "k1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`y:real^M`; `z - y:real^M`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min d (&1)` THEN ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`y:real^M`; `y':real^M`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(y:real^M) IN k \/ (y':real^M) IN k` THENL
   [SUBGOAL_THEN `(y:real^M) IN k1 /\ (y':real^M) IN k1` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THENL
       [EXISTS_TAC `y:real^M`; EXISTS_TAC `y:real^M`;
        EXISTS_TAC `y':real^M`; EXISTS_TAC `y':real^M`] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_POS] THEN
      MP_TAC(ISPECL [`y:real^M`; `y':real^M`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `d:real`)) (concl th)
                            then MP_TAC(SPECL [`y':real^M`; `y:real^M`] th)
                            else failwith "") THEN
    ASM_REWRITE_TAC[dist];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_NUM]]);;

let P2AW_SUPPORT_D1 = prove
 (`!(g:real^M->real) k e y.
     smooth_map_on (:real^M) (\y. lift(g y)) /\ compact k /\
     (!y. ~(y IN k) ==> g y = &0) /\ ~(y IN k)
     ==> p2aw_d1 g e y = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1] THEN
  MP_TAC(ISPECL [`g:real^M->real`; `k:real^M->bool`; `e:real^M`; `y:real^M`]
                WAN_TEST_DERIV_ZERO) THEN
  ASM_SIMP_TAC[DROP_VEC]);;

let P2AW_SUPPORT_D2 = prove
 (`!(g:real^M->real) k e y.
     smooth_map_on (:real^M) (\y. lift(g y)) /\ compact k /\
     (!y. ~(y IN k) ==> g y = &0) /\ ~(y IN k)
     ==> p2aw_d2 g e y = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2AW_D2_D1] THEN
  MATCH_MP_TAC P2AW_SUPPORT_D1 THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_SIMP_TAC[P2AW_D1_SMOOTH; OPEN_UNIV] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_SUPPORT_D1 THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let P2AW_D2_SMOOTH = prove
 (`!(s:real^M->bool) (f:real^M->real) e.
     open s /\ smooth_map_on s (\y. lift(f y))
     ==> smooth_map_on s (\y. lift(p2aw_d2 f e y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2AW_D2_D1] THEN
  MATCH_MP_TAC P2AW_D1_SMOOTH THEN ASM_SIMP_TAC[P2AW_D1_SMOOTH]);;

(* Uniform consistency of the discrete operator on smooth functions of     *)
(* compact support.                                                          *)

let P2AW_DQ_UNIF = prove
 (`!(w:real^M->real) (f:real^M->real) e kw kf.
     smooth_map_on (:real^M) (\y. lift(w y)) /\ smooth_map_on (:real^M) (\y. lift(f y)) /\
     compact kw /\ (!y. ~(y IN kw) ==> w y = &0) /\
     compact kf /\ (!y. ~(y IN kf) ==> f y = &0)
     ==> !eps. &0 < eps
               ==> ?d. &0 < d /\
                       !h z. &0 < abs h /\ abs h < d
                             ==> abs(p2aw_dq w e h f z - p2aw_dlim w e f z) < eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y. lift((w:real^M->real) y)) continuous_on (:real^M) /\
    (\y. lift(p2aw_d1 w e y)) continuous_on (:real^M) /\
    (\y. lift(p2aw_d2 w e y)) continuous_on (:real^M) /\
    (\y. lift(p2aw_d1 (f:real^M->real) e y)) continuous_on (:real^M) /\
    (\y. lift(p2aw_d2 f e y)) continuous_on (:real^M)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[P2AW_D1_SMOOTH; P2AW_D2_SMOOTH; OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y. ~(y IN kw) ==> p2aw_d1 (w:real^M->real) e y = &0) /\
    (!y. ~(y IN kw) ==> p2aw_d2 w e y = &0) /\
    (!y. ~(y IN kf) ==> p2aw_d1 (f:real^M->real) e y = &0) /\
    (!y. ~(y IN kf) ==> p2aw_d2 f e y = &0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC P2AW_SUPPORT_D1; MATCH_MP_TAC P2AW_SUPPORT_D2;
      MATCH_MP_TAC P2AW_SUPPORT_D1; MATCH_MP_TAC P2AW_SUPPORT_D2] THENL
     [EXISTS_TAC `kw:real^M->bool`; EXISTS_TAC `kw:real^M->bool`;
      EXISTS_TAC `kf:real^M->bool`; EXISTS_TAC `kf:real^M->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^M->real`; `kw:real^M->bool`] P2AW_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p2aw_d1 (w:real^M->real) e`; `kw:real^M->bool`] P2AW_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p2aw_d2 (w:real^M->real) e`; `kw:real^M->bool`] P2AW_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p2aw_d1 (f:real^M->real) e`; `kf:real^M->bool`] P2AW_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(X_CHOOSE_THEN `B3:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p2aw_d2 (f:real^M->real) e`; `kf:real^M->bool`] P2AW_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN(X_CHOOSE_THEN `B4:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M = B0 + B1 + B2 + B3 + B4 + &1` THEN
  SUBGOAL_THEN `&1 <= M` ASSUME_TAC THENL [EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^M. abs(w y) <= M /\ abs(p2aw_d1 w e y) <= M /\ abs(p2aw_d2 w e y) <= M /\
               abs(p2aw_d1 f e y) <= M /\ abs(p2aw_d2 f e y) <= M`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "M" THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M` o check (fun th ->
      is_forall(concl th) && not(is_imp(snd(strip_forall(concl th))))))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2aw_d2 (f:real^M->real) e`; `kf:real^M->bool`] P2AW_SUPPORT_UNIFORM) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN
  DISCH_THEN(MP_TAC o SPEC `min (eps / (&4 * M)) M`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (min (&1) (d1 / (norm(e:real^M) + &1))) (eps / (&12 * M pow 2 + &1))` THEN
  SUBGOAL_THEN `&0 < norm(e:real^M) + &1 /\ &0 < &12 * M pow 2 + &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `e:real^M` NORM_POS_LE) THEN REAL_ARITH_TAC;
      MP_TAC(SPEC `M:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_01; REAL_LT_DIV] THEN
  MAP_EVERY X_GEN_TAC [`h:real`; `z:real^M`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. abs t <= abs h
        ==> ((\t. (f:real^M->real)(z + t % e)) has_real_derivative
             p2aw_d1 f e (z + t % e)) (atreal t) /\
            ((\t. p2aw_d1 f e (z + t % e)) has_real_derivative
             p2aw_d2 f e (z + t % e)) (atreal t) /\
            ((\t. (w:real^M->real)(z + t % e)) has_real_derivative
             p2aw_d1 w e (z + t % e)) (atreal t) /\
            ((\t. p2aw_d1 w e (z + t % e)) has_real_derivative
             p2aw_d2 w e (z + t % e)) (atreal t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC P2AW_LINE_DERIV2; MATCH_MP_TAC P2AW_LINE_DERIV] THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. abs t <= abs h
        ==> abs(p2aw_d2 (f:real^M->real) e (z + t % e) - p2aw_d2 f e z) <=
            min (eps / (&4 * M)) M`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(z + t % e) - z:real^M = t % e`; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs h * norm(e:real^M)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `d1 / (norm(e:real^M) + &1) * norm e` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `d / a * n = (d * n) / a`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. (f:real^M->real)(z + t % e)`; `\t. p2aw_d1 (f:real^M->real) e (z + t % e)`;
    `\t. p2aw_d2 (f:real^M->real) e (z + t % e)`;
    `\t. (w:real^M->real)(z + t % e)`; `\t. p2aw_d1 (w:real^M->real) e (z + t % e)`;
    `\t. p2aw_d2 (w:real^M->real) e (z + t % e)`;
    `abs h`; `M:real`; `min (eps / (&4 * M)) M`; `h:real`] P2AW_DQ_1D) THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_LE_REFL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[p2aw_dq; p2aw_dlim; VECTOR_MUL_LNEG; GSYM VECTOR_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `!y. x <= y /\ y < e ==> abs a <= x ==> abs a < e`) THEN
  EXISTS_TAC `&6 * M pow 2 * eps / (&12 * M pow 2 + &1) + M * eps / (&4 * M)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `M * eps / (&4 * M) = eps / &4` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= M` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&6 * M pow 2 * eps / (&12 * M pow 2 + &1) <= eps / &2` MP_TAC THENL
   [SUBGOAL_THEN `&6 * M pow 2 * eps / (&12 * M pow 2 + &1) =
                  (&6 * M pow 2 * eps) / (&12 * M pow 2 + &1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Localization.  Smooth (or continuous) functions on an open set agree near *)
(* a compact subset with smooth (continuous) functions of compact support on *)
(* the whole space; p2aw_dq and p2aw_dlim only see the function near the     *)
(* point; hence the pointwise consistency of p2aw_dq for functions smooth    *)
(* near a point (used for the barriers).                                     *)
(* ========================================================================= *)

let P2AW_CUTOFF = prove
 (`!(s:real^M->bool) k.
     open s /\ compact k /\ k SUBSET s
     ==> ?chi kc u. wan_test s chi /\ compact kc /\ kc SUBSET s /\
                    (!y. ~(y IN kc) ==> chi y = &0) /\
                    open u /\ k SUBSET u /\ u SUBSET s /\ (!y. y IN u ==> chi y = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `{x + y:real^M | x IN k /\ y IN cball(vec 0,d)}`]
                WAN_SMOOTH_URYSOHN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `chi:real^M->real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:real^M->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`chi:real^M->real`; `kc:real^M->bool`;
                        `{x + y:real^M | x IN k /\ y IN ball(vec 0,d)}`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM SET_TAC[]]);;

let P2AW_LOCALIZE = prove
 (`!(s:real^M->bool) (f:real^M->real) k.
     open s /\ compact k /\ k SUBSET s /\ smooth_map_on s (\y. lift(f y))
     ==> ?g kg u. smooth_map_on (:real^M) (\y. lift(g y)) /\ compact kg /\ kg SUBSET s /\
                  (!y. ~(y IN kg) ==> g y = &0) /\
                  open u /\ k SUBSET u /\ u SUBSET s /\ (!y. y IN u ==> g y = f y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] P2AW_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^M->real` (X_CHOOSE_THEN `kc:real^M->bool`
    (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `chi:real^M->real`; `f:real^M->real`]
                WAN_TEST_MUL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[wan_test] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`\y:real^M. if y IN s then chi y * (f:real^M->real) y else &0`;
                        `k':real^M->bool`; `u:real^M->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^M) IN s` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_LID]);;

let P2AW_LOCALIZE_CONT = prove
 (`!(s:real^M->bool) (f:real^M->real) k.
     open s /\ compact k /\ k SUBSET s /\ (\y. lift(f y)) continuous_on s
     ==> ?g kg u. (\y. lift(g y)) continuous_on (:real^M) /\ compact kg /\ kg SUBSET s /\
                  (!y. ~(y IN kg) ==> g y = &0) /\
                  open u /\ k SUBSET u /\ u SUBSET s /\ (!y. y IN u ==> g y = f y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] P2AW_CUTOFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^M->real` (X_CHOOSE_THEN `kc:real^M->bool`
    (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`\y:real^M. if y IN s then chi y * (f:real^M->real) y else &0`;
                        `kc:real^M->bool`; `u:real^M->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^M. ~(y IN kc)
                           ==> (if y IN s then chi y * (f:real^M->real) y else &0) = &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^M. y IN u
                           ==> (if y IN s then chi y * (f:real^M->real) y else &0) = f y`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^M) IN s` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift((chi:real^M->real) y)) continuous_on (:real^M)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_MESON_TAC[wan_test]; ALL_TAC] THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `y:real^M` THEN ASM_CASES_TAC `(y:real^M) IN s` THENL
   [MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\y:real^M. lift(chi y * (f:real^M->real) y)` THEN
    MP_TAC(SPEC `y:real^M` (GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]
      (ASSUME `open(s:real^M->bool)`))) THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[DIST_SYM];
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
      REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
        ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]]];
    MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
    EXISTS_TAC `\y:real^M. lift(&0)` THEN
    REWRITE_TAC[LIFT_NUM; CONTINUOUS_CONST] THEN
    MP_TAC(ISPEC `kc:real^M->bool` COMPACT_IMP_CLOSED) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    SUBGOAL_THEN `(chi:real^M->real) z = &0` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[DIST_SYM]]);;

let P2AW_D1_LOCAL = prove
 (`!(f:real^M->real) g e x u.
     open u /\ x IN u /\ (!y. y IN u ==> g y = f y)
     ==> p2aw_d1 g e x = p2aw_d1 f e x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_MESON_TAC[DIST_SYM]);;

let P2AW_D2_LOCAL = prove
 (`!(f:real^M->real) g e x u.
     open u /\ x IN u /\ (!y. y IN u ==> g y = f y)
     ==> p2aw_d2 g e x = p2aw_d2 f e x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[P2AW_D2_D1] THEN
  MATCH_MP_TAC P2AW_D1_LOCAL THEN EXISTS_TAC `u:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_D1_LOCAL THEN
  EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let P2AW_DLIM_LOCAL = prove
 (`!(w:real^M->real) w' f f' e x u.
     open u /\ x IN u /\ (!y. y IN u ==> w' y = w y /\ f' y = f y)
     ==> p2aw_dlim w' e f' x = p2aw_dlim w e f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_dlim] THEN
  MP_TAC(ISPECL [`w:real^M->real`; `w':real^M->real`; `e:real^M`; `x:real^M`;
                 `u:real^M->bool`] P2AW_D1_LOCAL) THEN
  MP_TAC(ISPECL [`f:real^M->real`; `f':real^M->real`; `e:real^M`; `x:real^M`;
                 `u:real^M->bool`] P2AW_D1_LOCAL) THEN
  MP_TAC(ISPECL [`f:real^M->real`; `f':real^M->real`; `e:real^M`; `x:real^M`;
                 `u:real^M->bool`] P2AW_D2_LOCAL) THEN
  ASM_SIMP_TAC[]);;

let P2AW_DQ_LOCAL = prove
 (`!(w:real^M->real) w' f f' e h z u.
     (!y. y IN u ==> w' y = w y /\ f' y = f y) /\
     z IN u /\ z + h % e IN u /\ z - h % e IN u /\
     z + (h / &2) % e IN u /\ z - (h / &2) % e IN u
     ==> p2aw_dq w' e h f' z = p2aw_dq w e h f z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_dq] THEN ASM_SIMP_TAC[]);;

(* Pointwise consistency for functions smooth near the point. *)

let P2AW_DQ_POINT = prove
 (`!(s:real^M->bool) (w:real^M->real) (f:real^M->real) e x.
     open s /\ x IN s /\ smooth_map_on s (\y. lift(w y)) /\ smooth_map_on s (\y. lift(f y))
     ==> !eps. &0 < eps
               ==> ?d. &0 < d /\
                       !h. &0 < abs h /\ abs h < d
                           ==> abs(p2aw_dq w e h f x - p2aw_dlim w e f x) < eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `w:real^M->real`; `{x:real^M}`] P2AW_LOCALIZE) THEN
  ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `gw:real^M->real` (X_CHOOSE_THEN `kw:real^M->bool`
    (X_CHOOSE_THEN `uw:real^M->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `f:real^M->real`; `{x:real^M}`] P2AW_LOCALIZE) THEN
  ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `gf:real^M->real` (X_CHOOSE_THEN `kf:real^M->bool`
    (X_CHOOSE_THEN `uf:real^M->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`gw:real^M->real`; `gf:real^M->real`; `e:real^M`; `kw:real^M->bool`;
                 `kf:real^M->bool`] P2AW_DQ_UNIF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open(uw INTER uf:real^M->bool) /\ (x:real^M) IN uw INTER uf`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `x:real^M` (GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]
    (ASSUME `open(uw INTER uf:real^M->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d0 (r / (norm(e:real^M) + &1))` THEN
  SUBGOAL_THEN `&0 < norm(e:real^M) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^M` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. abs t <= abs h ==> x + t % e IN uw INTER (uf:real^M->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^M,x + y) = norm y`; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs h * norm(e:real^M)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `r / (norm(e:real^M) + &1) * norm e` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `d / a * n = (d * n) / a`; REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^M. y IN uw INTER uf
                           ==> (gw:real^M->real) y = (w:real^M->real) y /\
                               (gf:real^M->real) y = (f:real^M->real) y`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^M->real`; `gw:real^M->real`; `f:real^M->real`; `gf:real^M->real`;
                 `e:real^M`; `h:real`; `x:real^M`; `uw INTER uf:real^M->bool`]
                P2AW_DQ_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `h:real`);
      FIRST_X_ASSUM(MP_TAC o SPEC `--h:real`);
      FIRST_X_ASSUM(MP_TAC o SPEC `h / &2`);
      FIRST_X_ASSUM(MP_TAC o SPEC `--(h / &2)`)] THEN
    REWRITE_TAC[VECTOR_MUL_LNEG; GSYM VECTOR_SUB; REAL_ABS_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
    REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`w:real^M->real`; `gw:real^M->real`; `f:real^M->real`; `gf:real^M->real`;
                 `e:real^M`; `x:real^M`; `uw INTER uf:real^M->bool`] P2AW_DLIM_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The limit step.  If Q_n <= C on a compact k and limsup Q_n <= Fb almost   *)
(* everywhere where phi > 0 (Fb bounded measurable), then limsup int phi Q_n *)
(* <= int phi Fb (dominated convergence for the positive part phi (Q_n -     *)
(* Fb)^+).                                                                   *)
(* ========================================================================= *)

let P2AW_MEAS_BOUNDED_INT = prove
 (`!(g:real^M->real) k B.
     (\x. lift(g x)) measurable_on k /\ compact k /\ (!x. x IN k ==> abs(g x) <= B)
     ==> (\x. lift(g x)) integrable_on k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. lift B` THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_COMPACT; NORM_LIFT; LIFT_DROP]);;

let P2AW_CONT_COMPACT_INT = prove
 (`!(g:real^M->real) k.
     (\x. lift(g x)) continuous_on k /\ compact k
     ==> (\x. lift(g x)) measurable_on k /\ (\x. lift(g x)) integrable_on k /\
         ?B. !x. x IN k ==> abs(g x) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((g:real^M->real) x)) measurable_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `?B. !x:real^M. x IN k ==> abs(g x) <= B` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^M. lift((g:real^M->real) x)`; `k:real^M->bool`]
                  COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; NORM_LIFT] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC P2AW_MEAS_BOUNDED_INT THEN ASM_MESON_TAC[]);;

let P2AW_LIMSUP_INT = prove
 (`!(phi:real^M->real) (Q:num->real^M->real) Fb k C.
     compact k /\ (\x. lift(phi x)) continuous_on k /\ (!x. x IN k ==> &0 <= phi x) /\
     (!n. (\x. lift(Q n x)) continuous_on k) /\
     (\x. lift(Fb x)) measurable_on k /\ (!x. x IN k ==> abs(Fb x) <= C) /\
     (!n x. x IN k ==> Q n x <= C) /\
     (?N. negligible N /\
          !x. x IN k /\ ~(x IN N) /\ &0 < phi x
              ==> !e. &0 < e ==> ?n0. !n. n0 <= n ==> Q n x <= Fb x + e)
     ==> (\x. lift(phi x * Fb x)) integrable_on k /\
         (!n. (\x. lift(phi x * Q n x)) integrable_on k) /\
         !e. &0 < e
             ==> ?n0. !n. n0 <= n
                     ==> drop(integral k (\x. lift(phi x * Q n x))) <=
                         drop(integral k (\x. lift(phi x * Fb x))) + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`] P2AW_CONT_COMPACT_INT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `P:real`))) THEN
  SUBGOAL_THEN `(\x. lift((phi:real^M->real) x * Fb x)) integrable_on k` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_MEAS_BOUNDED_INT THEN EXISTS_TAC `P * C:real` THEN
    ASM_SIMP_TAC[MEASURABLE_ON_LIFT_MUL] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. (\x. lift((phi:real^M->real) x * (Q:num->real^M->real) n x)) integrable_on k`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`\x:real^M. (phi:real^M->real) x * Q (n:num) x`;
                                `k:real^M->bool`] P2AW_CONT_COMPACT_INT) THEN
    ASM_SIMP_TAC[WAN_CONT_LIFT_MUL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* The positive parts. *)
  ABBREV_TAC `g = \n x. (phi:real^M->real) x * max (&0) ((Q:num->real^M->real) n x - Fb x)` THEN
  SUBGOAL_THEN `!n. (\x. lift((g:num->real^M->real) n x)) integrable_on k` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2AW_MEAS_BOUNDED_INT THEN
    EXISTS_TAC `P * &2 * C` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "g" THEN BETA_TAC THEN
      MP_TAC(ISPECL [`phi:real^M->real`;
                     `\x:real^M. max (&0) ((Q:num->real^M->real) n x - Fb x)`;
                     `k:real^M->bool`] MEASURABLE_ON_LIFT_MUL) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^M. vec 0:real^1`;
                     `\x:real^M. lift((Q:num->real^M->real) n x - Fb x)`; `k:real^M->bool`]
                    MEASURABLE_ON_MAX) THEN
      REWRITE_TAC[MEASURABLE_ON_0] THEN ANTS_TAC THENL
       [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`(Q:num->real^M->real) n`; `k:real^M->bool`]
                      P2AW_CONT_COMPACT_INT) THEN
        ASM_SIMP_TAC[ETA_AX];
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA; DIMINDEX_1; FORALL_1; ARITH] THEN
        REWRITE_TAC[GSYM drop; LIFT_DROP; DROP_VEC]];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS] THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2
                              then MP_TAC(SPECL [`n:num`; `x:real^M`] th) else failwith "") THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `C:real`)) (concl th) &&
        can (find_term ((=) `Fb:real^M->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\n. integral k (\x. lift((g:num->real^M->real) n x))) --> vec 0) sequentially`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\n x. lift((g:num->real^M->real) n x)`; `\x:real^M. vec 0:real^1`;
                   `\x:real^M. lift(P * &2 * C)`; `k:real^M->bool`; `N:real^M->bool`]
                  DOMINATED_CONVERGENCE_AE) THEN
    REWRITE_TAC[INTEGRAL_0] THEN
    MATCH_MP_TAC(TAUT `a /\ (b /\ c ==> d) ==> (a ==> b /\ c) ==> d`) THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_COMPACT; IN_DIFF] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN STRIP_TAC THEN
      REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_ABS_POS] THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) && length(fst(strip_forall(concl th))) = 2
                              then MP_TAC(SPECL [`n:num`; `x:real^M`] th) else failwith "") THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `C:real`)) (concl th) &&
        can (find_term ((=) `Fb:real^M->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REWRITE_TAC[DIST_0; NORM_LIFT] THEN EXPAND_TAC "g" THEN
    ASM_CASES_TAC `(phi:real^M->real) x = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ABS_NUM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (phi:real^M->real) x` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&0 <= (phi:real^M->real) x`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `N:real^M->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / (P + &1)`) THEN
    SUBGOAL_THEN `&0 < P + &1 /\ abs((phi:real^M->real) x) <= P` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `P:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < e / (P + &1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `n0:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `P * e / (P + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= m /\ m <= a ==> abs m <= a`) THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH `P * e / q = (P * e) / q`; REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[DIST_0] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral k (\x. lift((phi:real^M->real) x * Fb x) +
                                  lift((g:num->real^M->real) n x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[INTEGRABLE_ADD] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN
    EXPAND_TAC "g" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&0 <= (phi:real^M->real) x`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `p * q <= p * f + p * m ==> p * q <= p * f + p * m`) THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGRAL_ADD; DROP_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH `abs b < e ==> a + b <= a + e`) THEN
    ASM_REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP]]);;

(* ========================================================================= *)
(* Pointwise facts about p2aw_dq used in the barrier principle: the upper    *)
(* bound from semiconcavity and Lipschitz bounds, the comparison with an     *)
(* upper barrier, and the test function W (D_e phi) whose derivative along e *)
(* is p2aw_dlim W e phi.                                                     *)
(* ========================================================================= *)

let P2AW_DQ_SEMI_UPPER = prove
 (`!(w:real^M->real) (u:real^M->real) e h z Lw Lu C B.
     &0 <= w z /\ w z <= B /\ &0 < abs h /\ &0 <= C /\ &0 <= Lw /\ &0 <= Lu /\
     abs(w(z + (h / &2) % e) - w z) <= Lw * abs h * norm e /\
     abs(w(z - (h / &2) % e) - w z) <= Lw * abs h * norm e /\
     abs(u(z + h % e) - u z) <= Lu * abs h * norm e /\
     abs(u(z - h % e) - u z) <= Lu * abs h * norm e /\
     u(z + h % e) + u(z - h % e) - &2 * u z <= C * h pow 2
     ==> p2aw_dq w e h u z <= B * C + &2 * Lw * Lu * norm e pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2aw_dq] THEN
  SUBGOAL_THEN `&0 < h pow 2 /\ abs h * abs h = h pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_POW_2; REAL_POW_2; GSYM REAL_ABS_MUL; REAL_ABS_REFL;
                REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MP_TAC(REAL_RING
   `!wz wp wm uz up um:real.
      wp * (up - uz) + wm * (um - uz) =
      wz * (up + um - &2 * uz) + (wp - wz) * (up - uz) + (wm - wz) * (um - uz)`) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[SPECL
    [`(w:real^M->real) z`; `(w:real^M->real)(z + (h / &2) % e)`;
     `(w:real^M->real)(z - (h / &2) % e)`; `(u:real^M->real) z`;
     `(u:real^M->real)(z + h % e)`; `(u:real^M->real)(z - h % e)`] th]) THEN
  SUBGOAL_THEN
   `(w:real^M->real) z * (u(z + h % e) + u(z - h % e) - &2 * u z) <= (B * C) * h pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(w:real^M->real) z * C * h pow 2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(((w:real^M->real)(z + (h / &2) % e) - w z) * ((u:real^M->real)(z + h % e) - u z))
    <= (Lw * Lu * norm(e:real^M) pow 2) * h pow 2 /\
    abs(((w:real^M->real)(z - (h / &2) % e) - w z) * ((u:real^M->real)(z - h % e) - u z))
    <= (Lw * Lu * norm(e:real^M) pow 2) * h pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Lw * abs h * norm(e:real^M)) * (Lu * abs h * norm e)` THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
       FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
         concl th = `abs h * abs h = h pow 2`)) THEN
       REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN ASM_REAL_ARITH_TAC);;

let P2AW_DQ_BARRIER = prove
 (`!(w:real^M->real) u psi e h z.
     &0 <= w(z + (h / &2) % e) /\ &0 <= w(z - (h / &2) % e) /\
     u(z + h % e) <= psi(z + h % e) /\ u(z - h % e) <= psi(z - h % e) /\ psi z = u z
     ==> p2aw_dq w e h u z <= p2aw_dq w e h psi z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_dq] THEN ONCE_REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC);;

let P2AW_TEST_D1 = prove
 (`!(s:real^M->bool) phi e. wan_test s phi ==> wan_test s (\x. p2aw_d1 phi e x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_test] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2AW_D1_SMOOTH; OPEN_UNIV] THEN EXISTS_TAC `k:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_SUPPORT_D1 THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let P2AW_D1_PRODUCT = prove
 (`!(s:real^M->bool) (f:real^M->real) g e x.
     open s /\ x IN s /\ smooth_map_on s (\y. lift(f y)) /\ smooth_map_on s (\y. lift(g y))
     ==> p2aw_d1 (\y. f y * g y) e x = f x * p2aw_d1 g e x + p2aw_d1 f e x * g x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_d1] THEN
  MP_TAC(ISPECL [`f:real^M->real`;
                 `\h. drop(frechet_derivative (\y. lift((f:real^M->real) y)) (at x) h)`;
                 `\y. lift((g:real^M->real) y)`;
                 `frechet_derivative (\y. lift((g:real^M->real) y)) (at x)`; `x:real^M`]
                HAS_DERIVATIVE_MUL_AT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

let P2AW_TEST_PRODUCT_D1 = prove
 (`!(s:real^M->bool) (w:real^M->real) phi e.
     open s /\ smooth_map_on s (\x. lift(w x)) /\ wan_test s phi
     ==> wan_test s (\x. if x IN s then p2aw_d1 phi e x * w x else &0) /\
         !x. x IN s
             ==> p2aw_d1 (\x. if x IN s then p2aw_d1 phi e x * w x else &0) e x =
                 p2aw_dlim w e phi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. p2aw_d1 (phi:real^M->real) e x`; `w:real^M->real`]
                WAN_TEST_MUL_SMOOTH) THEN
  ASM_SIMP_TAC[P2AW_TEST_D1] THEN DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y. p2aw_d1 (phi:real^M->real) e y * w y`;
                 `\x. if x IN s then p2aw_d1 (phi:real^M->real) e x * w x else &0`;
                 `e:real^M`; `x:real^M`; `s:real^M->bool`] P2AW_D1_LOCAL) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^M) (\y. lift((phi:real^M->real) y))` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_test]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\y. p2aw_d1 (phi:real^M->real) e y`; `w:real^M->real`;
                 `e:real^M`; `x:real^M`] P2AW_D1_PRODUCT) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC P2AW_D1_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[p2aw_dlim; GSYM P2AW_D2_D1; ETA_AX] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Finite families and the global limit.  Common deltas and                  *)
(* common indices over a finite index set; summation by parts for a finite *)
(* sum of discrete operators; integrals of uniformly convergent sequences  *)
(* against a function of compact support; the global barrier inequality    *)
(*   int gu (sum_k D_e_k (gW_k D_e_k phi)) <= int phi Fb                     *)
(* for continuous gu of compact support and smooth gW_k of compact support. *)
(* ========================================================================= *)

let P2AW_FINITE_DELTA = prove
 (`!(Q:K->real->bool) Ix.
     FINITE Ix /\ (!k. k IN Ix ==> ?d. &0 < d /\ !h. abs h < d ==> Q k h)
     ==> ?d. &0 < d /\ !k h. k IN Ix /\ abs h < d ==> Q k h`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [MESON_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_THEN(LABEL_TAC "H") THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "H" (MP_TAC o SPEC `a:K`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[REAL_LT_MIN]);;

let P2AW_FINITE_EVENTUALLY = prove
 (`!(P:K->num->bool) Ix.
     FINITE Ix /\ (!k. k IN Ix ==> ?n0. !n. n0 <= n ==> P k n)
     ==> ?n0. !k n. k IN Ix /\ n0 <= n ==> P k n`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_THEN(LABEL_TAC "H") THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "H" (MP_TAC o SPEC `a:K`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MAX n1 n2` THEN REWRITE_TAC[ARITH_RULE `MAX a b <= n <=> a <= n /\ b <= n`] THEN
  ASM_MESON_TAC[]);;

let P2AW_SUM_SBP = prove
 (`!(Ix:K->bool) (gW:K->real^M->real) e h gu phi k.
     FINITE Ix /\ (!k. k IN Ix ==> (\x. lift(gW k x)) continuous_on (:real^M)) /\
     (\x. lift(gu x)) continuous_on (:real^M) /\
     (\x. lift(phi x)) continuous_on (:real^M) /\ compact k /\
     (!x. ~(x IN k) ==> phi x = &0)
     ==> (\z. lift(phi z * sum Ix (\k. p2aw_dq (gW k) (e k) h gu z))) integrable_on (:real^M) /\
         (\z. lift(gu z * sum Ix (\k. p2aw_dq (gW k) (e k) h phi z))) integrable_on (:real^M) /\
         integral (:real^M) (\z. lift(phi z * sum Ix (\k. p2aw_dq (gW k) (e k) h gu z))) =
         integral (:real^M) (\z. lift(gu z * sum Ix (\k. p2aw_dq (gW k) (e k) h phi z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; LIFT_SUM; o_DEF] THEN
  SUBGOAL_THEN
   `!j. j IN Ix
        ==> (\z. lift((phi:real^M->real) z * p2aw_dq ((gW:K->real^M->real) j) (e j) h gu z))
              integrable_on (:real^M) /\
            (\z. lift(gu z * p2aw_dq (gW j) (e j) h phi z)) integrable_on (:real^M) /\
            integral (:real^M) (\z. lift(phi z * p2aw_dq (gW j) (e j) h gu z)) =
            integral (:real^M) (\z. lift(gu z * p2aw_dq (gW j) (e j) h phi z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:K` THEN DISCH_TAC THEN MATCH_MP_TAC P2AW_DQ_SBP THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRABLE_VSUM; INTEGRAL_VSUM] THEN MATCH_MP_TAC VSUM_EQ THEN
  ASM_SIMP_TAC[]);;

let P2AW_UNIF_INTEGRAL = prove
 (`!(gu:real^M->real) ku (S:num->real^M->real) Tf.
     (\x. lift(gu x)) continuous_on (:real^M) /\ compact ku /\
     (!x. ~(x IN ku) ==> gu x = &0) /\
     (!n. (\x. lift(gu x * S n x)) integrable_on (:real^M)) /\
     (\x. lift(gu x * Tf x)) integrable_on (:real^M) /\
     (!eps. &0 < eps ==> ?n0. !n x. n0 <= n ==> abs(S n x - Tf x) < eps)
     ==> ((\n. drop(integral (:real^M) (\x. lift(gu x * S n x)))) --->
          drop(integral (:real^M) (\x. lift(gu x * Tf x)))) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`gu:real^M->real`; `ku:real^M->bool`] P2AW_SUPPORT_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < B * (measure(ku:real^M->bool) + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_COMPACT;
      REAL_ARITH `&0 <= m ==> &0 < m + &1`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `eps / (B * (measure(ku:real^M->bool) + &1))`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n0:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM DROP_SUB; GSYM INTEGRAL_SUB] THEN
  REWRITE_TAC[GSYM LIFT_SUB; GSYM REAL_SUB_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `drop(integral (:real^M)
     (\x. if x IN ku then lift(B * eps / (B * (measure(ku:real^M->bool) + &1)))
          else vec 0))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP] THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; IN_UNIV] THEN
    ASM_SIMP_TAC[INTEGRABLE_ON_CONST; MEASURABLE_COMPACT; INTEGRABLE_SUB; LIFT_SUB] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM LIFT_SUB; GSYM REAL_SUB_LDISTRIB] THEN
      MATCH_MP_TAC INTEGRABLE_EQ THEN
      EXISTS_TAC `\x. lift((gu:real^M->real) x * S (n:num) x) - lift(gu x * Tf x)` THEN
      ASM_SIMP_TAC[INTEGRABLE_SUB; IN_UNIV] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[LIFT_SUB; REAL_SUB_LDISTRIB];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM; NORM_0; DROP_VEC; REAL_LE_REFL] THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN
  ASM_SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_COMPACT; DROP_CMUL; LIFT_DROP] THEN
  ASM_SIMP_TAC[REAL_ARITH `m * B * e / q = (B * m * e) / q`; REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < b * e ==> b * m * e < e * b * (m + &1)`) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]);;

let P2AW_DQ_CONT = prove
 (`!(w:real^M->real) e h f.
     (\x. lift(w x)) continuous_on (:real^M) /\ (\x. lift(f x)) continuous_on (:real^M)
     ==> (\z. lift(p2aw_dq w e h f z)) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!c:real^M. (\x. lift((w:real^M->real)(x + c))) continuous_on (:real^M) /\
                           (\x. lift((f:real^M->real)(x + c))) continuous_on (:real^M)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[P2AW_CONT_SHIFT]; ALL_TAC] THEN
  REWRITE_TAC[p2aw_dq; VECTOR_SUB] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV o RAND_CONV) [real_div] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV) [LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV) [LIFT_ADD] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_REWRITE_TAC[LIFT_SUB] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[]);;

let P2AW_DLIM_CONT = prove
 (`!(w:real^M->real) e f.
     smooth_map_on (:real^M) (\x. lift(w x)) /\ smooth_map_on (:real^M) (\x. lift(f x))
     ==> (\z. lift(p2aw_dlim w e f z)) continuous_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_dlim; LIFT_ADD] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  ASM_SIMP_TAC[P2AW_D1_SMOOTH; P2AW_D2_SMOOTH; OPEN_UNIV]);;

let P2AW_LE_EPS = prove
 (`!a b. (!e. &0 < e ==> a <= b + e) ==> a <= b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a - b) / &2`) THEN ASM_REAL_ARITH_TAC);;

let P2AW_NBP_GLOBAL = prove
 (`!(Ix:K->bool) (e:K->real^M) (gW:K->real^M->real) gu ku phi kp Fb C (hn:num->real).
     FINITE Ix /\
     (!k. k IN Ix ==> smooth_map_on (:real^M) (\x. lift(gW k x)) /\
                      ?kw. compact kw /\ !x. ~(x IN kw) ==> gW k x = &0) /\
     (\x. lift(gu x)) continuous_on (:real^M) /\ compact ku /\
     (!x. ~(x IN ku) ==> gu x = &0) /\
     smooth_map_on (:real^M) (\x. lift(phi x)) /\ compact kp /\
     (!x. ~(x IN kp) ==> phi x = &0) /\ (!x. &0 <= phi x) /\
     (\x. lift(Fb x)) measurable_on kp /\ (!x. x IN kp ==> abs(Fb x) <= C) /\
     (!n. ~(hn n = &0)) /\ (hn ---> &0) sequentially /\
     (!n x. x IN kp ==> sum Ix (\k. p2aw_dq (gW k) (e k) (hn n) gu x) <= C) /\
     (?N. negligible N /\
          !x. x IN kp /\ ~(x IN N) /\ &0 < phi x
              ==> !eps. &0 < eps
                        ==> ?n0. !n. n0 <= n
                                     ==> sum Ix (\k. p2aw_dq (gW k) (e k) (hn n) gu x) <=
                                         Fb x + eps)
     ==> (\x. lift(phi x * Fb x)) integrable_on kp /\
         drop(integral (:real^M)
                (\x. lift(gu x * sum Ix (\k. p2aw_dlim (gW k) (e k) phi x)))) <=
         drop(integral kp (\x. lift(phi x * Fb x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((phi:real^M->real) x)) continuous_on (:real^M)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. k IN Ix ==> (\x. lift((gW:K->real^M->real) k x)) continuous_on (:real^M)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. lift(sum Ix (\k. p2aw_dq ((gW:K->real^M->real) k) (e k) ((hn:num->real) n) gu x)))
          continuous_on (:real^M)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    ASM_SIMP_TAC[P2AW_DQ_CONT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`phi:real^M->real`;
                 `\n x. sum Ix (\k. p2aw_dq ((gW:K->real^M->real) k) (e k) ((hn:num->real) n) gu x)`;
                 `Fb:real^M->real`; `kp:real^M->bool`; `C:real`] P2AW_LIMSUP_INT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* summation by parts *)
  SUBGOAL_THEN
   `!n. integral kp (\x. lift((phi:real^M->real) x *
                       sum Ix (\k. p2aw_dq ((gW:K->real^M->real) k) (e k) ((hn:num->real) n) gu x))) =
        integral (:real^M) (\x. lift(gu x * sum Ix (\k. p2aw_dq (gW k) (e k) ((hn:num->real) n) phi x)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`Ix:K->bool`; `gW:K->real^M->real`; `e:K->real^M`; `(hn:num->real) n`;
                   `gu:real^M->real`; `phi:real^M->real`; `kp:real^M->bool`] P2AW_SUM_SBP) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN EXISTS_TAC `kp:real^M->bool` THEN
    ASM_SIMP_TAC[SUBSET_REFL; SUBSET_UNIV; REAL_MUL_LZERO; LIFT_NUM];
    ALL_TAC] THEN
  (* uniform convergence of the discrete operators applied to phi *)
  SUBGOAL_THEN
   `!eps. &0 < eps
          ==> ?n0. !n x. n0 <= n
                         ==> abs(sum Ix (\k. p2aw_dq ((gW:K->real^M->real) k) (e k) ((hn:num->real) n) phi x) -
                                 sum Ix (\k. p2aw_dlim (gW k) (e k) phi x)) < eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\k:K h. !x:real^M. &0 < abs h
                            ==> abs(p2aw_dq ((gW:K->real^M->real) k) (e k) h phi x -
                                    p2aw_dlim (gW k) (e k) phi x) <
                                eps / (&(CARD(Ix:K->bool)) + &1)`;
                   `Ix:K->bool`] P2AW_FINITE_DELTA) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:K` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on")) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "compact")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `kw:real^M->bool` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`(gW:K->real^M->real) k`; `phi:real^M->real`; `(e:K->real^M) k`;
                     `kw:real^M->bool`; `kp:real^M->bool`] P2AW_DQ_UNIF) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `eps / (&(CARD(Ix:K->bool)) + &1)`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &n + &1`] THEN
      MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `d:real` (GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]
      (ASSUME `((hn:num->real) ---> &0) sequentially`))) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `n0:num` THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN
    DISCH_TAC THEN ASM_SIMP_TAC[GSYM SUM_SUB] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum Ix (\k:K. eps / (&(CARD(Ix:K->bool)) + &1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN BETA_TAC THEN
      FIRST_X_ASSUM(fun th -> MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] th)) THEN
      ASM_SIMP_TAC[REAL_ARITH `~(h = &0) ==> &0 < abs h`];
      ASM_SIMP_TAC[SUM_CONST] THEN
      SIMP_TAC[REAL_ARITH `&0 < &n + &1`; REAL_ARITH `n * e / m = (n * e) / m`;
               REAL_LT_LDIV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e ==> n * e < e * (n + &1)`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* integrals of the uniformly convergent sequence *)
  MP_TAC(ISPECL [`gu:real^M->real`; `ku:real^M->bool`;
                 `\n x. sum Ix (\k. p2aw_dq ((gW:K->real^M->real) k) (e k) ((hn:num->real) n) phi x)`;
                 `\x. sum Ix (\k. p2aw_dlim ((gW:K->real^M->real) k) (e k) phi x)`]
                P2AW_UNIF_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC P2AW_CONT_SUPPORT_INT THEN EXISTS_TAC `ku:real^M->bool` THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN
      ASM_REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
      ASM_SIMP_TAC[P2AW_DQ_CONT];
      MATCH_MP_TAC P2AW_CONT_SUPPORT_INT THEN EXISTS_TAC `ku:real^M->bool` THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN
      ASM_REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
      ASM_SIMP_TAC[P2AW_DLIM_CONT]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  (* combine *)
  MATCH_MP_TAC P2AW_LE_EPS THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2` o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `Fb:real^M->real`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "integral")) (concl th))) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `n2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `MAX n1 n2` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `kp:real^M->bool`)) (concl th) &&
    can (find_term ((=) `gu:real^M->real`)) (concl th) &&
    not(can (find_term ((=) `C:real`)) (concl th)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `MAX n1 n2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `MAX n1 n2`) THEN
  REWRITE_TAC[ARITH_RULE `n1 <= MAX n1 n2 /\ n2 <= MAX n1 n2`] THEN
  REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Integration by parts for one direction, and the nonlinear barrier         *)
(* principle P2AW_NBP.                                                       *)
(* ========================================================================= *)

(* A continuous function on an open set times a function vanishing off a   *)
(* compact subset is integrable on the set.                                  *)

let P2AW_CONT_SUPPORT_INT_ON = prove
 (`!(s:real^M->bool) (f:real^M->real) k.
     (\x. lift(f x)) continuous_on s /\ compact k /\ k SUBSET s /\
     (!x. ~(x IN k) ==> f x = &0)
     ==> (\x. lift(f x)) integrable_on s /\
         integral s (\x. lift(f x)) = integral k (\x. lift(f x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. lift((f:real^M->real) x)) integrable_on k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real`; `k:real^M->bool`] P2AW_CONT_COMPACT_INT) THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[GSYM INTEGRABLE_RESTRICT_UNIV]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN k` THENL [ASM SET_TAC[]; ASM_SIMP_TAC[LIFT_NUM; COND_ID]];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[SUBSET_REFL; LIFT_NUM]]);;

let P2AW_DLIM_SUPPORT = prove
 (`!(w:real^M->real) e phi k x.
     smooth_map_on (:real^M) (\y. lift(phi y)) /\ compact k /\
     (!y. ~(y IN k) ==> phi y = &0) /\ ~(x IN k)
     ==> p2aw_dlim w e phi x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2aw_dlim] THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`; `e:real^M`; `x:real^M`]
                P2AW_SUPPORT_D1) THEN
  MP_TAC(ISPECL [`phi:real^M->real`; `k:real^M->bool`; `e:real^M`; `x:real^M`]
                P2AW_SUPPORT_D2) THEN
  ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_RID]);;

let P2AW_IBP_TERM = prove
 (`!(s:real^M->bool) (u:real^M->real) (w:real^M->real) e phi.
     open s /\ wan_loclip s u /\ smooth_map_on s (\x. lift(w x)) /\ wan_test s phi
     ==> (\x. lift(u x * p2aw_dlim w e phi x)) integrable_on s /\
         (\x. lift(w x * p2aw_d1 u e x * p2aw_d1 phi e x)) integrable_on s /\
         integral s (\x. lift(u x * p2aw_dlim w e phi x)) =
         --(integral s (\x. lift(w x * p2aw_d1 u e x * p2aw_d1 phi e x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `w:real^M->real`; `phi:real^M->real`; `e:real^M`]
                P2AW_TEST_PRODUCT_D1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(:M)` WAN_LIP_IBP) THEN REWRITE_TAC[WAN_LIP_IBP_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`s:real^M->bool`; `u:real^M->real`;
    `\x. if x IN s then p2aw_d1 (phi:real^M->real) e x * (w:real^M->real) x else &0`;
    `e:real^M`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN s
        ==> lift((u:real^M->real) x * p2aw_dlim (w:real^M->real) e phi x) =
            lift(u x * drop(frechet_derivative
              (\y. lift(if y IN s then p2aw_d1 (phi:real^M->real) e y * w y else &0))
              (at x) e)) /\
            lift(w x * p2aw_d1 u e x * p2aw_d1 phi e x) =
            lift(drop(frechet_derivative (\y. lift(u y)) (at x) e) *
                 (if x IN s then p2aw_d1 phi e x * w x else &0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN ASM_REWRITE_TAC[LIFT_EQ] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
                               can (find_term (fun t -> is_const t &&
                                                fst(dest_const t) = "p2aw_dlim")) (concl th)
                            then MP_TAC(SPEC `x:real^M` th) else failwith "") THEN
    ASM_REWRITE_TAC[p2aw_d1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift((u:real^M->real) x * p2aw_dlim (w:real^M->real) e phi x))
                integrable_on s`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `\x. (u:real^M->real) x * p2aw_dlim (w:real^M->real) e phi x`;
                   `k:real^M->bool`] P2AW_CONT_SUPPORT_INT_ON) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON] THEN
      REWRITE_TAC[p2aw_dlim; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN MATCH_MP_TAC WAN_CONT_LIFT_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[P2AW_D1_SMOOTH; P2AW_D2_SMOOTH] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
      ASM_SIMP_TAC[P2AW_D1_SMOOTH; P2AW_D2_SMOOTH; OPEN_UNIV; SUBSET_UNIV];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`w:real^M->real`; `e:real^M`; `phi:real^M->real`; `k:real^M->bool`;
                     `x:real^M`] P2AW_DLIM_SUPPORT) THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. lift(drop(frechet_derivative (\y. lift((u:real^M->real) y)) (at x) e) *
                         (if x IN s then p2aw_d1 (phi:real^M->real) e x * w x else &0))` THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral s (\x. lift((u:real^M->real) x * drop(frechet_derivative
              (\y. lift(if y IN s then p2aw_d1 (phi:real^M->real) e y * w y else &0))
              (at x) e)))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
  ASM_SIMP_TAC[]);;

let P2AW_STEP_SEQ = prove
 (`!h0. &0 < h0
        ==> (!n. ~(h0 / (&n + &1) = &0)) /\ (!n. abs(h0 / (&n + &1)) <= h0) /\
            ((\n. h0 / (&n + &1)) ---> &0) sequentially`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
    GEN_TAC THEN SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < &n + &1`;
             REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < h /\ &0 <= h * n ==> abs h <= h * (n + &1)`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]]);;

let P2AW_SUM_MEMBER_LE = prove
 (`!(f:K->real) s a. FINITE s /\ (!x. x IN s ==> &0 <= f x) /\ a IN s ==> f a <= sum s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{a:K}`; `s:K->bool`; `f:K->real`] SUM_SUBSET_SIMPLE) THEN
  ASM_SIMP_TAC[SUM_SING; IN_DIFF; SING_SUBSET]);;

(* ========================================================================= *)
(* The nonlinear barrier principle.  For u locally Lipschitz                 *)
(* on the open set s, semiconcave along the directions e_k (k in Ix), with *)
(* a smooth upper barrier psi at almost every x with phi x > 0, such that  *)
(*   sum_k D_e_k (W_k D_e_k psi)(x) <= Fb(x)                                *)
(* (W_k >= 0 smooth, Fb measurable and locally bounded), and every test    *)
(* phi >= 0:   0 <= int phi Fb + sum_k int W_k (D_e_k u)(D_e_k phi).        *)
(* ========================================================================= *)

let P2AW_LIP_SCALE = prove
 (`!L Lw a b. abs L <= Lw /\ &0 <= a /\ a <= b ==> L * a <= Lw * b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs L * a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let P2AW_BALL_STEP = prove
 (`!(x:real^M) c e r Em.
     &0 < Em /\ norm e <= Em /\ abs c < r / Em
     ==> x + c % e IN ball(x,r) /\ x - c % e IN ball(x,r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^M,x + y) = norm y`;
              NORM_ARITH `dist(x:real^M,x - y) = norm y`; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs c * Em` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]]);;

let P2AW_NBP = prove
 (`!(s:real^M->bool) (u:real^M->real) (Ix:K->bool) (e:K->real^M) (W:K->real^M->real)
    (Fb:real^M->real) (phi:real^M->real).
     open s /\ wan_loclip s u /\ FINITE Ix /\
     (!k. k IN Ix ==> smooth_map_on s (\x. lift(W k x)) /\ !x. x IN s ==> &0 <= W k x) /\
     wan_test s phi /\ (!x. &0 <= phi x) /\
     (!kk. compact kk /\ kk SUBSET s
           ==> ?C d. &0 < d /\
                     !k x t. k IN Ix /\ x IN kk /\ abs t < d
                             ==> u(x + t % e k) + u(x - t % e k) - &2 * u x <= C * t pow 2) /\
     (\x. lift(Fb x)) measurable_on s /\
     (!kk. compact kk /\ kk SUBSET s ==> ?C. !x. x IN kk ==> abs(Fb x) <= C) /\
     (?N. negligible N /\
          !x. x IN s /\ ~(x IN N) /\ &0 < phi x
              ==> ?psi r. &0 < r /\ ball(x,r) SUBSET s /\
                          smooth_map_on (ball(x,r)) (\y. lift(psi y)) /\
                          (!k t. k IN Ix /\ x + t % e k IN ball(x,r) /\
                                 x - t % e k IN ball(x,r)
                                 ==> u(x + t % e k) <= psi(x + t % e k) /\
                                     u(x - t % e k) <= psi(x - t % e k)) /\
                          psi x = u x /\
                          sum Ix (\k. p2aw_dlim (W k) (e k) psi x) <= Fb x)
     ==> (\x. lift(phi x * Fb x)) integrable_on s /\
         (!k. k IN Ix
              ==> (\x. lift(W k x * p2aw_d1 u (e k) x * p2aw_d1 phi (e k) x))
                    integrable_on s) /\
         &0 <= drop(integral s (\x. lift(phi x * Fb x))) +
               sum Ix (\k. drop(integral s (\x. lift(W k x * p2aw_d1 u (e k) x *
                                                    p2aw_d1 phi (e k) x))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "W")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "SC") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "FB") (X_CHOOSE_THEN `N:real^M->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "BAR")))))))))))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `kp:real^M->bool` STRIP_ASSUME_TAC)) THEN
  (* integration by parts, termwise *)
  SUBGOAL_THEN
   `!k. k IN Ix
        ==> (\x. lift((u:real^M->real) x * p2aw_dlim ((W:K->real^M->real) k) (e k) phi x))
              integrable_on s /\
            (\x. lift(W k x * p2aw_d1 u (e k) x * p2aw_d1 phi (e k) x)) integrable_on s /\
            integral s (\x. lift(u x * p2aw_dlim (W k) (e k) phi x)) =
            --(integral s (\x. lift(W k x * p2aw_d1 u (e k) x * p2aw_d1 phi (e k) x)))`
  (LABEL_TAC "IBP") THENL
   [X_GEN_TAC `k:K` THEN DISCH_TAC THEN MATCH_MP_TAC P2AW_IBP_TERM THEN
    ASM_SIMP_TAC[] THEN USE_THEN "W" (MP_TAC o SPEC `k:K`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* localization *)
  MP_TAC(ISPECL [`s:real^M->bool`; `kp:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K1 = {x + y:real^M | x IN kp /\ y IN cball(vec 0,d0)}` THEN
  SUBGOAL_THEN `!x y:real^M. x IN kp /\ norm y <= d0 ==> x + y IN K1` (LABEL_TAC "K1M") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "K1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real^M`; `y:real^M`] THEN ASM_REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kp:real^M->bool) SUBSET K1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x:real^M = x + vec 0` SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "K1M" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `u:real^M->real`; `K1:real^M->bool`]
                P2AW_LOCALIZE_CONT) THEN
  ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON] THEN
  DISCH_THEN(X_CHOOSE_THEN `gu:real^M->real` (X_CHOOSE_THEN `ku:real^M->bool`
    (X_CHOOSE_THEN `uu:real^M->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `?gW:K->real^M->real kW:K->real^M->bool uW:K->real^M->bool.
      !k. k IN Ix
          ==> smooth_map_on (:real^M) (\y. lift(gW k y)) /\ compact (kW k) /\
              kW k SUBSET s /\ (!y. ~(y IN kW k) ==> gW k y = &0) /\
              open (uW k) /\ K1 SUBSET uW k /\ uW k SUBSET s /\
              (!y. y IN uW k ==> gW k y = W k y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:K` THEN DISCH_TAC THEN MATCH_MP_TAC P2AW_LOCALIZE THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "W" (MP_TAC o SPEC `k:K`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?Lk:K->real Bk:K->real.
      !k. k IN Ix
          ==> (!x y. abs((gW:K->real^M->real) k x - gW k y) <= Lk k * norm(x - y)) /\
              (!x. abs(gW k x) <= Bk k)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:K` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `gW:K->real^M->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(gW:K->real^M->real) k`; `(kW:K->real^M->bool) k`]
                  WAN_SMOOTH_SUPPORT_LIPSCHITZ) THEN
    MP_TAC(ISPECL [`(gW:K->real^M->real) k`; `(kW:K->real^M->bool) k`]
                  P2AW_SUPPORT_BOUNDED) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* constants *)
  ABBREV_TAC `Lw = sum Ix (\k:K. abs((Lk:K->real) k))` THEN
  ABBREV_TAC `Bw = sum Ix (\k:K. abs((Bk:K->real) k))` THEN
  ABBREV_TAC `Em = sum Ix (\k:K. norm((e:K->real^M) k)) + &1` THEN
  SUBGOAL_THEN `&0 <= Lw /\ &0 <= Bw /\ &1 <= Em /\
                (!k. k IN Ix ==> abs((Lk:K->real) k) <= Lw /\ abs((Bk:K->real) k) <= Bw /\
                                 norm((e:K->real^M) k) <= Em)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Lw" THEN MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_ABS_POS];
      EXPAND_TAC "Bw" THEN MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[REAL_ABS_POS];
      EXPAND_TAC "Em" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= x + &1`) THEN
      MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[NORM_POS_LE];
      X_GEN_TAC `k:K` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "Lw" THEN
        MP_TAC(ISPECL [`\k:K. abs((Lk:K->real) k)`; `Ix:K->bool`; `k:K`]
                      P2AW_SUM_MEMBER_LE);
        EXPAND_TAC "Bw" THEN
        MP_TAC(ISPECL [`\k:K. abs((Bk:K->real) k)`; `Ix:K->bool`; `k:K`]
                      P2AW_SUM_MEMBER_LE);
        EXPAND_TAC "Em" THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= y + &1`) THEN
        MP_TAC(ISPECL [`\k:K. norm((e:K->real^M) k)`; `Ix:K->bool`; `k:K`]
                      P2AW_SUM_MEMBER_LE)] THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE]];
    ALL_TAC] THEN
  USE_THEN "SC" (MP_TAC o SPEC `K1:real^M->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Csc:real` (X_CHOOSE_THEN `dsc:real` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `K1:real^M->bool` o REWRITE_RULE[wan_loclip] o
    check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "wan_loclip"))
                         (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN(X_CHOOSE_TAC `Lu:real`) THEN
  USE_THEN "FB" (MP_TAC o SPEC `kp:real^M->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `CF:real`) THEN
  ABBREV_TAC `h0 = min (dsc / &2) (d0 / (&2 * Em))` THEN
  SUBGOAL_THEN `&0 < h0 /\ h0 < dsc /\ h0 * Em <= d0 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h0" THEN
    SUBGOAL_THEN `&0 < Em` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_LT_MUL; REAL_ARITH `&0 < &2`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d0 / (&2 * Em) * Em` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> d / (&2 * m) * m = d / &2`; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPEC `h0:real` P2AW_STEP_SEQ) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  ABBREV_TAC `hn = \n. h0 / (&n + &1)` THEN
  SUBGOAL_THEN
   `!k x t. k IN Ix /\ x IN kp /\ abs t <= h0
            ==> x + t % (e:K->real^M) k IN K1 /\ x - t % e k IN K1 /\
                x + (t / &2) % e k IN K1 /\ x - (t / &2) % e k IN K1 /\ x IN K1`
  (LABEL_TAC "PTS") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!c. abs c <= h0 ==> x + c % (e:K->real^M) k IN K1` ASSUME_TAC THENL
     [X_GEN_TAC `c:real` THEN DISCH_TAC THEN USE_THEN "K1M" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `h0 * Em` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS; NORM_POS_LE];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB; GSYM VECTOR_MUL_LNEG] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_NEG];
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `CQ = sum Ix (\k:K. Bw * max Csc (&0) +
                                 &2 * Lw * abs Lu * norm((e:K->real^M) k) pow 2)` THEN
  SUBGOAL_THEN
   `!n x. x IN kp
          ==> sum Ix (\k. p2aw_dq ((gW:K->real^M->real) k) (e k) ((hn:num->real) n) gu x) <= CQ`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN DISCH_TAC THEN EXPAND_TAC "CQ" THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `abs((hn:num->real) n) <= h0 /\ &0 < abs(hn n)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "hn" THEN ASM_SIMP_TAC[REAL_ARITH `~(x = &0) ==> &0 < abs x`];
      ALL_TAC] THEN
    USE_THEN "PTS" (MP_TAC o SPECL [`k:K`; `x:real^M`; `(hn:num->real) n`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`(W:K->real^M->real) k`; `(gW:K->real^M->real) k`; `u:real^M->real`;
                   `gu:real^M->real`; `(e:K->real^M) k`; `(hn:num->real) n`; `x:real^M`;
                   `K1:real^M->bool`] P2AW_DQ_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN CONJ_TAC THEN
      ASM_MESON_TAC[SUBSET];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC P2AW_DQ_SEMI_UPPER THEN
    SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!y. y IN K1 ==> (W:K->real^M->real) k y = gW k y` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `!y y'. abs((gW:K->real^M->real) k y - gW k y') <= Lk k * norm(y - y') /\
                         abs(gW k y) <= Bk k /\ abs((Lk:K->real) k) <= Lw /\
                         abs((Bk:K->real) k) <= Bw /\ norm((e:K->real^M) k) <= Em`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[REAL_ABS_POS; REAL_ARITH `&0 <= max c (&0)`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "W" (MP_TAC o SPEC `k:K`) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[REAL_ARITH `abs a <= b /\ abs b <= c ==> a <= c`];
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(Lk:K->real) k * norm((x + (hn:num->real) n / &2 % (e:K->real^M) k) - x)` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(x + c % e) - x:real^M = c % e`; NORM_MUL] THEN
      MATCH_MP_TAC P2AW_LIP_SCALE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(Lk:K->real) k * norm((x - (hn:num->real) n / &2 % (e:K->real^M) k) - x)` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(x - c % e) - x:real^M = --(c % e)`; NORM_NEG; NORM_MUL] THEN
      MATCH_MP_TAC P2AW_LIP_SCALE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Lu * norm((x + (hn:num->real) n % (e:K->real^M) k) - x)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH `(x + c % e) - x:real^M = c % e`; NORM_MUL] THEN
      MATCH_MP_TAC P2AW_LIP_SCALE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `Lu * norm((x - (hn:num->real) n % (e:K->real^M) k) - x)` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH `(x - c % e) - x:real^M = --(c % e)`; NORM_NEG; NORM_MUL] THEN
      MATCH_MP_TAC P2AW_LIP_SCALE THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; NORM_POS_LE; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Csc * (hn:num->real) n pow 2` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
                                   can (find_term ((=) `Csc:real`)) (concl th)
                                then MATCH_MP_TAC th else failwith "") THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN kp /\ ~(x IN N) /\ &0 < phi x
        ==> !eps. &0 < eps
                  ==> ?n0. !n. n0 <= n
                               ==> sum Ix (\k. p2aw_dq ((gW:K->real^M->real) k) (e k)
                                                 ((hn:num->real) n) gu x) <= Fb x + eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "BAR" (MP_TAC o SPEC `x:real^M`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:real^M->real` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL
     [`\k:K n. p2aw_dq ((gW:K->real^M->real) k) (e k) ((hn:num->real) n) gu x <
               p2aw_dlim ((W:K->real^M->real) k) (e k) psi x +
               eps / (&(CARD(Ix:K->bool)) + &1)`; `Ix:K->bool`] P2AW_FINITE_EVENTUALLY) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`ball(x:real^M,r)`; `(W:K->real^M->real) k`; `psi:real^M->real`;
                     `(e:K->real^M) k`; `x:real^M`] P2AW_DQ_POINT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "W" (MP_TAC o SPEC `k:K`) THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `eps / (&(CARD(Ix:K->bool)) + &1)`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &n + &1`] THEN
      DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `&0 < Em` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `min d1 (r / Em)` (GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]
        (ASSUME `((hn:num->real) ---> &0) sequentially`))) THEN
      ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_SUB_RZERO] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `abs((hn:num->real) n) <= h0 /\ &0 < abs(hn n)` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "hn" THEN ASM_SIMP_TAC[REAL_ARITH `~(x = &0) ==> &0 < abs x`];
        ALL_TAC] THEN
      USE_THEN "PTS" (MP_TAC o SPECL [`k:K`; `x:real^M`; `(hn:num->real) n`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`(W:K->real^M->real) k`; `(gW:K->real^M->real) k`; `u:real^M->real`;
                     `gu:real^M->real`; `(e:K->real^M) k`; `(hn:num->real) n`; `x:real^M`;
                     `K1:real^M->bool`] P2AW_DQ_LOCAL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN CONJ_TAC THEN
        ASM_MESON_TAC[SUBSET];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `norm((e:K->real^M) k) <= Em` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`x:real^M`; `(hn:num->real) n`; `(e:K->real^M) k`; `r:real`; `Em:real`]
                    P2AW_BALL_STEP) THEN
      MP_TAC(ISPECL [`x:real^M`; `(hn:num->real) n / &2`; `(e:K->real^M) k`; `r:real`; `Em:real`]
                    P2AW_BALL_STEP) THEN
      ASM_REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `p2aw_dq ((W:K->real^M->real) k) ((e:K->real^M) k) ((hn:num->real) n) psi x` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC P2AW_DQ_BARRIER THEN ASM_SIMP_TAC[] THEN
        CONJ_TAC THEN
        (USE_THEN "W" (MP_TAC o SPEC `k:K`) THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
         DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM SET_TAC[]);
        MATCH_MP_TAC(REAL_ARITH `abs(a - b) < c ==> a < b + c`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n0:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum Ix (\k. p2aw_dlim ((W:K->real^M->real) k) ((e:K->real^M) k) psi x +
                            eps / (&(CARD(Ix:K->bool)) + &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[SUM_ADD; SUM_CONST] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= f /\ c <= e ==> a + c <= f + e`) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[REAL_ARITH `&0 < &n + &1`; REAL_ARITH `n * e / m = (n * e) / m`;
               REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e ==> n * e <= e * (n + &1)`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ix:K->bool`; `e:K->real^M`; `gW:K->real^M->real`; `gu:real^M->real`;
                 `ku:real^M->bool`; `phi:real^M->real`; `kp:real^M->bool`; `Fb:real^M->real`;
                 `max CQ CF`; `hn:num->real`] P2AW_NBP_GLOBAL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:K` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `kW:K->real^M->bool`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(kW:K->real^M->bool) k` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= cf ==> a <= max cq cf`) THEN ASM_SIMP_TAC[];
      EXPAND_TAC "hn" THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= cq ==> a <= max cq cf`) THEN ASM_SIMP_TAC[];
      EXISTS_TAC `N:real^M->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. lift((phi:real^M->real) x * Fb x)) integrable_on s /\
    integral s (\x. lift(phi x * Fb x)) = integral kp (\x. lift(phi x * Fb x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
      FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[GSYM INTEGRABLE_RESTRICT_UNIV] o check (fun th ->
        can (find_term ((=) `Fb:real^M->real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "integrable_on")) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
      ASM_CASES_TAC `(x:real^M) IN kp` THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM; COND_ID]];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
      EXISTS_TAC `kp:real^M->bool` THEN
      ASM_SIMP_TAC[SUBSET_REFL; REAL_MUL_LZERO; LIFT_NUM]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral (:real^M)
      (\x. lift(gu x * sum Ix (\k. p2aw_dlim ((gW:K->real^M->real) k) (e k) phi x))) =
    integral s (\x. lift((u:real^M->real) x *
                         sum Ix (\k. p2aw_dlim ((W:K->real^M->real) k) (e k) phi x)))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral s
      (\x. lift(gu x * sum Ix (\k. p2aw_dlim ((gW:K->real^M->real) k) (e k) phi x)))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
      EXISTS_TAC `kp:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC(MESON[LIFT_NUM; REAL_MUL_RZERO] `a = &0 ==> lift(b * a) = vec 0`) THEN
      MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC P2AW_DLIM_SUPPORT THEN EXISTS_TAC `kp:real^M->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_EQ] THEN ASM_CASES_TAC `(x:real^M) IN kp` THENL
     [SUBGOAL_THEN `(gu:real^M->real) x = u x` SUBST1_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC P2AW_DLIM_LOCAL THEN
      EXISTS_TAC `(uW:K->real^M->bool) k` THEN ASM_MESON_TAC[SUBSET];
      SUBGOAL_THEN
       `sum Ix (\k. p2aw_dlim ((gW:K->real^M->real) k) (e k) phi x) = &0 /\
        sum Ix (\k. p2aw_dlim ((W:K->real^M->real) k) (e k) phi x) = &0`
      (fun th -> REWRITE_TAC[th; REAL_MUL_RZERO]) THEN
      CONJ_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC P2AW_DLIM_SUPPORT THEN EXISTS_TAC `kp:real^M->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s (\x. lift((u:real^M->real) x *
                         sum Ix (\k. p2aw_dlim ((W:K->real^M->real) k) (e k) phi x))) =
    vsum Ix (\k. --(integral s (\x. lift(W k x * p2aw_d1 u (e k) x * p2aw_d1 phi (e k) x))))`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; LIFT_SUM; o_DEF] THEN
    W(fun (asl,w) -> MP_TAC(ISPECL [`\k:K x:real^M. lift((u:real^M->real) x *
                                    p2aw_dlim ((W:K->real^M->real) k) (e k) phi x)`;
                                    `s:real^M->bool`; `Ix:K->bool`] INTEGRAL_VSUM)) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      USE_THEN "IBP" (MP_TAC o SPEC `k:K`) THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "IBP" (MP_TAC o SPEC `k:K`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "vsum")) (concl th))) THEN
  ASM_SIMP_TAC[DROP_VSUM; DROP_NEG; o_DEF; SUM_NEG] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `--a <= b ==> &0 <= b + a`) THEN FIRST_ASSUM ACCEPT_TAC);;

