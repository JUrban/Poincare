(* ========================================================================= *)
(* pc_sch_vflow: the pancake chart of the surgery (SCH5V_PANCAKE). Near a    *)
(* component C of a regular level x3 = a of a collared sphere S = g(S^2) the *)
(* vertical field                                                            *)
(*   V = e3 - chi (d3 rho / |grad_h rho|^2) grad_h rho,  rho = |g'(x)|^2 - 1, *)
(* is tangent to S near C and has V3 = 1; its complete flow Psi carries the *)
(* planar disc bounded by C (a planar ball chart c from SCH_R2) to the       *)
(* chart Theta y = Psi(lambda y3, (c(y1,y2), a)) in which S is the lateral  *)
(* cylinder, the height is a + lambda y3, and Theta is a product near the    *)
(* axis.                                                                     *)
(* ========================================================================= *)

needs "src/pc_sch_tube.ml";;
needs "src/pc_sch_planar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Complete flows of bounded smooth fields on real^N: first                  *)
(* integrals, translation where the field is constant, and the height of a   *)
(* field with constant last component.                                       *)
(* ------------------------------------------------------------------------- *)

(* The statement of SMT_RFLOW_BOUNDED_COMPLETE (pc_smt_straight.ml), proved  *)
(* again here because this file does not load that one.                      *)

let SCH5V_BOUNDED_COMPLETE = prove
 (`!(v:real^N->real^N) B.
        smooth_map_on (:real^N) v /\ (!x. norm(v x) <= B)
        ==> !y. ode_vf_maxint v (:real^N) y = (:real^1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (v:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`] ODE_VF_FIELD_FACTS) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[ode_vf_maxint] THEN
  MATCH_MP_TAC ODE_MAXINT_LINEAR_GROWTH THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IS_INTERVAL_UNIV; ODE_IN_PCROSS; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`B:real`; `&0`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; SNDCART_PASTECART]);;

(* Basic facts of a complete flow. *)

let SCH5V_FLOW_FACTS = prove
 (`!(v:real^N->real^N).
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
     ==> (!x. ode_vf_flow v (:real^N) (vec 0) x = x) /\
         (!x t. ((\s. ode_vf_flow v (:real^N) s x) has_vector_derivative
                 v(ode_vf_flow v (:real^N) t x)) (at t)) /\
         (!x s t. ode_vf_flow v (:real^N) t (ode_vf_flow v (:real^N) s x) =
                  ode_vf_flow v (:real^N) (s + t) x) /\
         smooth_map_on (:real^(1,N)finite_sum)
           (\w. ode_vf_flow v (:real^N) (fstcart w) (sndcart w)) /\
         (!t. diffeomorphism_on (:real^N) (:real^N)
                (ode_vf_flow v (:real^N) t) (ode_vf_flow v (:real^N) (--t)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (v:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `x:real^N`] ODE_VF_MAXIMAL) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `x:real^N`] ODE_VF_MAXIMAL) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `x:real^N`; `s:real^1`] ODE_VF_GROUP) THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`] ODE_VF_FLOW_SMOOTH) THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN
    SUBGOAL_THEN `ode_vf_domain (v:real^N->real^N) (:real^N) = (:real^(1,N)finite_sum)`
    (fun th -> SIMP_TAC[th]) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; ode_vf_domain; IN_ELIM_THM] THEN
    X_GEN_TAC `w:real^(1,N)finite_sum` THEN
    MAP_EVERY EXISTS_TAC [`fstcart(w:real^(1,N)finite_sum)`; `sndcart(w:real^(1,N)finite_sum)`] THEN
    ASM_REWRITE_TAC[PASTECART_FST_SND; IN_UNIV];
    GEN_TAC THEN
    MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `t:real^1`] ODE_VF_FLOW_DIFFEO) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; UNIV_GSPEC]]);;

(* A real function with zero derivative along the flow is constant on       *)
(* trajectory segments that stay in the region.                              *)

let SCH5V_ZERO_DERIV_CONST = prove
 (`!(f:real^1->real^N) a b.
     drop a <= drop b /\
     (!u. u IN interval[a,b] ==> (f has_vector_derivative vec 0) (at u))
     ==> f b = f a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `interval[a:real^1,b]`] HAS_DERIVATIVE_ZERO_CONSTANT) THEN
  REWRITE_TAC[CONVEX_INTERVAL] THEN ANTS_TAC THENL
   [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1`) THEN ASM_REWRITE_TAC[has_vector_derivative] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `a:real^1` th) THEN MP_TAC(SPEC `b:real^1` th)) THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_SIMP_TAC[REAL_LE_REFL]);;

let SCH5V_FLOW_FIRST_INTEGRAL = prove
 (`!(v:real^N->real^N) (F0:real^N->real^1) U x t.
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
     open U /\ (!y. y IN U ==> (F0 has_derivative frechet_derivative F0 (at y)) (at y) /\
                               frechet_derivative F0 (at y) (v y) = vec 0) /\
     (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
          ==> ode_vf_flow v (:real^N) u x IN U)
     ==> F0(ode_vf_flow v (:real^N) t x) = F0 x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^N) (v:real^N->real^N)`)) THEN
  SUBGOAL_THEN `!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                    ==> ((\s. (F0:real^N->real^1) (ode_vf_flow (v:real^N->real^N) (:real^N) s x))
                         has_vector_derivative vec 0) (at u)` ASSUME_TAC THENL
   [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\s. ode_vf_flow (v:real^N->real^N) (:real^N) s x`;
                   `(v:real^N->real^N) (ode_vf_flow v (:real^N) u x)`; `F0:real^N->real^1`;
                   `frechet_derivative (F0:real^N->real^1) (at (ode_vf_flow v (:real^N) u x))`;
                   `u:real^1`] SCH5_CHAIN_VECTOR) THEN
    REWRITE_TAC[o_DEF] THEN
    SUBGOAL_THEN `ode_vf_flow (v:real^N->real^N) (:real^N) u x IN U` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= drop t \/ drop t <= &0`) THENL
   [MP_TAC(ISPECL [`\s. (F0:real^N->real^1) (ode_vf_flow (v:real^N->real^N) (:real^N) s x)`;
                   `vec 0:real^1`; `t:real^1`] SCH5V_ZERO_DERIV_CONST) THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`\s. (F0:real^N->real^1) (ode_vf_flow (v:real^N->real^N) (:real^N) s x)`;
                   `t:real^1`; `vec 0:real^1`] SCH5V_ZERO_DERIV_CONST) THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION];
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM)]]);;

(* Where the field is a constant e the flow is the translation by e. *)

let SCH5V_FLOW_TRANSLATE = prove
 (`!(v:real^N->real^N) U x t e.
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
     (!y. y IN U ==> v y = e) /\
     (!u. u IN interval[lift(min (&0) (drop t)),lift(max (&0) (drop t))]
          ==> x + drop u % e IN U)
     ==> ode_vf_flow v (:real^N) t x = x + drop t % e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (v:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  ABBREV_TAC `J = interval[lift(min (&0) (drop t)),lift(max (&0) (drop t))]` THEN
  SUBGOAL_THEN `(vec 0:real^1) IN J /\ (t:real^1) IN J` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `J:real^1->bool`;
                 `\u:real^1. x + drop u % (e:real^N)`; `vec 0:real^1`] ODE_VF_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC[IS_INTERVAL_INTERVAL]; ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N->real^N) (x + drop u % e) = e` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(u:real^1) IN J` THEN EXPAND_TAC "J" THEN SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV) [VECTOR_ADD_SYM] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_RID] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
    REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* A field with last component 1 raises the height uniformly. *)

let SCH5V_FLOW_HEIGHT = prove
 (`!(v:real^3->real^3).
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!y. (v y)$3 = &1)
     ==> !t x. (ode_vf_flow v (:real^3) t x)$3 = x$3 + drop t`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `!u. ((\s. lift((ode_vf_flow (v:real^3->real^3) (:real^3) s x)$3 - drop s))
                     has_vector_derivative vec 0) (at u)` ASSUME_TAC THENL
   [X_GEN_TAC `u:real^1` THEN REWRITE_TAC[LIFT_SUB; LIFT_DROP] THEN
    SUBGOAL_THEN `vec 0:real^1 = lift(&1) - lift(&1)` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_SUB_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\s. ode_vf_flow (v:real^3->real^3) (:real^3) s x`;
                     `(v:real^3->real^3) (ode_vf_flow v (:real^3) u x)`;
                     `\y:real^3. lift(y$3)`; `\y:real^3. lift(y$3)`; `u:real^1`]
        SCH5_CHAIN_VECTOR) THEN
      ASM_REWRITE_TAC[o_DEF; HAS_DERIVATIVE_LIFT_COMPONENT];
      REWRITE_TAC[has_vector_derivative; GSYM LIFT_CMUL; REAL_MUL_RID; LIFT_DROP] THEN
      REWRITE_TAC[HAS_DERIVATIVE_ID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift((ode_vf_flow (v:real^3->real^3) (:real^3) t x)$3 - drop t) =
                lift((ode_vf_flow v (:real^3) (vec 0) x)$3 - drop(vec 0))` MP_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH `&0 <= drop t \/ drop t <= &0`) THENL
     [MP_TAC(ISPECL [`\s. lift((ode_vf_flow (v:real^3->real^3) (:real^3) s x)$3 - drop s)`;
                     `vec 0:real^1`; `t:real^1`] SCH5V_ZERO_DERIV_CONST);
      MP_TAC(ISPECL [`\s. lift((ode_vf_flow (v:real^3->real^3) (:real^3) s x)$3 - drop s)`;
                     `t:real^1`; `vec 0:real^1`] SCH5V_ZERO_DERIV_CONST)] THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[LIFT_EQ; DROP_VEC] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The defining function rho(x) = |g'(x)|^2 of a collared                   *)
(* sphere, its gradient, and critical points of the height: the tangent     *)
(* plane is the kernel of d rho, so t is critical iff the horizontal part of *)
(* grad rho vanishes at g t.                                                 *)
(* ------------------------------------------------------------------------- *)

let sch5v_grad = new_definition
 `sch5v_grad (g':real^3->real^3) (x:real^3) =
    vector[drop(frechet_derivative (\y. lift(norm(g' y) pow 2)) (at x) (basis 1));
           drop(frechet_derivative (\y. lift(norm(g' y) pow 2)) (at x) (basis 2));
           drop(frechet_derivative (\y. lift(norm(g' y) pow 2)) (at x) (basis 3))]:real^3`;;

let SCH5V_RHO_DERIV = prove
 (`!(g:real^3->real^3) g' t.
     sch_neck g g' /\ t IN annulus (&1 / &2) (&2)
     ==> ((\y. lift(norm(g' y) pow 2)) has_derivative
          (\w. &2 % lift(t dot frechet_derivative g' (at (g t)) w))) (at (g t)) /\
         (!w. frechet_derivative (\y. lift(norm(g' y) pow 2)) (at (g t)) w =
              &2 % lift(t dot frechet_derivative g' (at (g t)) w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift(norm((g':real^3->real^3) y) pow 2)) has_derivative
     (\w. &2 % lift(t dot frechet_derivative g' (at ((g:real^3->real^3) t)) w))) (at (g t))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. lift(norm((g':real^3->real^3) y) pow 2)) =
                  (\z:real^3. lift(norm z pow 2)) o g'` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\w. &2 % lift(t dot frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t)) w)) =
      (\z. &2 % lift(t dot z)) o frechet_derivative g' (at (g t))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]));;

let SCH5V_GRAD_DOT = prove
 (`!(g:real^3->real^3) g' t w.
     sch_neck g g' /\ t IN annulus (&1 / &2) (&2)
     ==> sch5v_grad g' (g t) dot w = &2 * (t dot frechet_derivative g' (at (g t)) w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5V_RHO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t)))`
  ASSUME_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[sch5v_grad] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
    [SPEC `w:real^3` (MATCH_MP SCH5_LINEAR_BASIS3 th)]) THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [DOT_3] THEN REWRITE_TAC[VECTOR_3] THEN
  ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* Critical points of the height in terms of the gradient. *)

let SCH5V_CRIT_GRAD = prove
 (`!(g:real^3->real^3) g' t.
     sch_neck g g' /\ t IN sphere(vec 0,&1)
     ==> ~(sch5v_grad g' (g t) = vec 0) /\
         (sch_crit g t <=> (sch5v_grad g' (g t))$1 = &0 /\ (sch5v_grad g' (g t))$2 = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH5_SPHERE_IN_ANNULUS) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5_NECK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. sch5v_grad g' ((g:real^3->real^3) t) dot w =
                    &2 * (t dot frechet_derivative (g':real^3->real^3) (at (g t)) w)`
  (LABEL_TAC "GD") THENL
   [GEN_TAC THEN MATCH_MP_TAC SCH5V_GRAD_DOT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3) dot t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1];
    ALL_TAC] THEN
  ABBREV_TAC `p = sch5v_grad g' ((g:real^3->real^3) t)` THEN
  SUBGOAL_THEN `~(p:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "GD" (MP_TAC o SPEC `frechet_derivative (g:real^3->real^3) (at t) t`) THEN
    REWRITE_TAC[ASSUME `p:real^3 = vec 0`; DOT_LZERO; ASSUME `(t:real^3) dot t = &1`;
      ASSUME `!h. frechet_derivative (g':real^3->real^3) (at ((g:real^3->real^3) t))
                    (frechet_derivative g (at t) h) = h`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch_crit] THEN
  SUBGOAL_THEN `!w. (?v. orthogonal t v /\ w = frechet_derivative (g:real^3->real^3) (at t) v) <=>
                    (p:real^3) dot w = &0` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`; `w:real^3`]
      SCH5_NECK_TANGENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "GD" (fun th -> REWRITE_TAC[th; orthogonal]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(!v. orthogonal t v ==> (frechet_derivative (g:real^3->real^3) (at t) v)$3 = &0)
                <=> (!w. (p:real^3) dot w = &0 ==> w$3 = &0)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN MESON_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vector[--((p:real^3)$3 * p$1); --(p$3 * p$2);
                                        p$1 pow 2 + p$2 pow 2]:real^3`) THEN
    REWRITE_TAC[DOT_3; VECTOR_3] THEN
    ANTS_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^3)$1 * p$1 = &0 /\ p$2 * p$2 = &0` MP_TAC THENL
     [MP_TAC(SPEC `(p:real^3)$1` REAL_LE_SQUARE) THEN
      MP_TAC(SPEC `(p:real^3)$2` REAL_LE_SQUARE) THEN
      UNDISCH_TAC `(p:real^3)$1 * p$1 + p$2 * p$2 = &0` THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ENTIRE]];
    STRIP_TAC THEN X_GEN_TAC `w:real^3` THEN
    REWRITE_TAC[DOT_3; ASSUME `(p:real^3)$1 = &0`; ASSUME `(p:real^3)$2 = &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    SUBGOAL_THEN `~((p:real^3)$3 = &0)` MP_TAC THENL
     [UNDISCH_TAC `~(p:real^3 = vec 0)` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
      REWRITE_TAC[ASSUME `(p:real^3)$1 = &0`; ASSUME `(p:real^3)$2 = &0`];
      REWRITE_TAC[REAL_ENTIRE] THEN CONV_TAC TAUT]]);;

(* ------------------------------------------------------------------------- *)
(* Helpers (points of a closed set near a compact set lie near               *)
(* the intersection; displacement of a flow of a bounded field), the        *)
(* defining function rho = |g'|^2 on the open collar O, its gradient on O,   *)
(* and the horizontal field w.                                               *)
(* ------------------------------------------------------------------------- *)

let SCH5V_NEAR_COMPACT = prove
 (`!s k u:real^N->bool.
     closed s /\ compact k /\ open u /\ s INTER k SUBSET u
     ==> ?e. &0 < e /\ !p q. p IN s /\ q IN k /\ dist(p,q) < e ==> p IN u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `s DIFF u:real^N->bool`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[CLOSED_DIFF] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "E"))) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`p:real^N`; `q:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:real^N) IN u` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "E" (MP_TAC o SPECL [`q:real^N`; `p:real^N`]) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC);;

let SCH5V_FLOW_DISPLACEMENT = prove
 (`!(v:real^N->real^N) B.
     smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
     (!y. norm(v y) <= B)
     ==> !x s t. norm(ode_vf_flow v (:real^N) s x - ode_vf_flow v (:real^N) t x) <=
                 B * abs(drop s - drop t)`,
  GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^N) (v:real^N->real^N)`)) THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `s:real^1`; `t:real^1`] THEN
  MP_TAC(ISPECL [`\u. ode_vf_flow (v:real^N->real^N) (:real^N) u x`;
                 `\u. (v:real^N->real^N) (ode_vf_flow v (:real^N) u x)`;
                 `(:real^1)`; `B:real`] VECTOR_DIFFERENTIABLE_BOUND) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `t:real^1`]) THEN
  REWRITE_TAC[NORM_1; DROP_SUB]);;

(* The defining function and its gradient on the open collar. *)

let SCH5V_NECK_OPEN = prove
 (`!(g:real^3->real^3) g'.
     sch_neck g g'
     ==> open(IMAGE g (annulus (&1 / &2) (&2))) /\
         smooth_map_on (IMAGE g (annulus (&1 / &2) (&2))) g' /\
         smooth_map_on (annulus (&1 / &2) (&2)) g /\
         (!x. x IN annulus (&1 / &2) (&2) ==> g'(g x) = x) /\
         (!y. y IN IMAGE g (annulus (&1 / &2) (&2)) ==> g(g' y) = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_neck; diffeomorphism_on] THEN SIMP_TAC[]);;

let SCH5V_RHO_SMOOTH = prove
 (`!(g:real^3->real^3) g'.
     sch_neck g g'
     ==> smooth_map_on (IMAGE g (annulus (&1 / &2) (&2))) (\z. lift(norm(g' z) pow 2))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_NECK_OPEN) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN ASM_REWRITE_TAC[]);;

let SCH5V_GRAD_SMOOTH = prove
 (`!(g:real^3->real^3) g'.
     sch_neck g g'
     ==> smooth_map_on (IMAGE g (annulus (&1 / &2) (&2))) (sch5v_grad g')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH5V_RHO_SMOOTH) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_NECK_OPEN) THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                 `sch5v_grad (g':real^3->real^3)`] SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  X_GEN_TAC `k:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[sch5v_grad; VECTOR_3; LIFT_DROP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]);;

let SCH5V_RHO_HAS_DERIVATIVE = prove
 (`!(g:real^3->real^3) g' y.
     sch_neck g g' /\ y IN IMAGE g (annulus (&1 / &2) (&2))
     ==> ((\z. lift(norm(g' z) pow 2)) has_derivative
          (\v. lift(sch5v_grad g' y dot v))) (at y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5V_RHO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `v:real^3` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`; `v:real^3`]
    SCH5V_GRAD_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LIFT_CMUL]);;

let SCH5V_IN_SURFACE = prove
 (`!(g:real^3->real^3) g' y.
     sch_neck g g' /\ y IN IMAGE g (annulus (&1 / &2) (&2))
     ==> (y IN IMAGE g (sphere(vec 0,&1)) <=> norm(g' y) pow 2 = &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_NECK_OPEN) THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `(g':real^3->real^3) ((g:real^3->real^3) t) = t` SUBST1_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(t:real^3) pow 2 = &1 <=> t IN sphere(vec 0,&1)` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_POW_2; IN_SPHERE_0; NORM_EQ_1]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^3) IN annulus (&1 / &2) (&2)` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t:real^3 = s` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `!x:real^3. x IN annulus (&1 / &2) (&2) ==> (g':real^3->real^3)(g x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `t:real^3` th) THEN MP_TAC(SPEC `s:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_TAC THEN EXISTS_TAC `t:real^3` THEN ASM_REWRITE_TAC[]]);;

(* The horizontal correction field w = -(p3 / |p_h|^2) p_h, p = grad rho,   *)
(* defined where the horizontal part p_h of the gradient is nonzero.         *)

let sch5v_oh = new_definition
 `sch5v_oh (g:real^3->real^3) (g':real^3->real^3) =
    {x | x IN IMAGE g (annulus (&1 / &2) (&2)) /\
         ~((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2 = &0)}`;;

let sch5v_hfield = new_definition
 `sch5v_hfield (g':real^3->real^3) (x:real^3) =
    (--((sch5v_grad g' x)$3) /
     ((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2)) %
    vector[(sch5v_grad g' x)$1; (sch5v_grad g' x)$2; &0]:real^3`;;

let SCH5V_OH_OPEN = prove
 (`!(g:real^3->real^3) g'. sch_neck g g' ==> open(sch5v_oh g g')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_NECK_OPEN) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH5V_GRAD_SMOOTH) THEN
  SUBGOAL_THEN `!k. smooth_map_on (IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)))
                      (\x. lift((sch5v_grad (g':real^3->real^3) x)$k))` (LABEL_TAC "C") THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[sch5v_oh] THEN
  SUBGOAL_THEN
   `{x | x IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)) /\
         ~((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2 = &0)} =
    {x | x IN IMAGE g (annulus (&1 / &2) (&2)) /\
         (\x. lift((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2)) x IN
         (:real^1) DIFF {vec 0}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
  ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                 `\x. lift((sch5v_grad (g':real^3->real^3) x)$1 pow 2)`;
                 `\x. lift((sch5v_grad (g':real^3->real^3) x)$2 pow 2)`]
    SMOOTH_MAP_ON_LIFT_ADD) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                   `\x. lift((sch5v_grad (g':real^3->real^3) x)$1)`; `2`]
      SMOOTH_MAP_ON_LIFT_POW);
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                   `\x. lift((sch5v_grad (g':real^3->real^3) x)$2)`; `2`]
      SMOOTH_MAP_ON_LIFT_POW)] THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

(* ------------------------------------------------------------------------- *)
(* The vertical field V = e3 + chi w for a cutoff chi with                   *)
(* compact support L in the region Oh where the horizontal gradient is       *)
(* nonzero: V is smooth and bounded, V3 = 1, V = e3 off L, and V is         *)
(* tangent to the level sets of rho where chi = 1.                          *)
(* ------------------------------------------------------------------------- *)

let SCH5V_HFIELD_SMOOTH = prove
 (`!(g:real^3->real^3) g'.
     sch_neck g g' ==> smooth_map_on (sch5v_oh g g') (sch5v_hfield g')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH5V_OH_OPEN) THEN
  SUBGOAL_THEN `!k. smooth_map_on (sch5v_oh g g')
                      (\x. lift((sch5v_grad (g':real^3->real^3) x)$k))`
  (LABEL_TAC "C") THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
    ASM_SIMP_TAC[SCH5V_GRAD_SMOOTH] THEN
    REWRITE_TAC[sch5v_oh; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (sch5v_oh g g')
                  (\x. lift((sch5v_grad (g':real^3->real^3) x)$1 pow 2 +
                            (sch5v_grad g' x)$2 pow 2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`;
                   `\x. lift((sch5v_grad (g':real^3->real^3) x)$1 pow 2)`;
                   `\x. lift((sch5v_grad (g':real^3->real^3) x)$2 pow 2)`]
      SMOOTH_MAP_ON_LIFT_ADD) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`;
                     `\x. lift((sch5v_grad (g':real^3->real^3) x)$1)`; `2`]
        SMOOTH_MAP_ON_LIFT_POW);
      MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`;
                     `\x. lift((sch5v_grad (g':real^3->real^3) x)$2)`; `2`]
        SMOOTH_MAP_ON_LIFT_POW)] THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (sch5v_oh g g')
                  (\x. lift(--((sch5v_grad (g':real^3->real^3) x)$3) /
                            ((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`;
                   `\x. lift(--((sch5v_grad (g':real^3->real^3) x)$3))`;
                   `\x. lift((sch5v_grad (g':real^3->real^3) x)$1 pow 2 +
                             (sch5v_grad g' x)$2 pow 2)`]
      SMOOTH_MAP_ON_LIFT_DIV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`;
                     `\x. lift((sch5v_grad (g':real^3->real^3) x)$3)`]
        SMOOTH_MAP_ON_LIFT_NEG) THEN ASM_REWRITE_TAC[LIFT_DROP];
      REWRITE_TAC[sch5v_oh; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (sch5v_oh g g')
                  (\x. vector[(sch5v_grad (g':real^3->real^3) x)$1;
                              (sch5v_grad g' x)$2; &0]:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`;
                   `\x. vector[(sch5v_grad (g':real^3->real^3) x)$1;
                               (sch5v_grad g' x)$2; &0]:real^3`]
      SMOOTH_MAP_ON_COMPONENTWISE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
    X_GEN_TAC `k:num` THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[VECTOR_3; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sch5v_hfield (g':real^3->real^3) =
    (\x. (--((sch5v_grad g' x)$3) /
          ((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2)) %
         vector[(sch5v_grad g' x)$1; (sch5v_grad g' x)$2; &0])`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; sch5v_hfield]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`;
                 `\x. lift(--((sch5v_grad (g':real^3->real^3) x)$3) /
                           ((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2))`;
                 `\x. vector[(sch5v_grad (g':real^3->real^3) x)$1;
                             (sch5v_grad g' x)$2; &0]:real^3`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let SCH5V_HFIELD_FACTS = prove
 (`!(g':real^3->real^3) x.
     (sch5v_hfield g' x)$3 = &0 /\
     (~((sch5v_grad g' x)$1 pow 2 + (sch5v_grad g' x)$2 pow 2 = &0)
      ==> sch5v_grad g' x dot (basis 3 + sch5v_hfield g' x) = &0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[sch5v_hfield; VECTOR_MUL_COMPONENT; VECTOR_3; REAL_MUL_RZERO] THEN
  SIMP_TAC[DOT_RADD; DOT_RMUL; DOT_BASIS; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[DOT_3; VECTOR_3] THEN
  ABBREV_TAC `p = sch5v_grad (g':real^3->real^3) x` THEN CONV_TAC REAL_FIELD);;

let SCH5V_FIELD = prove
 (`!(g:real^3->real^3) g' (chi:real^3->real) L.
     sch_neck g g' /\ smooth_map_on (:real^3) (\x. lift(chi x)) /\
     (!x. &0 <= chi x /\ chi x <= &1) /\
     compact L /\ L SUBSET sch5v_oh g g' /\ (!x. ~(x IN L) ==> chi x = &0)
     ==> smooth_map_on (:real^3) (\x. basis 3 + chi x % sch5v_hfield g' x) /\
         (?B. !x. norm(basis 3 + chi x % sch5v_hfield g' x) <= B) /\
         (!x. (basis 3 + chi x % sch5v_hfield g' x)$3 = &1) /\
         (!x. ~(x IN L) ==> basis 3 + chi x % sch5v_hfield g' x = basis 3) /\
         (!x. x IN sch5v_oh g g' /\ chi x = &1
              ==> sch5v_grad g' x dot (basis 3 + chi x % sch5v_hfield g' x) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH5V_OH_OPEN) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCH5V_HFIELD_SMOOTH) THEN
  SUBGOAL_THEN `!x. ~(x IN L) ==> basis 3 + (chi:real^3->real) x % sch5v_hfield g' x = basis 3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN sch5v_oh g g'` THENL
     [EXISTS_TAC `sch5v_oh (g:real^3->real^3) g'` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MP_TAC(ISPECL [`sch5v_oh (g:real^3->real^3) g'`; `\x. lift((chi:real^3->real) x)`;
                     `sch5v_hfield (g':real^3->real^3)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      EXISTS_TAC `(:real^3) DIFF L` THEN
      ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV; COMPACT_IMP_CLOSED; IN_DIFF; IN_UNIV] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. basis 3:real^3` THEN
      REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_DIFF; IN_UNIV] THEN ASM_SIMP_TAC[]];
    SUBGOAL_THEN `bounded(IMAGE (sch5v_hfield (g':real^3->real^3)) L)` MP_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sch5v_oh (g:real^3->real^3) g'` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      ALL_TAC] THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&1 + M` THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN L` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(basis 3:real^3) + norm((chi:real^3->real) x % sch5v_hfield g' x)` THEN
      REWRITE_TAC[NORM_TRIANGLE] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; NORM_MUL] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= M ==> &1 + x <= &1 + M`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * norm(sch5v_hfield (g':real^3->real^3) x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        MP_TAC(SPEC `x:real^3` (ASSUME `!x. &0 <= (chi:real^3->real) x /\ chi x <= &1`)) THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC];
    GEN_TAC THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; SCH5V_HFIELD_FACTS] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC_ALL SCH5V_HFIELD_FACTS)) THEN
    UNDISCH_TAC `(x:real^3) IN sch5v_oh g g'` THEN
    REWRITE_TAC[sch5v_oh; IN_ELIM_THM] THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Neighbourhoods of a compact set, a smooth cutoff equal to 1               *)
(* near a compact set C and supported near C inside a given open set, and    *)
(* the geometry of a regular level: a component C is compact, lies in the   *)
(* region Oh of nonzero horizontal gradient, and has positive distance from  *)
(* the rest of the level.                                                    *)
(* ------------------------------------------------------------------------- *)

let SCH5V_OPEN_NBHD = prove
 (`!(c:real^N->bool) r. open {x | ?y. y IN c /\ dist(y,x) < r}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\y:real^N. y IN c`; `\y x:real^N. dist(y,x) < r`] OPEN_EXISTS_IN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM ball; OPEN_BALL]);;

let SCH5V_COMPACT_NBHD_IN_OPEN = prove
 (`!(c:real^N->bool) w.
     compact c /\ open w /\ c SUBSET w
     ==> ?d. &0 < d /\ !y x. y IN c /\ dist(y,x) < d ==> x IN w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `(:real^N) DIFF w`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^N`; `x:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN w` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "D" (MP_TAC o SPECL [`y:real^N`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC);;

let SCH5V_CUTOFF = prove
 (`!(c:real^N->bool) w D.
     compact c /\ open w /\ c SUBSET w /\ &0 < D
     ==> ?d chi L. &0 < d /\ d < D /\
                   smooth_map_on (:real^N) (\x. lift(chi x)) /\
                   (!x. &0 <= chi x /\ chi x <= &1) /\
                   (!y x. y IN c /\ dist(y,x) < d ==> chi x = &1 /\ x IN w) /\
                   compact L /\ L SUBSET w /\
                   (!x. x IN L ==> ?y. y IN c /\ dist(y,x) < D) /\
                   (!x. ~(x IN L) ==> chi x = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:real^N->bool`; `w:real^N->bool`] SCH5V_COMPACT_NBHD_IN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1"))) THEN
  ABBREV_TAC `d = min d1 D / &2` THEN
  SUBGOAL_THEN `&0 < d /\ d < D /\ d < d1 /\ &2 * d <= D` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`{y + z:real^N | y IN c /\ z IN cball(vec 0,d)}`;
                 `w INTER {x:real^N | ?y. y IN c /\ dist(y,x) < &2 * d}`]
    GRGE_EUCLID_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL; OPEN_INTER; SCH5V_OPEN_NBHD] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_INTER; IN_ELIM_THM; IN_CBALL_0] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(y:real^N,y + z) = norm(z:real^N)` ASSUME_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `y - (y + z):real^N = --z`; NORM_NEG]; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "D1" MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:real^N->real` (X_CHOOSE_THEN `L:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `chi:real^N->real`; `L:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^N`; `x:real^N`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_CBALL_0] THEN
      MAP_EVERY EXISTS_TAC [`y:real^N`; `x - y:real^N`] THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `y + (x - y):real^N = x`] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "D1" MATCH_MP_TAC THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN w INTER {x:real^N | ?y. y IN c /\ dist(y,x) < &2 * d}`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Geometry of a regular level. *)

let SCH5V_SURFACE_COMPACT = prove
 (`!(g:real^3->real^3) g' (a:real).
     sch_neck g g'
     ==> compact(IMAGE g (sphere(vec 0,&1))) /\
         IMAGE g (sphere(vec 0,&1)) SUBSET IMAGE g (annulus (&1 / &2) (&2)) /\
         compact(sch_level g a) /\ sch_level g a SUBSET IMAGE g (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_NECK_OPEN) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (g:real^3->real^3) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    SUBGOAL_THEN `sch_level (g:real^3->real^3) a =
                  IMAGE g (sphere(vec 0,&1)) INTER {x:real^3 | x$3 = a}` SUBST1_TAC THENL
     [REWRITE_TAC[sch_level] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_INTER_CLOSED; CLOSED_STANDARD_HYPERPLANE];
    REWRITE_TAC[sch_level] THEN SET_TAC[]]);;

let SCH5V_LEVEL_COMPONENT = prove
 (`!(g:real^3->real^3) g' a C.
     sch_neck g g' /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     C IN components(sch_level g a) /\ FINITE(components(sch_level g a))
     ==> compact C /\ ~(C = {}) /\ C SUBSET sch_level g a /\
         C SUBSET sch5v_oh g g' /\
         (!x. x IN C ==> x$3 = a /\ x IN IMAGE g (sphere(vec 0,&1))) /\
         ?d0. &0 < d0 /\
              !x y. x IN sch_level g a /\ ~(x IN C) /\ y IN C ==> d0 <= dist(x,y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`] SCH5V_SURFACE_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `C SUBSET sch_level (g:real^3->real^3) a` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(C:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `sch_level (g:real^3->real^3) a` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
      MATCH_MP_TAC CLOSED_COMPONENTS THEN
      EXISTS_TAC `sch_level (g:real^3->real^3) a` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN C ==> x$3 = a /\ x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `C SUBSET sch_level (g:real^3->real^3) a` THEN
    REWRITE_TAC[sch_level; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(MP (SPEC `x:real^3` (ASSUME `!x. x IN C ==> x$3 = a /\
                                     x IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`))
              (ASSUME `(x:real^3) IN C`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^3`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `t:real^3`] SCH5V_CRIT_GRAD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[sch5v_oh; IN_ELIM_THM; REAL_SOS_EQ_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN UNDISCH_TAC `(t:real^3) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~sch_crit (g:real^3->real^3) t` MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(MP (SPEC `t:real^3` (ASSUME `!t. sch_crit (g:real^3->real^3) t ==> ~((g t)$3 = a)`))
               (ASSUME `sch_crit (g:real^3->real^3) t`)) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(sch_level (g:real^3->real^3) a DIFF C)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sch_level (g:real^3->real^3) a DIFF C =
                  UNIONS(components(sch_level g a) DELETE C)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_DELETE] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `D:real^3->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `D:real^3->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
       [EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`sch_level (g:real^3->real^3) a`; `D:real^3->bool`; `C:real^3->bool`]
        COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN D` THEN UNDISCH_TAC `(x:real^3) IN C` THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CLOSED_COMPONENTS THEN EXISTS_TAC `sch_level (g:real^3->real^3) a` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:real^3->bool`; `sch_level (g:real^3->real^3) a DIFF C`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The planar chart of the disc bounded by a level circle.                   *)
(* The planar neck Fn is first compressed radially so that its collar is     *)
(* thin; SCH_R2 then gives a ball chart c with c(S^1) = J = Fn(S^1),         *)
(* c(ball 1) = inside J and c(ball 2) inside J, J and the thin collar.       *)
(* ------------------------------------------------------------------------- *)

let sch5v_pr = new_definition
 `sch5v_pr (x:real^3) = vector[x$1; x$2]:real^2`;;

let sch5v_at = new_definition
 `sch5v_at (a:real) (z:real^2) = vector[z$1; z$2; a]:real^3`;;

let SCH5V_PR_AT = prove
 (`(!a z. sch5v_pr(sch5v_at a z) = z) /\
   (!a z. (sch5v_at a z)$3 = a) /\
   (!x:real^3. sch5v_at (x$3) (sch5v_pr x) = x) /\
   (!a z w. sch5v_at a z = sch5v_at a w <=> z = w) /\
   (!a z w. dist(sch5v_at a z,sch5v_at a w) = dist(z,w))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[sch5v_pr; sch5v_at; CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3;
              VECTOR_2; VECTOR_3; dist; NORM_EQ; DOT_2; DOT_3; VECTOR_SUB_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let SCH5V_PR_AT_SMOOTH = prove
 (`linear sch5v_pr /\ smooth_map_on (:real^3) sch5v_pr /\
   (!a. smooth_map_on (:real^2) (sch5v_at a)) /\
   (!a. sch5v_at a continuous_on (:real^2))`,
  SUBGOAL_THEN `linear sch5v_pr` ASSUME_TAC THENL
   [REWRITE_TAC[linear; sch5v_pr; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. smooth_map_on (:real^2) (sch5v_at a)` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `sch5v_at a =
                  (\z:real^2. (\w:real^2. vector[w$1; w$2; &0]:real^3) z + a % basis 3)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV] THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GRGE_SMOOTH_LINEAR; OPEN_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let SCH5V_PLANAR_COMPRESS = prove
 (`!(Fn:real^2->real^2) Fn' k.
     sch_neck Fn Fn' /\ &0 < k /\ k < &1
     ==> sch_neck (Fn o sch5_radial k) (sch5_radinv k o Fn') /\
         IMAGE (Fn o sch5_radial k) (sphere(vec 0,&1)) = IMAGE Fn (sphere(vec 0,&1)) /\
         IMAGE (Fn o sch5_radial k) (annulus (&1 / &2) (&2)) =
         IMAGE Fn (annulus (&1 - k / &2) (&1 + k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `annulus (&1 - k / &2) (&1 + k) SUBSET annulus (&1 / &2) (&2):real^2->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:2`,`:N`] (SPEC `k:real` SCH5_RADIAL_DIFFEO)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `diffeomorphism_on (annulus (&1 - k / &2) (&1 + k))
                  (IMAGE (Fn:real^2->real^2) (annulus (&1 - k / &2) (&1 + k))) Fn Fn'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH2_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^2->bool`;
                          `IMAGE (Fn:real^2->real^2) (annulus (&1 / &2) (&2))`] THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS; GSYM sch_neck];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((Fn:real^2->real^2) o sch5_radial k) (annulus (&1 / &2) (&2)) =
                IMAGE Fn (annulus (&1 - k / &2) (&1 + k))` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2)) (annulus (&1 - k / &2) (&1 + k))
                   (sch5_radial k:real^2->real^2) (sch5_radinv k)` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sch_neck] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `annulus (&1 - k / &2) (&1 + k):real^2->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[SCH5_RADIAL_SPHERE]]);;

let SCH5V_PLANAR_CHART = prove
 (`!(Fn:real^2->real^2) Fn' k.
     sch_neck Fn Fn' /\ &0 < k /\ k < &1
     ==> ?c c'. sch_ball c c' /\
                IMAGE c (sphere(vec 0,&1)) = IMAGE Fn (sphere(vec 0,&1)) /\
                IMAGE c (ball(vec 0,&1)) = inside(IMAGE Fn (sphere(vec 0,&1))) /\
                IMAGE c (cball(vec 0,&1)) =
                IMAGE Fn (sphere(vec 0,&1)) UNION inside(IMAGE Fn (sphere(vec 0,&1))) /\
                IMAGE c (ball(vec 0,&2)) SUBSET
                IMAGE Fn (sphere(vec 0,&1)) UNION inside(IMAGE Fn (sphere(vec 0,&1))) UNION
                IMAGE Fn (annulus (&1 - k / &2) (&1 + k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Fn:real^2->real^2`; `Fn':real^2->real^2`; `k:real`] SCH5V_PLANAR_COMPRESS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(Fn:real^2->real^2) o sch5_radial k`; `sch5_radinv k o (Fn':real^2->real^2)`]
    (REWRITE_RULE[SCH_R2_STATEMENT] SCH_R2)) THEN
  ASM_REWRITE_TAC[sch_fills] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CASE"))))) THEN
  MAP_EVERY EXISTS_TAC [`c:real^2->real^2`; `c':real^2->real^2`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^2. x IN sphere(vec 0,&1) ==> (c:real^2->real^2) x = Fn x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN annulus (&3 / &4) (&2) /\ norm x = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^2) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "CASE" (DISJ_CASES_THEN (MP_TAC o SPEC `x:real^2`)) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[SCH5_RADIAL_SPHERE; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID] THEN
    ASM_SIMP_TAC[SCH5_RADIAL_SPHERE; IN_SPHERE_0; REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^2. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\
                             (c:real^2->real^2) x = c y ==> x = y` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^2->real^2) (sphere(vec 0,&1)) =
                IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (c:real^2->real^2) x = f x)
                            ==> IMAGE c s = IMAGE f s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `ball(vec 0:real^2,&1) = cball(vec 0,&1) DIFF sphere(vec 0,&1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (c:real^2->real^2) (cball(vec 0,&1) DIFF sphere(vec 0,&1)) =
                  IMAGE c (cball(vec 0,&1)) DIFF IMAGE c (sphere(vec 0,&1))` SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_DIFF_INJ THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      UNDISCH_TAC `(x:real^2) IN cball(vec 0,&1)` THEN
      UNDISCH_TAC `(y:real^2) IN sphere(vec 0,&1)` THEN
      ASM_REWRITE_TAC[IN_BALL_0; IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1))` INSIDE_NO_OVERLAP) THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  ASM_CASES_TAC `norm(x:real^2) <= &1` THENL
   [SUBGOAL_THEN `(c:real^2->real^2) x IN IMAGE c (cball(vec 0,&1))` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN annulus (&3 / &4) (&2) /\ (x:real^2) IN annulus (&1 / &2) (&2) /\
                &1 < norm x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ2_TAC THEN
  USE_THEN "CASE" (DISJ_CASES_THEN (MP_TAC o SPEC `x:real^2`)) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THENL
   [MP_TAC(ISPECL [`k:real`; `x:real^2`] SCH5_RADIAL_FACTS) THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`k:real`; `inv(norm(x:real^2) pow 2) % x`] SCH5_RADIAL_FACTS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    SUBGOAL_THEN `norm(inv(norm(x:real^2) pow 2) % x) = inv(norm x)` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
      UNDISCH_TAC `&1 < norm(x:real^2)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&2) < inv(norm(x:real^2)) /\ inv(norm x) < inv(&1)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The flow box.  For a complete flow Psi with height raised                *)
(* uniformly and a planar diffeomorphism c of U, the map                     *)
(* Theta y = Psi (lam y3) (c(y1,y2), a) is a diffeomorphism of the slab      *)
(* U x (-h,h) onto an open set, with an explicit inverse.                    *)
(* ------------------------------------------------------------------------- *)

let SCH5V_FLOW_COMPOSE_SMOOTH = prove
 (`!(Psi:real^1->real^N->real^N) s (f:real^M->real) (k:real^M->real^N).
     smooth_map_on (:real^(1,N)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s k
     ==> smooth_map_on s (\x. Psi (lift(f x)) (k x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (Psi:real^1->real^N->real^N) (lift((f:real^M->real) x))
                       ((k:real^M->real^N) x)) =
                (\w. Psi (fstcart w) (sndcart w)) o (\x. pastecart (lift(f x)) (k x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^(1,N)finite_sum)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX]);;

let SCH5V_FLOW_INV = prove
 (`!(Psi:real^1->real^N->real^N).
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x)
     ==> !s x. Psi (lift(--s)) (Psi (lift s) x) = x /\ Psi (lift s) (Psi (lift(--s)) x) = x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM LIFT_ADD] THEN
  REWRITE_TAC[REAL_ADD_RINV; REAL_ADD_LINV; LIFT_NUM] THEN ASM_REWRITE_TAC[]);;

let SCH5V_LIFT_AFFINE = prove
 (`!s (m:real) (b:real) k. open s ==> smooth_map_on s (\x:real^N. lift(m * x$k + b))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(m * x$k)`; `\x:real^N. lift b`]
    SMOOTH_MAP_ON_LIFT_ADD) THEN
  REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GRGE_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; GSYM LIFT_ADD;
              GSYM LIFT_CMUL; LIFT_EQ] THEN
  REPEAT STRIP_TAC THEN CONV_TAC REAL_RING);;

let SCH5V_FLOWBOX_FACTS = prove
 (`!(Psi:real^1->real^3->real^3) (c:real^2->real^2) c' U a lam.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     diffeomorphism_on U (IMAGE c U) c c' /\ &0 < lam
     ==> (!y. (Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y))))$3 = a + lam * y$3) /\
         (!y. Psi (lift(--((Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y))))$3 - a)))
                  (Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y)))) =
              sch5v_at a (c(sch5v_pr y))) /\
         (!y. sch5v_pr y IN U
              ==> vector[(c'(sch5v_pr(Psi (lift(--((Psi (lift(lam * y$3))
                                (sch5v_at a (c(sch5v_pr y))))$3 - a)))
                             (Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y)))))))$1;
                         (c'(sch5v_pr(Psi (lift(--((Psi (lift(lam * y$3))
                                (sch5v_at a (c(sch5v_pr y))))$3 - a)))
                             (Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y)))))))$2;
                         ((Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y))))$3 - a) / lam]
                  = y) /\
         (!x. sch5v_pr(Psi (lift(--(x$3 - a))) x) IN IMAGE c U
              ==> sch5v_pr(vector[(c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$1;
                                  (c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$2;
                                  (x$3 - a) / lam]:real^3) IN U /\
                  (vector[(c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$1;
                          (c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$2;
                          (x$3 - a) / lam]:real^3)$3 = (x$3 - a) / lam /\
                  Psi (lift(lam * (x$3 - a) / lam))
                      (sch5v_at a (c(sch5v_pr(vector[(c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$1;
                                  (c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$2;
                                  (x$3 - a) / lam]:real^3)))) = x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "P0") (CONJUNCTS_THEN2 (LABEL_TAC "GRP")
    (CONJUNCTS_THEN2 (LABEL_TAC "HT") (CONJUNCTS_THEN2 (LABEL_TAC "DF") ASSUME_TAC)))) THEN
  USE_THEN "DF" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!s x. (Psi:real^1->real^3->real^3) (lift(--s)) (Psi (lift s) x) = x /\
                      Psi (lift s) (Psi (lift(--s)) x) = x` (LABEL_TAC "INV") THENL
   [MATCH_MP_TAC SCH5V_FLOW_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. (Psi:real^1->real^3->real^3) (lift(lam * y$3))
                      (sch5v_at a ((c:real^2->real^2)(sch5v_pr y)))$3 = a + lam * y$3`
  (LABEL_TAC "H1") THENL
   [USE_THEN "HT" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SCH5V_PR_AT; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (Psi:real^1->real^3->real^3)
                      (lift(--((Psi (lift(lam * y$3))
                                 (sch5v_at a ((c:real^2->real^2)(sch5v_pr y))))$3 - a)))
                      (Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y)))) =
                    sch5v_at a (c(sch5v_pr y))` (LABEL_TAC "B1") THENL
   [GEN_TAC THEN USE_THEN "H1" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ARITH `(a + l) - a = l`] THEN USE_THEN "INV" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  USE_THEN "B1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "H1" (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[SCH5V_PR_AT; REAL_ARITH `(a + l) - a = l`] THEN
    SUBGOAL_THEN `(c':real^2->real^2) ((c:real^2->real^2) (sch5v_pr y)) = sch5v_pr y`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `z = sch5v_pr((Psi:real^1->real^3->real^3) (lift(--(x$3 - a))) x)` THEN
  SUBGOAL_THEN `sch5v_pr(vector[((c':real^2->real^2) z)$1; (c' z)$2;
                                ((x:real^3)$3 - a) / lam]:real^3) = c' z` SUBST1_TAC THENL
   [REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_3]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_3] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^2->real^2) ((c':real^2->real^2) z) = z` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lam * ((x:real^3)$3 - a) / lam = x$3 - a` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `sch5v_at a z = (Psi:real^1->real^3->real^3) (lift(--((x:real^3)$3 - a))) x`
  SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN
    SUBGOAL_THEN `a = ((Psi:real^1->real^3->real^3) (lift(--((x:real^3)$3 - a))) x)$3`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
     [USE_THEN "HT" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[LIFT_DROP] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[SCH5V_PR_AT]];
    ALL_TAC] THEN
  USE_THEN "INV" (fun th -> REWRITE_TAC[th]));;

let SCH5V_FLOWBOX = prove
 (`!(Psi:real^1->real^3->real^3) (c:real^2->real^2) c' U a lam h.
     (!x. Psi (vec 0) x = x) /\ (!x s t. Psi t (Psi s x) = Psi (s + t) x) /\
     (!t x. (Psi t x)$3 = x$3 + drop t) /\
     smooth_map_on (:real^(1,3)finite_sum) (\w. Psi (fstcart w) (sndcart w)) /\
     diffeomorphism_on U (IMAGE c U) c c' /\ &0 < lam /\ &0 < h
     ==> diffeomorphism_on {y | sch5v_pr y IN U /\ abs(y$3) < h}
           {x | sch5v_pr(Psi (lift(--(x$3 - a))) x) IN IMAGE c U /\
                abs((x$3 - a) / lam) < h}
           (\y. Psi (lift(lam * y$3)) (sch5v_at a (c(sch5v_pr y))))
           (\x. vector[(c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$1;
                       (c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$2;
                       (x$3 - a) / lam]:real^3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `c:real^2->real^2`; `c':real^2->real^2`;
                 `U:real^2->bool`; `a:real`; `lam:real`] SCH5V_FLOWBOX_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "H1") (CONJUNCTS_THEN2 (LABEL_TAC "B1")
    (CONJUNCTS_THEN2 (LABEL_TAC "L1") (LABEL_TAC "R1")))) THEN
  UNDISCH_TAC `diffeomorphism_on U (IMAGE c U) (c:real^2->real^2) c'` THEN
  GEN_REWRITE_TAC LAND_CONV [diffeomorphism_on] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^3)
                  (\x. sch5v_pr((Psi:real^1->real^3->real^3) (lift(--(x$3 - a))) x))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x. sch5v_pr((Psi:real^1->real^3->real^3) (lift(--(x$3 - a))) x)) =
                  sch5v_pr o (\x. Psi (lift(--(x$3 - a))) x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN REWRITE_TAC[OPEN_UNIV; SCH5V_PR_AT_SMOOTH] THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `(:real^3)`; `\x:real^3. --(x$3 - a)`;
                   `\x:real^3. x`] SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^3. lift(--(&1) * x$3 + a)` THEN
    SIMP_TAC[SCH5V_LIFT_AFFINE; OPEN_UNIV] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `D = {y:real^3 | sch5v_pr y IN U /\ abs(y$3) < h}` THEN
  ABBREV_TAC `E = {x | sch5v_pr((Psi:real^1->real^3->real^3) (lift(--(x$3 - a))) x) IN
                       IMAGE (c:real^2->real^2) U /\ abs((x$3 - a) / lam) < h}` THEN
  ABBREV_TAC `Th = \y:real^3. (Psi:real^1->real^3->real^3) (lift(lam * y$3))
                                (sch5v_at a ((c:real^2->real^2)(sch5v_pr y)))` THEN
  ABBREV_TAC `Th' = \x:real^3.
     vector[((c':real^2->real^2)(sch5v_pr((Psi:real^1->real^3->real^3)
              (lift(--(x$3 - a))) x)))$1;
            (c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$2; (x$3 - a) / lam]:real^3` THEN
  SUBGOAL_THEN `!y. y IN D ==> (Th:real^3->real^3) y IN E /\ (Th':real^3->real^3)(Th y) = y`
  (LABEL_TAC "S1") THENL
   [X_GEN_TAC `y:real^3` THEN
    MAP_EVERY EXPAND_TAC ["D"; "E"; "Th'"; "Th"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "L1" (fun th -> SIMP_TAC[th; ASSUME `sch5v_pr y IN U`]) THEN
    USE_THEN "B1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "H1" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SCH5V_PR_AT; REAL_ARITH `(a + l) - a = l`] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      SUBGOAL_THEN `(lam * (y:real^3)$3) / lam = y$3` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN E ==> (Th':real^3->real^3) x IN D /\ (Th:real^3->real^3)(Th' x) = x`
  (LABEL_TAC "S2") THENL
   [X_GEN_TAC `x:real^3` THEN
    MAP_EVERY EXPAND_TAC ["D"; "E"; "Th"; "Th'"] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "R1" (fun th -> MP_TAC(MP (SPEC `x:real^3` th) (ASSUME
      `sch5v_pr((Psi:real^1->real^3->real^3) (lift(--((x:real^3)$3 - a))) x) IN
       IMAGE (c:real^2->real^2) U`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(D:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    SUBGOAL_THEN `{y:real^3 | sch5v_pr y IN U /\ abs(y$3) < h} =
                  {y | sch5v_pr y IN U} INTER {y | (\y:real^3. lift(y$3)) y IN ball(vec 0,h)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_LIFT]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[SCH5V_PR_AT_SMOOTH; LINEAR_LIFT_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(E:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    SUBGOAL_THEN `{x | sch5v_pr((Psi:real^1->real^3->real^3) (lift(--(x$3 - a))) x) IN
                       IMAGE (c:real^2->real^2) U /\ abs((x$3 - a) / lam) < h} =
                  {x | (\x. sch5v_pr(Psi (lift(--(x$3 - a))) x)) x IN IMAGE c U} INTER
                  {x | (\x:real^3. lift(inv lam * x$3 + --(a / lam))) x IN ball(vec 0,h)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_LIFT] THEN
      X_GEN_TAC `x:real^3` THEN
      SUBGOAL_THEN `((x:real^3)$3 - a) / lam = inv lam * x$3 + --(a / lam)`
      (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN X_GEN_TAC `x:real^3` THEN
    MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[INTERIOR_UNIV; IN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[SCH5V_LIFT_AFFINE; OPEN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[diffeomorphism_on] THEN
  REWRITE_TAC[ASSUME `open(D:real^3->bool)`; ASSUME `open(E:real^3->bool)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    USE_THEN "S1" (fun s1 -> USE_THEN "S2" (fun s2 -> MESON_TAC[s1; s2]));
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    USE_THEN "S1" (fun s1 -> USE_THEN "S2" (fun s2 -> MESON_TAC[s1; s2]));
    USE_THEN "S1" (fun th -> SIMP_TAC[th]);
    USE_THEN "S2" (fun th -> SIMP_TAC[th]);
    EXPAND_TAC "Th" THEN
    MP_TAC(ISPECL [`Psi:real^1->real^3->real^3`; `D:real^3->bool`; `\y:real^3. lam * y$3`;
                   `\y:real^3. sch5v_at a ((c:real^2->real^2)(sch5v_pr y))`]
      SCH5V_FLOW_COMPOSE_SMOOTH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`D:real^3->bool`; `lam:real`; `&0`; `3`] SCH5V_LIFT_AFFINE) THEN
      ASM_REWRITE_TAC[REAL_ADD_RID];
      SUBGOAL_THEN `(\y:real^3. sch5v_at a ((c:real^2->real^2)(sch5v_pr y))) =
                    sch5v_at a o (c o sch5v_pr)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SCH5V_PR_AT_SMOOTH] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "D" THEN SET_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH]]];
    EXPAND_TAC "Th'" THEN
    MP_TAC(ISPECL [`E:real^3->bool`;
      `\x. vector[((c':real^2->real^2)(sch5v_pr((Psi:real^1->real^3->real^3)
                     (lift(--(x$3 - a))) x)))$1;
                  (c'(sch5v_pr(Psi (lift(--(x$3 - a))) x)))$2; (x$3 - a) / lam]:real^3`]
      SMOOTH_MAP_ON_COMPONENTWISE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
    SUBGOAL_THEN `smooth_map_on E (\x. (c':real^2->real^2)
                    (sch5v_pr((Psi:real^1->real^3->real^3) (lift(--(x$3 - a))) x)))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(\x. (c':real^2->real^2)
                      (sch5v_pr((Psi:real^1->real^3->real^3) (lift(--(x$3 - a))) x))) =
                    c' o (\x. sch5v_pr(Psi (lift(--(x$3 - a))) x))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
      EXISTS_TAC `IMAGE (c:real^2->real^2) U` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[VECTOR_3] THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\x:real^3. lift(inv lam * x$3 + --(a / lam))` THEN
      ASM_SIMP_TAC[SCH5V_LIFT_AFFINE] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING]]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for the pancake chart: discs and slabs in terms of                *)
(* the projection, a thin collar of a planar neck, spheres of necks are     *)
(* topological spheres, connected sets off a set lie on one side, and the   *)
(* two parts of the slab off the lateral cylinder are connected.             *)
(* ------------------------------------------------------------------------- *)

let SCH5V_PR_FACTS = prove
 (`!y:real^3 r.
     (sch5v_pr y IN sphere(vec 0,&1) <=> y$1 pow 2 + y$2 pow 2 = &1) /\
     (sch5v_pr y IN ball(vec 0,r) <=> &0 < r /\ y$1 pow 2 + y$2 pow 2 < r pow 2) /\
     (sch5v_pr y IN cball(vec 0,r) <=> &0 <= r /\ y$1 pow 2 + y$2 pow 2 <= r pow 2)`,
  REWRITE_TAC[IN_SPHERE_0; IN_BALL_0; IN_CBALL_0; NORM_EQ_SQUARE; NORM_LT_SQUARE;
              NORM_LE_SQUARE; sch5v_pr; DOT_2; VECTOR_2] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let sch5v_slab = new_definition
 `sch5v_slab (H:real) = {y:real^3 | y$1 pow 2 + y$2 pow 2 < &4 /\ abs(y$3) < H}`;;

let SCH5V_SLAB_EQ = prove
 (`!H. sch5v_slab H = {y | sch5v_pr y IN ball(vec 0,&2) /\ abs(y$3) < H}`,
  REWRITE_TAC[sch5v_slab; EXTENSION; IN_ELIM_THM; SCH5V_PR_FACTS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let SCH5V_SLAB_FACTS = prove
 (`sch_slab_nbhd = sch5v_slab (&5 / &4) /\
   (!H. &5 / &4 <= H ==> sch_slab_nbhd SUBSET sch5v_slab H) /\
   (!H. open(sch5v_slab H))`,
  REWRITE_TAC[sch_slab_nbhd; sch5v_slab] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[GSYM sch5v_slab; SCH5V_SLAB_EQ] THEN
    SUBGOAL_THEN `{y:real^3 | sch5v_pr y IN ball(vec 0,&2) /\ abs(y$3) < H} =
                  {y | sch5v_pr y IN ball(vec 0,&2)} INTER
                  {y | (\y:real^3. lift(y$3)) y IN ball(vec 0,H)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_LIFT]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    REWRITE_TAC[OPEN_BALL] THEN GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[SCH5V_PR_AT_SMOOTH; LINEAR_LIFT_COMPONENT]]);;

let SCH5V_DIST_NORMALIZE = prove
 (`!x:real^N. ~(x = vec 0) ==> dist(inv(norm x) % x,x) = abs(norm x - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN
  SUBGOAL_THEN `inv(norm x) % (x:real^N) - x = (inv(norm x) - &1) % x` SUBST1_TAC THENL
   [VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `(inv(norm(x:real^N)) - &1) * norm x = --(norm x - &1)` MP_TAC THENL
   [UNDISCH_TAC `&0 < norm(x:real^N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < n ==> abs n = n`]);;

let SCH5V_THIN_COLLAR = prove
 (`!(Fn:real^2->real^2) e.
     Fn continuous_on annulus (&1 / &2) (&2) /\ &0 < e
     ==> ?k. &0 < k /\ k < &1 /\
             !x. x IN annulus (&1 - k / &2) (&1 + k)
                 ==> ?j. j IN sphere(vec 0,&1) /\ dist(Fn j,Fn x) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(Fn:real^2->real^2) uniformly_continuous_on
                  {x | &3 / &4 <= norm x /\ norm x <= &3 / &2}` MP_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus (&1 / &2) (&2):real^2->bool` THEN
      ASM_REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `{x:real^2 | &3 / &4 <= norm x /\ norm x <= &3 / &2} =
                    cball(vec 0,&3 / &2) DIFF ball(vec 0,&3 / &4)` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]]];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "U"))) THEN
  EXISTS_TAC `min (del / &2) (&1 / &4)` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^2` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^2 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `&1 - min (del / &2) (&1 / &4) / &2 <
                                               norm(vec 0:real^2)` THEN
    REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv(norm x) % (x:real^2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  REMOVE_THEN "U" MATCH_MP_TAC THEN
  ASM_SIMP_TAC[SCH5V_DIST_NORMALIZE; IN_ELIM_THM; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM;
               REAL_MUL_LINV; NORM_EQ_0] THEN
  ASM_REAL_ARITH_TAC);;

let SCH5V_NECK_SPHERE_HOMEOMORPHIC = prove
 (`!(g:real^3->real^3) g'.
     sch_neck g g' ==> IMAGE g (sphere(vec 0,&1)) homeomorphic sphere(vec 0:real^3,&1)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN EXISTS_TAC `g:real^3->real^3` THEN
  REWRITE_TAC[COMPACT_SPHERE] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_NECK_OPEN) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2) /\ (y:real^3) IN annulus (&1 / &2) (&2)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!x:real^3. x IN annulus (&1 / &2) (&2) ==> (g':real^3->real^3)(g x) = x` THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `x:real^3` th) THEN MP_TAC(SPEC `y:real^3` th)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* The statement of SMT_CONNECTED_INSIDE_OUTSIDE (pc_smt_pb2.ml), proved     *)
(* again here because this file does not load that one.                      *)

let SCH5V_CONNECTED_SIDE = prove
 (`!s c:real^N->bool.
        connected c /\ c INTER s = {}
        ==> c SUBSET inside s \/ c SUBSET outside s`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `!y:real^N. y IN c ==> connected_component ((:real^N) DIFF s) x y`
  ASSUME_TAC THENL
   [REWRITE_TAC[connected_component] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN inside s \/ x IN outside s` MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` INSIDE_UNION_OUTSIDE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_MESON_TAC[INSIDE_SAME_COMPONENT];
    DISJ2_TAC THEN ASM_MESON_TAC[OUTSIDE_SAME_COMPONENT]]);;

(* The two parts of the slab off the lateral cylinder are connected. *)

let SCH5V_SLAB_PARTS_CONNECTED = prove
 (`!H. connected {y:real^3 | y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1} /\
       connected {y:real^3 | y IN sch5v_slab H /\ &1 < y$1 pow 2 + y$2 pow 2}`,
  GEN_TAC THEN ABBREV_TAC `m = \w:real^(2,1)finite_sum.
                    vector[(fstcart w)$1; (fstcart w)$2; drop(sndcart w)]:real^3` THEN
  SUBGOAL_THEN `linear(m:real^(2,1)finite_sum->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                DROP_ADD; DROP_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P:real^2->bool.
      connected P
      ==> connected {y:real^3 | sch5v_pr y IN P /\ abs(y$3) < H}`
  (LABEL_TAC "C") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `{y:real^3 | sch5v_pr y IN P /\ abs(y$3) < H} =
                  IMAGE (m:real^(2,1)finite_sum->real^3)
                    (P PCROSS interval(lift(--(H)),lift(H)))` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART; PASTECART_IN_PCROSS] THEN
      X_GEN_TAC `y:real^3` THEN EXPAND_TAC "m" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
      EQ_TAC THENL
       [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`sch5v_pr y`; `lift((y:real^3)$3)`] THEN
        ASM_REWRITE_TAC[LIFT_DROP] THEN
        REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2] THEN
        ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `z:real^2` (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)) THEN
        ASM_REWRITE_TAC[VECTOR_3] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `sch5v_pr(vector[(z:real^2)$1; z$2; drop t]:real^3) = z`
          (fun th -> ASM_REWRITE_TAC[th]) THEN
          REWRITE_TAC[sch5v_pr; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_3];
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONNECTED_PCROSS; CONNECTED_INTERVAL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{y:real^3 | y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1} =
                  {y:real^3 | sch5v_pr y IN ball(vec 0,&1) /\ abs(y$3) < H}`
    SUBST1_TAC THENL
     [REWRITE_TAC[sch5v_slab; EXTENSION; IN_ELIM_THM; SCH5V_PR_FACTS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      USE_THEN "C" MATCH_MP_TAC THEN REWRITE_TAC[CONNECTED_BALL]];
    SUBGOAL_THEN `{y:real^3 | y IN sch5v_slab H /\ &1 < y$1 pow 2 + y$2 pow 2} =
                  {y:real^3 | sch5v_pr y IN {z:real^2 | &1 < norm(z - vec 0) /\
                                                       norm(z - vec 0) < &2} /\
                              abs(y$3) < H}`
    SUBST1_TAC THENL
     [REWRITE_TAC[sch5v_slab; EXTENSION; IN_ELIM_THM; VECTOR_SUB_RZERO] THEN
      REWRITE_TAC[REAL_ARITH `&1 < n <=> ~(n <= &1)`; NORM_LE_SQUARE; NORM_LT_SQUARE] THEN
      REWRITE_TAC[sch5v_pr; DOT_2; VECTOR_2; REAL_POW_2] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      USE_THEN "C" MATCH_MP_TAC THEN SIMP_TAC[CONNECTED_ANNULUS; DIMINDEX_2; LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* A chart of the slab in which a topological sphere S is the               *)
(* lateral cylinder puts the solid cylinder on one side of S and the rest   *)
(* of the slab on the other (Jordan-Brouwer: both sides have frontier S).   *)
(* ------------------------------------------------------------------------- *)

let SCH5V_SIDES = prove
 (`!(S:real^3->bool) (Theta:real^3->real^3) Theta' H.
     &0 < H /\ S homeomorphic sphere(vec 0:real^3,&1) /\
     diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
     (!y. y IN sch5v_slab H ==> (Theta y IN S <=> y$1 pow 2 + y$2 pow 2 = &1))
     ==> (!y. y IN sch5v_slab H
              ==> (Theta y IN inside S <=> y$1 pow 2 + y$2 pow 2 < &1)) \/
         (!y. y IN sch5v_slab H
              ==> (Theta y IN outside S <=> y$1 pow 2 + y$2 pow 2 < &1))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "IN")))) THEN
  GEN_REWRITE_TAC LAND_CONV [diffeomorphism_on] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^3->bool` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `S:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `N1 = {y:real^3 | y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1}` THEN
  ABBREV_TAC `N2 = {y:real^3 | y IN sch5v_slab H /\ &1 < y$1 pow 2 + y$2 pow 2}` THEN
  SUBGOAL_THEN `connected(IMAGE (Theta:real^3->real^3) N1) /\
                connected(IMAGE (Theta:real^3->real^3) N2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN REWRITE_TAC[SCH5V_SLAB_PARTS_CONNECTED] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sch5v_slab H` THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; SET_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Theta:real^3->real^3) N1 INTER S = {} /\
                IMAGE (Theta:real^3->real^3) N2 INTER S = {}` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) MP_TAC) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN USE_THEN "IN" (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Theta:real^3->real^3) (sch5v_slab H) SUBSET
                IMAGE Theta N1 UNION IMAGE Theta N2 UNION S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N1"; "N2"] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `(y:real^3)$1 pow 2 + y$2 pow 2 < &1 \/
                               y$1 pow 2 + y$2 pow 2 = &1 \/ &1 < y$1 pow 2 + y$2 pow 2`) THENL
     [DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [DISJ2_TAC THEN DISJ2_TAC THEN USE_THEN "IN" (fun th -> ASM_SIMP_TAC[th]);
        DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `S SUBSET closure(inside S:real^3->bool) /\ S SUBSET closure(outside S)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun tm -> MP_TAC(ASSUME tm))
      [`frontier(inside S:real^3->bool) = S`; `frontier(outside S:real^3->bool) = S`] THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Theta:real^3->real^3)(basis 1) IN S /\ basis 1 IN sch5v_slab H`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(basis 1:real^3) IN sch5v_slab H /\ (basis 1:real^3)$1 pow 2 + (basis 1:real^3)$2 pow 2 = &1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[sch5v_slab; IN_ELIM_THM] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "IN" (fun th -> ASM_SIMP_TAC[th])];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (Theta:real^3->real^3) (sch5v_slab H) INTER inside S = {}) /\
                ~(IMAGE (Theta:real^3->real^3) (sch5v_slab H) INTER outside S = {})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (Theta:real^3->real^3) (sch5v_slab H)`; `inside S:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    MP_TAC(ISPECL [`IMAGE (Theta:real^3->real^3) (sch5v_slab H)`; `outside S:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN CONJ_TAC THEN
    EXISTS_TAC `(Theta:real^3->real^3)(basis 1)` THEN
    (CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `IMAGE (Theta:real^3->real^3) N1`] SCH5V_CONNECTED_SIDE) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `IMAGE (Theta:real^3->real^3) N2`] SCH5V_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1
                    ==> (Theta:real^3->real^3) y IN IMAGE Theta N1` (LABEL_TAC "M1") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "N1" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H /\ &1 < y$1 pow 2 + y$2 pow 2
                    ==> (Theta:real^3->real^3) y IN IMAGE Theta N2` (LABEL_TAC "M2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "N2" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THENL
   [UNDISCH_TAC `~(IMAGE (Theta:real^3->real^3) (sch5v_slab H) INTER outside S = {})` THEN
    UNDISCH_TAC `IMAGE (Theta:real^3->real^3) (sch5v_slab H) SUBSET
                 IMAGE Theta N1 UNION IMAGE Theta N2 UNION S` THEN
    UNDISCH_TAC `IMAGE (Theta:real^3->real^3) N1 SUBSET inside S` THEN
    UNDISCH_TAC `IMAGE (Theta:real^3->real^3) N2 SUBSET inside S` THEN
    UNDISCH_TAC `inside S INTER outside S:real^3->bool = {}` THEN
    UNDISCH_TAC `outside S INTER S:real^3->bool = {}` THEN SET_TAC[];
    DISJ2_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `(y:real^3)$1 pow 2 + y$2 pow 2 < &1 \/
                               y$1 pow 2 + y$2 pow 2 = &1 \/ &1 < y$1 pow 2 + y$2 pow 2`) THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "M1" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[];
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [SUBGOAL_THEN `(Theta:real^3->real^3) y IN S` MP_TAC THENL
         [USE_THEN "IN" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
        ASM_REWRITE_TAC[REAL_LT_REFL] THEN ASM SET_TAC[];
        SUBGOAL_THEN `~((y:real^3)$1 pow 2 + y$2 pow 2 < &1)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "M2" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[]]];
    DISJ1_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `(y:real^3)$1 pow 2 + y$2 pow 2 < &1 \/
                               y$1 pow 2 + y$2 pow 2 = &1 \/ &1 < y$1 pow 2 + y$2 pow 2`) THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "M1" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[];
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [SUBGOAL_THEN `(Theta:real^3->real^3) y IN S` MP_TAC THENL
         [USE_THEN "IN" (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
        ASM_REWRITE_TAC[REAL_LT_REFL] THEN ASM SET_TAC[];
        SUBGOAL_THEN `~((y:real^3)$1 pow 2 + y$2 pow 2 < &1)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "M2" (MP_TAC o SPEC `y:real^3`) THEN ASM SET_TAC[]]];
    UNDISCH_TAC `~(IMAGE (Theta:real^3->real^3) (sch5v_slab H) INTER inside S = {})` THEN
    UNDISCH_TAC `IMAGE (Theta:real^3->real^3) (sch5v_slab H) SUBSET
                 IMAGE Theta N1 UNION IMAGE Theta N2 UNION S` THEN
    UNDISCH_TAC `IMAGE (Theta:real^3->real^3) N1 SUBSET outside S` THEN
    UNDISCH_TAC `IMAGE (Theta:real^3->real^3) N2 SUBSET outside S` THEN
    UNDISCH_TAC `inside S INTER outside S:real^3->bool = {}` THEN
    UNDISCH_TAC `inside S INTER S:real^3->bool = {}` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The pancake chart from a field that is vertical away from                *)
(* C and has |g'|^2 as a first integral near C.  For small lam the chart    *)
(* Theta y = Psi(lam y3)(c(y1,y2), a) meets S exactly in the lateral         *)
(* cylinder (flow lines from the disc stay near the disc, and S near the     *)
(* disc is near C), is the product chart near the axis, and puts the solid  *)
(* cylinder on one side of S.                                                *)
(* ------------------------------------------------------------------------- *)

let SCH5V_SEGMENT_BOUNDS = prove
 (`!s u:real^1.
     u IN interval[vec 0,s] UNION interval[s,vec 0]
     ==> abs(drop u) <= abs(drop s) /\ abs(drop s - drop u) <= abs(drop s)`,
  REWRITE_TAC[IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC);;

let SCH5V_PANCAKE_CHART = prove
 (`!(g:real^3->real^3) g' a C (c:real^2->real^2) c' K0 dax (v:real^3->real^3) B d e lam H.
     sch_neck g g' /\ sch_ball c c' /\
     C SUBSET IMAGE g (sphere(vec 0,&1)) /\
     (!z. z IN ball(vec 0,&2) ==> sch5v_at a (c z) IN K0) /\
     IMAGE g (sphere(vec 0,&1)) INTER K0 SUBSET C /\
     (!z. z IN ball(vec 0,&2) ==> (sch5v_at a (c z) IN C <=> z IN sphere(vec 0,&1))) /\
     (!z y. z IN cball(vec 0,&1 / &2) /\ y IN C ==> dax <= dist(sch5v_at a (c z),y)) /\
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\ &0 < d /\
     (!x. ~(?y. y IN C /\ dist(y,x) < dax / &2) ==> v x = basis 3) /\
     (!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                 ==> ?y. y IN C /\ dist(y,ode_vf_flow v (:real^3) u x) < &2 * d)
            ==> norm(g'(ode_vf_flow v (:real^3) t x)) pow 2 = norm(g' x) pow 2) /\
     (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> x IN IMAGE g (annulus (&1 / &2) (&2))) /\
     (!p q. p IN IMAGE g (sphere(vec 0,&1)) /\ q IN K0 /\ dist(p,q) < e
            ==> ?y. y IN C /\ dist(y,p) < d) /\
     &0 < lam /\ B * lam * H < e /\ B * lam * H < d /\
     B * lam * H < dax / &2 /\ &0 < H
     ==> ?Theta Theta'.
           diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
           (!y. y IN sch5v_slab H ==> (Theta y)$3 = a + lam * y$3) /\
           (!y. y IN sch5v_slab H /\ y$3 = &0 ==> Theta y = sch5v_at a (c(sch5v_pr y))) /\
           (!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
                ==> Theta y = sch5v_at (a + lam * y$3) (c(sch5v_pr y))) /\
           (!y. y IN sch5v_slab H
                ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=>
                     y$1 pow 2 + y$2 pow 2 = &1)) /\
           ((!y. y IN sch5v_slab H
                 ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                      y$1 pow 2 + y$2 pow 2 < &1)) \/
            (!y. y IN sch5v_slab H
                 ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                      y$1 pow 2 + y$2 pow 2 < &1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "K0")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CS")
   (CONJUNCTS_THEN2 (LABEL_TAC "AX") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "BD")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "VERT") (CONJUNCTS_THEN2 (LABEL_TAC "FI")
   (CONJUNCTS_THEN2 (LABEL_TAC "NO") (CONJUNCTS_THEN2 (LABEL_TAC "NEAR")
    STRIP_ASSUME_TAC)))))))))))))))) THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((v:real^3->real^3)(vec 0))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(v:real^3->real^3)(vec 0)`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH5V_FLOW_FACTS o CONJ
    (ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`)) THEN
  MP_TAC(ISPEC `v:real^3->real^3` SCH5V_FLOW_HEIGHT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "HT") THEN
  MP_TAC(ISPECL [`v:real^3->real^3`; `B:real`] SCH5V_FLOW_DISPLACEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "DSP") THEN
  MP_TAC(ISPECL [`ode_vf_flow (v:real^3->real^3) (:real^3)`; `c:real^2->real^2`;
                 `c':real^2->real^2`; `ball(vec 0:real^2,&2)`; `a:real`; `lam:real`;
                 `H:real`] SCH5V_FLOWBOX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN REWRITE_TAC[sch_ball];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SCH5V_SLAB_EQ] THEN
  ABBREV_TAC `Th = \y:real^3. ode_vf_flow (v:real^3->real^3) (:real^3) (lift(lam * y$3))
                                (sch5v_at a ((c:real^2->real^2)(sch5v_pr y)))` THEN
  ABBREV_TAC `E = {x | sch5v_pr(ode_vf_flow (v:real^3->real^3) (:real^3)
                                  (lift(--(x$3 - a))) x) IN IMAGE (c:real^2->real^2) (ball(vec 0,&2)) /\
                       abs((x$3 - a) / lam) < H}` THEN
  ABBREV_TAC `Th' = \x:real^3.
     vector[((c':real^2->real^2)(sch5v_pr(ode_vf_flow (v:real^3->real^3) (:real^3)
              (lift(--(x$3 - a))) x)))$1;
            (c'(sch5v_pr(ode_vf_flow v (:real^3) (lift(--(x$3 - a))) x)))$2;
            (x$3 - a) / lam]:real^3` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (Th:real^3->real^3) (sch5v_slab H) = E` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (sch5v_slab H) E (Th:real^3->real^3) Th'` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Th:real^3->real^3`; `Th':real^3->real^3`] THEN
  SUBGOAL_THEN `!y. (Th:real^3->real^3) y =
                    ode_vf_flow (v:real^3->real^3) (:real^3) (lift(lam * y$3))
                      (sch5v_at a ((c:real^2->real^2)(sch5v_pr y)))` (LABEL_TAC "TH") THENL
   [EXPAND_TAC "Th" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H ==> sch5v_pr y IN ball(vec 0,&2) /\ abs(y$3) < H`
  (LABEL_TAC "NB") THENL
   [REWRITE_TAC[SCH5V_SLAB_EQ; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch5v_slab H
                    ==> ((Th:real^3->real^3) y IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) <=>
                         y$1 pow 2 + y$2 pow 2 = &1)`
  (LABEL_TAC "SURF") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "NB" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^3) IN sch5v_slab H`))) THEN
    STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(y:real^3)$1 pow 2 + y$2 pow 2 = &1 <=>
                  sch5v_at a ((c:real^2->real^2)(sch5v_pr y)) IN C` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SCH5V_PR_FACTS] THEN CONV_TAC SYM_CONV THEN
      USE_THEN "CS" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `q = sch5v_at a ((c:real^2->real^2)(sch5v_pr y))` THEN
    SUBGOAL_THEN `(q:real^3) IN K0` ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN USE_THEN "K0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `s = lift(lam * (y:real^3)$3)` THEN
    SUBGOAL_THEN `abs(drop s) <= lam * H` ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC[LIFT_DROP; REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `ode_vf_flow (v:real^3->real^3) (:real^3) (vec 0) q = q` (LABEL_TAC "P0") THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!u. u IN interval[vec 0,s] UNION interval[s,vec 0]
                      ==> dist(q,ode_vf_flow (v:real^3->real^3) (:real^3) u q) <= B * lam * H /\
                          dist(ode_vf_flow (v:real^3->real^3) (:real^3) s q,ode_vf_flow (v:real^3->real^3) (:real^3) u q) <= B * lam * H`
    (LABEL_TAC "SEG") THENL
     [X_GEN_TAC `u:real^1` THEN DISCH_THEN(MP_TAC o MATCH_MP SCH5V_SEGMENT_BOUNDS) THEN
      STRIP_TAC THEN REWRITE_TAC[dist] THEN CONJ_TAC THENL
       [USE_THEN "DSP" (MP_TAC o SPECL [`q:real^3`; `vec 0:real^1`; `u:real^1`]) THEN
        USE_THEN "P0" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[DROP_VEC; REAL_SUB_LZERO; REAL_ABS_NEG];
        USE_THEN "DSP" (MP_TAC o SPECL [`q:real^3`; `s:real^1`; `u:real^1`])] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * abs(drop s)` THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,s] UNION interval[s,vec 0] /\ (s:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_UNION; IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`] SCH5V_SURFACE_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EQ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `?y0. y0 IN C /\ dist(y0,ode_vf_flow (v:real^3->real^3) (:real^3) s q) < d` STRIP_ASSUME_TAC THENL
       [USE_THEN "NEAR" MATCH_MP_TAC THEN EXISTS_TAC `q:real^3` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "SEG" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
          (ASSUME `(s:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)))) THEN
        MP_TAC(ISPECL [`q:real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d` (LABEL_TAC "CL") THENL
       [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN EXISTS_TAC `y0:real^3` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "SEG" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP th
          (ASSUME `(u:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)))) THEN
        MP_TAC(ISPECL [`y0:real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`; `ode_vf_flow (v:real^3->real^3) (:real^3) u q`] DIST_TRIANGLE) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "FI" (fun th -> MP_TAC(MP (SPECL [`q:real^3`; `s:real^1`] th)
        (ASSUME `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d`))) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`
      ASSUME_TAC THENL
       [USE_THEN "NO" MATCH_MP_TAC THEN
        USE_THEN "CL" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(vec 0:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`))) THEN
        USE_THEN "P0" (fun th -> REWRITE_TAC[th]);
        ALL_TAC] THEN
      SUBGOAL_THEN `ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`] SCH5V_IN_SURFACE) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `q:real^3`] SCH5V_IN_SURFACE) THEN
      REWRITE_TAC[ASSUME `sch_neck (g:real^3->real^3) g'`;
                  ASSUME `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                  ASSUME `ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (sphere(vec 0,&1)) INTER K0 SUBSET C` THEN
      UNDISCH_TAC `(q:real^3) IN K0` THEN SET_TAC[];
      SUBGOAL_THEN `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d` (LABEL_TAC "CL") THENL
       [X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN EXISTS_TAC `q:real^3` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "SEG" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th
          (ASSUME `(u:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "FI" (fun th -> MP_TAC(MP (SPECL [`q:real^3`; `s:real^1`] th)
        (ASSUME `!u. u IN interval[vec 0,s] UNION interval[s,vec 0] ==> ?y. y IN C /\ dist(y,ode_vf_flow (v:real^3->real^3) (:real^3) u q) < &2 * d`))) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (sphere(vec 0,&1))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2)) /\
                    ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        USE_THEN "NO" MATCH_MP_TAC THEN
        USE_THEN "CL" (fun th -> MATCH_ACCEPT_TAC(MATCH_MP th (ASSUME `(s:real^1) IN interval[vec 0,s] UNION interval[s,vec 0]`)));
        ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `ode_vf_flow (v:real^3->real^3) (:real^3) s q`] SCH5V_IN_SURFACE) THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `q:real^3`] SCH5V_IN_SURFACE) THEN
      REWRITE_TAC[ASSUME `sch_neck (g:real^3->real^3) g'`;
                  ASSUME `(q:real^3) IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`;
                  ASSUME `ode_vf_flow (v:real^3->real^3) (:real^3) s q IN IMAGE (g:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "HT" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[SCH5V_PR_AT; LIFT_DROP];
    REPEAT STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; LIFT_NUM];
    REPEAT STRIP_TAC THEN USE_THEN "TH" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "NB" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^3) IN sch5v_slab H`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `sch5v_pr y IN cball(vec 0:real^2,&1 / &2)` ASSUME_TAC THENL
     [REWRITE_TAC[SCH5V_PR_FACTS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `q = sch5v_at a ((c:real^2->real^2)(sch5v_pr y))` THEN
    MP_TAC(ISPECL [`v:real^3->real^3`; `{x:real^3 | ~(?y. y IN C /\ dist(y,x) < dax / &2)}`;
                   `q:real^3`; `lift(lam * (y:real^3)$3)`; `basis 3:real^3`]
      SCH5V_FLOW_TRANSLATE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; ASSUME `smooth_map_on (:real^3) (v:real^3->real^3)`;
                  ASSUME `!y. ode_vf_maxint (v:real^3->real^3) (:real^3) y = (:real^1)`] THEN
      CONJ_TAC THENL [USE_THEN "VERT" ACCEPT_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "AX" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `sch5v_pr y IN cball(vec 0:real^2,&1 / &2)`) (ASSUME `(y':real^3) IN C`)))) THEN
      REWRITE_TAC[ASSUME `sch5v_at a ((c:real^2->real^2)(sch5v_pr y)) = q`] THEN
      MP_TAC(ISPECL [`q:real^3`; `q + drop u % basis 3:real^3`; `y':real^3`] DIST_TRIANGLE) THEN
      SUBGOAL_THEN `dist(q:real^3,q + drop u % basis 3) = abs(drop u)` SUBST1_TAC THENL
       [REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`; NORM_MUL] THEN
        SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`y':real^3`; `q + drop u % basis 3:real^3`] DIST_SYM) THEN
      SUBGOAL_THEN `abs(drop u) <= lam * H` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(lam * (y:real^3)$3)` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `lam * H <= B * lam * H` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[sch5v_at; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; LIFT_DROP] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    USE_THEN "SURF" ACCEPT_TAC;
    MATCH_MP_TAC SCH5V_SIDES THEN EXISTS_TAC `Th':real^3->real^3` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC SCH5V_NECK_SPHERE_HOMEOMORPHIC THEN EXISTS_TAC `g':real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      USE_THEN "SURF" ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The vertical field near a compact set C of regular points                *)
(* of the height: vertical away from a given neighbourhood of C, |g'|^2 is a *)
(* first integral near C, and points of S near a compact K0 with            *)
(* S INTER K0 SUBSET C are near C.                                           *)
(* ------------------------------------------------------------------------- *)

let SCH5V_PANCAKE_FIELD = prove
 (`!(g:real^3->real^3) g' C K0 D.
     sch_neck g g' /\ compact C /\ C SUBSET sch5v_oh g g' /\
     C SUBSET IMAGE g (sphere(vec 0,&1)) /\ compact K0 /\
     IMAGE g (sphere(vec 0,&1)) INTER K0 SUBSET C /\ &0 < D
     ==> ?v B d e.
           smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
           (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\
           &0 < d /\ &0 < e /\
           (!x. ~(?y. y IN C /\ dist(y,x) < D) ==> v x = basis 3) /\
           (!x t. (!u. u IN interval[vec 0,t] UNION interval[t,vec 0]
                       ==> ?y. y IN C /\ dist(y,ode_vf_flow v (:real^3) u x) < &2 * d)
                  ==> norm(g'(ode_vf_flow v (:real^3) t x)) pow 2 = norm(g' x) pow 2) /\
           (!x. (?y. y IN C /\ dist(y,x) < &2 * d) ==> x IN IMAGE g (annulus (&1 / &2) (&2))) /\
           (!p q. p IN IMAGE g (sphere(vec 0,&1)) /\ q IN K0 /\ dist(p,q) < e
                  ==> ?y. y IN C /\ dist(y,p) < d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`C:real^3->bool`; `sch5v_oh (g:real^3->real^3) g'`; `D:real`] SCH5V_CUTOFF) THEN
  ASM_SIMP_TAC[SCH5V_OH_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `chi:real^3->real`
    (X_CHOOSE_THEN `L:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `chi:real^3->real`; `L:real^3->bool`]
    SCH5V_FIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "OFFL") (LABEL_TAC "DOT"))))) THEN
  SUBGOAL_THEN `sch5v_oh (g:real^3->real^3) g' SUBSET IMAGE g (annulus (&1 / &2) (&2))`
  ASSUME_TAC THENL [REWRITE_TAC[sch5v_oh] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (sphere(vec 0,&1))`; `K0:real^3->bool`;
                 `{x:real^3 | ?y. y IN C /\ dist(y,x) < d1 / &2}`] SCH5V_NEAR_COMPACT) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `&0`] SCH5V_SURFACE_COMPACT) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SCH5V_OPEN_NBHD] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `C:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. basis 3 + (chi:real^3->real) x % sch5v_hfield (g':real^3->real^3) x`;
    `B:real`; `d1 / &2`; `e:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. ode_vf_maxint (\x:real^3. basis 3 + (chi:real^3->real) x %
                                    sch5v_hfield (g':real^3->real^3) x) (:real^3) y = (:real^1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH5V_BOUNDED_COMPLETE THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&2 * d1 / &2 = d1`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "OFFL" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `t:real^1`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:real^3. basis 3 + (chi:real^3->real) x % sch5v_hfield (g':real^3->real^3) x`;
                   `\z:real^3. lift(norm((g':real^3->real^3) z) pow 2)`;
                   `{x:real^3 | ?y. y IN C /\ dist(y,x) < d1}`; `x:real^3`; `t:real^1`]
      SCH5V_FLOW_FIRST_INTEGRAL) THEN
    REWRITE_TAC[LIFT_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SCH5V_OPEN_NBHD; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(chi:real^3->real) z = &1 /\ z IN sch5v_oh (g:real^3->real^3) g'`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `z:real^3`]
      SCH5V_RHO_HAS_DERIVATIVE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN USE_THEN "DOT" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^3) IN sch5v_oh (g:real^3->real^3) g'` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM SET_TAC[]]]);;

(* The planar chart of the disc bounded by C, a compact set K0 containing    *)
(* the disc and its thin collar at height a with S INTER K0 = C, and the    *)
(* distance of the axis part of the disc from C.                             *)

let SCH5V_PANCAKE_SETUP = prove
 (`!(g:real^3->real^3) g' a C (Fn:real^2->real^2) Fn'.
     sch_neck g g' /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     C IN components(sch_level g a) /\ FINITE(components(sch_level g a)) /\
     sch_neck Fn Fn' /\
     C = IMAGE (\x. vector[(Fn x)$1; (Fn x)$2; a]:real^3) (sphere(vec 0,&1)) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; a]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> ?c c' K0 dax.
           sch_ball c c' /\
           IMAGE c (sphere(vec 0,&1)) = IMAGE Fn (sphere(vec 0,&1)) /\
           IMAGE c (ball(vec 0,&1)) = inside(IMAGE Fn (sphere(vec 0,&1))) /\
           compact C /\ C SUBSET sch5v_oh g g' /\ C SUBSET IMAGE g (sphere(vec 0,&1)) /\
           compact K0 /\ (!z. z IN ball(vec 0,&2) ==> sch5v_at a (c z) IN K0) /\
           IMAGE g (sphere(vec 0,&1)) INTER K0 SUBSET C /\
           (!z. z IN ball(vec 0,&2) ==> (sch5v_at a (c z) IN C <=> z IN sphere(vec 0,&1))) /\
           &0 < dax /\
           (!z y. z IN cball(vec 0,&1 / &2) /\ y IN C ==> dax <= dist(sch5v_at a (c z),y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "CEQ") (LABEL_TAC "INNER"))))))) THEN
  ABBREV_TAC `J = IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1))` THEN
  SUBGOAL_THEN `IMAGE (sch5v_at a) (J:real^2->bool) = C` (LABEL_TAC "CJ") THENL
   [REMOVE_THEN "CEQ" SUBST1_TAC THEN EXPAND_TAC "J" THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; sch5v_at];
    ALL_TAC] THEN
  REMOVE_THEN "CEQ" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`]
    SCH5V_LEVEL_COMPONENT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "CPT")
   (X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SEP")))))))) THEN
  SUBGOAL_THEN `!z:real^2. z IN inside J ==> ~(sch5v_at a z IN IMAGE (g:real^3->real^3)
                                               (sphere(vec 0,&1)))` (LABEL_TAC "IN2") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[sch5v_at] THEN
    USE_THEN "INNER" MATCH_MP_TAC THEN
    SUBGOAL_THEN `IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C = J` (fun th -> ASM_REWRITE_TAC[th]) THEN
    USE_THEN "CJ" (SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[GSYM sch5v_pr; SCH5V_PR_AT; IMAGE_ID] THEN REWRITE_TAC[ETA_AX; IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fn:real^2->real^2) continuous_on annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_neck (Fn:real^2->real^2) Fn'` THEN
    SIMP_TAC[sch_neck; diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fn:real^2->real^2`; `d0 / &2`] SCH5V_THIN_COLLAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "THIN")))) THEN
  MP_TAC(ISPECL [`Fn:real^2->real^2`; `Fn':real^2->real^2`; `k:real`] SCH5V_PLANAR_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x y:real^2. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\
                             (c:real^2->real^2) x = c y ==> x = y` (LABEL_TAC "CINJ") THENL
   [UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN
    REWRITE_TAC[sch_ball; diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^2->real^2) continuous_on ball(vec 0,&2)` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN
    SIMP_TAC[sch_ball; diffeomorphism_on; SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(J:real^2->bool) /\ compact(J UNION inside J)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact(J:real^2->bool)` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1)) = J`)) THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `annulus (&1 / &2) (&2):real^2->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [REWRITE_TAC[BOUNDED_UNION] THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; BOUNDED_INSIDE];
      SUBGOAL_THEN `(J:real^2->bool) UNION inside J = (:real^2) DIFF outside J` SUBST1_TAC THENL
       [MP_TAC(ISPEC `J:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
        MP_TAC(ISPEC `J:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
        MP_TAC(ISPEC `J:real^2->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[];
        REWRITE_TAC[GSYM OPEN_CLOSED] THEN MATCH_MP_TAC OPEN_OUTSIDE THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]];
    ALL_TAC] THEN
  ABBREV_TAC `K1 = {j + w:real^2 | j IN J /\ w IN cball(vec 0,d0 / &2)} UNION
                   (J UNION inside J)` THEN
  SUBGOAL_THEN `compact(K1:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN MATCH_MP_TAC COMPACT_UNION THEN
    ASM_SIMP_TAC[COMPACT_SUMS; COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN ball(vec 0,&2) ==> (c:real^2->real^2) z IN K1` (LABEL_TAC "CK1") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:real^2->real^2) z IN J UNION inside J UNION
                  IMAGE (Fn:real^2->real^2) (annulus (&1 - k / &2) (&1 + k))` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "K1" THEN REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    USE_THEN "THIN" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(x:real^2) IN annulus (&1 - k / &2) (&1 + k)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^2` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`(Fn:real^2->real^2) j`; `(Fn:real^2->real^2) x - Fn j`] THEN
    REWRITE_TAC[VECTOR_ARITH `j + (x - j):real^N = x`; IN_CBALL_0] THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (Fn:real^2->real^2) (sphere(vec 0,&1)) = J`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM dist] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN ball(vec 0,&2)
                    ==> (sch5v_at a ((c:real^2->real^2) z) IN C <=> z IN sphere(vec 0,&1))`
  (LABEL_TAC "CS") THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN USE_THEN "CJ" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_IMAGE; SCH5V_PR_AT] THEN
    SUBGOAL_THEN `!w. sch5v_at a ((c:real^2->real^2) z) = sch5v_at a w <=> c z = w`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[SCH5V_PR_AT]; ALL_TAC] THEN
    REWRITE_TAC[UNWIND_THM1] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(c:real^2->real^2) z IN IMAGE c (sphere(vec 0,&1))` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^2 = u` (fun th -> ASM_REWRITE_TAC[th]) THEN
      USE_THEN "CINJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(u:real^2) IN sphere(vec 0,&1)` THEN
      REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `(c:real^2->real^2) z IN IMAGE c (sphere(vec 0,&1))` MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN cball(vec 0:real^2,&1 / &2) ==> z IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\z. sch5v_at a ((c:real^2->real^2) z)) (cball(vec 0,&1 / &2))`;
                 `C:real^3->bool`] SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
      SUBGOAL_THEN `(\z. sch5v_at a ((c:real^2->real^2) z)) = sch5v_at a o c` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&2)` THEN
        ASM_REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH]];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^3` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) MP_TAC) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN
      SUBGOAL_THEN `(z:real^2) IN ball(vec 0,&2)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "CS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^2) IN ball(vec 0,&2)`)]) THEN
      UNDISCH_TAC `(z:real^2) IN cball(vec 0,&1 / &2)` THEN
      REWRITE_TAC[IN_CBALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dax:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DAX"))) THEN
  MAP_EVERY EXISTS_TAC [`c:real^2->real^2`; `c':real^2->real^2`;
                        `IMAGE (sch5v_at a) (K1:real^2->bool)`; `dax:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV; SCH5V_PR_AT_SMOOTH];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "CK1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
    EXPAND_TAC "K1" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(z:real^2) = j + w` THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_CASES_TAC `sch5v_at a (j + w:real^2) IN C` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `sch5v_at a (j + w:real^2) IN sch_level (g:real^3->real^3) a /\
                    sch5v_at a (j:real^2) IN C` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[sch_level; IN_ELIM_THM; SCH5V_PR_AT] THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "CJ" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "SEP" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `sch5v_at a (j + w:real^2) IN sch_level (g:real^3->real^3) a`)
        (CONJ (ASSUME `~(sch5v_at a (j + w:real^2) IN C)`)
              (ASSUME `sch5v_at a (j:real^2) IN C`))))) THEN
      REWRITE_TAC[SCH5V_PR_AT] THEN
      UNDISCH_TAC `(w:real^2) IN cball(vec 0,d0 / &2)` THEN
      ASM_REWRITE_TAC[IN_CBALL_0; dist; VECTOR_ARITH `(j + w) - j:real^N = w`] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "CJ" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      USE_THEN "IN2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^2) IN inside J`))) THEN
      ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN USE_THEN "DAX" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[]]);;

(* The pancake chart: the main theorem of pc_sch_vflow. *)

let SCH5V_PANCAKE = prove
 (`!(g:real^3->real^3) g' a C (Fn:real^2->real^2) Fn'.
     sch_neck g g' /\ (!t. sch_crit g t ==> ~((g t)$3 = a)) /\
     C IN components(sch_level g a) /\ FINITE(components(sch_level g a)) /\
     sch_neck Fn Fn' /\
     C = IMAGE (\x. vector[(Fn x)$1; (Fn x)$2; a]:real^3) (sphere(vec 0,&1)) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; a]:real^3) IN IMAGE g (sphere(vec 0,&1))))
     ==> ?c c'.
           sch_ball c c' /\
           IMAGE c (sphere(vec 0,&1)) = IMAGE Fn (sphere(vec 0,&1)) /\
           IMAGE c (ball(vec 0,&1)) = inside(IMAGE Fn (sphere(vec 0,&1))) /\
           !H. &0 < H
               ==> ?lam0. &0 < lam0 /\
                 !lam. &0 < lam /\ lam < lam0
                 ==> ?Theta Theta'.
                       diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H))
                                         Theta Theta' /\
                       (!y. y IN sch5v_slab H ==> (Theta y)$3 = a + lam * y$3) /\
                       (!y. y IN sch5v_slab H /\ y$3 = &0
                            ==> Theta y = sch5v_at a (c(sch5v_pr y))) /\
                       (!y. y IN sch5v_slab H /\ y$1 pow 2 + y$2 pow 2 < &1 / &4
                            ==> Theta y = sch5v_at (a + lam * y$3) (c(sch5v_pr y))) /\
                       (!y. y IN sch5v_slab H
                            ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=>
                                 y$1 pow 2 + y$2 pow 2 = &1)) /\
                       ((!y. y IN sch5v_slab H
                             ==> (Theta y IN inside(IMAGE g (sphere(vec 0,&1))) <=>
                                  y$1 pow 2 + y$2 pow 2 < &1)) \/
                        (!y. y IN sch5v_slab H
                             ==> (Theta y IN outside(IMAGE g (sphere(vec 0,&1))) <=>
                                  y$1 pow 2 + y$2 pow 2 < &1)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH5V_PANCAKE_SETUP) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    (X_CHOOSE_THEN `K0:real^3->bool` (X_CHOOSE_THEN `dax:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `sch_neck (g:real^3->real^3) g'` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `C:real^3->bool`;
                 `K0:real^3->bool`; `dax / &2`] SCH5V_PANCAKE_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3->real^3` (X_CHOOSE_THEN `B:real`
    (X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm((v:real^3->real^3)(vec 0))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(v:real^3->real^3)(vec 0)`; `3`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = min e (min d (dax / &2))` THEN
  SUBGOAL_THEN `&0 < m /\ m <= e /\ m <= d /\ m <= dax / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:real^2->real^2`; `c':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `H:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &2 * B * H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `m / (&2 * B * H)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `lam:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `B * lam * H < m` ASSUME_TAC THENL
   [SUBGOAL_THEN `lam * (&2 * B * H) < m` MP_TAC THENL
     [UNDISCH_TAC `lam < m / (&2 * B * H)` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < B * lam * H` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `a:real`; `C:real^3->bool`;
                 `c:real^2->real^2`; `c':real^2->real^2`; `K0:real^3->bool`; `dax:real`;
                 `v:real^3->real^3`; `B:real`; `d:real`; `e:real`; `lam:real`; `H:real`]
    SCH5V_PANCAKE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

