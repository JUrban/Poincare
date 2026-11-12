(* ========================================================================= *)
(* pc_smt_straight: S3c, straightening a family of nonvanishing planar      *)
(* fields V s equal to e_1 outside ball(0,r) and stationary outside [0,1]:  *)
(* each V s is complete, and Psi s x = phi_s(x$1 + r, (-r, x$2)) (phi_s the  *)
(* flow of V s) is a diffeo_isotopy pushing e_1 to V s, the identity left   *)
(* of the ball and outside the strip, a translation for large x$1, and the  *)
(* only differentiable map with these properties.  The joint smoothness in  *)
(* (s, x) comes from the flow of the augmented field (0, V s y) on R x R^2, *)
(* the exit to the right from Lemma SMT_NO_BOUNDED_COMPLETE (pc_smt_pb2,    *)
(* S3b for complete fields), and the uniform exit time from compactness of  *)
(* [0,1] x [-r,r].                                                           *)
(*                                                                           *)
(* Completeness and straight trajectories.                                  *)
(* ========================================================================= *)

needs "src/pc_smt_pb2.ml";;
needs "src/pc_smt_planar.ml";;

prioritize_real();;
type_invention_error := true;;

(* Bounded smooth fields are complete.                                       *)

let SMT_RFLOW_BOUNDED_COMPLETE = prove
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

(* The flow maps of a complete smooth field are diffeomorphisms.             *)

let SMT_RFLOW_DIFFEO = prove
 (`!v:real^N->real^N.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1))
        ==> !t. diffeomorphism_on (:real^N) (:real^N) (vf_rflow v t) (vf_rflow v (--t))`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `lift t`] ODE_VF_FLOW_DIFFEO) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; UNIV_GSPEC] THEN
  SUBGOAL_THEN `vf_rflow (v:real^N->real^N) t = ode_vf_flow v (:real^N) (lift t) /\
                vf_rflow v (--t) = ode_vf_flow v (:real^N) (--(lift t))`
  (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM; vf_rflow; LIFT_NEG]);;

(* Components along e_1 and e_2 in the plane.                                *)

let SMT_STR_E1_COMPONENTS = prove
 (`!(q:real^2) t. (q + t % basis 1)$1 = q$1 + t /\ (q + t % basis 1)$2 = q$2`,
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let SMT_STR_E2_COMPONENTS = prove
 (`!(q:real^2) t. (q + t % basis 2)$1 = q$1 /\ (q + t % basis 2)$2 = q$2 + t`,
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

let SMT_STR_START_SHIFT = prove
 (`!(x:real^2) r. vector[--r; x$2] + (x$1 + r) % basis 1 = x`,
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT; VECTOR_2; ARITH] THEN REAL_ARITH_TAC);;

let SMT_STR_NORM_COMPONENT = prove
 (`!r (x:real^2). r <= abs(x$1) \/ r <= abs(x$2) ==> r <= norm x`,
  MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]);;

(* Straight trajectories: where the field is e along a line, the flow is    *)
(* translation along it.                                                     *)

let SMT_STR_LINE_DERIV = prove
 (`!(q:real^N) e t. ((\u. q + drop u % e) has_vector_derivative e) (at t)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  REWRITE_TAC[has_vector_derivative] THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  MATCH_MP_TAC LINEAR_VMUL_DROP THEN REWRITE_TAC[LINEAR_ID]);;

let SMT_STR_RFLOW_LINE = prove
 (`!(v:real^N->real^N) q e J.
        smooth_map_on (:real^N) v /\ (!y. ode_vf_maxint v (:real^N) y = (:real^1)) /\
        is_interval J /\ vec 0 IN J /\ (!u. u IN J ==> v(q + drop u % e) = e)
        ==> !u. u IN J ==> vf_rflow v (drop u) q = q + drop u % e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^N) (v:real^N->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->real^N`; `(:real^N)`; `J:real^1->bool`;
                 `\u:real^1. (q:real^N) + drop u % e`; `vec 0:real^1`] ODE_VF_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                  VECTOR_SUB_RZERO] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N->real^N)(q + drop t % e) = e` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[SMT_STR_LINE_DERIV];
    DISCH_TAC THEN REWRITE_TAC[vf_rflow; LIFT_DROP] THEN ASM_MESON_TAC[]]);;

(* Each V s is smooth and complete.                                          *)

let SMT_STR_COMPLETE = prove
 (`!(V:real->real^2->real^2) r.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1)
        ==> !s. smooth_map_on (:real^2) (V s) /\
                (!y. ode_vf_maxint (V s) (:real^2) y = (:real^1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `smooth_map_on (:real^2) ((V:real->real^2->real^2) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMT_FAMILY_SLICE THEN ASM_REWRITE_TAC[OPEN_UNIV]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMT_RFLOW_BOUNDED_COMPLETE THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `IMAGE ((V:real->real^2->real^2) s) (cball(vec 0,r))` COMPACT_IMP_BOUNDED) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_CBALL_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B + &1` THEN X_GEN_TAC `x:real^2` THEN
  ASM_CASES_TAC `norm(x:real^2) <= r` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(V:real->real^2->real^2) s x = basis 1` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC]);;

let SMT_STR_LINE = prove
 (`!(V:real->real^2->real^2) r s q J.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        is_interval J /\ vec 0 IN J /\ (!u. u IN J ==> r <= norm(q + drop u % basis 1))
        ==> !u. u IN J ==> vf_rflow (V s) (drop u) q = q + drop u % basis 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MATCH_MP_TAC SMT_STR_RFLOW_LINE THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* Left of the ball the past is straight, right of it the future, and at    *)
(* heights |x$2| >= r the whole trajectory.                                  *)

let SMT_STR_LEFT = prove
 (`!(V:real->real^2->real^2) r s q t.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        q$1 <= --r /\ t <= &0
        ==> vf_rflow (V s) t q = q + t % basis 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `q:real^2`;
                 `{u:real^1 | drop u <= &0}`] SMT_STR_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM; DROP_VEC; REAL_LE_REFL] THEN
    CONJ_TAC THENL [MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC SMT_STR_NORM_COMPONENT THEN
    DISJ1_TAC THEN REWRITE_TAC[SMT_STR_E1_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `lift t`) THEN ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP]]);;

let SMT_STR_RIGHT = prove
 (`!(V:real->real^2->real^2) r s q t.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        r <= q$1 /\ &0 <= t
        ==> vf_rflow (V s) t q = q + t % basis 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `q:real^2`;
                 `{u:real^1 | &0 <= drop u}`] SMT_STR_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IS_INTERVAL_1; IN_ELIM_THM; DROP_VEC; REAL_LE_REFL] THEN
    CONJ_TAC THENL [MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN MATCH_MP_TAC SMT_STR_NORM_COMPONENT THEN
    DISJ1_TAC THEN REWRITE_TAC[SMT_STR_E1_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `lift t`) THEN ASM_REWRITE_TAC[IN_ELIM_THM; LIFT_DROP]]);;

let SMT_STR_HIGH = prove
 (`!(V:real->real^2->real^2) r s q t.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        r <= abs(q$2)
        ==> vf_rflow (V s) t q = q + t % basis 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `q:real^2`;
                 `(:real^1)`] SMT_STR_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IS_INTERVAL_UNIV; IN_UNIV] THEN
    X_GEN_TAC `u:real^1` THEN MATCH_MP_TAC SMT_STR_NORM_COMPONENT THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[SMT_STR_E1_COMPONENTS];
    DISCH_THEN(MP_TAC o SPEC `lift t`) THEN REWRITE_TAC[IN_UNIV; LIFT_DROP]]);;

(* Psi s is the identity left of the ball and outside the strip.             *)

let SMT_STR_PSI_ID = prove
 (`!(V:real->real^2->real^2) r s x.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        (x$1 <= --r \/ r <= abs(x$2))
        ==> vf_rflow (V s) (x$1 + r) (vector[--r; x$2]) = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
   [MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `vector[--r; (x:real^2)$2]:real^2`;
                   `(x:real^2)$1 + r`] SMT_STR_LEFT) THEN
    ASM_REWRITE_TAC[VECTOR_2; REAL_LE_REFL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[SMT_STR_START_SHIFT]];
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `vector[--r; (x:real^2)$2]:real^2`;
                   `(x:real^2)$1 + r`] SMT_STR_HIGH) THEN
    ASM_REWRITE_TAC[VECTOR_2; SMT_STR_START_SHIFT]]);;

(* ------------------------------------------------------------------------- *)
(* Joint smoothness.  The augmented field (0, V s y) on R x R^2              *)
(* has the complete flow (s, phi_s(t, y)), so (t, s, y) |-> phi_s(t, y) is  *)
(* smooth (ODE_VF_FLOW_SMOOTH), and so is Psi as a family.                   *)
(* ------------------------------------------------------------------------- *)

let SMT_STR_VDERIV_PASTECART = prove
 (`!(c:real^M) (u:real^1->real^N) u' net.
        (u has_vector_derivative u') net
        ==> ((\x. pastecart c (u x)) has_vector_derivative pastecart (vec 0) u') net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x:real^1. drop x % pastecart (vec 0:real^M) (u':real^N)) =
                (\x. pastecart (vec 0) (drop x % u'))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GSYM PASTECART_CMUL; VECTOR_MUL_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_PASTECART THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST]);;

let SMT_STR_AUG = prove
 (`!(V:real->real^2->real^2) r.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1)
        ==> smooth_map_on (:real^(1,2)finite_sum)
              (\z. pastecart (vec 0:real^1) (V (drop(fstcart z)) (sndcart z))) /\
            (!z. ode_vf_maxint (\z. pastecart (vec 0:real^1) (V (drop(fstcart z)) (sndcart z)))
                               (:real^(1,2)finite_sum) z = (:real^1)) /\
            (!t z. ode_vf_flow (\z. pastecart (vec 0:real^1) (V (drop(fstcart z)) (sndcart z)))
                               (:real^(1,2)finite_sum) t z =
                   pastecart (fstcart z) (vf_rflow (V (drop(fstcart z))) (drop t) (sndcart z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = \z:real^(1,2)finite_sum.
                    pastecart (vec 0:real^1) ((V:real->real^2->real^2) (drop(fstcart z)) (sndcart z))` THEN
  SUBGOAL_THEN `smooth_map_on (:real^(1,2)finite_sum)
                  (W:real^(1,2)finite_sum->real^(1,2)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    UNDISCH_TAC `smooth_family (:real^2) (V:real->real^2->real^2)` THEN
    REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^(1,2)finite_sum)
                  (W:real^(1,2)finite_sum->real^(1,2)finite_sum)` ASSUME_TAC THENL
   [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!z:real^(1,2)finite_sum t.
        t IN ode_vf_maxint W (:real^(1,2)finite_sum) z /\
        ode_vf_flow W (:real^(1,2)finite_sum) t z =
        pastecart (fstcart z)
          (vf_rflow ((V:real->real^2->real^2) (drop(fstcart z))) (drop t) (sndcart z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(1,2)finite_sum` THEN
    MP_TAC(ISPEC `(V:real->real^2->real^2) (drop(fstcart(z:real^(1,2)finite_sum)))`
      SMT_RFLOW_BASIC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "der")))) THEN
    MP_TAC(ISPECL [`W:real^(1,2)finite_sum->real^(1,2)finite_sum`; `(:real^(1,2)finite_sum)`;
                   `(:real^1)`;
                   `\t:real^1. pastecart (fstcart(z:real^(1,2)finite_sum))
                     (vf_rflow ((V:real->real^2->real^2) (drop(fstcart z))) (drop t) (sndcart z))`;
                   `vec 0:real^1`] ODE_VF_UNIQUE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; IS_INTERVAL_UNIV; WITHIN_UNIV; VECTOR_SUB_RZERO;
                    DROP_VEC] THEN
    USE_THEN "id" (fun th -> REWRITE_TAC[th; PASTECART_FST_SND]) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `t:real^1` THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MATCH_MP_TAC SMT_STR_VDERIV_PASTECART THEN
      USE_THEN "der" (MP_TAC o SPECL [`sndcart(z:real^(1,2)finite_sum)`; `drop t`]) THEN
      REWRITE_TAC[LIFT_DROP];
      MESON_TAC[]];
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNIV] THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

let SMT_STR_FLOW_SMOOTH = prove
 (`!(V:real->real^2->real^2) r.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1)
        ==> smooth_map_on (:real^(1,(1,2)finite_sum)finite_sum)
              (\w. vf_rflow (V (drop(fstcart(sndcart w)))) (drop(fstcart w))
                            (sndcart(sndcart w)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SMT_STR_AUG) THEN
  ABBREV_TAC `W = \z:real^(1,2)finite_sum.
                    pastecart (vec 0:real^1) ((V:real->real^2->real^2) (drop(fstcart z)) (sndcart z))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`W:real^(1,2)finite_sum->real^(1,2)finite_sum`; `(:real^(1,2)finite_sum)`]
    ODE_VF_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[OPEN_UNIV] THEN
  SUBGOAL_THEN `ode_vf_domain W (:real^(1,2)finite_sum) =
                (:real^(1,(1,2)finite_sum)finite_sum)` SUBST1_TAC THENL
   [MATCH_MP_TAC SMT_RFLOW_DOMAIN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\w:real^(1,(1,2)finite_sum)finite_sum.
        vf_rflow ((V:real->real^2->real^2) (drop(fstcart(sndcart w)))) (drop(fstcart w))
                 (sndcart(sndcart w))) =
    sndcart o (\w. ode_vf_flow W (:real^(1,2)finite_sum) (fstcart w) (sndcart w))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SNDCART_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

(* Smoothness of (y |-> phi_(b y)(a y, c y)) for smooth a, b, c.  Use it   *)
(* through ISPECL: MATCH_MP_TAC fails on the pattern V (b y) (the higher-    *)
(* order matcher calls dest_var on an instantiated pattern pair).            *)

let SMT_STR_FLOW_COMPOSE = prove
 (`!(V:real->real^2->real^2) r (a:real^M->real) (b:real^M->real) (c:real^M->real^2).
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        smooth_map_on (:real^M) (\y. lift(a y)) /\ smooth_map_on (:real^M) (\y. lift(b y)) /\
        smooth_map_on (:real^M) c
        ==> smooth_map_on (:real^M) (\y. vf_rflow (V (b y)) (a y) (c y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\y:real^M. vf_rflow ((V:real->real^2->real^2) (b y)) (a y) (c y)) =
    (\w:real^(1,(1,2)finite_sum)finite_sum.
        vf_rflow (V (drop(fstcart(sndcart w)))) (drop(fstcart w)) (sndcart(sndcart w))) o
    (\y. pastecart (lift(a y)) (pastecart (lift(b y)) (c y)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `(:real^(1,(1,2)finite_sum)finite_sum)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[OPEN_UNIV]);;

let SMT_STR_PSI_SMOOTH = prove
 (`!(V:real->real^2->real^2) r.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1)
        ==> smooth_family (:real^2) (\s x. vf_rflow (V s) (x$1 + r) (vector[--r; x$2]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[smooth_family; UNIV_PCROSS_UNIV] THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`;
                 `\z:real^(1,2)finite_sum. (sndcart z)$1 + r`;
                 `\z:real^(1,2)finite_sum. drop(fstcart z)`;
                 `\z:real^(1,2)finite_sum. vector[--r; (sndcart z)$2]:real^2`]
    SMT_STR_FLOW_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMT_SNDCART_COMPONENT_SMOOTH];
    REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `(\y:real^(1,2)finite_sum. fstcart y) = fstcart o (\y. y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FSTCART_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMT_SNDCART_COMPONENT_SMOOTH]]);;

(* ------------------------------------------------------------------------- *)
(* Derivatives.  Psi s pushes e_1 to V s (directional                       *)
(* derivative along the trajectory), and its derivative is injective: near  *)
(* x, Psi s = phi_(x$1 + r) o G with G y = phi_(y$1 - x$1)(-r, y$2), where   *)
(* G' x = I (G moves (-r, x$2) along e_1 and e_2 at unit speed) and phi_t   *)
(* is a diffeomorphism.                                                      *)
(* ------------------------------------------------------------------------- *)

let SMT_STR_DIRECTIONAL = prove
 (`!(f:real^M->real^N) x e w.
        f differentiable (at x) /\
        ((\t. f(x + drop t % e)) has_vector_derivative w) (at (vec 0))
        ==> frechet_derivative f (at x) e = w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`\t:real^1. (f:real^M->real^N)(x + drop t % e)`; `vec 0:real^1`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\t:real^1. (x:real^M) + drop t % e`; `f:real^M->real^N`; `e:real^M`;
                 `frechet_derivative (f:real^M->real^N) (at x)`; `vec 0:real^1`]
    ODE_HAS_VECTOR_DERIVATIVE_CHAIN) THEN
  REWRITE_TAC[SMT_STR_LINE_DERIV; DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let SMT_STR_V_LINE = prove
 (`!(V:real->real^2->real^2) r s c.
        (!s x. r <= norm x ==> V s x = basis 1) ==> V s (vector[--r; c]) = basis 1`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC SMT_STR_NORM_COMPONENT THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC);;

let SMT_STR_PSI_E1 = prove
 (`!(V:real->real^2->real^2) r s x.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1)
        ==> frechet_derivative (\x:real^2. vf_rflow (V s) (x$1 + r) (vector[--r; x$2])) (at x)
                               (basis 1) =
            V s (vf_rflow (V s) (x$1 + r) (vector[--r; x$2]))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SMT_STR_PSI_SMOOTH) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SMT_STR_COMPLETE) THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "der")))) THEN
  MATCH_MP_TAC SMT_STR_DIRECTIONAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MP_TAC(ISPECL [`(:real^2)`;
                   `\s (x:real^2). vf_rflow ((V:real->real^2->real^2) s) (x$1 + r)
                                            (vector[--r; x$2])`; `s:real`]
      SMT_FAMILY_SLICE) THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[SMT_STR_E1_COMPONENTS] THEN
  SUBGOAL_THEN
   `(\t. vf_rflow ((V:real->real^2->real^2) s) (((x:real^2)$1 + drop t) + r) (vector[--r; x$2])) =
    (\t. vf_rflow (V s) (drop t) (vf_rflow (V s) (x$1 + r) (vector[--r; x$2])))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real^1` THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "der" (MP_TAC o SPECL
    [`vf_rflow ((V:real->real^2->real^2) s) ((x:real^2)$1 + r) (vector[--r; x$2])`; `&0`]) THEN
  USE_THEN "id" (fun th -> REWRITE_TAC[th; LIFT_NUM]));;

let SMT_STR_PSI_DERIV_INJ = prove
 (`!(V:real->real^2->real^2) r s x h.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        frechet_derivative (\x:real^2. vf_rflow (V s) (x$1 + r) (vector[--r; x$2])) (at x) h =
        vec 0
        ==> h = vec 0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "der")))) THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_CONTINUOUS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sm" o CONJUNCT1) THEN
  ABBREV_TAC `G = \y:real^2. vf_rflow ((V:real->real^2->real^2) s) (y$1 - (x:real^2)$1)
                                       (vector[--r; y$2])` THEN
  SUBGOAL_THEN
   `(\y:real^2. vf_rflow ((V:real->real^2->real^2) s) (y$1 + r) (vector[--r; y$2])) =
    vf_rflow (V s) ((x:real^2)$1 + r) o G`
  SUBST1_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `y:real^2` THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* G is smooth, G x = (-r, x$2) and G' x = I *)
  SUBGOAL_THEN `(G:real^2->real^2) differentiable (at x)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN EXPAND_TAC "G" THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`;
                   `\y:real^2. y$1 - (x:real^2)$1`; `\y:real^2. (s:real)`;
                   `\y:real^2. vector[--r; y$2]:real^2`] SMT_STR_FLOW_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_LIFT_COORDINATE];
      MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
      SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_LIFT_COORDINATE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^2->real^2) x = vector[--r; x$2]` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[REAL_SUB_REFL] THEN
    USE_THEN "id" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (G:real^2->real^2) (at x) = (\h. h)` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE; LINEAR_ID] THEN
    REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
    GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC SMT_STR_DIRECTIONAL THEN ASM_REWRITE_TAC[] THENL
     [EXPAND_TAC "G" THEN REWRITE_TAC[SMT_STR_E1_COMPONENTS; REAL_ADD_SUB] THEN
      USE_THEN "der" (MP_TAC o SPECL [`vector[--r; (x:real^2)$2]:real^2`; `&0`]) THEN
      USE_THEN "id" (fun th -> REWRITE_TAC[th; LIFT_NUM]) THEN
      ASM_SIMP_TAC[SMT_STR_V_LINE];
      SUBGOAL_THEN `(\t. (G:real^2->real^2) (x + drop t % basis 2)) =
                    (\t. vector[--r; (x:real^2)$2] + drop t % basis 2)` SUBST1_TAC THENL
       [EXPAND_TAC "G" THEN REWRITE_TAC[FUN_EQ_THM; SMT_STR_E2_COMPONENTS; REAL_SUB_REFL] THEN
        USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN GEN_TAC THEN
        SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 BASIS_COMPONENT; VECTOR_2; ARITH] THEN REAL_ARITH_TAC;
        REWRITE_TAC[SMT_STR_LINE_DERIV]]];
    ALL_TAC] THEN
  (* the chain rule *)
  SUBGOAL_THEN `vf_rflow ((V:real->real^2->real^2) s) ((x:real^2)$1 + r) differentiable
                (at ((G:real^2->real^2) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    USE_THEN "sm" (fun th -> REWRITE_TAC[th; OPEN_UNIV; IN_UNIV]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (vf_rflow ((V:real->real^2->real^2) s) ((x:real^2)$1 + r) o G) (at x) =
    frechet_derivative (vf_rflow (V s) (x$1 + r)) (at (G x)) o
    frechet_derivative G (at x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC SMT_DIFFEO_DERIV_INJ THEN
  MAP_EVERY EXISTS_TAC
   [`vf_rflow ((V:real->real^2->real^2) s) ((x:real^2)$1 + r)`;
    `vf_rflow ((V:real->real^2->real^2) s) (--((x:real^2)$1 + r))`;
    `vector[--r; (x:real^2)$2]:real^2`] THEN
  ASM_SIMP_TAC[SMT_RFLOW_DIFFEO]);;

(* ------------------------------------------------------------------------- *)
(* Psi s is a bijection.  A trajectory meets the line                       *)
(* x$1 = -r at most once (its past left of the ball is straight), so Psi s  *)
(* is injective.  Heights |x$2| are bounded along trajectories, the first   *)
(* coordinate is bounded below in the future and above in the past, so by  *)
(* S3b (SMT_NO_BOUNDED_COMPLETE for V s and -V s) every trajectory reaches  *)
(* x$1 > r in the future and x$1 < -r in the past; the intermediate value   *)
(* theorem on the past gives the crossing of x$1 = -r, so Psi s is onto.   *)
(* ------------------------------------------------------------------------- *)

let SMT_STR_LINE_ONCE = prove
 (`!(V:real->real^2->real^2) r s d c c'.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        vf_rflow (V s) d (vector[--r; c']) = vector[--r; c] /\ d <= &0
        ==> d = &0 /\ c = c'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `vector[--r; c']:real^2`;
                 `d:real`] SMT_STR_LEFT) THEN
  ASM_REWRITE_TAC[VECTOR_2; REAL_LE_REFL] THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
  REAL_ARITH_TAC);;

let SMT_STR_PSI_INJ = prove
 (`!(V:real->real^2->real^2) r s (x:real^2) (y:real^2).
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        vf_rflow (V s) (x$1 + r) (vector[--r; x$2]) =
        vf_rflow (V s) (y$1 + r) (vector[--r; y$2])
        ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  SUBGOAL_THEN
   `!(p:real^2) (q:real^2).
        vf_rflow ((V:real->real^2->real^2) s) (p$1 + r) (vector[--r; p$2]) =
        vf_rflow (V s) (q$1 + r) (vector[--r; q$2])
        ==> vf_rflow (V s) (q$1 - p$1) (vector[--r; q$2]) = vector[--r; p$2]`
  (LABEL_TAC "back") THENL
   [MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN
    DISCH_THEN(MP_TAC o AP_TERM
      `vf_rflow ((V:real->real^2->real^2) s) (--((p:real^2)$1 + r))`) THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ADD_RINV; REAL_ARITH `(y + r) + --(x + r) = y - x:real`;
                REAL_SUB_REFL] THEN
    USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^2)$1 - (x:real^2)$1 <= &0` THENL
   [MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `(y:real^2)$1 - (x:real^2)$1`;
                   `(x:real^2)$2`; `(y:real^2)$2`] SMT_STR_LINE_ONCE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "back" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC];
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `(x:real^2)$1 - (y:real^2)$1`;
                   `(y:real^2)$2`; `(x:real^2)$2`] SMT_STR_LINE_ONCE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "back" MATCH_MP_TAC THEN CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC]] THEN
  STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REAL_ARITH_TAC);;

(* Bounds along trajectories.                                                *)

let SMT_STR_HEIGHT = prove
 (`!(V:real->real^2->real^2) r s t y.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\ &0 <= r
        ==> abs((vf_rflow (V s) t y)$2) <= abs(y$2) + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  ASM_CASES_TAC `r <= abs((vf_rflow ((V:real->real^2->real^2) s) t y)$2)` THENL
   [MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`;
                   `vf_rflow ((V:real->real^2->real^2) s) t y`; `--t`] SMT_STR_HIGH) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ADD_RINV] THEN USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:real^2. z$2`) THEN
    REWRITE_TAC[SMT_STR_E1_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SMT_STR_FWD_BOUND = prove
 (`!(V:real->real^2->real^2) r s t y.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        &0 <= r /\ &0 <= t
        ==> --(abs(y$1) + r) <= (vf_rflow (V s) t y)$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  ASM_CASES_TAC `(vf_rflow ((V:real->real^2->real^2) s) t y)$1 <= --r` THENL
   [MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`;
                   `vf_rflow ((V:real->real^2->real^2) s) t y`; `--t`] SMT_STR_LEFT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ADD_RINV] THEN USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:real^2. z$1`) THEN
    REWRITE_TAC[SMT_STR_E1_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let SMT_STR_BACK_BOUND = prove
 (`!(V:real->real^2->real^2) r s t y.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        &0 <= r /\ &0 <= t
        ==> (vf_rflow (V s) (--t) y)$1 <= abs(y$1) + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  ASM_CASES_TAC `r <= (vf_rflow ((V:real->real^2->real^2) s) (--t) y)$1` THENL
   [MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`;
                   `vf_rflow ((V:real->real^2->real^2) s) (--t) y`; `t:real`] SMT_STR_RIGHT) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ADD_LINV] THEN USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:real^2. z$1`) THEN
    REWRITE_TAC[SMT_STR_E1_COMPONENTS] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Every trajectory reaches x$1 > r in the future and x$1 < -r in the past.  *)

let SMT_STR_FWD_REACH = prove
 (`!(V:real->real^2->real^2) r s y.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        (!s x. ~(V s x = vec 0)) /\ &0 <= r
        ==> ?t. &0 <= t /\ r < (vf_rflow (V s) t y)$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(V:real->real^2->real^2) s`; `y:real^2`] SMT_NO_BOUNDED_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN
  DISCH_THEN(LABEL_TAC "nr") THEN
  REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `(abs((y:real^2)$1) + r) + (abs(y$2) + r)` THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `vf_rflow ((V:real->real^2->real^2) s) t y` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `t:real`; `y:real^2`]
    SMT_STR_HEIGHT) THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `t:real`; `y:real^2`]
    SMT_STR_FWD_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "nr" (MP_TAC o SPEC `t:real`) THEN ASM_REAL_ARITH_TAC);;

let SMT_STR_BACK_REACH = prove
 (`!(V:real->real^2->real^2) r s y.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        (!s x. ~(V s x = vec 0)) /\ &0 <= r
        ==> ?t. &0 <= t /\ (vf_rflow (V s) (--t) y)$1 < --r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_REVERSE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rev"))) THEN
  MP_TAC(ISPECL [`\x. --((V:real->real^2->real^2) s x)`; `y:real^2`]
    SMT_NO_BOUNDED_COMPLETE) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_EQ_0] THEN
  USE_THEN "rev" (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN
  DISCH_THEN(LABEL_TAC "nr") THEN
  REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `(abs((y:real^2)$1) + r) + (abs(y$2) + r)` THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `vf_rflow ((V:real->real^2->real^2) s) (--t) y` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `--t:real`; `y:real^2`]
    SMT_STR_HEIGHT) THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `t:real`; `y:real^2`]
    SMT_STR_BACK_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "nr" (MP_TAC o SPEC `t:real`) THEN ASM_REAL_ARITH_TAC);;

let SMT_STR_PSI_ONTO = prove
 (`!(V:real->real^2->real^2) r s y.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        (!s x. ~(V s x = vec 0)) /\ &0 <= r
        ==> ?x:real^2. vf_rflow (V s) (x$1 + r) (vector[--r; x$2]) = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_REVERSE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rev"))) THEN
  ASM_CASES_TAC `(y:real^2)$1 <= --r` THENL
   [EXISTS_TAC `y:real^2` THEN MATCH_MP_TAC SMT_STR_PSI_ID THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `y:real^2`]
    SMT_STR_BACK_REACH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\u:real^1. vf_rflow ((V:real->real^2->real^2) s) (--(drop u)) y`;
                 `vec 0:real^1`; `lift t1`; `--r`; `1`] IVT_DECREASING_COMPONENT_ON_1) THEN
  REWRITE_TAC[DROP_VEC; LIFT_DROP; REAL_NEG_0; DIMINDEX_2; ARITH] THEN
  USE_THEN "id" (fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `\x. --((V:real->real^2->real^2) s x)` SMT_RFLOW_CONTINUOUS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^2` o CONJUNCT2 o CONJUNCT2) THEN
      USE_THEN "rev" (fun th -> REWRITE_TAC[th]) THEN
      MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `vector[drop u - r;
                     (vf_rflow ((V:real->real^2->real^2) s) (--(drop u)) y)$2]:real^2` THEN
  REWRITE_TAC[VECTOR_2; REAL_SUB_ADD] THEN
  SUBGOAL_THEN `vector[--r; (vf_rflow ((V:real->real^2->real^2) s) (--(drop u)) y)$2]:real^2 =
                vf_rflow (V s) (--(drop u)) y` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[REAL_ADD_LINV] THEN
  USE_THEN "id" (fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* A uniform exit time.  Once a trajectory is right of the                  *)
(* ball it moves along e_1; the sets of (s, c) whose trajectory from        *)
(* (-r, c) is right of the ball at time n are open, increase with n and     *)
(* cover the plane, so finitely many cover [0,1] x [-r,r] (Heine-Borel),    *)
(* and stationarity of V outside [0,1] gives all s.  For x$1 >= t0 - r,     *)
(* Psi s x is then the time t0 point translated along e_1.                  *)
(* ------------------------------------------------------------------------- *)

let SMT_STR_EXIT_MONO = prove
 (`!(V:real->real^2->real^2) r s p t0 t1.
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        r < (vf_rflow (V s) t0 p)$1 /\ t0 <= t1
        ==> vf_rflow (V s) t1 p = vf_rflow (V s) t0 p + (t1 - t0) % basis 1 /\
            r < (vf_rflow (V s) t1 p)$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(V:real->real^2->real^2) s` SMT_RFLOW_BASIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "id") (CONJUNCTS_THEN2 (LABEL_TAC "grp")
    (K ALL_TAC))) THEN
  SUBGOAL_THEN `vf_rflow ((V:real->real^2->real^2) s) t1 p =
                vf_rflow (V s) t0 p + (t1 - t0) % basis 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `vf_rflow ((V:real->real^2->real^2) s) t1 p =
                  vf_rflow (V s) (t1 - t0) (vf_rflow (V s) t0 p)` SUBST1_TAC THENL
     [USE_THEN "grp" (fun th -> REWRITE_TAC[th]) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMT_STR_RIGHT THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[SMT_STR_E1_COMPONENTS] THEN ASM_REAL_ARITH_TAC]);;

let SMT_STR_UNIFORM_EXIT = prove
 (`!(V:real->real^2->real^2) r.
        smooth_family (:real^2) V /\ &0 < r /\ (!s x. ~(V s x = vec 0)) /\
        (!s x. r <= norm x ==> V s x = basis 1) /\
        (!s x. s <= &0 ==> V s x = V (&0) x) /\ (!s x. &1 <= s ==> V s x = V (&1) x)
        ==> ?t0. &0 <= t0 /\
                 !s c. abs c <= r ==> r < (vf_rflow (V s) t0 (vector[--r; c]))$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* openness *)
  SUBGOAL_THEN
   `!n. open {q:real^2 | r < (vf_rflow ((V:real->real^2->real^2) (q$1)) (&n)
                                       (vector[--r; q$2]))$1}`
  (LABEL_TAC "open") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `{q:real^2 | r < (vf_rflow ((V:real->real^2->real^2) (q$1)) (&n) (vector[--r; q$2]))$1} =
      {q | (\q:real^2. vf_rflow (V (q$1)) (&n) (vector[--r; q$2])) q IN {x:real^2 | x$1 > r}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN X_GEN_TAC `q:real^2` THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `\q:real^2. &n`; `\q:real^2. q$1`;
                   `\q:real^2. vector[--r; q$2]:real^2`] SMT_STR_FLOW_COMPOSE) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN ANTS_TAC THENL
     [SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_LIFT_COORDINATE] THEN
      MATCH_MP_TAC SMT_SMOOTH_VECTOR2 THEN
      SIMP_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_LIFT_COORDINATE];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
    ALL_TAC] THEN
  (* monotonicity *)
  SUBGOAL_THEN
   `!m n (q:real^2).
        m <= n /\ r < (vf_rflow ((V:real->real^2->real^2) (q$1)) (&m) (vector[--r; q$2]))$1
        ==> r < (vf_rflow (V (q$1)) (&n) (vector[--r; q$2]))$1`
  (LABEL_TAC "mono") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `(q:real^2)$1`;
                   `vector[--r; (q:real^2)$2]:real^2`; `&m`; `&n`] SMT_STR_EXIT_MONO) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the cover *)
  SUBGOAL_THEN
   `!q:real^2. ?n. r < (vf_rflow ((V:real->real^2->real^2) (q$1)) (&n) (vector[--r; q$2]))$1`
  (LABEL_TAC "cover") THENL
   [X_GEN_TAC `q:real^2` THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `(q:real^2)$1`;
                   `vector[--r; (q:real^2)$2]:real^2`] SMT_STR_FWD_REACH) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `t:real` REAL_ARCH_SIMPLE) THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `n:num` THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `(q:real^2)$1`;
                   `vector[--r; (q:real^2)$2]:real^2`; `t:real`; `&n`] SMT_STR_EXIT_MONO) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Heine-Borel on [0,1] x [-r,r] *)
  MP_TAC(ISPEC `interval[vector[&0; --r]:real^2,vector[&1; r]]` COMPACT_EQ_HEINE_BOREL) THEN
  REWRITE_TAC[COMPACT_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\n. {q:real^2 | r < (vf_rflow ((V:real->real^2->real^2) (q$1)) (&n)
                                         (vector[--r; q$2]))$1}) (:num)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN USE_THEN "open" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    USE_THEN "cover" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\n. {q:real^2 | r < (vf_rflow ((V:real->real^2->real^2) (q$1)) (&n)
                                               (vector[--r; q$2]))$1}`;
                 `(:num)`; `ff:(real^2->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ns:num->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `ns:num->bool` num_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN
   `!q:real^2. q IN interval[vector[&0; --r],vector[&1; r]]
               ==> r < (vf_rflow ((V:real->real^2->real^2) (q$1)) (&N) (vector[--r; q$2]))$1`
  (LABEL_TAC "unif") THENL
   [X_GEN_TAC `q:real^2` THEN DISCH_TAC THEN
    UNDISCH_TAC `interval[vector[&0; --r]:real^2,vector[&1; r]] SUBSET
                 UNIONS (ff:(real^2->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `m:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the uniform time *)
  EXISTS_TAC `&N` THEN REWRITE_TAC[REAL_POS] THEN
  SUBGOAL_THEN
   `!s c. &0 <= s /\ s <= &1 /\ abs c <= r
          ==> r < (vf_rflow ((V:real->real^2->real^2) s) (&N) (vector[--r; c]))$1`
  (LABEL_TAC "mid") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "unif" (MP_TAC o SPEC `vector[s; c]:real^2`) THEN
    REWRITE_TAC[VECTOR_2] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `c:real`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `s <= &0` THENL
   [SUBGOAL_THEN `(V:real->real^2->real^2) s = V (&0)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "mid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= s` THENL
   [SUBGOAL_THEN `(V:real->real^2->real^2) s = V (&1)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "mid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    USE_THEN "mid" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let SMT_STR_PSI_FAR = prove
 (`!(V:real->real^2->real^2) r t0 s (x:real^2).
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        (!s c. abs c <= r ==> r < (vf_rflow (V s) t0 (vector[--r; c]))$1) /\
        t0 - r <= x$1
        ==> vf_rflow (V s) (x$1 + r) (vector[--r; x$2]) =
            vf_rflow (V s) t0 (vector[--r; x$2]) + ((x$1 + r) - t0) % basis 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs((x:real^2)$2) <= r` THENL
   [MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`;
                   `vector[--r; (x:real^2)$2]:real^2`; `t0:real`; `(x:real^2)$1 + r`]
      SMT_STR_EXIT_MONO) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    SUBGOAL_THEN `r <= abs((x:real^2)$2)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`;
                   `vector[--r; (x:real^2)$2]:real^2`; `t0:real`] SMT_STR_HIGH) THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`;
                   `vector[--r; (x:real^2)$2]:real^2`; `(x:real^2)$1 + r`] SMT_STR_HIGH) THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness (a differentiable f with f = I left of the ball               *)
(* and f' e_1 = V s o f maps the line t |-> (t - r, x$2) onto the           *)
(* trajectory from (-r, x$2), by uniqueness of solutions) and S3c.          *)
(* ------------------------------------------------------------------------- *)

let SMT_STR_PSI_UNIQUE = prove
 (`!(V:real->real^2->real^2) r s (f:real^2->real^2).
        smooth_family (:real^2) V /\ (!s x. r <= norm x ==> V s x = basis 1) /\
        (!x. f differentiable at x) /\ (!x. x$1 <= --r ==> f x = x) /\
        (!x. frechet_derivative f (at x) (basis 1) = V s (f x))
        ==> !x. f x = vf_rflow (V s) (x$1 + r) (vector[--r; x$2])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "fd") (CONJUNCTS_THEN2 (LABEL_TAC "fl") (LABEL_TAC "fe"))))) THEN
  X_GEN_TAC `x:real^2` THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuously_differentiable 1 (:real^2) ((V:real->real^2->real^2) s)`
  ASSUME_TAC THENL [ASM_MESON_TAC[smooth_map_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(V:real->real^2->real^2) s`; `(:real^2)`; `(:real^1)`;
                 `\t:real^1. (f:real^2->real^2)(vector[--r; (x:real^2)$2] + drop t % basis 1)`;
                 `vec 0:real^1`] ODE_VF_UNIQUE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; IS_INTERVAL_UNIV; WITHIN_UNIV; VECTOR_SUB_RZERO;
                  DROP_VEC; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real^1` THEN
    MP_TAC(ISPECL [`\t:real^1. vector[--r; (x:real^2)$2] + drop t % basis 1`;
                   `f:real^2->real^2`; `basis 1:real^2`;
                   `frechet_derivative (f:real^2->real^2)
                      (at (vector[--r; (x:real^2)$2] + drop t % basis 1))`; `t:real^1`]
      ODE_HAS_VECTOR_DERIVATIVE_CHAIN) THEN
    REWRITE_TAC[SMT_STR_LINE_DERIV; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    USE_THEN "fd" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fe" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^2)(vector[--r; (x:real^2)$2]) = vector[--r; x$2]`
  SUBST1_TAC THENL
   [USE_THEN "fl" MATCH_MP_TAC THEN REWRITE_TAC[VECTOR_2; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift((x:real^2)$1 + r)`) THEN
  REWRITE_TAC[LIFT_DROP; SMT_STR_START_SHIFT; vf_rflow]);;

(* S3c.                                                                      *)

let SMT_STRAIGHTENING = prove
 (`SMT_STRAIGHTENING_STATEMENT`,
  REWRITE_TAC[SMT_STRAIGHTENING_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`V:real->real^2->real^2`; `r:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_COMPLETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM vf_rflow] THEN
  MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`] SMT_STR_UNIFORM_EXIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\s (x:real^2). vf_rflow ((V:real->real^2->real^2) s) (x$1 + r)
                                       (vector[--r; x$2])` THEN
  EXISTS_TAC `\s (y:real^2). @x:real^2. vf_rflow ((V:real->real^2->real^2) s) (x$1 + r)
                                                  (vector[--r; x$2]) = y` THEN
  EXISTS_TAC `\s c. (vf_rflow ((V:real->real^2->real^2) s) t0 (vector[--r; c]))$1 +
                    r - t0` THEN
  EXISTS_TAC `\s c. (vf_rflow ((V:real->real^2->real^2) s) t0 (vector[--r; c]))$2` THEN
  EXISTS_TAC `t0 - r` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* a diffeo_isotopy *)
    MATCH_MP_TAC SMT_FAMILY_INVERSE_SMOOTH THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMT_STR_PSI_SMOOTH THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^2`] THEN
      MATCH_MP_TAC SMT_STR_PSI_INJ THEN
      MAP_EVERY EXISTS_TAC [`V:real->real^2->real^2`; `r:real`; `s:real`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:real^2`] THEN CONV_TAC SELECT_CONV THEN
      MATCH_MP_TAC SMT_STR_PSI_ONTO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^2`; `h:real^2`] THEN DISCH_TAC THEN
      MATCH_MP_TAC SMT_STR_PSI_DERIV_INJ THEN
      MAP_EVERY EXISTS_TAC [`V:real->real^2->real^2`; `r:real`; `s:real`; `x:real^2`] THEN
      ASM_REWRITE_TAC[]];
    (* e_1 is pushed to V s *)
    MAP_EVERY X_GEN_TAC [`s:real`; `x:real^2`] THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `x:real^2`]
      SMT_STR_PSI_E1) THEN
    ASM_REWRITE_TAC[];
    (* the identity left of the ball and outside the strip *)
    MAP_EVERY X_GEN_TAC [`s:real`; `x:real^2`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `x:real^2`]
      SMT_STR_PSI_ID) THEN
    ASM_REWRITE_TAC[];
    (* a translation for large x$1 *)
    MAP_EVERY X_GEN_TAC [`s:real`; `x:real^2`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `t0:real`; `s:real`; `x:real^2`]
      SMT_STR_PSI_FAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC;
    (* uniqueness *)
    MAP_EVERY X_GEN_TAC [`s:real`; `f:real^2->real^2`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:real->real^2->real^2`; `r:real`; `s:real`; `f:real^2->real^2`]
      SMT_STR_PSI_UNIQUE) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The S3 assembly. S3a (SMT_SMOOTH_ANGLE, pc_smt_rn), S3c and S3d           *)
(* (SMT_END_CORRECTION, pc_smt_planar) give the planar isotopy theorem S3;   *)
(* with the pole step (pc_smt_pole) and the stereographic transport          *)
(* (pc_smt_sphere) they give S2 and Smale's theorem in radial form S1, and   *)
(* with S1 the gluing of balls and the twisted spheres of pc_smt_glue        *)
(* follow.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SMT_PLANAR_ISOTOPY = prove
 (`SMT_PLANAR_ISOTOPY_STATEMENT`,
  MATCH_MP_TAC SMT_PLANAR_FROM_PARTS THEN
  REWRITE_TAC[SMT_SMOOTH_ANGLE; SMT_STRAIGHTENING; SMT_END_CORRECTION]);;

let SMT_SPHERE_ISOTOPY = prove
 (`SMT_SPHERE_ISOTOPY_STATEMENT`,
  MATCH_MP_TAC SMT_SPHERE_ISOTOPY_FROM_PARTS THEN
  REWRITE_TAC[SMT_SPHERE_POLE; SMT_PLANAR_ISOTOPY; SMT_STEREO_TRANSPORT]);;

let SMT_SMALE_RADIAL = prove
 (`SMT_SMALE_RADIAL_STATEMENT`,
  MATCH_MP_TAC SMT_SMALE_FROM_PLANAR THEN REWRITE_TAC[SMT_PLANAR_ISOTOPY]);;

let SMT_GLUE_BALL_ALL = prove
 (`!u:A->bool v:B->bool. SMT_GLUE_BALL_STATEMENT u v`,
  MATCH_ACCEPT_TAC(MP SMT_GLUE_BALL SMT_SMALE_RADIAL));;

let SMT_TWISTED_SPHERE_ALL = prove
 (`!u:A->bool. SMT_TWISTED_SPHERE_STATEMENT u`,
  MATCH_ACCEPT_TAC(MP SMT_TWISTED_SPHERE SMT_SMALE_RADIAL));;

